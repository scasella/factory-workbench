// §9.4 semantic mutants of the PROTECTED KERNEL. Each mutant patches a copy of
// the kernel source, rebuilds the executable with the pinned toolchain, and
// runs a targeted scenario against the mutated binary. A mutant is KILLED only
// if the intended guard/test observes the unsafe behaviour (a compile error is
// NOT a kill). If Factory/Proofs.lean exists, we additionally record whether
// the kernel proofs still compile against the mutant (a proof kill).
// Timeouts are reported as inconclusive, never as killed.
import { test } from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { DatabaseSync } from "node:sqlite";
import { KernelClient, fileDigest } from "../../../apps/control/kernel.ts";
import { REPO_ROOT } from "../../../apps/control/config.ts";
import { templateState } from "../harness.ts";

const sha = (s: string) => createHash("sha256").update(s).digest("hex");
const env = { ...process.env, PATH: `${process.env.HOME}/.elan/bin:${process.env.PATH}` };

interface Mutant { id: string; file: string; from: string; to: string; scenario: (k: K) => Promise<string | null> }

/** In-memory driver over a kernel binary (no SQLite): returns violation text or null. */
class K {
  st: any;
  kc: KernelClient;
  tick = 0;
  constructor(kc: KernelClient, st: any) {
    this.kc = kc;
    this.st = st;
    this.tick = Number(st.clock);
  }
  async ap(actor: any, command: any): Promise<any> {
    this.tick += 1;
    const r = await this.kc.query({ op: "apply", state: this.st, envelope: { actor, epoch: this.st.ctrl_epoch, tick: String(this.tick), command } as any });
    if (r.accepted === true) this.st = (r.transition as any).state;
    return r;
  }
  job(id: string) {
    const j = this.st.jobs.find((x: any) => x.id === id);
    if (!j) throw new Error(`scenario setup failed: no job ${id}`);
    return j;
  }
  env(jobId: string, step: string, over: any = {}) {
    const j = this.job(jobId);
    const att = [...j.attempts].reverse().find((a: any) => a.step === step);
    const wf = this.st.releases.find((r: any) => r.digest === j.release).workflows.find((w: any) => w.kind === j.kind);
    const role = wf.steps.find((s: any) => s.id === step).role;
    return { result: sha(`r${jobId}${step}${att.gen}`), model_outcome: "pass", trusted_outcome: "pass",
      produced: role === "build" ? sha(`p${j.subject}`) : role === "materialize" ? sha(`s${jobId}`) : null,
      exports: role === "build" ? this.st.releases[0].workflows : [], contract: ["build", "prove"].includes(role) ? this.st.contract : "",
      fingerprint: att.fingerprint, ...over };
  }
  async run(jobId: string, step: string, over: any = {}) {
    const s = await this.ap(CO, { type: "start_attempt", job: jobId, step, fingerprint: sha(`fp${step}`) });
    if (s.accepted !== true) return s;
    const gen = this.job(jobId).attempts.at(-1).gen;
    await this.ap(SUP, { type: "observe_process_started", job: jobId, step, gen, container: "c" });
    const wf = this.st.releases.find((r: any) => r.digest === this.job(jobId).release).workflows.find((w: any) => w.kind === this.job(jobId).kind);
    const role = wf.steps.find((x: any) => x.id === step).role;
    const v = role === "build" || role === "prove";
    return this.ap(v ? VER : SUP, { type: v ? "record_verification" : "commit_result", job: jobId, step, gen, result: this.env(jobId, step, over) });
  }
  async runAll(jobId: string, over: Record<string, any> = {}) {
    for (const s of this.job(jobId).steps.map((x: any) => x.id)) if (!this.job(jobId).steps.find((x: any) => x.id === s).accepted) await this.run(jobId, s, over[s] ?? {});
  }
  async publish(tag: string, workflows: any[]) {
    const c = `c${tag}`;
    await this.ap(OP, { type: "create_change", change: c, request: sha("rq"), author_job: `${c}a`, budget: `${c}b`, attempt_limit: "99", revision_limit: "3" });
    await this.runAll(`${c}a`, { materialize: { produced: sha(`src${tag}`) } });
    await this.ap(CO, { type: "register_candidate", change: c, author_job: `${c}a`, eval_job: `${c}e`, source: sha(`src${tag}`) });
    await this.runAll(`${c}e`, { build: { exports: workflows, produced: sha(`pay${tag}`) } });
    await this.ap(CO, { type: "publish_release", job: `${c}e`, release: sha(`rel${tag}`), assets: [] });
    return sha(`rel${tag}`);
  }
}
const OP = { type: "operator", name: "m" };
const CO = { type: "coordinator" };
const SUP = { type: "supervisor" };
const VER = { type: "verifier" };
const audit = (k: K, id: string) => k.ap(OP, { type: "create_job", job: id, kind: "package_audit", input: sha("fx"), subject: sha("fx"), release: null, budget: `${id}b`, limit: "50" });
const parallel = (ws: any[]) => ws.map((w: any) => {
  const x = JSON.parse(JSON.stringify(w));
  if (x.kind !== "change_author") {
    x.steps.find((s: any) => s.id === "refute").after = [];
    x.max_parallel = "2";
  }
  return x;
});

const MUTANTS: Mutant[] = [
  {
    id: "accept_stale_result", file: "Factory/Kernel.lean",
    from: "  check (st.current == some gen) .notCurrentAttempt\n  check a.status.live .notCurrentAttempt",
    to: "  check true .notCurrentAttempt\n  check true .notCurrentAttempt",
    scenario: async (k) => {
      // A is superseded (transport failure → retry B) but its success arrives while A's lease is still valid.
      await audit(k, "j");
      await k.ap(CO, { type: "start_attempt", job: "j", step: "build", fingerprint: sha("a") });
      const genA = k.job("j").attempts[0].gen;
      await k.ap(SUP, { type: "observe_process_started", job: "j", step: "build", gen: genA, container: "cA" });
      await k.ap(SUP, { type: "fail_attempt", job: "j", step: "build", gen: genA });
      const b = await k.ap(CO, { type: "start_attempt", job: "j", step: "build", fingerprint: sha("a") });
      if (b.accepted !== true) throw new Error("scenario setup: retry B not authorized");
      const late = await k.ap(VER, { type: "record_verification", job: "j", step: "build", gen: genA, result: k.env("j", "build") });
      return late.accepted === true ? "result from a superseded attempt accepted" : null;
    },
  },
  {
    id: "start_after_cancel", file: "Factory/Access.lean",
    from: "def dispatchable (st : JobStatus) : Bool := st == .queued || st == .running",
    to: "def dispatchable (st : JobStatus) : Bool := st == .queued || st == .running || st == .cancelled",
    scenario: async (k) => {
      await audit(k, "j");
      await k.ap(OP, { type: "cancel_job", job: "j" });
      const s = await k.ap(CO, { type: "start_attempt", job: "j", step: "build", fingerprint: sha("b") });
      return s.accepted === true ? "authority granted after cancellation" : null;
    },
  },
  {
    id: "publish_without_refutation", file: "Factory/Kernel.lean",
    from: "  let rf ← need (gateEvidence j w .refute) .gateFailed",
    to: "  let rf ← need (gateEvidence j w .reproduce) .gateFailed",
    scenario: async (k) => {
      await k.ap(OP, { type: "create_change", change: "c", request: sha("r"), author_job: "ca", budget: "cb", attempt_limit: "99", revision_limit: "3" });
      await k.runAll("ca", { materialize: { produced: sha("s") } });
      await k.ap(CO, { type: "register_candidate", change: "c", author_job: "ca", eval_job: "ce", source: sha("s") });
      await k.runAll("ce", { refute: { model_outcome: "fail" } });
      // the job is failed; force the gate path with a forged-succeeded state as an attacker controlling job status would
      const st = JSON.parse(JSON.stringify(k.st));
      st.jobs.find((j: any) => j.id === "ce").status = "succeeded";
      const rf = st.jobs.find((j: any) => j.id === "ce").steps.find((s: any) => s.id === "refute");
      rf.accepted = null;
      rf.status = "pending";
      k.st = st;
      const p = await k.ap(CO, { type: "publish_release", job: "ce", release: sha("x"), assets: [] });
      return p.accepted === true ? "release published without refutation evidence" : null;
    },
  },
  {
    id: "approval_for_different_digest", file: "Factory/Kernel.lean",
    from: "  check (a.release == rel && a.expectedBase == expected && a.contract == s.contract) .approvalMismatch",
    to: "  check (a.expectedBase == expected && a.contract == s.contract) .approvalMismatch",
    scenario: async (k) => {
      const P0 = k.st.active;
      const a = await k.publish("a", parallel(k.st.releases[0].workflows));
      const b = await k.publish("b", parallel(k.st.releases[0].workflows));
      await k.ap(OP, { type: "record_approval", approval: "ap", release: a, expected_base: P0 });
      const r = await k.ap(OP, { type: "activate_release", release: b, expected_active: P0, approval: "ap" });
      return r.accepted === true ? "activated a release with an approval for a different digest" : null;
    },
  },
  {
    id: "drop_evidence_on_migration", file: "Factory/Migration.lean",
    from: "    | some st => if st.accepted.isSome then st else { st with status := .pending, current := none }",
    to: "    | some st => { st with status := .pending, current := none, accepted := none }",
    scenario: async (k) => {
      const P0 = k.st.active;
      await audit(k, "j");
      await k.run("j", "build");
      await k.run("j", "prove");
      const p1 = await k.publish("p1", parallel(k.st.releases[0].workflows));
      await k.ap(OP, { type: "record_approval", approval: "ap", release: p1, expected_base: P0 });
      await k.ap(OP, { type: "activate_release", release: p1, expected_active: P0, approval: "ap" });
      await k.ap(OP, { type: "pause_job", job: "j" });
      await k.ap(CO, { type: "acknowledge_quiescence", job: "j", containers_clear: true });
      const before = JSON.stringify(k.job("j").steps.find((s: any) => s.id === "build").accepted);
      await k.ap(OP, { type: "migrate_job", job: "j", target: p1, expected_revision: k.job("j").revision });
      const after = JSON.stringify(k.job("j").steps.find((s: any) => s.id === "build").accepted);
      return before !== after ? "migration dropped completed evidence" : null;
    },
  },
  {
    id: "activation_mutates_pinned_jobs", file: "Factory/Kernel.lean",
    from: "  ok { s with active := some rel, activations := s.activations ++ [act] }",
    to: "  ok { s with active := some rel, activations := s.activations ++ [act], jobs := s.jobs.map (fun j => { j with release := rel }) }",
    scenario: async (k) => {
      const P0 = k.st.active;
      await audit(k, "j");
      const p1 = await k.publish("p1", parallel(k.st.releases[0].workflows));
      await k.ap(OP, { type: "record_approval", approval: "ap", release: p1, expected_base: P0 });
      await k.ap(OP, { type: "activate_release", release: p1, expected_active: P0, approval: "ap" });
      return k.job("j").release !== P0 ? "changing the default moved an existing pinned job" : null;
    },
  },
];

function buildMutant(m: Mutant): { dir: string; bin: string; ok: boolean; log: string; proofsCompile: boolean | null } {
  const src = path.join(REPO_ROOT, "protected/lean");
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), `fw-mut-${m.id}-`));
  fs.cpSync(src, dir, { recursive: true, filter: (p) => !p.includes(`${path.sep}.lake${path.sep}`) || p.includes(`${path.sep}.lake${path.sep}packages`) });
  // reuse compiled artifacts of unchanged modules to keep builds fast
  if (fs.existsSync(path.join(src, ".lake"))) fs.cpSync(path.join(src, ".lake"), path.join(dir, ".lake"), { recursive: true });
  const f = path.join(dir, m.file);
  const text = fs.readFileSync(f, "utf8");
  assert.ok(text.includes(m.from), `mutant ${m.id}: patch anchor not found in ${m.file} (kernel changed; update the mutant)`);
  fs.writeFileSync(f, text.replace(m.from, m.to));
  const r = spawnSync("lake", ["build", "factory-kernel"], { cwd: dir, env, encoding: "utf8", timeout: 1_800_000 });
  let proofsCompile: boolean | null = null;
  if (r.status === 0 && fs.existsSync(path.join(dir, "Factory/Proofs.lean"))) {
    const p = spawnSync("lake", ["build", "Factory.Proofs"], { cwd: dir, env, encoding: "utf8", timeout: 3_600_000 });
    proofsCompile = p.status === 0;
  }
  return { dir, bin: path.join(dir, ".lake/build/bin/factory-kernel"), ok: r.status === 0, log: (r.stdout ?? "") + (r.stderr ?? ""), proofsCompile };
}

test("§9.4 kernel semantic mutants are killed by their intended guard/test (and proof, when present)", async () => {
  const tpl = await templateState();
  const db = new DatabaseSync(path.join(tpl, "workbench.sqlite"), { readOnly: true });
  const init = JSON.parse((db.prepare("SELECT state FROM kstate WHERE id = 1").get() as any).state);
  db.close();
  const report: any[] = [];
  // Control: the unmutated kernel passes every scenario (otherwise "kills" would be meaningless).
  const real = path.join(REPO_ROOT, "protected/lean/.lake/build/bin/factory-kernel");
  const rk = new KernelClient(real, fileDigest(real));
  for (const m of MUTANTS) {
    const v = await m.scenario(new K(rk, JSON.parse(JSON.stringify(init))));
    assert.equal(v, null, `control: unmutated kernel must pass scenario ${m.id} (got: ${v})`);
  }
  rk.stop();
  for (const m of MUTANTS) {
    const b = buildMutant(m);
    if (!b.ok) {
      report.push({ id: m.id, status: "compile_error (not a kill)", detail: b.log.split("\n").filter((l) => /error/.test(l)).slice(0, 3) });
      continue;
    }
    const kc = new KernelClient(b.bin, fileDigest(b.bin), 60_000);
    let verdict: string | null;
    try {
      verdict = await m.scenario(new K(kc, JSON.parse(JSON.stringify(init))));
    } finally {
      kc.stop();
    }
    report.push({ id: m.id, status: verdict ? "killed_by_test" : "SURVIVED", observed: verdict,
      proof_kill: b.proofsCompile === null ? "no Factory/Proofs.lean" : b.proofsCompile ? "proofs still compile (NOT killed by proof)" : "killed_by_proof (Proofs.lean fails against mutant)" });
    fs.rmSync(b.dir, { recursive: true, force: true });
  }
  fs.mkdirSync(path.join(REPO_ROOT, "docs"), { recursive: true });
  fs.writeFileSync(path.join(REPO_ROOT, "docs/kernel-mutants.json"), JSON.stringify(report, null, 2) + "\n");
  console.log(JSON.stringify(report, null, 2));
  for (const r of report) assert.equal(r.status, "killed_by_test", `mutant ${r.id}: ${r.status}`);
});
