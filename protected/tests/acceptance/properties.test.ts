// A24: generated valid/invalid command traces against the ACTUAL executable
// kernel, checked after every step by (a) the kernel's own invariant checker
// and (b) independent TS oracle expectations. Seeds are fixed and printed;
// failures are minimized by delta debugging and written to docs/.
import { test } from "node:test";
// (fs/path imported below are also used to write docs/a24-coverage.json)
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { createHash } from "node:crypto";
import { KernelClient, fileDigest } from "../../../apps/control/kernel.ts";
import { REPO_ROOT } from "../../../apps/control/config.ts";
import type { Json } from "../../../packages/protocol/json.ts";
import { templateState } from "../harness.ts";
import { DatabaseSync } from "node:sqlite";

const sha = (s: string) => createHash("sha256").update(s).digest("hex");

class Rng {
  s: number;
  constructor(seed: number) {
    this.s = seed >>> 0 || 1;
  }
  next(): number {
    // xorshift32
    let x = this.s;
    x ^= x << 13;
    x ^= x >>> 17;
    x ^= x << 5;
    this.s = x >>> 0;
    return this.s;
  }
  int(n: number): number {
    return this.next() % n;
  }
  pick<T>(xs: T[]): T {
    return xs[this.int(xs.length)];
  }
  chance(p: number): boolean {
    return this.int(1000) < p * 1000;
  }
}

const ACT = { op: { type: "operator", name: "prop" }, co: { type: "coordinator" }, sup: { type: "supervisor" }, ver: { type: "verifier" } };
const STEPS = ["build", "prove", "reproduce", "refute", "summarize", "author", "materialize", "nope"];

/** Generate the next envelope from the current state (mostly plausible, sometimes invalid). */
function gen(r: Rng, st: any, tick: number, n: number): any {
  const jobs = st.jobs as any[];
  const jobIds = [...jobs.map((j) => j.id), "ghost"];
  const releases = [...st.releases.map((x: any) => x.digest), sha("unknown-release")];
  const anyJob = () => r.pick(jobIds);
  const liveAtt = jobs.flatMap((j) => j.attempts.filter((a: any) => ["authorized", "starting", "running"].includes(a.status)).map((a: any) => ({ j, a })));
  const anyAtt = jobs.flatMap((j) => j.attempts.map((a: any) => ({ j, a })));
  const wrongActor = r.chance(0.05);
  const actor = (a: any) => (wrongActor ? r.pick(Object.values(ACT)) : a);
  const epoch = r.chance(0.03) ? String(Number(st.ctrl_epoch) + 5) : st.ctrl_epoch;
  const env = (a: any, command: any) => ({ actor: actor(a), epoch, tick: String(tick), command });
  const k = r.int(100);
  const envFor = (j: any, step: string, a: any) => {
    const wf = st.releases.find((x: any) => x.digest === j.release)?.workflows.find((w: any) => w.kind === j.kind);
    const role = wf?.steps.find((s: any) => s.id === step)?.role ?? "build";
    const outcome = r.chance(0.85) ? "pass" : r.pick(["fail", "inconclusive"]);
    return {
      role,
      result: {
        result: sha(`res${n}`), model_outcome: ["build", "prove", "materialize"].includes(role) ? "pass" : outcome,
        trusted_outcome: ["build", "prove", "materialize", "reproduce"].includes(role) ? (r.chance(0.9) ? "pass" : "fail") : "pass",
        produced: role === "build" ? sha(`payload${n}`) : role === "materialize" ? sha(`src${r.int(3)}`) : null,
        exports: role === "build" ? st.releases[0].workflows : [], contract: ["build", "prove"].includes(role) ? st.contract : "",
        fingerprint: r.chance(0.95) ? a.fingerprint : sha("wrong-fp"),
      },
    };
  };
  if (k < 8) return env(ACT.op, { type: "create_job", job: `j${r.int(6)}`, kind: "package_audit", input: sha("fx"), subject: sha("fx"),
    release: r.chance(0.2) ? r.pick(releases) : null, budget: `b${n}`, limit: String(1 + r.int(12)) });
  if (k < 30) {
    const j = r.pick(jobs.length ? jobs : [{ id: "ghost", steps: [] }]);
    const ready = j.steps?.filter((s: any) => s.status === "pending").map((s: any) => s.id) ?? [];
    return env(ACT.co, { type: "start_attempt", job: j.id, step: ready.length && r.chance(0.8) ? r.pick(ready) : r.pick(STEPS), fingerprint: sha(`fp${n}`) });
  }
  if (k < 36 && anyAtt.length) {
    const { j, a } = r.chance(0.8) && liveAtt.length ? r.pick(liveAtt) : r.pick(anyAtt);
    return env(ACT.sup, { type: "observe_process_started", job: j.id, step: a.step, gen: a.gen, container: `c${n}` });
  }
  if (k < 40 && anyAtt.length) {
    const { j, a } = r.pick(anyAtt);
    return env(ACT.sup, { type: "heartbeat", job: j.id, step: a.step, gen: a.gen });
  }
  if (k < 62 && anyAtt.length) {
    const { j, a } = r.chance(0.75) && liveAtt.length ? r.pick(liveAtt) : r.pick(anyAtt);
    const e = envFor(j, a.step, a);
    const verifier = ["build", "prove"].includes(e.role);
    const viaV = r.chance(0.93) ? verifier : !verifier;
    return env(viaV ? ACT.ver : ACT.sup, { type: viaV ? "record_verification" : "commit_result", job: j.id, step: a.step,
      gen: r.chance(0.95) ? a.gen : String(Number(a.gen) + 1), result: e.result });
  }
  if (k < 66 && anyAtt.length) {
    const { j, a } = r.pick(anyAtt);
    return env(ACT.sup, { type: "fail_attempt", job: j.id, step: a.step, gen: a.gen });
  }
  if (k < 70 && anyAtt.length) {
    const { j, a } = r.pick(anyAtt);
    return env(ACT.co, { type: "expire_attempt", job: j.id, step: a.step, gen: a.gen });
  }
  if (k < 74) return env(ACT.op, { type: "pause_job", job: anyJob() });
  if (k < 78) return env(ACT.co, { type: "acknowledge_quiescence", job: anyJob(), containers_clear: r.chance(0.8) });
  if (k < 81) return env(ACT.op, { type: "resume_job", job: anyJob() });
  if (k < 84) return env(ACT.op, { type: "cancel_job", job: anyJob() });
  if (k < 86) return env(ACT.op, { type: "create_change", change: `c${r.int(3)}`, request: sha("req"), author_job: `ca${n}`, budget: `cb${n}`, attempt_limit: String(5 + r.int(20)), revision_limit: String(1 + r.int(3)) });
  if (k < 88) {
    const cs = st.changes as any[];
    const c = cs.length ? r.pick(cs) : { id: "c9", jobs: ["x"] };
    return env(ACT.co, { type: "register_candidate", change: c.id, author_job: r.pick(c.jobs), eval_job: `ce${n}`, source: sha(`src${r.int(3)}`) });
  }
  if (k < 90) return env(ACT.co, { type: "publish_release", job: anyJob(), release: sha(`rel${n}`), assets: [] });
  if (k < 91) return env(ACT.co, { type: "publish_report", job: anyJob(), report: sha(`rep${n}`) });
  if (k < 93) return env(ACT.op, { type: "record_approval", approval: `a${r.int(4)}`, release: r.pick(releases), expected_base: st.active ?? releases[0] });
  if (k < 94) return env(ACT.op, { type: "revoke_approval", approval: `a${r.int(4)}` });
  if (k < 96) return env(ACT.op, { type: "activate_release", release: r.pick(releases), expected_active: r.chance(0.8) ? st.active : r.pick(releases), approval: `a${r.int(4)}` });
  if (k < 98) {
    const j = jobs.length ? r.pick(jobs) : { id: "ghost", revision: "0" };
    return env(ACT.op, { type: "migrate_job", job: j.id, target: r.pick(releases), expected_revision: r.chance(0.8) ? j.revision : "999" });
  }
  return { actor: ACT.co, epoch: String(Number(st.ctrl_epoch) + 1), tick: String(tick), command: { type: "recover_controller" } };
}

type Violation = string;

/** Independent TS oracle for transition properties. */
function oracle(pre: any, post: any, e: any, effects: any[]): Violation[] {
  const v: Violation[] = [];
  const find = (s: any, id: string) => s.jobs.find((j: any) => j.id === id);
  for (const j of pre.jobs) {
    const j2 = find(post, j.id);
    if (!j2) {
      v.push(`job ${j.id} disappeared`);
      continue;
    }
    if (e.command.type !== "migrate_job" && j2.release !== j.release) v.push(`K08: job ${j.id} release changed by ${e.command.type}`);
    for (const s of j.steps) {
      if (s.accepted) {
        const s2 = j2.steps.find((x: any) => x.id === s.id);
        if (!s2 || JSON.stringify(s2.accepted) !== JSON.stringify(s.accepted)) v.push(`K02: accepted result of ${j.id}/${s.id} changed`);
      }
    }
    if (["cancelled", "succeeded", "failed", "blocked"].includes(j.status)) {
      if (j2.status !== j.status) v.push(`K05: terminal status of ${j.id} changed`);
      if (j2.attempts.length !== j.attempts.length) v.push(`K05: new authority for terminal job ${j.id}`);
      for (const s of j2.steps) {
        const s1 = j.steps.find((x: any) => x.id === s.id);
        if (s.accepted && !s1?.accepted) v.push(`K05: new acceptance for terminal job ${j.id}`);
      }
    }
  }
  for (const eff of effects) {
    if (eff.kind === "launch") {
      const jPre = find(pre, eff.job);
      const jPost = find(post, eff.job);
      if (jPre?.attempts.some((a: any) => a.step === eff.step && a.gen === eff.gen)) v.push(`K12: launch for pre-existing attempt ${eff.id}`);
      const a = jPost?.attempts.find((x: any) => x.step === eff.step && x.gen === eff.gen);
      if (!a || a.status !== "authorized") v.push(`K12: launch ${eff.id} without authorized attempt`);
    }
  }
  if (e.command.type === "activate_release") {
    const ap = pre.approvals.find((a: any) => a.id === e.command.approval);
    if (!ap || ap.revoked || ap.release !== e.command.release || pre.active !== e.command.expected_active) v.push("K07: activation without live matching approval");
    if (JSON.stringify(pre.jobs) !== JSON.stringify(post.jobs)) v.push("K08: activation changed jobs");
  }
  return v;
}

/** Deterministic valid prefix: publish a P1-like release and record an approval,
 *  so random suffixes can exercise activation, migration and publication paths. */
async function prefix(kernel: KernelClient, st0: any, tick0: number): Promise<any[]> {
  let st = st0;
  let tick = tick0;
  const out: any[] = [];
  const ap = async (actor: any, command: any) => {
    tick += 10;
    const e = { actor, epoch: st.ctrl_epoch, tick: String(tick), command };
    out.push(e);
    const r = await kernel.query({ op: "apply", state: st, envelope: e as any });
    if (r.accepted === true) st = (r.transition as any).state;
    return r;
  };
  const run = async (job: string, step: string, over: any = {}) => {
    await ap(ACT.co, { type: "start_attempt", job, step, fingerprint: sha(`pfx${job}${step}`) });
    const j = st.jobs.find((x: any) => x.id === job);
    const a = j.attempts.at(-1);
    await ap(ACT.sup, { type: "observe_process_started", job, step, gen: a.gen, container: "pfx" });
    const wf = st.releases.find((r: any) => r.digest === j.release).workflows.find((w: any) => w.kind === j.kind);
    const role = wf.steps.find((x: any) => x.id === step).role;
    const v = role === "build" || role === "prove";
    await ap(v ? ACT.ver : ACT.sup, { type: v ? "record_verification" : "commit_result", job, step, gen: a.gen, result: {
      result: sha(`pr${job}${step}`), model_outcome: "pass", trusted_outcome: "pass",
      produced: role === "build" ? sha(`pp${job}`) : role === "materialize" ? sha("psrc") : null,
      exports: role === "build" ? st.releases[0].workflows.map((w: any) => {
        const x = JSON.parse(JSON.stringify(w));
        if (x.kind !== "change_author") { x.steps.find((q: any) => q.id === "refute").after = []; x.max_parallel = "2"; }
        return x;
      }) : [], contract: v ? st.contract : "", fingerprint: a.fingerprint, ...over } });
  };
  await ap(ACT.op, { type: "create_change", change: "pc", request: sha("prq"), author_job: "pca", budget: "pcb", attempt_limit: "40", revision_limit: "3" });
  for (const s2 of ["author", "materialize"]) await run("pca", s2);
  await ap(ACT.co, { type: "register_candidate", change: "pc", author_job: "pca", eval_job: "pce", source: sha("psrc") });
  for (const s2 of ["build", "prove", "reproduce", "refute", "summarize"]) await run("pce", s2);
  await ap(ACT.co, { type: "publish_release", job: "pce", release: sha("prel"), assets: st.releases[0].assets });
  await ap(ACT.op, { type: "record_approval", approval: "a1", release: sha("prel"), expected_base: st.active });
  return out;
}

async function runTrace(kernel: KernelClient, init: any, envs: any[] | null, seed: number, length: number, acceptedKinds?: Map<string, number>):
  Promise<{ trace: any[]; failure: string | null; accepted: number }> {
  const r = new Rng(seed);
  let st = init;
  let tick = Number(init.clock);
  const trace: any[] = [];
  let accepted = 0;
  const pre = !envs && seed % 2 === 0 ? await prefix(kernel, init, tick) : [];
  const total = envs ? envs.length : pre.length + length;
  for (let n = 0; n < total; n++) {
    const e = envs ? envs[n] : n < pre.length ? pre[n] : gen(r, st, (tick += r.chance(0.1) ? 40_000 : r.int(3000)), n);
    if (!envs && n < pre.length) tick = Math.max(tick, Number(e.tick));
    if (envs) tick = Math.max(tick, Number(e.tick));
    trace.push(e);
    const res = await kernel.query({ op: "apply", state: st as Json, envelope: e as Json });
    if (res.accepted !== true) continue;
    accepted++;
    acceptedKinds?.set(e.command.type, (acceptedKinds.get(e.command.type) ?? 0) + 1);
    const t = res.transition as any;
    const inv = await kernel.query({ op: "invariants", state: t.state });
    if (inv.safe !== true) return { trace, failure: `kernel invariant violated after ${e.command.type}: ${JSON.stringify(inv.violations)}`, accepted };
    const ov = oracle(st, t.state, e, t.effects);
    if (ov.length) return { trace, failure: `oracle: ${ov.join("; ")}`, accepted };
    st = t.state;
    if (e.command.type === "recover_controller") tick = Number(e.tick);
  }
  return { trace, failure: null, accepted };
}

async function minimize(kernel: KernelClient, init: any, trace: any[]): Promise<any[]> {
  let cur = trace;
  let chunk = Math.max(1, Math.floor(cur.length / 2));
  while (chunk >= 1) {
    let changed = false;
    for (let i = 0; i + chunk <= cur.length; ) {
      const cand = [...cur.slice(0, i), ...cur.slice(i + chunk)];
      if ((await runTrace(kernel, init, cand, 1, 0)).failure) {
        cur = cand;
        changed = true;
      } else i += chunk;
    }
    if (!changed) chunk = Math.floor(chunk / 2);
  }
  return cur;
}

test("A24: generated command traces — executable kernel preserves invariants and oracle transition properties", async () => {
  const tpl = await templateState();
  const db = new DatabaseSync(path.join(tpl, "workbench.sqlite"), { readOnly: true });
  const init = JSON.parse((db.prepare("SELECT state FROM kstate WHERE id = 1").get() as any).state);
  db.close();
  const bin = path.join(REPO_ROOT, "protected/lean/.lake/build/bin/factory-kernel");
  const kernel = new KernelClient(bin, fileDigest(bin), 30_000);
  const seeds = Array.from({ length: Number(process.env.A24_SEEDS ?? 40) }, (_, i) => 1000 + i * 7919);
  let total = 0;
  let acc = 0;
  const kinds = new Set<string>();
  const acceptedKinds = new Map<string, number>();
  try {
    for (const seed of seeds) {
      const res = await runTrace(kernel, init, null, seed, Number(process.env.A24_LENGTH ?? 160), acceptedKinds);
      total += res.trace.length;
      acc += res.accepted;
      for (const e of res.trace) kinds.add(e.command.type);
      if (res.failure) {
        const min = await minimize(kernel, init, res.trace);
        const out = path.join(REPO_ROOT, "docs", `a24-counterexample-seed${seed}.json`);
        fs.mkdirSync(path.dirname(out), { recursive: true });
        fs.writeFileSync(out, JSON.stringify({ seed, failure: res.failure, minimized: min }, null, 2));
        assert.fail(`seed ${seed}: ${res.failure} (minimized ${min.length} commands → ${out})`);
      }
    }
  } finally {
    kernel.stop();
  }
  const ak = [...acceptedKinds.entries()].sort().map(([k, v]) => `${k}=${v}`).join(",");
  console.log(`A24: ${seeds.length} seeds, ${total} commands, ${acc} accepted; accepted by kind: ${ak}`);
  fs.writeFileSync(path.join(REPO_ROOT, "docs", "a24-coverage.json"), JSON.stringify({ seeds, total, accepted: acc, generated_kinds: [...kinds].sort(), accepted_by_kind: Object.fromEntries(acceptedKinds) }, null, 2) + "\n");
  assert.ok(acc > total * 0.1, "trace generator must produce a meaningful share of accepted transitions");
  assert.ok(kinds.size >= 20, "trace generator covers the command space");
  for (const k of ["create_job", "start_attempt", "record_verification", "commit_result", "fail_attempt", "expire_attempt", "pause_job",
    "acknowledge_quiescence", "resume_job", "cancel_job", "create_change", "recover_controller", "record_approval"]) {
    assert.ok((acceptedKinds.get(k) ?? 0) > 0, `no accepted ${k} transitions were exercised`);
  }
});
