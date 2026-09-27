// Test-only controller harness (§18). Tests use the REAL Lean kernel, SQLite
// journal, blob store and (where stated) real containers. "Synthetic"
// observations below are authenticated supervisor/verifier commands supplied
// by the test harness in place of running a container — they exercise the
// kernel's admission logic, never bypass it. No fault injection is reachable
// from the production API.

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { createHash, randomBytes } from "node:crypto";
import { digestOf, type Json } from "../../packages/protocol/json.ts";
import type { Actor, Command, Job, KernelState, ResultEnvelope, WorkflowDef } from "../../packages/protocol/kernel-types.ts";
import { loadSettings, REPO_ROOT, type Settings } from "../../apps/control/config.ts";
import { ManualClock, type Receipt } from "../../apps/control/coordinator.ts";
import { Workbench } from "../../apps/control/workbench.ts";

export const OPERATOR: Actor = { type: "operator", name: "tester" };
export const COORD: Actor = { type: "coordinator" };
export const SUP: Actor = { type: "supervisor" };
export const VER: Actor = { type: "verifier" };

const TEMPLATE = path.join(os.tmpdir(), "fw-test-template");

export function sha(s: string): string {
  return createHash("sha256").update(s).digest("hex");
}

export function tmpDir(tag: string): string {
  return fs.mkdtempSync(path.join(os.tmpdir(), `fw-${tag}-`));
}

/** Bootstrap once (real sandboxed genesis verification), reuse by copying. */
export async function templateState(): Promise<string> {
  const marker = path.join(TEMPLATE, "READY");
  const img = JSON.parse(fs.readFileSync(path.join(REPO_ROOT, "toolchains.lock.json"), "utf8")).images.verifier.id;
  if (fs.existsSync(marker) && fs.readFileSync(marker, "utf8") === img) return TEMPLATE;
  fs.rmSync(TEMPLATE, { recursive: true, force: true });
  const settings = loadSettings({ stateDir: TEMPLATE, instance: `tpl${process.pid}` });
  const wb = await Workbench.open(settings);
  try {
    await wb.bootstrap(path.join(REPO_ROOT, "orchestration/genesis"));
  } finally {
    await wb.close();
  }
  fs.writeFileSync(marker, img);
  return TEMPLATE;
}

export interface Opened {
  wb: Workbench;
  clock: ManualClock;
  dir: string;
  settings: Settings;
}

export async function openCopy(tag: string, overrides: Partial<Settings> = {}, scenario?: string): Promise<Opened> {
  const tpl = await templateState();
  const dir = tmpDir(tag);
  fs.cpSync(tpl, dir, { recursive: true });
  fs.rmSync(path.join(dir, "controller.lock"), { force: true });
  fs.chmodSync(dir, 0o700);
  const base = loadSettings({ stateDir: dir, instance: `t${randomBytes(3).toString("hex")}`, ...overrides });
  if (scenario) base.codex.fakeScenario = path.join(REPO_ROOT, "protected/tests/fixtures/fake-codex", scenario);
  const clock = new ManualClock();
  const wb = await Workbench.open(base, { clock });
  wb.engine.autoDispatch = false;
  // advance epoch as a real start would (fences nothing on a fresh copy)
  await wb.recover();
  return { wb, clock, dir, settings: base };
}

let seq = 0;
export function cid(tag: string): string {
  return `t-${tag}-${++seq}-${randomBytes(2).toString("hex")}`;
}

export async function submit(wb: Workbench, actor: Actor, cmd: Command, tag: string = cmd.type): Promise<Receipt> {
  return wb.coord.submit(actor, cmd, cid(tag));
}

export function job(wb: Workbench, id: string): Job {
  const j = wb.state().jobs.find((x) => x.id === id);
  if (!j) throw new Error(`no job ${id}`);
  return j;
}

export function workflowOf(st: KernelState, j: Job): WorkflowDef {
  return st.releases.find((r) => r.digest === j.release)!.workflows.find((w) => w.kind === j.kind)!;
}

export async function createAudit(wb: Workbench, id: string, release: string | null = null, limit = 20): Promise<Receipt> {
  const fx = wb.db.db.prepare("SELECT digest FROM fixtures LIMIT 1").get() as { digest: string };
  return submit(wb, OPERATOR, { type: "create_job", job: id, kind: "package_audit", input: fx.digest, subject: fx.digest,
    release, budget: `${id}-b`, limit: String(limit) });
}

/** Authorize + observe a step. Returns the generation. */
export async function startStep(wb: Workbench, jobId: string, step: string, fp = sha(`fp-${jobId}-${step}`)): Promise<{ gen: string; receipt: Receipt }> {
  const r = await submit(wb, COORD, { type: "start_attempt", job: jobId, step, fingerprint: fp });
  if (!r.accepted) return { gen: "", receipt: r };
  const j = job(wb, jobId);
  const gen = j.attempts[j.attempts.length - 1].gen;
  await submit(wb, SUP, { type: "observe_process_started", job: jobId, step, gen, container: `test:${jobId}:${step}:${gen}` });
  return { gen, receipt: r };
}

export function envelopeFor(wb: Workbench, jobId: string, step: string, over: Partial<ResultEnvelope> = {}): ResultEnvelope {
  const st = wb.state();
  const j = job(wb, jobId);
  const att = [...j.attempts].reverse().find((a) => a.step === step)!;
  const wf = workflowOf(st, j);
  const role = wf.steps.find((s) => s.id === step)!.role;
  const payload = sha(`payload-${j.subject}`);
  const base: ResultEnvelope = {
    result: sha(`result-${jobId}-${step}-${att.gen}`), model_outcome: "pass", trusted_outcome: "pass",
    produced: role === "build" ? payload : role === "materialize" ? sha(`src-${jobId}`) : null,
    exports: role === "build" ? st.releases.find((r) => r.digest === st.active)!.workflows : [],
    contract: ["build", "prove"].includes(role) ? st.contract : "", fingerprint: att.fingerprint,
  };
  return { ...base, ...over };
}

export async function commitStep(wb: Workbench, jobId: string, step: string, gen: string, env: ResultEnvelope, tag?: string): Promise<Receipt> {
  const st = wb.state();
  const j = job(wb, jobId);
  const role = workflowOf(st, j).steps.find((s) => s.id === step)!.role;
  const verifier = role === "build" || role === "prove";
  return wb.coord.submit(verifier ? VER : SUP,
    verifier ? { type: "record_verification", job: jobId, step, gen, result: env } : { type: "commit_result", job: jobId, step, gen, result: env },
    tag ?? cid(`commit-${step}`));
}

/** Drive one step through start → observe → commit with a synthetic observation. */
export async function runStep(wb: Workbench, jobId: string, step: string, over: Partial<ResultEnvelope> = {}): Promise<Receipt> {
  const { gen, receipt } = await startStep(wb, jobId, step);
  if (!receipt.accepted) return receipt;
  return commitStep(wb, jobId, step, gen, envelopeFor(wb, jobId, step, over));
}

/** Drive every remaining step in workflow order (ignores planner; kernel still checks eligibility). */
export async function runAll(wb: Workbench, jobId: string, over: Record<string, Partial<ResultEnvelope>> = {}): Promise<void> {
  const st = wb.state();
  const wf = workflowOf(st, job(wb, jobId));
  for (const s of wf.steps) {
    const cur = job(wb, jobId).steps.find((x) => x.id === s.id)!;
    if (cur.accepted) continue;
    const r = await runStep(wb, jobId, s.id, over[s.id] ?? {});
    if (!r.accepted) throw new Error(`runAll ${jobId}/${s.id}: ${r.reject_code}`);
  }
}

/** Genesis workflows with a transform (e.g. P1-like ordering-only change). */
export function transformWorkflows(ws: WorkflowDef[], f: (w: WorkflowDef) => WorkflowDef): WorkflowDef[] {
  return ws.map((w) => f(JSON.parse(JSON.stringify(w))));
}

export function parallelReviews(w: WorkflowDef): WorkflowDef {
  if (w.kind === "change_author") return w;
  for (const s of w.steps) if (s.id === "refute") s.after = [];
  w.max_parallel = "2";
  return w;
}

/**
 * Publish a release through the REAL change-request path (create change →
 * author/materialize → register candidate → evaluate → publish), with synthetic
 * observations whose build step exports `workflows`. Returns the release digest.
 */
export async function publishSynthetic(wb: Workbench, tag: string, workflows: WorkflowDef[]): Promise<{ release: string; evalJob: string; change: string }> {
  const change = `chg-${tag}`;
  const req = sha(`req-${tag}`);
  let r = await submit(wb, OPERATOR, { type: "create_change", change, request: req, author_job: `${change}-a1`, budget: `${change}-b`, attempt_limit: "50", revision_limit: "3" });
  if (!r.accepted) throw new Error(`create_change ${r.reject_code}`);
  const src = sha(`source-${tag}`);
  await runAll(wb, `${change}-a1`, { materialize: { produced: src } });
  r = await submit(wb, COORD, { type: "register_candidate", change, author_job: `${change}-a1`, eval_job: `${change}-e1`, source: src });
  if (!r.accepted) throw new Error(`register ${r.reject_code}`);
  await runAll(wb, `${change}-e1`, { build: { exports: workflows, produced: sha(`payload-${tag}`) } });
  const release = sha(`release-${tag}`);
  // same prompt assets as genesis (prompt bytes unchanged) unless a test overrides them
  const assets = wb.state().releases[0].assets;
  r = await submit(wb, COORD, { type: "publish_release", job: `${change}-e1`, release, assets });
  if (!r.accepted) throw new Error(`publish ${r.reject_code}`);
  return { release, evalJob: `${change}-e1`, change };
}

export async function approveAndActivate(wb: Workbench, release: string, base: string, aid = `ap-${release.slice(0, 8)}`): Promise<Receipt> {
  const a = await submit(wb, OPERATOR, { type: "record_approval", approval: aid, release, expected_base: base });
  if (!a.accepted) return a;
  return submit(wb, OPERATOR, { type: "activate_release", release, expected_active: base, approval: aid });
}

export async function invariants(wb: Workbench): Promise<{ safe: boolean; violations: string[] }> {
  const r = await wb.kernel.query({ op: "invariants", state: wb.state() as unknown as Json });
  return { safe: r.safe === true, violations: r.violations as string[] };
}

export async function close(o: Opened, keep = false): Promise<void> {
  await o.wb.close();
  if (!keep) fs.rmSync(o.dir, { recursive: true, force: true });
}

export { digestOf };
