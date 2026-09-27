// Execution engine: turns committed kernel state into supervised work.
// It never decides authority itself — every state change is a command to the
// coordinator (and therefore the Lean kernel). It only executes committed
// effect intents (commit-before-execute) and reports trusted observations.

import { createHash } from "node:crypto";
import { canonicalize, digestOf, type Json } from "../../packages/protocol/json.ts";
import type { Actor, Attempt, Command, EffectIntent, Job, KernelState, PlannerView, StepSpec, WorkflowDef } from "../../packages/protocol/kernel-types.ts";
import { LIVE_ATTEMPT, TERMINAL_JOB } from "../../packages/protocol/kernel-types.ts";
import { LABEL_ROOT } from "../../packages/runner/docker.ts";
import { nowIso } from "../../packages/store/db.ts";
import type { BuildReceipt } from "../../protected/verifier/verifier.ts";
import { executeAttempt, loadManifest, type AttemptCtx, type ExecOutcome } from "./executors.ts";
import { PlannerFault } from "./planner.ts";
import { createBundle, type EvidenceRef } from "./releases.ts";
import type { Workbench } from "./workbench.ts";

export const COORD: Actor = { type: "coordinator" };
export const SUPERVISOR: Actor = { type: "supervisor" };
export const VERIFIER: Actor = { type: "verifier" };

interface Running {
  abort: AbortController;
  heartbeat: NodeJS.Timeout | null;
  beats: number;
  job: string;
  step: string;
  gen: string;
}

export function attemptKey(job: string, step: string, gen: string | number): string {
  return `${job}/${step}/${gen}`;
}

export function workflowOf(st: KernelState, job: Job): WorkflowDef | null {
  const r = st.releases.find((x) => x.digest === job.release);
  return r?.workflows.find((w) => w.kind === job.kind) ?? null;
}

export class Engine {
  readonly wb: Workbench;
  readonly running = new Map<string, Running>();
  private ticking = false;
  private again = false;
  private timer: NodeJS.Timeout | null = null;
  stopped = false;
  /** Automatic dispatch; tests may disable it to drive steps deterministically. */
  autoDispatch = true;
  plannerDiagnostics = new Map<string, string>();

  private listening = false;

  constructor(wb: Workbench) {
    this.wb = wb;
  }

  start(intervalMs = 300): void {
    this.stopped = false;
    if (this.timer) clearInterval(this.timer);
    this.timer = setInterval(() => void this.kick(), intervalMs);
    if (!this.listening) {
      this.listening = true;
      this.wb.coord.onCommit((r) => {
        if (r.accepted && !this.stopped) void this.kick();
      });
    }
    void this.kick();
  }

  async stop(): Promise<void> {
    this.stopped = true;
    if (this.timer) clearInterval(this.timer);
    for (const r of this.running.values()) {
      if (r.heartbeat) clearInterval(r.heartbeat);
      r.abort.abort();
    }
  }

  async kick(): Promise<void> {
    if (this.stopped || !this.autoDispatch) return;
    if (this.ticking) {
      this.again = true;
      return;
    }
    this.ticking = true;
    try {
      do {
        this.again = false;
        await this.tick();
      } while (this.again && !this.stopped);
    } catch (e) {
      this.wb.log(`engine tick error: ${(e as Error).message}`);
    } finally {
      this.ticking = false;
    }
  }

  async tick(): Promise<void> {
    if (this.wb.coord.disabled) return;
    await this.expireLeases();
    await this.dispatchEffects();
    await this.schedule();
    await this.quiesce();
    await this.driveChanges();
    await this.publishReports();
  }

  private submit(actor: Actor, cmd: Command, id: string) {
    return this.wb.coord.submit(actor, cmd, id);
  }

  // ------------------------------------------------------------------ scheduling

  fingerprint(st: KernelState, job: Job, spec: StepSpec): string {
    const rel = st.releases.find((r) => r.digest === job.release);
    const promptDigest = spec.prompt === "" ? "" : rel?.assets.find((a) => a.path === spec.prompt)?.digest ?? "missing";
    const inputs = spec.inputs.map((b) => {
      if (b.source.type === "job_input") return [b.name, job.input];
      const src = b.source.step;
      const s = job.steps.find((x) => x.id === src);
      return [b.name, s?.accepted?.result ?? "missing"];
    }).sort((a, b) => (a[0] < b[0] ? -1 : 1));
    const runner = ["build", "prove"].includes(spec.role) ? `verifier:${this.wb.ids.harness_digest}`
      : spec.role === "materialize" ? "materializer:v1" : `codex-adapter:v1:${this.wb.codexConfig().configDigest}`;
    return digestOf({ runner, role: spec.role, prompt: promptDigest, schema: spec.role, inputs,
      contract: this.wb.ids.contract_digest } as unknown as Json);
  }

  async schedule(): Promise<void> {
    const st = this.wb.coord.state().state;
    for (const job of st.jobs) {
      if (!(job.status === "queued" || job.status === "running")) continue;
      const q = await this.wb.kernel.query({ op: "ready", state: st as unknown as Json, job: job.id });
      const ready = q.ready as string[];
      const slots = q.slots as string;
      if (ready.length === 0 || slots === "0") continue;
      const wf = q.workflow as unknown as WorkflowDef;
      const view: PlannerView = { workflow: wf, ready, slots };
      let plan: string[];
      try {
        plan = await this.wb.planners.plan(job.release, view);
      } catch (e) {
        this.diagnose(job.id, `planner fault (${(e as Error).message}); scheduling blocked for this job`);
        continue;
      }
      const chk = await this.wb.kernel.query({ op: "check_plan", view: view as unknown as Json, plan });
      if (chk.plan_ok !== true) {
        this.diagnose(job.id, `planner output ${canonicalize(plan)} violates the fixed plan contract for ready ${canonicalize(ready)}; scheduling blocked`);
        continue;
      }
      this.plannerDiagnostics.delete(job.id);
      for (const sid of plan) {
        const cur = this.wb.coord.state();
        const j = cur.state.jobs.find((x) => x.id === job.id)!;
        const spec = wf.steps.find((s) => s.id === sid)!;
        // Capacity pre-check (an optimization only — the kernel re-checks every start):
        // do not propose starts that the kernel would reject for a full resource class.
        const cls = ["build", "prove", "materialize"].includes(spec.role) ? "container" : "llm";
        const live = cur.state.jobs.flatMap((x) => x.attempts).filter((a) => LIVE_ATTEMPT.has(a.status) &&
          (["build", "prove", "materialize"].includes(a.role) ? "container" : "llm") === cls).length;
        const limit = Number(cls === "container" ? cur.state.config.container_slots : cur.state.config.llm_slots);
        if (live >= limit) continue;
        const gen = j.attempts.length + 1;
        // Idempotency key includes the state digest: retrying against unchanged state
        // replays the recorded receipt (no new journal entry); after any accepted
        // change (e.g. a freed slot) the retry is a new request.
        const r = await this.submit(COORD, { type: "start_attempt", job: job.id, step: sid, fingerprint: this.fingerprint(cur.state, j, spec) },
          `start:${job.id}:${sid}:${gen}:${cur.state.ctrl_epoch}:${cur.digest.slice(0, 16)}`);
        if (!r.accepted && !r.duplicate) this.wb.log(`start ${job.id}/${sid} rejected: ${r.reject_code}`);
      }
    }
  }

  diagnose(job: string, msg: string): void {
    if (this.plannerDiagnostics.get(job) !== msg) {
      this.plannerDiagnostics.set(job, msg);
      this.wb.db.db.prepare("INSERT INTO job_diagnostics(job, kind, detail, created) VALUES (?,?,?,?)").run(job, "planner", msg, nowIso());
      this.wb.log(`job ${job}: ${msg}`);
    }
  }

  // ------------------------------------------------------------------ effects (outbox)

  async dispatchEffects(): Promise<void> {
    const rows = this.wb.db.db.prepare("SELECT effect_id, body, kind FROM outbox WHERE status = 'pending' ORDER BY seq").all() as
      { effect_id: string; body: string; kind: string }[];
    for (const row of rows) {
      const eff = JSON.parse(row.body) as EffectIntent;
      if (eff.kind === "launch") await this.launch(eff);
      else if (eff.kind === "terminate") await this.terminate(eff);
      else this.markEffect(eff.id, "done", "publication registered");
    }
  }

  markEffect(id: string, status: string, note: string): void {
    this.wb.db.db.prepare("UPDATE outbox SET status = ?, note = ?, attempts = attempts + 1, updated = ? WHERE effect_id = ?")
      .run(status, note, nowIso(), id);
  }

  obs(job: string, step: string, gen: string, fields: { container?: string | null; phase?: string; cleanup?: string; detail?: string; lastOutput?: string }): void {
    const now = nowIso();
    this.wb.db.db.prepare(`INSERT INTO attempt_obs(job, step, gen, container, phase, last_output, cleanup, detail, updated)
      VALUES (?,?,?,?,?,?,?,?,?) ON CONFLICT(job, step, gen) DO UPDATE SET
      container = COALESCE(excluded.container, attempt_obs.container), phase = COALESCE(?, attempt_obs.phase),
      last_output = COALESCE(excluded.last_output, attempt_obs.last_output), cleanup = COALESCE(?, attempt_obs.cleanup),
      detail = COALESCE(excluded.detail, attempt_obs.detail), updated = excluded.updated`)
      .run(job, step, Number(gen), fields.container ?? null, fields.phase ?? "authorized", fields.lastOutput ?? null,
        fields.cleanup ?? "none", fields.detail ?? null, now, fields.phase ?? null, fields.cleanup ?? null);
  }

  containerName(effectId: string): string {
    return `fw-${this.wb.settings.instance}-${createHash("sha256").update(effectId).digest("hex").slice(0, 16)}`;
  }

  private async launch(eff: EffectIntent): Promise<void> {
    const st = this.wb.coord.state().state;
    const job = st.jobs.find((j) => j.id === eff.job);
    const att = job?.attempts.find((a) => a.step === eff.step && a.gen === eff.gen);
    if (!job || !att || att.status !== "authorized" || att.ctrl_epoch !== st.ctrl_epoch) {
      this.markEffect(eff.id, "superseded", "attempt no longer holds launch authority");
      return;
    }
    const wf = workflowOf(st, job)!;
    const spec = wf.steps.find((s) => s.id === eff.step)!;
    const key = attemptKey(eff.job, eff.step, eff.gen);
    if (this.running.has(key)) return;
    // Durable launch registry entry BEFORE any external start (uncertainty window, §7.3).
    const name = this.containerName(eff.id);
    this.wb.db.db.prepare("INSERT OR IGNORE INTO launches(effect_id, container_name, job, step, gen, epoch, state, updated) VALUES (?,?,?,?,?,?,?,?)")
      .run(eff.id, name, eff.job, eff.step, Number(eff.gen), Number(st.ctrl_epoch), "intent", nowIso());
    this.markEffect(eff.id, "dispatched", name);
    const r = await this.submit(COORD, { type: "observe_launch_dispatched", job: eff.job, step: eff.step, gen: eff.gen },
      `dispatched:${eff.job}:${eff.step}:${eff.gen}`);
    if (!r.accepted) return;
    this.obs(eff.job, eff.step, eff.gen, { phase: "starting", container: name });
    const abort = new AbortController();
    const running: Running = { abort, heartbeat: null, beats: 0, job: eff.job, step: eff.step, gen: eff.gen };
    this.running.set(key, running);
    const ctx: AttemptCtx = {
      job, spec, attempt: att, effectId: eff.id, signal: abort.signal, containerName: name,
      labels: {
        [`${LABEL_ROOT}.effect`]: createHash("sha256").update(eff.id).digest("hex").slice(0, 32),
        [`${LABEL_ROOT}.job`]: eff.job, [`${LABEL_ROOT}.step`]: eff.step, [`${LABEL_ROOT}.gen`]: eff.gen,
        [`${LABEL_ROOT}.epoch`]: st.ctrl_epoch,
      },
      onStarted: async (identity) => {
        this.wb.db.db.prepare("UPDATE launches SET container_id = ?, state = 'started', updated = ? WHERE effect_id = ?").run(identity, nowIso(), eff.id);
        // Test-only fault hook (A08): crash between container launch and recording it.
        // Reachable only when the process was started with FACTORY_TEST_MODE=1; never via API/UI.
        if (process.env.FACTORY_TEST_MODE === "1" && process.env.FACTORY_TEST_FAULT === `crash_after_start:${spec.role}`) process.exit(137);
        const o = await this.submit(SUPERVISOR, { type: "observe_process_started", job: eff.job, step: eff.step, gen: eff.gen, container: identity },
          `started:${eff.job}:${eff.step}:${eff.gen}:${identity}`);
        if (o.accepted) this.obs(eff.job, eff.step, eff.gen, { phase: "running", container: identity });
        if (!running.heartbeat) {
          running.heartbeat = setInterval(() => void this.heartbeat(running), this.wb.settings.limits.heartbeatMs);
        }
      },
    };
    void this.runAttempt(ctx, running);
  }

  private async heartbeat(r: Running): Promise<void> {
    r.beats++;
    try {
      const res = await this.submit(SUPERVISOR, { type: "heartbeat", job: r.job, step: r.step, gen: r.gen },
        `hb:${r.job}:${r.step}:${r.gen}:${r.beats}`);
      if (!res.accepted) {
        // Authority is gone (expired/cancelled/fenced): stop the work.
        if (r.heartbeat) clearInterval(r.heartbeat);
        r.abort.abort();
      }
    } catch {
      /* coordinator disabled: supervisor stops heartbeating */
    }
  }

  private async runAttempt(ctx: AttemptCtx, r: Running): Promise<void> {
    const { job, step, gen } = r;
    let out: ExecOutcome;
    try {
      out = await executeAttempt(this.wb, ctx);
    } finally {
      if (r.heartbeat) clearInterval(r.heartbeat);
    }
    this.running.delete(attemptKey(job, step, gen));
    this.wb.db.db.prepare("UPDATE launches SET state = 'exited', updated = ? WHERE effect_id = ?").run(nowIso(), ctx.effectId);
    this.markEffect(ctx.effectId, "done", out.kind === "result" ? "executed; result submitted" : `executed; ${out.reason}`);
    try {
      if (out.kind === "result") {
        const cmd: Command = out.viaVerifier
          ? { type: "record_verification", job, step, gen, result: out.envelope }
          : { type: "commit_result", job, step, gen, result: out.envelope };
        // Stage the observed result durably, then settle it through the kernel.
        this.wb.db.db.prepare("INSERT OR REPLACE INTO staged_results(job, step, gen, command, status, created) VALUES (?,?,?,?,'staged',?)")
          .run(job, step, Number(gen), canonicalize(cmd as unknown as Json), nowIso());
        const res = await this.submit(out.viaVerifier ? VERIFIER : SUPERVISOR, cmd, `commit:${job}:${step}:${gen}`);
        this.wb.db.db.prepare("UPDATE staged_results SET status = 'submitted' WHERE job = ? AND step = ? AND gen = ?").run(job, step, Number(gen));
        this.obs(job, step, gen, { phase: res.accepted ? "settled" : "rejected", cleanup: "done",
          detail: res.accepted ? out.note : `result not accepted: ${res.reject_code} (${out.note})` });
      } else {
        const res = await this.submit(SUPERVISOR, { type: "fail_attempt", job, step, gen }, `fail:${job}:${step}:${gen}`);
        this.obs(job, step, gen, { phase: res.accepted ? "failed" : "rejected", cleanup: "done", detail: out.reason });
      }
    } catch (e) {
      this.wb.log(`settling ${job}/${step}/${gen} failed: ${(e as Error).message}`);
    }
    void this.kick();
  }

  private async terminate(eff: EffectIntent): Promise<void> {
    const key = attemptKey(eff.job, eff.step, eff.gen);
    const r = this.running.get(key);
    this.obs(eff.job, eff.step, eff.gen, { cleanup: "pending" });
    if (r) r.abort.abort();
    // Terminate the whole container tree for this attempt, identified by deterministic labels.
    const inv = await this.wb.docker.inventory(this.wb.settings.instance).catch(() => []);
    for (const c of inv) {
      if (c.labels[`${LABEL_ROOT}.job`] === eff.job && c.labels[`${LABEL_ROOT}.step`] === eff.step && c.labels[`${LABEL_ROOT}.gen`] === eff.gen) {
        await this.wb.docker.terminate(c.id, this.wb.settings.limits.graceSec);
      }
    }
    this.obs(eff.job, eff.step, eff.gen, { cleanup: "done" });
    this.markEffect(eff.id, "done", "terminated");
  }

  // ------------------------------------------------------------------ leases / pause

  async expireLeases(): Promise<void> {
    const st = this.wb.coord.state().state;
    const now = this.wb.coord.clock.tick();
    for (const job of st.jobs) {
      for (const a of job.attempts) {
        if (LIVE_ATTEMPT.has(a.status) && a.ctrl_epoch === st.ctrl_epoch && now >= Number(a.deadline)) {
          await this.submit(COORD, { type: "expire_attempt", job: job.id, step: a.step, gen: a.gen }, `expire:${job.id}:${a.step}:${a.gen}`);
        }
      }
    }
  }

  async quiesce(): Promise<void> {
    const st = this.wb.coord.state().state;
    for (const job of st.jobs) {
      if (job.status !== "pause_requested") continue;
      if (job.attempts.some((a) => LIVE_ATTEMPT.has(a.status))) continue;
      const busy = [...this.running.values()].some((r) => r.job === job.id);
      const pendingLaunch = this.wb.db.db.prepare("SELECT 1 FROM outbox WHERE status = 'pending' AND kind = 'launch' AND body LIKE ?")
        .get(`%"job":${JSON.stringify(job.id)}%`);
      const inv = await this.wb.docker.inventory(this.wb.settings.instance).catch(() => null);
      const containers = inv === null ? true : inv.some((c) => c.labels[`${LABEL_ROOT}.job`] === job.id);
      const clear = !busy && !containers;
      if (pendingLaunch) {
        // dispatched-but-superseded launches are settled by the kernel state; mark them
        // pending launches whose attempts no longer hold authority (kernel says none are live)
        this.wb.db.db.prepare("UPDATE outbox SET status = 'superseded', updated = ? WHERE status = 'pending' AND kind = 'launch' AND body LIKE ?")
          .run(nowIso(), `%"job":${JSON.stringify(job.id)}%`);
      }
      await this.submit(COORD, { type: "acknowledge_quiescence", job: job.id, containers_clear: clear }, `ack:${job.id}:${job.revision}:${clear}`);
    }
  }

  // ------------------------------------------------------------------ self-improvement driver

  async driveChanges(): Promise<void> {
    const st = this.wb.coord.state().state;
    for (const c of st.changes) {
      if (c.status !== "open") continue;
      for (const jid of c.jobs) {
        const j = st.jobs.find((x) => x.id === jid);
        if (!j) continue;
        if (j.kind === "change_author") await this.afterAuthor(st, c.id, j);
        else if (j.kind === "change_evaluate") await this.afterEvaluate(st, c.id, j);
      }
    }
  }

  private evalJobFor(st: KernelState, changeId: string, source: string): Job | undefined {
    return st.jobs.find((j) => j.kind === "change_evaluate" && j.change === changeId && j.subject === source);
  }

  private async afterAuthor(st: KernelState, changeId: string, j: Job): Promise<void> {
    const c = st.changes.find((x) => x.id === changeId)!;
    if (j.status === "succeeded") {
      const m = j.steps.find((s) => s.id === "materialize") ?? j.steps.find((s) => s.accepted?.produced);
      const src = m?.accepted?.produced;
      if (!src || c.candidates.includes(src)) return;
      const evalId = `${changeId}-eval${c.candidates.length + 1}`;
      const r = await this.submit(COORD, { type: "register_candidate", change: changeId, author_job: j.id, eval_job: evalId, source: src },
        `register:${changeId}:${j.id}`);
      if (r.accepted) {
        this.wb.db.db.prepare("INSERT OR IGNORE INTO candidates(source_digest, change_id, revision, author_job, manifest_digest, created) VALUES (?,?,?,?,?,?)")
          .run(src, changeId, Number(c.revisions), j.id, src, nowIso());
      }
    } else if (j.status === "failed" && !this.revised(changeId, j.id)) {
      const mat = j.steps.find((s) => s.id === "materialize");
      if (mat?.accepted && mat.accepted.outcome !== "pass") {
        const doc = JSON.parse(this.wb.blobs.getText(mat.accepted.result));
        await this.autoRevise(st, changeId, j.id, { failed_stage: "materialize", source_digest: null, failure: doc.reason ?? "materialization rejected" });
      }
    }
  }

  private revised(changeId: string, fromJob: string): boolean {
    return !!this.wb.db.db.prepare("SELECT 1 FROM revisions WHERE change_id = ? AND from_job = ?").get(changeId, fromJob);
  }

  /** Bounded repair loop: a new recorded author invocation fed the actual
   *  trusted diagnostics. Model review failures are NOT auto-retried. */
  private async autoRevise(st: KernelState, changeId: string, fromJob: string, diag: { failed_stage: string; source_digest: string | null; failure: string; receipt?: string }): Promise<void> {
    const c = st.changes.find((x) => x.id === changeId)!;
    if (Number(c.revisions) >= Number(c.revision_limit)) {
      this.wb.db.db.prepare("INSERT OR IGNORE INTO revisions(change_id, from_job, new_job, status, created) VALUES (?,?,?,?,?)")
        .run(changeId, fromJob, null, "revision_budget_exhausted", nowIso());
      return;
    }
    const d = this.wb.blobs.put(canonicalize({ kind: "repair_diagnostics", change: changeId, from_job: fromJob, ...diag } as unknown as Json));
    const newJob = `${changeId}-author${Number(c.revisions) + 1}`;
    const r = await this.submit(COORD, { type: "revise_change", change: changeId, author_job: newJob, diagnostics: d },
      `revise:${changeId}:${fromJob}`);
    this.wb.db.db.prepare("INSERT OR IGNORE INTO revisions(change_id, from_job, new_job, status, created) VALUES (?,?,?,?,?)")
      .run(changeId, fromJob, r.accepted ? newJob : null, r.accepted ? "revised" : `rejected:${r.reject_code}`, nowIso());
  }

  private async afterEvaluate(st: KernelState, changeId: string, j: Job): Promise<void> {
    if (j.status === "succeeded") {
      await this.publishRelease(st, changeId, j);
      return;
    }
    if (j.status !== "failed" || this.revised(changeId, j.id)) return;
    // Only trusted build/proof failures trigger automatic bounded repair.
    for (const stepId of ["build", "prove"]) {
      const s = j.steps.find((x) => x.id === stepId);
      if (s?.accepted && s.accepted.outcome === "fail") {
        const rec = JSON.parse(this.wb.blobs.getText(s.accepted.result));
        const author = st.jobs.find((x) => x.kind === "change_author" && x.change === changeId &&
          x.steps.some((y) => y.accepted?.produced === j.subject));
        this.wb.db.db.prepare("INSERT INTO rejected_candidates(change_id, author_job, stage, reason, detail_digest, created) VALUES (?,?,?,?,?,?)")
          .run(changeId, author?.id ?? "", stepId, String(rec.failure ?? "failed"), s.accepted.result, nowIso());
        await this.autoRevise(st, changeId, j.id, { failed_stage: stepId, source_digest: j.subject, failure: String(rec.failure ?? ""), receipt: s.accepted.result });
        return;
      }
    }
    this.wb.db.db.prepare("INSERT OR IGNORE INTO revisions(change_id, from_job, new_job, status, created) VALUES (?,?,?,?,?)")
      .run(changeId, j.id, null, "stopped: review gate failed or transport exhausted; explicit revise required", nowIso());
  }

  private async publishRelease(st: KernelState, changeId: string, j: Job): Promise<void> {
    const c = st.changes.find((x) => x.id === changeId)!;
    const byRole = (role: string) => {
      const wf = workflowOf(st, j)!;
      const spec = wf.steps.find((s) => s.role === role)!;
      return j.steps.find((s) => s.id === spec.id)!;
    };
    const b = byRole("build").accepted!;
    const build = JSON.parse(this.wb.blobs.getText(b.result)) as BuildReceipt;
    const evidence: EvidenceRef[] = ["build", "prove", "reproduce", "refute"].map((role) => {
      const s = byRole(role);
      return { role, job: j.id, step: s.id, gen: s.accepted!.gen, result: s.accepted!.result };
    });
    const envelope = { payload_digest: b.produced!, evidence, recipe: build.recipe ?? "pin_only",
      lineage: { parent: c.base, producer: j.release } };
    const source = loadManifest(this.wb, j.subject);
    const { releaseDigest } = createBundle(this.wb.settings.stateDir, this.wb.blobs, this.wb.db,
      { source, build, buildReceiptDigest: b.result, envelope });
    const r = await this.submit(COORD, { type: "publish_release", job: j.id, release: releaseDigest, assets: build.assets },
      `publish-release:${j.id}`);
    if (!r.accepted && !r.duplicate) this.wb.log(`publish release for ${j.id} rejected: ${r.reject_code}`);
  }

  async publishReports(): Promise<void> {
    const st = this.wb.coord.state().state;
    for (const j of st.jobs) {
      if (j.kind !== "package_audit" || j.status !== "succeeded") continue;
      if (st.reports.some((r) => r.job === j.id)) continue;
      const summary = j.steps.find((s) => s.id === "summarize")?.accepted?.result ?? null;
      const report = { kind: "package_audit_report", job: j.id, subject: j.subject, release: j.release,
        evidence: j.steps.map((s) => ({ step: s.id, outcome: s.accepted?.outcome ?? null, result: s.accepted?.result ?? null,
          producer_release: s.accepted?.release ?? null })), summary };
      const d = this.wb.blobs.put(canonicalize(report as unknown as Json));
      const r = await this.submit(COORD, { type: "publish_report", job: j.id, report: d }, `publish-report:${j.id}`);
      if (!r.accepted && !r.duplicate) this.wb.log(`publish report for ${j.id} rejected: ${r.reject_code}`);
    }
  }
}

export function isTerminal(j: Job): boolean {
  return TERMINAL_JOB.has(j.status);
}

export function liveAttempts(j: Job): Attempt[] {
  return j.attempts.filter((a) => LIVE_ATTEMPT.has(a.status));
}
