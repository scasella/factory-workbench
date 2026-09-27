// Operator operations and read projections shared by API, CLI and demos.
// Every mutation is a kernel command through the coordinator; this layer only
// validates request shape, allocates stable identifiers and performs host-side
// integrity checks (e.g. bundle re-verification before activation).

import { randomBytes } from "node:crypto";
import { canonicalize, isDigest, strictParse, type Json } from "../../packages/protocol/json.ts";
import type { Job, KernelState, Release, WorkflowDef } from "../../packages/protocol/kernel-types.ts";
import { LIVE_ATTEMPT } from "../../packages/protocol/kernel-types.ts";
import { nowIso } from "../../packages/store/db.ts";
import type { Receipt } from "./coordinator.ts";
import { workflowOf } from "./engine.ts";
import { bundleBuildReceipt, verifyBundle, BundleError } from "./releases.ts";
import type { Workbench } from "./workbench.ts";

export class OpError extends Error {
  readonly code: string;
  readonly status: number;
  constructor(code: string, msg: string, status = 400) {
    super(msg);
    this.code = code;
    this.status = status;
  }
}

const ID_RE = /^[a-z0-9][a-z0-9-]{0,62}$/;

function newId(prefix: string): string {
  return `${prefix}-${randomBytes(4).toString("hex")}`;
}

export function receiptOrThrow(r: Receipt): Receipt {
  if (!r.accepted) throw new OpError(r.reject_code ?? "REJECTED", `kernel rejected the command: ${r.reject_code}`, 409);
  return r;
}

// ------------------------------------------------------------------ jobs

export async function submitAudit(wb: Workbench, args: { fixture: string; release?: string | null; commandId: string; jobId?: string; attempts?: number }) {
  const fx = wb.db.db.prepare("SELECT digest FROM fixtures WHERE name = ? OR digest = ?").get(args.fixture, args.fixture) as { digest: string } | undefined;
  if (!fx) {
    const names = (wb.db.db.prepare("SELECT name FROM fixtures ORDER BY name").all() as { name: string }[]).map((r) => r.name);
    throw new OpError("UNKNOWN_FIXTURE", `no registered package fixture '${args.fixture}'; registered: ${names.join(", ") || "none"}`, 404);
  }
  const jobId = args.jobId ?? newId("audit");
  if (!ID_RE.test(jobId)) throw new OpError("BAD_ID", "invalid job id");
  if (args.release != null && !isDigest(args.release)) throw new OpError("BAD_DIGEST", "release must be a digest");
  const r = await wb.coord.submit(wb.operator(), {
    type: "create_job", job: jobId, kind: "package_audit", input: fx.digest, subject: fx.digest,
    release: args.release ?? null, budget: `${jobId}-budget`, limit: String(args.attempts ?? wb.settings.limits.attemptsPerAudit),
  }, args.commandId);
  return { job: jobId, receipt: receiptOrThrow(r) };
}

export async function pauseJob(wb: Workbench, job: string, commandId: string) {
  return receiptOrThrow(await wb.coord.submit(wb.operator(), { type: "pause_job", job }, commandId));
}
export async function resumeJob(wb: Workbench, job: string, commandId: string) {
  return receiptOrThrow(await wb.coord.submit(wb.operator(), { type: "resume_job", job }, commandId));
}
export async function cancelJob(wb: Workbench, job: string, commandId: string) {
  return receiptOrThrow(await wb.coord.submit(wb.operator(), { type: "cancel_job", job }, commandId));
}

/** Out-of-band recovery: request pause for every dispatchable job. */
export async function pauseAll(wb: Workbench, commandPrefix: string) {
  const out: { job: string; accepted: boolean; code: string | null }[] = [];
  for (const j of wb.state().jobs) {
    if (j.status === "queued" || j.status === "running") {
      const r = await wb.coord.submit(wb.operator(), { type: "pause_job", job: j.id }, `${commandPrefix}:${j.id}`);
      out.push({ job: j.id, accepted: r.accepted, code: r.reject_code });
    }
  }
  return out;
}

// ------------------------------------------------------------------ changes

export async function proposeChange(wb: Workbench, args: { request: string; commandId: string; changeId?: string; attempts?: number; revisions?: number }) {
  if (typeof args.request !== "string" || args.request.trim().length < 8 || args.request.length > 8000) {
    throw new OpError("BAD_REQUEST", "request must be 8..8000 characters");
  }
  const id = args.changeId ?? newId("chg");
  if (!ID_RE.test(id)) throw new OpError("BAD_ID", "invalid change id");
  const reqDigest = wb.blobs.put(canonicalize({ kind: "change_request", text: args.request } as Json));
  const st = wb.state();
  wb.db.db.prepare("INSERT OR IGNORE INTO changes_meta(change_id, request_text, request_digest, base, created) VALUES (?,?,?,?,?)")
    .run(id, args.request, reqDigest, st.active ?? "", nowIso());
  const r = await wb.coord.submit(wb.operator(), {
    type: "create_change", change: id, request: reqDigest, author_job: `${id}-author1`, budget: `${id}-budget`,
    attempt_limit: String(args.attempts ?? wb.settings.limits.attemptsPerChange),
    revision_limit: String(args.revisions ?? wb.settings.limits.revisionsPerChange),
  }, args.commandId);
  if (!r.accepted) wb.db.db.prepare("DELETE FROM changes_meta WHERE change_id = ?").run(id);
  return { change: id, receipt: receiptOrThrow(r) };
}

export async function reviseChange(wb: Workbench, args: { change: string; note: string; commandId: string }) {
  const st = wb.state();
  const c = st.changes.find((x) => x.id === args.change);
  if (!c) throw new OpError("UNKNOWN_CHANGE", "unknown change", 404);
  const d = wb.blobs.put(canonicalize({ kind: "operator_revision_request", change: c.id, note: args.note } as Json));
  const r = await wb.coord.submit(wb.operator(), { type: "revise_change", change: c.id, author_job: `${c.id}-author${Number(c.revisions) + 1}`, diagnostics: d }, args.commandId);
  return receiptOrThrow(r);
}

// ------------------------------------------------------------------ releases

/** Accept a full digest or a unique prefix (≥ 6 hex characters, any case) of a known release. */
export function resolveRelease(wb: Workbench, ref: string): string {
  const s = String(ref ?? "").trim().toLowerCase();
  if (isDigest(s)) return s;
  if (!/^[0-9a-f]{6,63}$/.test(s)) throw new OpError("BAD_DIGEST", "expected a release digest or a unique prefix of at least 6 hex characters");
  const hits = wb.state().releases.filter((r) => r.digest.startsWith(s));
  if (hits.length === 0) throw new OpError("UNKNOWN_RELEASE", `no release starts with ${s}`, 404);
  if (hits.length > 1) throw new OpError("AMBIGUOUS_RELEASE", `${hits.length} releases start with ${s}; give more characters`);
  return hits[0].digest;
}

/** Name the actual active release when an approval/activation lost a race or used a stale base. */
function withActive(wb: Workbench, r: Receipt): Receipt {
  if (!r.accepted && /BASE|ACTIVE/.test(String(r.reject_code))) {
    throw new OpError(r.reject_code ?? "REJECTED", `kernel rejected the command: ${r.reject_code}; the active release is now ${wb.state().active ?? "none"}`, 409);
  }
  return receiptOrThrow(r);
}

export async function approveRelease(wb: Workbench, args: { release: string; expectedBase: string; commandId: string }) {
  args = { ...args, release: resolveRelease(wb, args.release), expectedBase: resolveRelease(wb, args.expectedBase) };
  const approvalId = `appr-${args.commandId.replace(/[^a-z0-9-]/gi, "").slice(0, 40).toLowerCase() || newId("x")}`;
  const r = await wb.coord.submit(wb.operator(), { type: "record_approval", approval: approvalId, release: args.release, expected_base: args.expectedBase }, args.commandId);
  return { approval: approvalId, receipt: withActive(wb, r) };
}

export async function activateRelease(wb: Workbench, args: { release: string; expectedActive: string; approval: string; commandId: string }) {
  args = { ...args, release: resolveRelease(wb, args.release), expectedActive: resolveRelease(wb, args.expectedActive) };
  try {
    verifyBundle(wb.settings.stateDir, args.release); // host re-check of bundle integrity before CAS
  } catch (e) {
    throw new OpError("BUNDLE_INTEGRITY", (e as BundleError).message, 409);
  }
  const r = await wb.coord.submit(wb.operator(), { type: "activate_release", release: args.release, expected_active: args.expectedActive, approval: args.approval }, args.commandId);
  return withActive(wb, r);
}

export async function revokeApproval(wb: Workbench, approval: string, commandId: string) {
  return receiptOrThrow(await wb.coord.submit(wb.operator(), { type: "revoke_approval", approval }, commandId));
}

// ------------------------------------------------------------------ migrations

export async function migrationPreview(wb: Workbench, job: string, target: string) {
  const st = wb.state();
  const r = await wb.kernel.call({ op: "migration_preview", state: st as unknown as Json, job, target });
  if (r.ok !== true) throw new OpError("PREVIEW_FAILED", String(r.message), 404);
  return r.preview as Record<string, Json>;
}

export async function migrationApply(wb: Workbench, args: { job: string; target: string; expectedRevision: string; commandId: string }) {
  const r = await wb.coord.submit(wb.operator(), { type: "migrate_job", job: args.job, target: args.target, expected_revision: args.expectedRevision }, args.commandId);
  return receiptOrThrow(r);
}

/** Activation preview: disposition of every unfinished job under a candidate default. */
export async function activationPreview(wb: Workbench, ref: string) {
  const release = resolveRelease(wb, ref);
  const st = wb.state();
  const out: { job: string; kind: string; status: string; pinned: string; disposition: string; reasons: string[] }[] = [];
  for (const j of st.jobs) {
    if (["succeeded", "failed", "cancelled", "blocked"].includes(j.status)) continue;
    let disposition = "remains pinned";
    let reasons: string[] = ["default policy: existing jobs stay on their pinned release"];
    if (j.kind === "package_audit" && j.release !== release) {
      const p = await wb.kernel.call({ op: "migration_preview", state: st as unknown as Json, job: j.id, target: release });
      const pv = p.preview as Record<string, Json> | undefined;
      const rs = ((pv?.reasons as string[]) ?? ["preview unavailable"]);
      const quiescence = ["job is not paused/quiescent", "job has live attempt authority"];
      if (rs.length === 0) {
        disposition = "eligible for checked migration";
        reasons = ["paused and quiescent; completed steps keep identical identity; stays pinned unless the operator applies the migration"];
      } else if (rs.every((x) => quiescence.includes(x))) {
        disposition = "remains pinned";
        reasons = ["not paused/quiescent (could become eligible after pause)", ...rs];
      } else {
        disposition = "ineligible";
        reasons = rs;
      }
    } else if (j.kind !== "package_audit") {
      reasons = ["self-improvement jobs are never migrated (v1)"];
    }
    out.push({ job: j.id, kind: j.kind, status: j.status, pinned: j.release, disposition, reasons });
  }
  return out;
}

// ------------------------------------------------------------------ projections

export function statusView(wb: Workbench) {
  const st = wb.state();
  const live = st.jobs.flatMap((j) => j.attempts.filter((a) => LIVE_ATTEMPT.has(a.status)));
  return {
    active_release: st.active,
    controller_epoch: st.ctrl_epoch,
    clock: st.clock,
    contract_digest: st.contract,
    bootstrapped: wb.bootstrapped(),
    mutation_disabled: wb.coord.disabled,
    verifier: wb.verifierAvailable(),
    trust: wb.trustStatus(),
    inference: { mode: wb.settings.codex.mode, mocked: wb.settings.codex.mode === "fake", live_blocked: wb.codexConfig().blocked },
    limits: wb.settings.limits,
    capacity: {
      llm: { live: live.filter((a) => ["author", "reproduce", "refute", "summarize"].includes(a.role)).length, limit: Number(st.config.llm_slots) },
      container: { live: live.filter((a) => ["build", "prove", "materialize"].includes(a.role)).length, limit: Number(st.config.container_slots) },
    },
    counts: {
      jobs: st.jobs.length, releases: st.releases.length, changes: st.changes.length,
      running_executors: wb.engine.running.size,
    },
    isolation: { network: "none", root_fs: "read-only", caps: "all dropped", user: "10001", image: wb.ids.verifier_image, image_id: wb.ids.verifier_image_id },
  };
}

function obsFor(wb: Workbench, job: string) {
  return wb.db.db.prepare("SELECT step, gen, container, phase, last_output, cleanup, detail, updated FROM attempt_obs WHERE job = ?").all(job) as any[];
}

export function jobView(wb: Workbench, j: Job, st: KernelState = wb.state()) {
  const wf = workflowOf(st, j);
  const obs = obsFor(wb, j.id);
  const budget = st.budgets.find((b) => b.id === j.budget);
  return {
    ...j,
    workflow: wf,
    budget_detail: budget ?? null,
    ready_diagnostic: wb.engine.plannerDiagnostics.get(j.id) ?? null,
    attempts: j.attempts.map((a) => {
      const o = obs.find((x) => x.step === a.step && String(x.gen) === a.gen);
      return { ...a, observation: o ?? null };
    }),
    report: st.reports.find((r) => r.job === j.id) ?? null,
    invocations: wb.db.db.prepare("SELECT id, step, gen, role, fake, transport, exit_code, usage, transcript_digest, context_digest, created FROM invocations WHERE job = ? ORDER BY created").all(j.id),
    diagnostics: wb.db.db.prepare("SELECT kind, detail, created FROM job_diagnostics WHERE job = ? ORDER BY id DESC LIMIT 20").all(j.id),
  };
}

/** Structural comparison of a candidate's exported workflows against the base
 *  release: removed/added ordering edges, semantic-input changes, and which
 *  step pairs may now run in parallel (no ordering edge and no data dependency). */
export function graphChanges(base: WorkflowDef[], cand: WorkflowDef[]) {
  const out: any[] = [];
  for (const b of base) {
    const c = cand.find((w) => w.kind === b.kind);
    if (!c) {
      out.push({ kind: b.kind, missing_workflow: true });
      continue;
    }
    const edges: any[] = [];
    const inputs: any[] = [];
    for (const s of c.steps) {
      const o = b.steps.find((x) => x.id === s.id);
      if (!o) {
        edges.push({ step: s.id, change: "added step" });
        continue;
      }
      for (const a of o.after) if (!s.after.includes(a)) edges.push({ step: s.id, removed_after: a });
      for (const a of s.after) if (!o.after.includes(a)) edges.push({ step: s.id, added_after: a });
      if (JSON.stringify(o.inputs) !== JSON.stringify(s.inputs)) inputs.push({ step: s.id, before: o.inputs, after: s.inputs });
      if (o.role !== s.role || o.prompt !== s.prompt) inputs.push({ step: s.id, role_or_prompt_changed: true });
    }
    const removedSteps = b.steps.filter((x) => !c.steps.some((y) => y.id === x.id)).map((x) => x.id);
    const reach = (w: WorkflowDef, from: string, to: string): boolean => {
      const seen = new Set<string>();
      const go = (id: string): boolean => {
        if (id === to) return true;
        if (seen.has(id)) return false;
        seen.add(id);
        const st = w.steps.find((x) => x.id === id);
        if (!st) return false;
        const pre = [...st.after, ...st.inputs.flatMap((i) => (i.source.type === "step_output" ? [i.source.step] : []))];
        return pre.some(go);
      };
      return go(from);
    };
    const parallel: string[] = [];
    for (let i = 0; i < c.steps.length; i++) for (let k = i + 1; k < c.steps.length; k++) {
      const x = c.steps[i].id;
      const y = c.steps[k].id;
      const nowIndep = !reach(c, x, y) && !reach(c, y, x);
      const wasIndep = b.steps.some((s) => s.id === x) && b.steps.some((s) => s.id === y) && !reach(b, x, y) && !reach(b, y, x);
      if (nowIndep && !wasIndep) parallel.push(`${x} ∥ ${y}: no ordering edge and no semantic input dependency between them in the candidate`);
    }
    out.push({ kind: b.kind, ordering_edges: edges, semantic_input_changes: inputs, removed_steps: removedSteps,
      max_parallel: { before: b.max_parallel, after: c.max_parallel }, newly_parallel: parallel });
  }
  return out;
}

export function changeView(wb: Workbench, id: string) {
  const st = wb.state();
  const c = st.changes.find((x) => x.id === id);
  if (!c) throw new OpError("UNKNOWN_CHANGE", "unknown change", 404);
  const meta = wb.db.db.prepare("SELECT request_text, created FROM changes_meta WHERE change_id = ?").get(id) as any;
  const jobs = c.jobs.map((jid) => st.jobs.find((j) => j.id === jid)).filter(Boolean) as Job[];
  const releases = st.releases.filter((r) => r.evidence_job && c.jobs.includes(r.evidence_job));
  return {
    change: c,
    request: meta?.request_text ?? null,
    budget: st.budgets.find((b) => b.id === c.budget) ?? null,
    jobs: jobs.map((j) => ({ id: j.id, kind: j.kind, status: j.status, subject: j.subject, release: j.release,
      steps: j.steps.map((s) => ({ id: s.id, status: s.status, outcome: s.accepted?.outcome ?? null, result: s.accepted?.result ?? null })) })),
    candidates: wb.db.db.prepare("SELECT source_digest, revision, author_job, created FROM candidates WHERE change_id = ? ORDER BY created").all(id),
    rejected: wb.db.db.prepare("SELECT author_job, stage, reason, detail_digest, created FROM rejected_candidates WHERE change_id = ? ORDER BY id").all(id),
    revisions: wb.db.db.prepare("SELECT from_job, new_job, status, created FROM revisions WHERE change_id = ? ORDER BY created").all(id),
    releases: releases.map((r) => r.digest),
    graph_changes: jobs.filter((j) => j.kind === "change_evaluate").map((j) => {
      const b = j.steps.find((s) => s.id === "build")?.accepted;
      if (!b || b.outcome !== "pass") return { eval_job: j.id, candidate: j.subject, available: false };
      const receipt = strictParse(wb.blobs.getText(b.result)) as any;
      const base = st.releases.find((r) => r.digest === c.base)!;
      return { eval_job: j.id, candidate: j.subject, available: true, changes: graphChanges(base.workflows, receipt.exports),
        retained_gates: ["build", "prove", "reproduce", "refute"], recipe: receipt.recipe };
    }),
  };
}

export function releaseView(wb: Workbench, ref: string) {
  const digest = resolveRelease(wb, ref);
  const st = wb.state();
  const r = st.releases.find((x) => x.digest === digest);
  if (!r) throw new OpError("UNKNOWN_RELEASE", "unknown release", 404);
  let bundle: Json = null;
  let integrity = "ok";
  try {
    bundle = verifyBundle(wb.settings.stateDir, digest) as unknown as Json;
  } catch (e) {
    integrity = (e as Error).message;
  }
  let build: Json = null;
  let prove: Json = null;
  let tests: Json = null;
  const evidence = (bundle as any)?.envelope?.evidence ?? [];
  for (const ev of evidence) {
    const doc = strictParse(wb.blobs.getText(ev.result)) as any;
    if (ev.role === "build") build = doc;
    if (ev.role === "prove") prove = doc;
    if (ev.role === "protected_tests") tests = doc;
    if (ev.role === "reproduce" && doc.test_report) tests = strictParse(wb.blobs.getText(doc.test_report)) as Json;
  }
  if (!build) {
    try {
      build = bundleBuildReceipt(wb.settings.stateDir, digest) as unknown as Json;
    } catch {
      /* ignore */
    }
  }
  const reviews = evidence.filter((e: any) => ["reproduce", "refute"].includes(e.role)).map((e: any) => {
    const doc = strictParse(wb.blobs.getText(e.result)) as any;
    return { role: e.role, verdict: doc.output?.verdict ?? null, summary: doc.output?.summary ?? null, concerns: doc.output?.concerns ?? [],
      fake: doc.invocation?.fake ?? null, test_report: doc.test_report ?? null };
  });
  return {
    release: r as Release,
    active: st.active === digest,
    activations: st.activations.filter((a) => a.release === digest),
    approvals: st.approvals.filter((a) => a.release === digest),
    integrity,
    bundle,
    build_receipt: build,
    prove_receipt: prove,
    protected_tests: tests,
    reviews,
    assumptions: TRUSTED_ASSUMPTIONS,
  };
}

export const TRUSTED_ASSUMPTIONS = [
  "Lean 4 kernel/checker, compiler and runtime (v4.34.1) are sound; leanchecker --fresh is an independent re-check, not a different logic",
  "Codec (Factory.Json/Codec) and the executable wrapper (Factory.Main) faithfully encode/decode — audited, not proved",
  "SHA-256 collision resistance; digests are computed by trusted host code",
  "SQLite transaction durability (WAL, synchronous=FULL) and the single-writer coordinator",
  "Docker/Linux container isolation (network none, read-only root, caps dropped, non-root) and the host OS",
  "The supervisor's observations (container ids, exit codes, monotonic clock ticks) are authentic",
  "Model reviews are judgments, not proofs; a passing review does not make a candidate correct",
];

export function jobsList(wb: Workbench) {
  const st = wb.state();
  return st.jobs.map((j) => {
    const obs = obsFor(wb, j.id);
    const budget = st.budgets.find((b) => b.id === j.budget);
    return {
      id: j.id, kind: j.kind, status: j.status, release: j.release, subject: j.subject, epoch: j.epoch, revision: j.revision,
      change: j.change,
      steps: j.steps.map((s) => ({ id: s.id, status: s.status })),
      live: j.attempts.filter((a) => LIVE_ATTEMPT.has(a.status)).length,
      cleanup_pending: obs.filter((o) => o.cleanup === "pending").length,
      last_progress: obs.reduce((m: string | null, o: any) => (!m || o.updated > m ? o.updated : m), null),
      budget: budget ? { used: budget.used, limit: budget.limit } : null,
      created: (wb.db.db.prepare("SELECT wall_time FROM journal WHERE accepted = 1 AND events LIKE ? LIMIT 1")
        .get(`%{"job":${JSON.stringify(j.id)},"release":%"type":"job_created"%`) as { wall_time: string } | undefined)?.wall_time ?? null,
    };
  });
}
