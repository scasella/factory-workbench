// Acceptance tests exercising the REAL Lean kernel + SQLite coordinator with
// authenticated synthetic observations (no containers needed for these IDs).
import { test } from "node:test";
import assert from "node:assert/strict";
import { CommandConflict } from "../../../apps/control/coordinator.ts";
import {
  approveAndActivate, close, commitStep, COORD, createAudit, envelopeFor, invariants, job, OPERATOR, openCopy,
  parallelReviews, publishSynthetic, runAll, runStep, sha, startStep, submit, SUP, transformWorkflows, VER, workflowOf,
} from "../harness.ts";

test("A03: stale result — expire A, authorize B, deliver A's success: rejected, B/current state untouched", async () => {
  const o = await openCopy("a03");
  try {
    const { wb, clock } = o;
    assert.equal((await createAudit(wb, "j")).accepted, true);
    const a = await startStep(wb, "j", "build");
    clock.advance(Number(wb.state().config.lease_ticks)); // now == deadline → expired (equality is expired)
    const exp = await submit(wb, COORD, { type: "expire_attempt", job: "j", step: "build", gen: a.gen });
    assert.equal(exp.accepted, true);
    assert.ok(exp.effects.some((e) => e.kind === "terminate" && e.gen === a.gen), "expiry requests cleanup");
    const b = await startStep(wb, "j", "build");
    assert.notEqual(b.gen, a.gen);
    const before = JSON.stringify(job(wb, "j"));
    const late = await commitStep(wb, "j", "build", a.gen, envelopeFor(wb, "j", "build", { fingerprint: job(wb, "j").attempts[0].fingerprint }));
    assert.equal(late.accepted, false);
    assert.equal(late.reject_code, "STALE_ATTEMPT");
    assert.equal(JSON.stringify(job(wb, "j")), before, "rejected stale result leaves job state unchanged");
    // B can still commit normally
    const ok = await commitStep(wb, "j", "build", b.gen, envelopeFor(wb, "j", "build"));
    assert.equal(ok.accepted, true);
    assert.equal(job(wb, "j").steps[0].accepted!.gen, b.gen);
    // A late heartbeat cannot resurrect the expired attempt
    const hb = await submit(wb, SUP, { type: "heartbeat", job: "j", step: "build", gen: a.gen });
    assert.equal(hb.accepted, false);
    assert.equal((await invariants(wb)).safe, true);
  } finally {
    await close(o);
  }
});

test("A04: duplicate callbacks — repeated delivery yields one accepted commit and one semantic completion", async () => {
  const o = await openCopy("a04");
  try {
    const { wb } = o;
    await createAudit(wb, "j");
    const { gen } = await startStep(wb, "j", "build");
    const env = envelopeFor(wb, "j", "build");
    const r1 = await commitStep(wb, "j", "build", gen, env, "same-id");
    const r2 = await commitStep(wb, "j", "build", gen, env, "same-id");
    assert.equal(r1.accepted, true);
    assert.equal(r2.duplicate, true, "same command id + same bytes returns the original receipt");
    assert.equal(r2.seq, r1.seq);
    const r3 = await commitStep(wb, "j", "build", gen, env, "other-id");
    assert.equal(r3.accepted, true);
    assert.deepEqual(r3.events.map((e: any) => e.type), ["idempotent_replay"], "identical completion is idempotent");
    const accepted = wb.db.db.prepare("SELECT COUNT(*) AS n FROM journal WHERE accepted = 1 AND events LIKE '%result_accepted%'").get() as { n: number };
    assert.equal(accepted.n, 1, "exactly one semantic completion in the journal");
  } finally {
    await close(o);
  }
});

test("A05: conflicting duplicate — reused command id with different bytes, or different result for a completed attempt", async () => {
  const o = await openCopy("a05");
  try {
    const { wb } = o;
    await createAudit(wb, "j");
    const { gen } = await startStep(wb, "j", "build");
    const env = envelopeFor(wb, "j", "build");
    await commitStep(wb, "j", "build", gen, env, "cmd-x");
    await assert.rejects(commitStep(wb, "j", "build", gen, { ...env, result: sha("different") }, "cmd-x"), (e) => e instanceof CommandConflict);
    const conflict = await commitStep(wb, "j", "build", gen, { ...env, result: sha("different") });
    assert.equal(conflict.accepted, false);
    assert.equal(conflict.reject_code, "CONFLICTING_COMPLETION");
    assert.equal(job(wb, "j").steps[0].accepted!.result, env.result, "original accepted result not overwritten");
    const audit = wb.db.db.prepare("SELECT COUNT(*) AS n FROM journal WHERE reject_code = 'CONFLICTING_COMPLETION'").get() as { n: number };
    assert.equal(audit.n, 1, "conflict is audited in the journal");
  } finally {
    await close(o);
  }
});

test("A06: cancellation race (kernel barrier) — no new authority or acceptance after cancel; terminate intents emitted", async () => {
  const o = await openCopy("a06k");
  try {
    const { wb } = o;
    await createAudit(wb, "j");
    // authorized but not yet launched (barrier between authorization and launch)
    const s = await submit(wb, COORD, { type: "start_attempt", job: "j", step: "build", fingerprint: sha("fp") });
    assert.equal(s.accepted, true);
    const gen = job(wb, "j").attempts[0].gen;
    const c = await submit(wb, OPERATOR, { type: "cancel_job", job: "j" });
    assert.equal(c.accepted, true);
    assert.ok(c.effects.some((e) => e.kind === "terminate" && e.gen === gen), "cleanup requested for pre-authorized launch");
    assert.equal(job(wb, "j").attempts[0].status, "cancelled");
    assert.equal(job(wb, "j").epoch, "1", "job epoch advanced");
    for (const cmd of [
      { type: "observe_launch_dispatched", job: "j", step: "build", gen },
      { type: "observe_process_started", job: "j", step: "build", gen, container: "late" },
      { type: "start_attempt", job: "j", step: "build", fingerprint: sha("fp2") },
      { type: "resume_job", job: "j" },
    ] as any[]) {
      const actor = cmd.type === "observe_process_started" ? SUP : cmd.type === "resume_job" ? OPERATOR : COORD;
      const r = await submit(wb, actor, cmd);
      assert.equal(r.accepted, false, `${cmd.type} after cancel must be rejected`);
    }
    const late = await wb.coord.submit(VER, { type: "record_verification", job: "j", step: "build", gen, result: envelopeFor(wb, "j", "build") }, "late-commit");
    assert.equal(late.accepted, false);
    assert.equal(job(wb, "j").steps[0].accepted, null, "no acceptance after cancellation");
    assert.equal(job(wb, "j").status, "cancelled", "terminal status is irreversible");
  } finally {
    await close(o);
  }
});

test("A09: mixed source evidence — evidence is bound to a payload; a changed byte creates a new subject with no evidence", async () => {
  const o = await openCopy("a09");
  try {
    const { wb } = o;
    const P0 = wb.state().active!;
    const pub = await publishSynthetic(wb, "a", transformWorkflows(wb.state().releases[0].workflows, parallelReviews));
    const evalA = job(wb, pub.evalJob);
    const payloadA = evalA.steps.find((s) => s.id === "build")!.accepted!.produced!;
    for (const sid of ["prove", "reproduce", "refute"]) assert.equal(evalA.steps.find((s) => s.id === sid)!.accepted!.subject, payloadA);
    // Source B differs by one byte → different digest → new evaluation job without evidence
    const chg = wb.state().changes.find((c) => c.id === pub.change)!;
    assert.equal(chg.status, "published");
    const r = await submit(wb, OPERATOR, { type: "create_change", change: "chg-b", request: sha("rb"), author_job: "chg-b-a1", budget: "chg-b-b", attempt_limit: "50", revision_limit: "3" });
    assert.equal(r.accepted, true);
    await runAll(wb, "chg-b-a1", { materialize: { produced: sha("source-a-with-one-byte-changed") } });
    await submit(wb, COORD, { type: "register_candidate", change: "chg-b", author_job: "chg-b-a1", eval_job: "chg-b-e1", source: sha("source-a-with-one-byte-changed") });
    await runStep(wb, "chg-b-e1", "build", { produced: sha("payload-b") });
    // Try to publish B now: its reviews do not exist; payload A's reviews are not transferable.
    const p = await submit(wb, COORD, { type: "publish_release", job: "chg-b-e1", release: sha("rel-b"), assets: [] });
    assert.equal(p.accepted, false);
    assert.equal(p.reject_code, "NOT_PUBLISHABLE");
    // Guard check on a forged state: a review bound to payload A inside job B → SUBJECT_MISMATCH
    await runAll(wb, "chg-b-e1");
    const st = JSON.parse(JSON.stringify(wb.state()));
    const jb = st.jobs.find((j: any) => j.id === "chg-b-e1");
    jb.steps.find((s: any) => s.id === "refute").accepted.subject = payloadA;
    const forged = await wb.kernel.query({ op: "apply", state: st, envelope: { actor: COORD, epoch: st.ctrl_epoch, tick: st.clock,
      command: { type: "publish_release", job: "chg-b-e1", release: sha("rel-b2"), assets: [] } } as any });
    assert.equal(forged.accepted, false);
    assert.equal(forged.reject, "SUBJECT_MISMATCH");
    assert.equal(wb.state().active, P0);
  } finally {
    await close(o);
  }
});

test("A10: missing/negative/inconclusive review — no publication (kernel gate)", async () => {
  const o = await openCopy("a10k");
  try {
    const { wb } = o;
    const r = await submit(wb, OPERATOR, { type: "create_change", change: "c", request: sha("r"), author_job: "c-a1", budget: "c-b", attempt_limit: "50", revision_limit: "3" });
    assert.equal(r.accepted, true);
    await runAll(wb, "c-a1", { materialize: { produced: sha("s1") } });
    await submit(wb, COORD, { type: "register_candidate", change: "c", author_job: "c-a1", eval_job: "c-e1", source: sha("s1") });
    await runStep(wb, "c-e1", "build");
    await runStep(wb, "c-e1", "prove");
    await runStep(wb, "c-e1", "reproduce");
    // (a) refutation missing
    let p = await submit(wb, COORD, { type: "publish_release", job: "c-e1", release: sha("x1"), assets: [] });
    assert.equal(p.accepted, false);
    // (b) refutation returns inconclusive → job blocked, never publishable
    const ref = await runStep(wb, "c-e1", "refute", { model_outcome: "inconclusive" });
    assert.equal(ref.accepted, true);
    assert.equal(job(wb, "c-e1").status, "blocked");
    p = await submit(wb, COORD, { type: "publish_release", job: "c-e1", release: sha("x2"), assets: [] });
    assert.equal(p.reject_code, "NOT_PUBLISHABLE");
    // a blocked review cannot be re-asked until it says pass
    const again = await submit(wb, COORD, { type: "start_attempt", job: "c-e1", step: "refute", fingerprint: sha("again") });
    assert.equal(again.accepted, false);
    // (c) forged state: refute evidence marked pass but produced by a failing verdict is impossible; a
    //     forged summary-only job without refute evidence is rejected by the gate
    const st = JSON.parse(JSON.stringify(wb.state()));
    const jj = st.jobs.find((j: any) => j.id === "c-e1");
    jj.status = "succeeded";
    const rf = jj.steps.find((s: any) => s.id === "refute");
    rf.status = "pending";
    rf.accepted = null;
    const forged = await wb.kernel.query({ op: "apply", state: st, envelope: { actor: COORD, epoch: st.ctrl_epoch, tick: st.clock,
      command: { type: "publish_release", job: "c-e1", release: sha("x3"), assets: [] } } as any });
    assert.equal(forged.accepted, false);
    assert.equal(forged.reject, "GATE_FAILED");
  } finally {
    await close(o);
  }
});

test("A13: activation race — two approvals based on P0; the second activation gets BASE_RELEASE_CHANGED", async () => {
  const o = await openCopy("a13");
  try {
    const { wb } = o;
    const P0 = wb.state().active!;
    const w = transformWorkflows(wb.state().releases[0].workflows, parallelReviews);
    const a = await publishSynthetic(wb, "ra", w);
    const b = await publishSynthetic(wb, "rb", w);
    assert.equal((await submit(wb, OPERATOR, { type: "record_approval", approval: "apA", release: a.release, expected_base: P0 })).accepted, true);
    assert.equal((await submit(wb, OPERATOR, { type: "record_approval", approval: "apB", release: b.release, expected_base: P0 })).accepted, true);
    assert.equal((await submit(wb, OPERATOR, { type: "activate_release", release: a.release, expected_active: P0, approval: "apA" })).accepted, true);
    const second = await submit(wb, OPERATOR, { type: "activate_release", release: b.release, expected_active: P0, approval: "apB" });
    assert.equal(second.accepted, false);
    assert.equal(second.reject_code, "BASE_RELEASE_CHANGED");
    // the old approval cannot be silently rebased
    const rebased = await submit(wb, OPERATOR, { type: "activate_release", release: b.release, expected_active: a.release, approval: "apB" });
    assert.equal(rebased.reject_code, "APPROVAL_MISMATCH");
    assert.equal(wb.state().active, a.release);
  } finally {
    await close(o);
  }
});

test("A14: create/activate race — every new job pins exactly one complete release", async () => {
  const o = await openCopy("a14");
  try {
    const { wb } = o;
    const P0 = wb.state().active!;
    const pub = await publishSynthetic(wb, "r14", transformWorkflows(wb.state().releases[0].workflows, parallelReviews));
    await submit(wb, OPERATOR, { type: "record_approval", approval: "ap14", release: pub.release, expected_base: P0 });
    const creates = Array.from({ length: 12 }, (_, i) => createAudit(wb, `race-${i}`));
    const act = submit(wb, OPERATOR, { type: "activate_release", release: pub.release, expected_active: P0, approval: "ap14" });
    const res = await Promise.all([...creates, act]);
    assert.ok(res.every((r) => r.accepted));
    const st = wb.state();
    const actSeq = res[res.length - 1].seq;
    for (let i = 0; i < 12; i++) {
      const j = job(wb, `race-${i}`);
      assert.ok(j.release === P0 || j.release === pub.release);
      assert.equal(j.release, res[i].seq < actSeq ? P0 : pub.release, "pinned release is the default at the job's commit point");
      const wf = workflowOf(st, j);
      assert.deepEqual(j.steps.map((s) => s.id), wf.steps.map((s) => s.id), "steps come from the same release as the pin");
    }
  } finally {
    await close(o);
  }
});

test("A15: safe migration — paused P0 job with committed build/prove migrates to P1, reuses results exactly, completes reviews", async () => {
  const o = await openCopy("a15");
  try {
    const { wb } = o;
    const P0 = wb.state().active!;
    await createAudit(wb, "j");
    await runStep(wb, "j", "build");
    await runStep(wb, "j", "prove");
    const pub = await publishSynthetic(wb, "p1", transformWorkflows(wb.state().releases[0].workflows, parallelReviews));
    assert.equal((await approveAndActivate(wb, pub.release, P0)).accepted, true);
    assert.equal(job(wb, "j").release, P0, "activation did not move the job");
    await submit(wb, OPERATOR, { type: "pause_job", job: "j" });
    assert.equal((await submit(wb, COORD, { type: "acknowledge_quiescence", job: "j", containers_clear: true })).accepted, true);
    const before = job(wb, "j");
    const pv = await wb.kernel.query({ op: "migration_preview", state: wb.state() as any, job: "j", target: pub.release });
    const preview = pv.preview as any;
    assert.equal(preview.can_migrate, true);
    assert.deepEqual(preview.kept, ["build", "prove"]);
    const m = await submit(wb, OPERATOR, { type: "migrate_job", job: "j", target: pub.release, expected_revision: preview.revision });
    assert.equal(m.accepted, true);
    const after = job(wb, "j");
    assert.equal(after.release, pub.release);
    assert.equal(after.status, "paused", "resume is a separate explicit command");
    assert.equal(Number(after.epoch), Number(before.epoch) + 1);
    for (const sid of ["build", "prove"]) {
      assert.deepEqual(after.steps.find((s) => s.id === sid)!.accepted, before.steps.find((s) => s.id === sid)!.accepted,
        "completed evidence keeps its original acceptance-time provenance");
      assert.equal(after.steps.find((s) => s.id === sid)!.accepted!.release, P0, "producer release retained");
    }
    assert.equal(wb.state().migrations.length, 1);
    await submit(wb, OPERATOR, { type: "resume_job", job: "j" });
    // under P1, reproduce and refute are both eligible at once
    const rd = await wb.kernel.query({ op: "ready", state: wb.state() as any, job: "j" });
    assert.deepEqual(rd.ready, ["reproduce", "refute"]);
    assert.equal(rd.slots, "2");
    await runAll(wb, "j");
    assert.equal(job(wb, "j").status, "succeeded");
    assert.equal((await submit(wb, COORD, { type: "publish_report", job: "j", report: sha("rep") })).accepted, true);
    assert.equal((await invariants(wb)).safe, true);
  } finally {
    await close(o);
  }
});

test("A16: unsafe migration — changed fingerprint, unmet prerequisite, active attempt, stale preview are rejected without moving versions", async () => {
  const o = await openCopy("a16");
  try {
    const { wb } = o;
    const P0 = wb.state().active!;
    const g = wb.state().releases[0].workflows;
    // (1) target changes a completed step's semantic inputs (fingerprint identity)
    const changedInputs = transformWorkflows(g, (w) => {
      if (w.kind === "change_author") return w;
      const b = w.steps.find((s) => s.id === "build")!;
      b.inputs = [{ name: "candidate", source: { type: "job_input" } }, { name: "extra", source: { type: "job_input" } }];
      return w;
    });
    // (2) target adds a NEW pending step and makes the completed `prove` depend on it
    //     (downward closure of completed prerequisites would be violated)
    const newPrereq = transformWorkflows(g, (w) => {
      if (w.kind === "change_author") return w;
      const [build, prove, ...rest] = w.steps;
      const note = { id: "note", role: "summarize" as const, after: [], inputs: [], prompt: "prompts/summarize.md", retries: "0" };
      w.steps = [build, note, { ...prove, after: ["note"] }, ...rest];
      return w;
    });
    const r1 = await publishSynthetic(wb, "bad1", changedInputs);
    const r2 = await publishSynthetic(wb, "bad2", newPrereq);
    await approveAndActivate(wb, r1.release, P0, "ap1");
    await approveAndActivate(wb, r2.release, r1.release, "ap2");
    await createAudit(wb, "j", P0);
    await runStep(wb, "j", "build");
    await runStep(wb, "j", "prove");
    // active attempt / not paused
    await startStep(wb, "j", "reproduce");
    let pv = (await wb.kernel.query({ op: "migration_preview", state: wb.state() as any, job: "j", target: r1.release })).preview as any;
    let m = await submit(wb, OPERATOR, { type: "migrate_job", job: "j", target: r1.release, expected_revision: pv.revision });
    assert.equal(m.reject_code, "MIGRATION_INELIGIBLE");
    // settle and pause
    const gen = job(wb, "j").attempts.at(-1)!.gen;
    await commitStep(wb, "j", "reproduce", gen, envelopeFor(wb, "j", "reproduce"));
    await submit(wb, OPERATOR, { type: "pause_job", job: "j" });
    await submit(wb, COORD, { type: "acknowledge_quiescence", job: "j", containers_clear: true });
    for (const t of [r1.release, r2.release]) {
      pv = (await wb.kernel.query({ op: "migration_preview", state: wb.state() as any, job: "j", target: t })).preview as any;
      assert.equal(pv.can_migrate, false);
      assert.ok(pv.reasons.length > 0);
      m = await submit(wb, OPERATOR, { type: "migrate_job", job: "j", target: t, expected_revision: pv.revision });
      assert.equal(m.reject_code, "MIGRATION_INELIGIBLE");
    }
    // stale preview: revision moves (resume+pause) after the preview was computed
    const good = await publishSynthetic(wb, "good", transformWorkflows(g, parallelReviews));
    await approveAndActivate(wb, good.release, r2.release, "ap3");
    pv = (await wb.kernel.query({ op: "migration_preview", state: wb.state() as any, job: "j", target: good.release })).preview as any;
    assert.equal(pv.can_migrate, true);
    await submit(wb, OPERATOR, { type: "resume_job", job: "j" });
    await submit(wb, OPERATOR, { type: "pause_job", job: "j" });
    await submit(wb, COORD, { type: "acknowledge_quiescence", job: "j", containers_clear: true });
    m = await submit(wb, OPERATOR, { type: "migrate_job", job: "j", target: good.release, expected_revision: pv.revision });
    assert.equal(m.reject_code, "STALE_MIGRATION_PLAN");
    assert.equal(job(wb, "j").release, P0, "job stayed on its old version throughout");
    // self-improvement jobs are never migrated
    const ev = job(wb, good.evalJob);
    assert.equal(ev.kind, "change_evaluate");
  } finally {
    await close(o);
  }
});

test("A17: pinning — jobs not selected for migration finish on P0 after P1 activation; P0 artifacts retained", async () => {
  const o = await openCopy("a17");
  try {
    const { wb } = o;
    const P0 = wb.state().active!;
    await createAudit(wb, "old");
    await runStep(wb, "old", "build");
    const pub = await publishSynthetic(wb, "p1", transformWorkflows(wb.state().releases[0].workflows, parallelReviews));
    await approveAndActivate(wb, pub.release, P0);
    await runAll(wb, "old");
    const j = job(wb, "old");
    assert.equal(j.status, "succeeded");
    assert.equal(j.release, P0);
    assert.ok(j.steps.every((s) => s.accepted!.release === P0));
    const { verifyBundle } = await import("../../../apps/control/releases.ts");
    assert.doesNotThrow(() => verifyBundle(wb.settings.stateDir, P0), "P0 bundle retained and intact");
    await createAudit(wb, "new");
    assert.equal(job(wb, "new").release, pub.release);
  } finally {
    await close(o);
  }
});

test("A18: rollback — re-activating P0 changes only future defaults; P1 jobs/history unchanged", async () => {
  const o = await openCopy("a18");
  try {
    const { wb } = o;
    const P0 = wb.state().active!;
    const pub = await publishSynthetic(wb, "p1", transformWorkflows(wb.state().releases[0].workflows, parallelReviews));
    await approveAndActivate(wb, pub.release, P0, "ap-fwd");
    await createAudit(wb, "on-p1");
    await runStep(wb, "on-p1", "build");
    const snapshot = JSON.stringify(job(wb, "on-p1"));
    const rb = await approveAndActivate(wb, P0, pub.release, "ap-back");
    assert.equal(rb.accepted, true, "rollback is an audited activation with explicit approval");
    assert.equal(wb.state().active, P0);
    assert.equal(JSON.stringify(job(wb, "on-p1")), snapshot, "existing P1 job untouched");
    await createAudit(wb, "after-rollback");
    assert.equal(job(wb, "after-rollback").release, P0);
    assert.equal(wb.state().activations.length, 3);
  } finally {
    await close(o);
  }
});

test("A28: budgets — retries, restarts, child jobs and revisions do not reset parent limits", async () => {
  const o = await openCopy("a28");
  try {
    const { wb, clock } = o;
    // audit job with an attempt budget of 3: retries consume budget
    await createAudit(wb, "j", null, 3);
    for (let i = 0; i < 2; i++) {
      const a = await startStep(wb, "j", "build");
      assert.equal(a.receipt.accepted, true);
      await submit(wb, SUP, { type: "fail_attempt", job: "j", step: "build", gen: a.gen });
    }
    // build.retries = 1 → two transport failures fail the step (and job)
    assert.equal(job(wb, "j").status, "failed");
    await createAudit(wb, "k", null, 2);
    const a1 = await startStep(wb, "k", "build");
    // restart (new controller epoch) does not reset consumed attempts
    await wb.recover();
    const b = wb.state().budgets.find((x) => x.id === "k-b")!;
    assert.equal(b.used, "1");
    assert.equal(job(wb, "k").attempts[0].status, "lost");
    const a2 = await startStep(wb, "k", "build");
    assert.equal(a2.receipt.accepted, true);
    clock.advance(1);
    await submit(wb, SUP, { type: "fail_attempt", job: "k", step: "build", gen: a2.gen });
    // budget 2 exhausted: no more authorization (step may still be retryable by policy)
    const k = job(wb, "k");
    if (k.status !== "failed") {
      const a3 = await submit(wb, COORD, { type: "start_attempt", job: "k", step: "build", fingerprint: sha("x") });
      assert.equal(a3.reject_code, "BUDGET_EXHAUSTED");
    }
    void a1;
    // change requests: author/eval jobs share one budget; revisions bounded
    const r = await submit(wb, OPERATOR, { type: "create_change", change: "c", request: sha("r"), author_job: "c-a1", budget: "c-b", attempt_limit: "3", revision_limit: "2" });
    assert.equal(r.accepted, true);
    await runAll(wb, "c-a1", { materialize: { produced: sha("s") } });
    await submit(wb, COORD, { type: "register_candidate", change: "c", author_job: "c-a1", eval_job: "c-e1", source: sha("s") });
    const e1 = await startStep(wb, "c-e1", "build");
    assert.equal(e1.receipt.accepted, true, "third attempt of the shared change budget");
    const e2 = await submit(wb, COORD, { type: "start_attempt", job: "c-e1", step: "build", fingerprint: sha("y") });
    assert.ok(!e2.accepted, "child job cannot exceed the parent change budget");
    assert.equal((await submit(wb, OPERATOR, { type: "revise_change", change: "c", author_job: "c-a2", diagnostics: sha("d") })).accepted, true);
    const rv = await submit(wb, OPERATOR, { type: "revise_change", change: "c", author_job: "c-a3", diagnostics: sha("d2") });
    assert.equal(rv.reject_code, "REVISION_BUDGET_EXHAUSTED");
    const c2 = await submit(wb, COORD, { type: "start_attempt", job: "c-a2", step: "author", fingerprint: sha("z") });
    assert.equal(c2.reject_code, "BUDGET_EXHAUSTED", "new revision does not get a fresh budget");
  } finally {
    await close(o);
  }
});

test("A29: approval integrity — forged, changed-digest and revoked approvals fail; revocation does not rewrite history", async () => {
  const o = await openCopy("a29");
  try {
    const { wb } = o;
    const P0 = wb.state().active!;
    const w = transformWorkflows(wb.state().releases[0].workflows, parallelReviews);
    const a = await publishSynthetic(wb, "ra", w);
    const b = await publishSynthetic(wb, "rb", w);
    const forged = await submit(wb, OPERATOR, { type: "activate_release", release: a.release, expected_active: P0, approval: "never-recorded" });
    assert.equal(forged.reject_code, "UNKNOWN_APPROVAL");
    await submit(wb, OPERATOR, { type: "record_approval", approval: "apA", release: a.release, expected_base: P0 });
    const wrong = await submit(wb, OPERATOR, { type: "activate_release", release: b.release, expected_active: P0, approval: "apA" });
    assert.equal(wrong.reject_code, "APPROVAL_MISMATCH");
    // model/agent actors cannot approve or activate
    const byAgent = await submit(wb, SUP, { type: "record_approval", approval: "apX", release: b.release, expected_base: P0 });
    assert.equal(byAgent.reject_code, "UNAUTHORIZED_ACTOR");
    await submit(wb, OPERATOR, { type: "record_approval", approval: "apB", release: b.release, expected_base: P0 });
    await submit(wb, OPERATOR, { type: "revoke_approval", approval: "apB" });
    const revoked = await submit(wb, OPERATOR, { type: "activate_release", release: b.release, expected_active: P0, approval: "apB" });
    assert.equal(revoked.reject_code, "APPROVAL_REVOKED");
    assert.equal((await submit(wb, OPERATOR, { type: "activate_release", release: a.release, expected_active: P0, approval: "apA" })).accepted, true);
    await submit(wb, OPERATOR, { type: "revoke_approval", approval: "apA" });
    assert.equal(wb.state().active, a.release, "revocation does not undo an earlier valid activation");
    assert.equal(wb.state().activations.at(-1)!.approval, "apA");
    assert.equal((await invariants(wb)).safe, true, "K07 history invariant still holds after revocation");
  } finally {
    await close(o);
  }
});

test("A22: replay — rebuild authoritative state from genesis and the accepted journal without any LLM call", async () => {
  const o = await openCopy("a22");
  try {
    const { wb } = o;
    const P0 = wb.state().active!;
    await createAudit(wb, "j");
    await runAll(wb, "j");
    const pub = await publishSynthetic(wb, "p1", transformWorkflows(wb.state().releases[0].workflows, parallelReviews));
    await approveAndActivate(wb, pub.release, P0);
    await submit(wb, OPERATOR, { type: "cancel_job", job: "nonexistent" });
    const calls = wb.db.db.prepare("SELECT COUNT(*) AS n FROM invocations").get() as { n: number };
    const v = await wb.coord.verifyJournal();
    assert.equal(v.ok, true, v.detail.join("; "));
    assert.ok(v.entries > 40);
    const calls2 = wb.db.db.prepare("SELECT COUNT(*) AS n FROM invocations").get() as { n: number };
    assert.equal(calls2.n, calls.n, "replay performed no model invocations");
  } finally {
    await close(o);
  }
});
