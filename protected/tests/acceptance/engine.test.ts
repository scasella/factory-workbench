// A01, A02, A06, A07, A08, A10 — the full engine with REAL containers, Lean
// build/proof replay and the deterministic FAKE Codex CLI for inference.
import { test } from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { spawn } from "node:child_process";
import { Docker, LABEL_ROOT } from "../../../packages/runner/docker.ts";
import { REPO_ROOT, loadSettings } from "../../../apps/control/config.ts";
import { Workbench } from "../../../apps/control/workbench.ts";
import { ManualClock } from "../../../apps/control/coordinator.ts";
import { close, createAudit, job, openCopy, sha, submit, OPERATOR, COORD, type Opened } from "../harness.ts";

const sleep = (ms: number) => new Promise((r) => setTimeout(r, ms));

async function until(o: Opened, pred: () => boolean, label: string, ms = 600_000) {
  const end = Date.now() + ms;
  while (Date.now() < end) {
    if (pred()) return;
    await sleep(250);
  }
  throw new Error(`timeout: ${label}`);
}

const terminal = (s: string) => ["succeeded", "failed", "blocked", "cancelled"].includes(s);

test("A01: happy path — real build, proof replay and two distinct review attempts; publication requires their evidence", async () => {
  const o = await openCopy("a01");
  try {
    const { wb } = o;
    await createAudit(wb, "j");
    // publication before evidence exists is rejected by the kernel
    const early = await submit(wb, COORD, { type: "publish_report", job: "j", report: sha("early") });
    assert.equal(early.reject_code, "NOT_PUBLISHABLE");
    wb.engine.autoDispatch = true;
    wb.engine.start(150);
    await until(o, () => wb.state().reports.some((r) => r.job === "j"), "report published");
    await wb.engine.stop();
    const j = job(wb, "j");
    assert.equal(j.status, "succeeded");
    const by = (id: string) => j.steps.find((s) => s.id === id)!.accepted!;
    const payload = by("build").produced!;
    for (const s of ["prove", "reproduce", "refute"]) assert.equal(by(s).subject, payload, `${s} bound to the payload`);
    const build = JSON.parse(wb.blobs.getText(by("build").result));
    const prove = JSON.parse(wb.blobs.getText(by("prove").result));
    assert.equal(build.kind, "build");
    assert.equal(prove.kind, "prove");
    assert.ok(prove.checks.some((c: any) => c.id === "independent_replay" && c.outcome === "pass"), "leanchecker replay ran");
    assert.ok(prove.obligations.every((ob: any) => ob.ok));
    const rep = JSON.parse(wb.blobs.getText(by("reproduce").result));
    const ref = JSON.parse(wb.blobs.getText(by("refute").result));
    assert.equal(rep.invocation.fake, true, "inference is labeled fake");
    assert.notEqual(rep.invocation.id, ref.invocation.id, "two distinct review invocations");
    assert.notEqual(rep.invocation.context_digest, ref.invocation.context_digest, "separate contexts");
    assert.ok(rep.test_report, "reproduction includes the protected test run");
    const refContext = wb.db.db.prepare("SELECT context_digest FROM invocations WHERE role = 'refute'").get() as { context_digest: string };
    assert.ok(refContext);
    const report = wb.state().reports.find((r) => r.job === "j")!;
    assert.equal(report.subject, payload);
    assert.equal((await wb.coord.verifyJournal()).ok, true);
  } finally {
    await close(o);
  }
});

test("A02: restart after committed completion — the committed step is not reinvoked; its artifact is unchanged", async () => {
  const o = await openCopy("a02");
  const dir = o.dir;
  let wb = o.wb;
  try {
    await createAudit(wb, "j");
    // run only the build step, then stop before the next step is scheduled
    await wb.engine.schedule();
    await wb.engine.dispatchEffects();
    await until(o, () => !!job(wb, "j").steps[0].accepted, "build committed", 300_000);
    const build = JSON.parse(JSON.stringify(job(wb, "j").steps[0].accepted));
    const artifact = wb.blobs.get(build.result);
    await wb.close();
    // restart (new controller epoch), then run to completion
    wb = await Workbench.open(o.settings, { clock: new ManualClock() });
    await wb.recover();
    wb.engine.start(150);
    await until({ ...o, wb }, () => terminal(job(wb, "j").status), "job terminal");
    await wb.engine.stop();
    const j = job(wb, "j");
    assert.equal(j.status, "succeeded");
    assert.equal(j.attempts.filter((a) => a.step === "build").length, 1, "build was not reinvoked");
    assert.deepEqual(j.steps[0].accepted, build, "accepted build result identical (incl. acceptance-time epoch/gen)");
    assert.ok(wb.blobs.get(build.result).equals(artifact), "artifact bytes unchanged");
    assert.ok(Number(wb.state().ctrl_epoch) > Number(build.ctrl_epoch));
  } finally {
    await wb.close();
    fs.rmSync(dir, { recursive: true, force: true });
  }
});

test("A06: cancellation race with a live container — authority revoked at commit; container cleaned up; result rejected", async () => {
  const o = await openCopy("a06");
  try {
    const { wb } = o;
    await createAudit(wb, "j");
    wb.engine.autoDispatch = true;
    wb.engine.start(150);
    const docker = new Docker();
    await until(o, () => job(wb, "j").attempts.some((a) => a.step === "prove" && a.status === "running"), "prove running");
    const inv0 = (await docker.inventory(wb.settings.instance)).filter((c) => c.labels[`${LABEL_ROOT}.job`] === "j");
    assert.ok(inv0.length >= 1, "prove container exists");
    const c = await submit(wb, OPERATOR, { type: "cancel_job", job: "j" });
    assert.equal(c.accepted, true);
    assert.equal(job(wb, "j").status, "cancelled", "authority revoked in the committed state immediately");
    await until(o, () => {
      const row = wb.db.db.prepare("SELECT cleanup FROM attempt_obs WHERE job = 'j' AND step = 'prove'").get() as { cleanup: string } | undefined;
      return row?.cleanup === "done";
    }, "cleanup done", 120_000);
    await sleep(2000);
    const inv1 = (await docker.inventory(wb.settings.instance)).filter((c) => c.labels[`${LABEL_ROOT}.job`] === "j");
    assert.equal(inv1.length, 0, "process tree/container terminated");
    await wb.engine.stop();
    const j = job(wb, "j");
    assert.equal(j.steps.find((s) => s.id === "prove")!.accepted, null, "no accepted completion after cancellation");
    assert.ok(j.attempts.filter((a) => a.step === "prove").every((a) => a.status === "cancelled"));
  } finally {
    await close(o);
  }
});

test("A10: negative and inconclusive reviews block publication end-to-end; the reviewer is not re-asked until pass", async () => {
  for (const [scenario, expect] of [["scenario-refute-fail.json", "failed"], ["scenario-refute-inconclusive.json", "blocked"]] as const) {
    const o = await openCopy(`a10-${expect}`, {}, scenario);
    try {
      const { wb } = o;
      await createAudit(wb, "j");
      wb.engine.autoDispatch = true;
      wb.engine.start(150);
      await until(o, () => terminal(job(wb, "j").status), `job ${expect}`);
      await sleep(1500);
      await wb.engine.stop();
      const j = job(wb, "j");
      assert.equal(j.status, expect);
      assert.equal(j.attempts.filter((a) => a.step === "refute").length, 1, "no repeated asking");
      assert.equal(wb.state().reports.length, 0, "no publication");
      const p = await submit(wb, COORD, { type: "publish_report", job: "j", report: sha("x") });
      assert.equal(p.accepted, false);
    } finally {
      await close(o);
    }
  }
});

// ---------------------------------------------------------------------------
// Process-level crash tests: the workbench runs as a child process and is killed.

function serve(dir: string, port: number, env: Record<string, string> = {}) {
  const p = spawn(process.execPath, [path.join(REPO_ROOT, "apps/control/cli.ts"), "serve", "--state", dir, "--port", String(port)],
    { stdio: ["ignore", "pipe", "pipe"], env: { ...process.env, ...env } });
  let buf = "";
  p.stdout!.on("data", (d) => (buf += d));
  p.stderr!.on("data", (d) => (buf += d));
  const ready = (async () => {
    for (let i = 0; i < 200; i++) {
      if (buf.includes("serving on")) return;
      if (p.exitCode !== null) throw new Error(buf);
      await sleep(200);
    }
    throw new Error("server did not start");
  })();
  return { p, ready, out: () => buf };
}

async function api(dir: string, port: number, method: string, route: string, body?: unknown) {
  const token = fs.readFileSync(path.join(dir, "operator", "token"), "utf8").trim();
  const r = await fetch(`http://127.0.0.1:${port}${route}`, { method, headers: { Authorization: `Bearer ${token}`, "Content-Type": "application/json", "X-Factory-Request": "1" },
    body: body === undefined ? undefined : JSON.stringify(body) });
  return r.json() as any;
}

async function copyState(tag: string): Promise<string> {
  const o = await openCopy(tag);
  const dir = o.dir;
  await o.wb.close();
  return dir;
}

test("A07: lost supervisor/process — kill the workbench mid-attempt; recovery fences, terminates the container, retries", async () => {
  const dir = await copyState("a07");
  const port = 4460 + (process.pid % 100);
  let s = serve(dir, port);
  try {
    await s.ready;
    const j = (await api(dir, port, "POST", "/api/jobs", { fixture: "genesis-package", command_id: "a07-job" })).job;
    let view: any;
    for (let i = 0; i < 600; i++) {
      view = await api(dir, port, "GET", `/api/jobs/${j}`);
      if (view.attempts.some((a: any) => a.step === "prove" && a.status === "running")) break;
      await sleep(250);
    }
    const settings = loadSettings({ stateDir: dir });
    s.p.kill("SIGKILL");
    await new Promise((r) => s.p.on("close", r));
    const docker = new Docker();
    const orphans = (await docker.inventory(settings.instance)).filter((c) => c.labels[`${LABEL_ROOT}.job`] === j);
    assert.ok(orphans.length >= 1, "container survived the controller crash (to be reconciled)");
    s = serve(dir, port);
    await s.ready;
    await sleep(1500);
    const after = (await docker.inventory(settings.instance)).filter((c) => orphans.some((o) => o.id === c.id));
    assert.equal(after.length, 0, "old container terminated by recovery (not by broad name matching)");
    for (let i = 0; i < 1200; i++) {
      view = await api(dir, port, "GET", `/api/jobs/${j}`);
      if (terminal(view.status)) break;
      await sleep(500);
    }
    assert.equal(view.status, "succeeded");
    const prove = view.attempts.filter((a: any) => a.step === "prove");
    assert.ok(prove.some((a: any) => a.status === "lost"), "the in-flight attempt is marked lost, not finished");
    assert.equal(prove.filter((a: any) => a.status === "succeeded").length, 1);
    assert.equal(view.attempts.filter((a: any) => a.step === "build").length, 1, "finished work not recomputed");
  } finally {
    s.p.kill("SIGTERM");
    await new Promise((r) => s.p.on("close", r));
    fs.rmSync(dir, { recursive: true, force: true });
  }
});

test("A08: launch uncertainty — crash between container launch and recording it; recover without blind double launch", async () => {
  const dir = await copyState("a08");
  const port = 4560 + (process.pid % 100);
  let s = serve(dir, port, { FACTORY_TEST_MODE: "1", FACTORY_TEST_FAULT: "crash_after_start:build" });
  try {
    await s.ready;
    const j = (await api(dir, port, "POST", "/api/jobs", { fixture: "genesis-package", command_id: "a08-job" })).job;
    await new Promise((r) => s.p.on("close", r));
    const settings = loadSettings({ stateDir: dir });
    const docker = new Docker();
    const orphans = (await docker.inventory(settings.instance)).filter((c) => c.labels[`${LABEL_ROOT}.job`] === j);
    assert.ok(orphans.length >= 1, "uncertain launch left a labeled container");
    s = serve(dir, port);
    await s.ready;
    let view: any;
    for (let i = 0; i < 1200; i++) {
      view = await api(dir, port, "GET", `/api/jobs/${j}`);
      if (terminal(view.status)) break;
      await sleep(500);
    }
    assert.equal(view.status, "succeeded");
    const builds = view.attempts.filter((a: any) => a.step === "build");
    assert.equal(builds[0].status, "lost", "uncertain execution never marked succeeded");
    assert.equal(builds.filter((a: any) => a.status === "succeeded").length, 1, "exactly one accepted build");
    assert.notEqual(builds[0].ctrl_epoch, builds[builds.length - 1].ctrl_epoch, "retry happened only after fencing (new epoch)");
    const still = (await docker.inventory(settings.instance)).filter((c) => orphans.some((o) => o.id === c.id));
    assert.equal(still.length, 0);
  } finally {
    s.p.kill("SIGTERM");
    await new Promise((r) => s.p.on("close", r));
    fs.rmSync(dir, { recursive: true, force: true });
  }
});
