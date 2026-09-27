// A21 (path attacks) and A23 (crash persistence) — real blob store, SQLite, kernel.
import { test } from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { BlobStore } from "../../../packages/store/blobs.ts";
import { importPackageDir, materialize, PathRejected, checkPackagePath, type SourceManifest } from "../../verifier/package-source.ts";
import { REPO_ROOT } from "../../../apps/control/config.ts";
import { close, createAudit, envelopeFor, job, openCopy, sha, startStep, submit, SUP, tmpDir, VER } from "../harness.ts";

const GENESIS = path.join(REPO_ROOT, "orchestration/genesis");

test("A21: path attacks — traversal, absolute, hidden, symlinks, hard links, wrong preimage, oversized, unicode", () => {
  const blobs = new BlobStore(tmpDir("a21") + "/blobs");
  const base = importPackageDir(GENESIS, blobs);
  const pkg = base.files.find((f) => f.path === "Package.lean")!;
  const edit = (p: string, extra: Partial<{ operation: any; expected_sha256: string | null; content: string | null }> = {}) =>
    ({ path: p, operation: "replace" as const, expected_sha256: pkg.digest, content: "x", ...extra });
  const rejects = (edits: any[], why: RegExp) => assert.throws(() => materialize(base, edits, blobs), (e) => e instanceof PathRejected && why.test(e.message));
  rejects([edit("../protected/lean/Factory/Kernel.lean")], /traversal|disallowed|allowlist/);
  rejects([edit("/etc/passwd")], /absolute|disallowed/);
  rejects([edit("prompts/../../x.md")], /traversal/);
  rejects([edit(".git/config")], /hidden|traversal/);
  rejects([edit("lakefile.toml")], /allowlist/);
  rejects([edit("protected/contracts.json")], /allowlist/);
  rejects([edit("Package.lean", { expected_sha256: sha("wrong") })], /wrong preimage/);
  rejects([edit("prompts/new.md", { operation: "create", expected_sha256: null, content: "a".repeat(300 * 1024) })], /exceeds/);
  rejects([edit("prompts/réfute.md", { operation: "create", expected_sha256: null })], /non-NFC|disallowed/);
  rejects([edit("prompts/x‮.md", { operation: "create", expected_sha256: null })], /disallowed/);
  rejects([edit("Package.lean", { content: "namespace FactoryPkg‮ end" })], /bidi|control/);
  rejects([edit("Proofs.lean", { operation: "delete", content: null, expected_sha256: base.files.find((f) => f.path === "Proofs.lean")!.digest })], /required/);
  rejects(Array.from({ length: 17 }, (_, i) => edit(`prompts/p${i}.md`, { operation: "create", expected_sha256: null })), /too many edits/);
  assert.throws(() => checkPackagePath("supplemental-tests/../../run.sh"), PathRejected);
  // symlink and hard link in an imported package dir
  const d = tmpDir("a21pkg");
  fs.cpSync(GENESIS, d, { recursive: true });
  fs.symlinkSync("/etc/hosts", path.join(d, "prompts", "evil.md"));
  assert.throws(() => importPackageDir(d, blobs), (e) => e instanceof PathRejected && /symlink/.test(e.message));
  fs.rmSync(path.join(d, "prompts", "evil.md"));
  fs.linkSync(path.join(d, "Package.lean"), path.join(d, "prompts", "hard.md"));
  assert.throws(() => importPackageDir(d, blobs), (e) => e instanceof PathRejected && /hard link/.test(e.message));
  // a valid edit still works and never touches anything outside the manifest
  const ok = materialize(base, [edit("prompts/refute.md", { expected_sha256: base.files.find((f) => f.path === "prompts/refute.md")!.digest, content: "new prompt" })], blobs);
  assert.deepEqual(ok.changed, ["prompts/refute.md"]);
});

test("A23: crash persistence — failures around blob fsync/rename, journal commit, receipt return, outbox dispatch", async () => {
  // Blob store: crash before rename leaves no committed reference and no visible blob.
  const blobs = new BlobStore(tmpDir("a23b"));
  blobs.faults.beforeRename = () => {
    throw new Error("crash before rename");
  };
  assert.throws(() => blobs.put("payload-1"));
  assert.equal(blobs.has(sha("payload-1")), false, "incomplete blob is not visible under its digest");
  blobs.faults = {};
  blobs.faults.beforeDirSync = () => {
    throw new Error("crash before directory sync");
  };
  assert.throws(() => blobs.put("payload-2"));
  blobs.faults = {};
  assert.equal(blobs.put("payload-2"), sha("payload-2"), "retry after crash is idempotent and verified");
  assert.equal(blobs.getText(sha("payload-2")), "payload-2");
  fs.chmodSync(blobs.pathFor(sha("payload-2")), 0o600);
  fs.writeFileSync(blobs.pathFor(sha("payload-2")), "tampered");
  assert.throws(() => blobs.get(sha("payload-2")), /corrupt/, "corruption fails closed");

  const o = await openCopy("a23");
  try {
    const { wb } = o;
    await createAudit(wb, "j");
    const before = wb.coord.stateText();
    const journalBefore = (wb.db.db.prepare("SELECT COUNT(*) AS n FROM journal").get() as { n: number }).n;
    // Crash after kernel decision, before COMMIT → nothing persisted.
    wb.coord.faults.afterKernelBeforeCommit = () => {
      throw new Error("crash before commit");
    };
    await assert.rejects(submit(wb, { type: "coordinator" }, { type: "start_attempt", job: "j", step: "build", fingerprint: sha("f") }, "x"));
    wb.coord.faults = {};
    assert.equal(wb.coord.stateText().digest, before.digest, "state unchanged");
    assert.equal((wb.db.db.prepare("SELECT COUNT(*) AS n FROM journal").get() as { n: number }).n, journalBefore);
    assert.equal((wb.db.db.prepare("SELECT COUNT(*) AS n FROM outbox WHERE effect_id LIKE 'launch:j:%'").get() as { n: number }).n, 0, "no outbox intent without a committed transition");
    // Crash after COMMIT, before the receipt is returned → retry with the same command id returns the committed receipt.
    wb.coord.faults.afterCommitBeforeReturn = () => {
      throw new Error("crash after commit");
    };
    await assert.rejects(wb.coord.submit({ type: "coordinator" }, { type: "start_attempt", job: "j", step: "build", fingerprint: sha("f") }, "same-cmd"));
    wb.coord.faults = {};
    const again = await wb.coord.submit({ type: "coordinator" }, { type: "start_attempt", job: "j", step: "build", fingerprint: sha("f") }, "same-cmd");
    assert.equal(again.duplicate, true);
    assert.equal(again.accepted, true);
    assert.equal(job(wb, "j").attempts.length, 1, "no second authorization");
    // Outbox dispatch crash: intent committed, never dispatched → recovery supersedes it and fences the attempt.
    const pend = wb.db.db.prepare("SELECT status FROM outbox WHERE effect_id = 'launch:j:build:1'").get() as { status: string };
    assert.equal(pend.status, "pending");
    const rec = await wb.recover();
    assert.ok(rec.superseded >= 1);
    assert.equal(job(wb, "j").attempts[0].status, "lost", "uncertain execution is never marked succeeded");
    const late = await wb.coord.submit(VER, { type: "record_verification", job: "j", step: "build", gen: "1", result: envelopeFor(wb, "j", "build") }, "late");
    assert.equal(late.accepted, false);
    // Kernel fault → mutation disabled (fail closed) until diagnosed.
    const o2 = wb.kernel;
    (o2 as any).expectedDigest = sha("not-the-kernel");
    o2.stop();
    await assert.rejects(submit(wb, SUP, { type: "heartbeat", job: "j", step: "build", gen: "1" }));
    assert.ok(wb.coord.disabled, "coordinator disabled after kernel fault");
    const v = (await startStep(wb, "j", "build").catch((e) => ({ err: e }))) as any;
    assert.ok(v.err, "no further mutation");
  } finally {
    await close(o);
  }
});
