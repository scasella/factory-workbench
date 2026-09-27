// A11, A12, A20, A25, A30 — the fixed verifier and sandbox, with REAL
// containers, Lean compilation, statement bridge, axiom audit and replay.
import { test } from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { createHash } from "node:crypto";
import { BlobStore } from "../../../packages/store/blobs.ts";
import { Docker, dockerArgsCreate, execFile, LABEL_ROOT } from "../../../packages/runner/docker.ts";
import { KernelClient, fileDigest } from "../../../apps/control/kernel.ts";
import { REPO_ROOT, loadSettings } from "../../../apps/control/config.ts";
import { importPackageDir, materialize, PathRejected, type SourceManifest } from "../../verifier/package-source.ts";
import { computeIdentities } from "../../verifier/identity.ts";
import { buildPhase, provePhase, receiptDigest, type BuildReceipt, type VerifierEnv } from "../../verifier/verifier.ts";
import { parseAxioms } from "../../verifier/bridge.ts";
import { verifyBundle } from "../../../apps/control/releases.ts";
import { close, createAudit, job, openCopy, tmpDir } from "../harness.ts";

const GENESIS = path.join(REPO_ROOT, "orchestration/genesis");
const sha = (s: string | Buffer) => createHash("sha256").update(s).digest("hex");

async function env(): Promise<{ env: VerifierEnv; blobs: BlobStore; kernel: KernelClient; base: SourceManifest }> {
  const dir = tmpDir("ver");
  const blobs = new BlobStore(path.join(dir, "blobs"));
  const bin = path.join(REPO_ROOT, "protected/lean/.lake/build/bin/factory-kernel");
  const kernel = new KernelClient(bin, fileDigest(bin));
  const docker = new Docker();
  const settings = loadSettings({ stateDir: dir });
  const img = await docker.inspectImage(settings.verifierImage);
  const ids = computeIdentities(REPO_ROOT, settings.verifierImage, img!.id, img!.labels);
  fs.mkdirSync(path.join(dir, "scratch"));
  const e: VerifierEnv = { docker, blobs, kernel, ids, scratch: path.join(dir, "scratch"), instance: `vt${process.pid}`,
    buildTimeoutMs: 600_000, proveTimeoutMs: 1_800_000, testTimeoutMs: 120_000 };
  return { env: e, blobs, kernel, base: importPackageDir(GENESIS, blobs) };
}

function edit(base: SourceManifest, blobs: BlobStore, file: string, f: (t: string) => string): SourceManifest {
  const cur = base.files.find((x) => x.path === file)!;
  return materialize(base, [{ path: file, operation: "replace", expected_sha256: cur.digest, content: f(blobs.getText(cur.digest)) }], blobs).manifest;
}

let n = 0;
const hooks = () => ({ name: `fw-vt${process.pid}-${++n}`, labels: {} });

test("A12: proof cheats fail for recorded reasons; raw stdout/claims never create a receipt", async () => {
  const { env: e, blobs, kernel, base } = await env();
  try {
    const expectLint = async (m: SourceManifest, token: string) => {
      const b = await buildPhase(e, hooks(), m, base);
      assert.equal(b.receipt.outcome, "fail");
      assert.match(b.receipt.failure!, new RegExp(`lint: .*${token}`), `expected lint rejection for ${token}: ${b.receipt.failure}`);
      return b.receipt.failure;
    };
    // Prohibited constructs (compile-time rejections, NOT semantic mutation kills)
    const reasons: Record<string, string | null> = {};
    reasons.sorry = await expectLint(edit(base, blobs, "Proofs.lean", (t) => t.replace("theorem p03 : P03 FactoryPrev.workflows workflows := by unfold P03; decide", "theorem p03 : P03 FactoryPrev.workflows workflows := sorry")), "sorry");
    reasons.extra_axiom = await expectLint(edit(base, blobs, "Proofs.lean", (t) => t.replace("namespace FactoryPkg\nopen", "namespace FactoryPkg\naxiom cheat : False\nopen")), "axiom");
    reasons.native_decide = await expectLint(edit(base, blobs, "Proofs.lean", (t) => t.replace("by unfold P01; decide", "by unfold P01; native_decide")), "native_decide");
    reasons.implemented_by = await expectLint(edit(base, blobs, "Planner.lean", (t) => t.replace("def plan (v : PlannerView)", "def planFast (v : PlannerView) : List StepId := v.ready\n\n@[implemented_by planFast]\ndef plan (v : PlannerView)")), "implemented_by");
    reasons.protected_import = await expectLint(edit(base, blobs, "Proofs.lean", (t) => t.replace("import Factory.PackageContracts", "import Factory.PackageContracts\nimport Factory.Kernel")), "Factory.Kernel");
    reasons.protected_namespace = await expectLint(edit(base, blobs, "Proofs.lean", (t) => t + "\nnamespace Factory.Contracts\nend Factory.Contracts\n"), "Factory.Contracts");
    // Substituted protected module: not even materializable.
    assert.throws(() => materialize(base, [{ path: "Factory/PackageContracts.lean", operation: "create", expected_sha256: null, content: "def P02 := True" }], blobs), PathRejected);

    // Semantic kill 1: weaker theorem statement → trusted bridge rejects the candidate's declaration.
    const weaker = edit(base, blobs, "Proofs.lean", (t) => t.replace(/theorem p02 : P02 plan := by[\s\S]*?\n\ntheorem p03/,
      "theorem p02 : ∀ v : PlannerView, (plan v).length ≤ v.slots := by\n  intro v; simp [plan]; omega\n\ntheorem p03"));
    const bw = await buildPhase(e, hooks(), weaker, base);
    assert.equal(bw.receipt.outcome, "pass", "a weaker proof still builds");
    const pw = await provePhase(e, hooks(), weaker, base, bw.receipt, receiptDigest(bw.receipt));
    assert.equal(pw.outcome, "fail");
    assert.match(pw.failure!, /statement_bridge/);
    reasons.weaker_statement = pw.failure;

    // Semantic kill 2: false "pass" claims + a broken proof. Metadata/comments claiming verification are ignored.
    const liar = materialize(base, [
      { path: "package-metadata.json", operation: "replace", expected_sha256: base.files.find((f) => f.path === "package-metadata.json")!.digest,
        content: JSON.stringify({ name: "liar", verified: true, receipt: { outcome: "pass" }, claims: ["P01", "P02", "P03"] }) },
      { path: "Proofs.lean", operation: "replace", expected_sha256: base.files.find((f) => f.path === "Proofs.lean")!.digest,
        content: blobs.getText(base.files.find((f) => f.path === "Proofs.lean")!.digest).replace("  · simp [plan]; omega\n", "  · -- VERIFIED: all proofs passed\n    simp [plan]\n") },
    ], blobs).manifest;
    const bl = await buildPhase(e, hooks(), liar, base);
    const pl = await provePhase(e, hooks(), liar, base, bl.receipt, receiptDigest(bl.receipt));
    assert.equal(pl.outcome, "fail");
    assert.match(pl.failure!, /candidate_proofs/);
    reasons.false_pass_claim = pl.failure;

    // Semantic kill 3: compiler/binary replacement — binary output that disagrees with the proved
    // definition. Simulated by a build receipt whose observed planner output was altered.
    const good = await buildPhase(e, hooks(), base, base);
    const tampered: BuildReceipt = JSON.parse(JSON.stringify(good.receipt));
    assert.deepEqual(tampered.fixtures[2].plan, ["build"]);
    tampered.fixtures[2].plan = ["prove"]; // what a lying/replaced binary might have produced
    const pt = await provePhase(e, hooks(), base, base, tampered, receiptDigest(tampered));
    assert.equal(pt.outcome, "fail");
    assert.match(pt.failure!, /statement_bridge/, "binary/definition disagreement is caught by the kernel-checked binding");
    reasons.binary_definition_mismatch = pt.failure;

    // Source/binary mismatch: a build receipt for different source cannot be used for this source.
    const other = edit(base, blobs, "prompts/refute.md", (t) => t + "\n");
    const po = await provePhase(e, hooks(), other, base, good.receipt, receiptDigest(good.receipt));
    assert.equal(po.outcome, "fail");
    assert.match(po.failure!, /source_binding/);
    reasons.source_binary_mismatch = po.failure;

    // Axiom audit parser: sorryAx / custom axioms / missing reports are rejected independently of lint.
    const bad = parseAxioms("'FactoryBridge.P01' depends on axioms: [propext, sorryAx]\n'FactoryBridge.P02' depends on axioms: [FactoryPkg.cheat]\n", ["FactoryBridge.P01", "FactoryBridge.P02", "FactoryBridge.P03"]);
    assert.ok(bad.problems.some((p) => /sorryAx/.test(p)));
    assert.ok(bad.problems.some((p) => /FactoryPkg.cheat/.test(p)));
    assert.ok(bad.problems.some((p) => /no axiom report for FactoryBridge.P03/.test(p)));
    const forged = parseAxioms("verified: true\nall proofs passed\n", ["FactoryBridge.P01"]);
    assert.ok(forged.problems.length >= 2, "stdout text cannot stand in for the audit");
    fs.writeFileSync(path.join(REPO_ROOT, "docs", "a12-cheat-reasons.json"), JSON.stringify(reasons, null, 2) + "\n");
  } finally {
    kernel.stop();
  }
});

test("A25: nonvacuity — an empty/reject-all planner fails the fixed plan contract; the positive case passes", async () => {
  const { env: e, blobs, kernel, base } = await env();
  try {
    const empty = edit(base, blobs, "Planner.lean", (t) => t.replace("  (dedup v.ready).take (min 1 v.slots)", "  []"));
    const b = await buildPhase(e, hooks(), empty, base);
    assert.equal(b.receipt.outcome, "fail");
    assert.match(b.receipt.failure!, /fixtures: .*violates the fixed plan contract/);
    const pos = await buildPhase(e, hooks(), base, base);
    assert.equal(pos.receipt.outcome, "pass");
    // Kernel runtime check agrees: empty plan for nonempty ready list with free slots is rejected.
    const v = pos.receipt.fixtures.find((f) => f.view.ready.length > 0 && f.view.slots !== "0")!.view;
    const c = await kernel.query({ op: "check_plan", view: v as any, plan: [] });
    assert.equal(c.plan_ok, false);
  } finally {
    kernel.stop();
  }
});

test("A11: protected file edits are rejected at materialization (kernel, verifier, contracts, build files, isolation profile)", async () => {
  const { blobs, base, kernel } = await env();
  kernel.stop();
  for (const p of ["protected/lean/Factory/Kernel.lean", "Factory/Kernel.lean", "protected/verifier/verifier.ts", "protected/contracts.json",
    "lakefile.toml", "lean-toolchain", "lake-manifest.json", "FactoryExport.lean", "protected/runner-profiles/images/verifier.Dockerfile",
    "prompts/../../protected/contracts.json", "supplemental-tests/x.sh", "FactoryPrev/Planner.lean"]) {
    assert.throws(() => materialize(base, [{ path: p, operation: "create", expected_sha256: null, content: "x" }], blobs), PathRejected, p);
  }
});

test("A20: candidate/build containers cannot read credentials, controller data, host sockets, or the network", async () => {
  const docker = new Docker();
  const settings = loadSettings();
  const dir = tmpDir("a20");
  const inDir = path.join(dir, "in");
  const outDir = path.join(dir, "out");
  fs.mkdirSync(inDir);
  fs.mkdirSync(outDir, { mode: 0o777 });
  fs.chmodSync(outDir, 0o777);
  // planted sentinel in a host location the controller owns (never mounted)
  const sentinel = `SENTINEL-${sha(String(Date.now())).slice(0, 12)}`;
  const secretDir = path.join(dir, "operator", "codex-home");
  fs.mkdirSync(secretDir, { recursive: true });
  fs.writeFileSync(path.join(secretDir, "auth.json"), JSON.stringify({ token: sentinel }));
  fs.writeFileSync(path.join(inDir, "probe.sh"), [
    "id -u", "(getent hosts example.com >/dev/null 2>&1 && echo NET_OK) || echo NET_BLOCKED",
    // the sentinel is split so that only the planted secret file (never mounted) could match
    `S1=${sentinel.slice(0, 5)}; S2=${sentinel.slice(5)}; grep -rsl "$S1$S2" / --exclude-dir=proc --exclude-dir=sys 2>/dev/null | head -1 || true`, "echo GREP_DONE",
    "ls /var/run/docker.sock 2>/dev/null && echo SOCK_PRESENT || echo SOCK_ABSENT",
    "env | grep -i -E 'codex|openai|token' || echo NO_CRED_ENV",
    "touch /opt/factory/x 2>/dev/null && echo PROTECTED_WRITABLE || echo PROTECTED_READONLY",
    "touch /in/x 2>/dev/null && echo IN_WRITABLE || echo IN_READONLY",
  ].join("\n"));
  const spec = { name: `fw-a20-${process.pid}`, image: settings.verifierImage, cmd: ["sh", "/in/probe.sh"],
    labels: { [`${LABEL_ROOT}.instance`]: "a20" },
    mounts: [{ host: inDir, container: "/in", readOnly: true }, { host: outDir, container: "/out", readOnly: false }] };
  const args = dockerArgsCreate(spec);
  assert.ok(!args.join(" ").includes("docker.sock"));
  assert.ok(args.includes("--network") && args[args.indexOf("--network") + 1] === "none");
  const r = await execFile("docker", ["run", "--rm", ...args.slice(1)], { timeoutMs: 180_000 });
  const out = r.stdout;
  assert.match(out, /^10001$/m, "non-root");
  assert.match(out, /NET_BLOCKED/);
  assert.doesNotMatch(out, new RegExp(`${sentinel}`), "credential sentinel unreadable from the build sandbox");
  assert.match(out, /GREP_DONE/);
  assert.match(out, /SOCK_ABSENT/);
  assert.match(out, /NO_CRED_ENV/);
  assert.match(out, /PROTECTED_READONLY/);
  assert.match(out, /IN_READONLY/);
  void docker;
});

test("A30: no fake assurance — with the verifier unavailable, jobs cannot produce verified evidence or publish", async () => {
  const o = await openCopy("a30", { verifierImage: "factory-verifier:does-not-exist" });
  try {
    const { wb } = o;
    assert.equal(wb.verifierAvailable().ok, false);
    await createAudit(wb, "j");
    wb.engine.autoDispatch = true;
    wb.engine.start(100);
    const end = Date.now() + 30_000;
    while (Date.now() < end && !["failed", "succeeded", "blocked"].includes(job(wb, "j").status)) await new Promise((r) => setTimeout(r, 300));
    await wb.engine.stop();
    const j = job(wb, "j");
    assert.notEqual(j.status, "succeeded");
    assert.equal(j.steps.find((s) => s.id === "build")!.accepted, null, "no verifier evidence was fabricated");
    const diag = wb.db.db.prepare("SELECT COUNT(*) AS n FROM job_diagnostics WHERE job = 'j'").get() as { n: number };
    assert.ok(j.status === "failed" || diag.n > 0, "the missing verifier/runtime surfaces as a failure or diagnostic");
    assert.equal(wb.state().reports.length, 0);
    const bad = wb.trustStatus().filter((t) => !t.ok).map((t) => t.id);
    assert.ok(bad.includes("verifier_image_id"));
  } finally {
    await close(o);
  }
});

test("A12b: tampered release bundle binary is detected before activation/execution", async () => {
  const o = await openCopy("a12b");
  try {
    const P0 = o.wb.state().active!;
    const f = path.join(o.dir, "releases", P0, "package.bin");
    fs.chmodSync(f, 0o755);
    fs.appendFileSync(f, Buffer.from([0]));
    assert.throws(() => verifyBundle(o.dir, P0), /digest mismatch/);
  } finally {
    await close(o);
  }
});
