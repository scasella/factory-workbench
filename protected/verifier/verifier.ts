// The fixed, protected verifier (§9.3). It produces receipts ONLY from what
// it observes: container exit codes, files collected by the trusted collector,
// kernel-checked bridge elaboration, axiom reports and leanchecker replay.
// Candidate stdout, manifests or "verified: true" claims are never evidence.

import * as fs from "node:fs";
import * as path from "node:path";
import { canonicalize, digestOf, sha256Hex, strictParse, type Json } from "../../packages/protocol/json.ts";
import type { PlannerView, WorkflowDef } from "../../packages/protocol/kernel-types.ts";
import type { BlobStore } from "../../packages/store/blobs.ts";
import { Docker, runToCompletion, LABEL_ROOT, type ContainerSpec } from "../../packages/runner/docker.ts";
import type { KernelClient } from "../../apps/control/kernel.ts";
import { bridgeSource, obligationsFor, parseAxioms, type Recipe } from "./bridge.ts";
import { lintJson, lintLean, type LintFinding } from "./lint.ts";
import { fileText, writeManifestTo, type SourceManifest } from "./package-source.ts";
import type { Identities } from "./identity.ts";

export type CheckOutcome = "pass" | "fail" | "inconclusive" | "not_run";
export interface Check { id: string; outcome: CheckOutcome; detail: string }

export interface BuildReceipt {
  kind: "build";
  version: "1";
  source_digest: string;
  prev_source_digest: string;
  identities: Identities;
  checks: Check[];
  binary_digest: string | null;
  export_digest: string | null;
  exports: WorkflowDef[];
  fixtures: { view: PlannerView; plan: string[] }[];
  assets: { path: string; digest: string }[];
  recipe: Recipe | null;
  payload_digest: string | null;
  build_log_digest: string | null;
  outcome: "pass" | "fail" | "inconclusive";
  failure: string | null;
}

export interface ProveReceipt {
  kind: "prove";
  version: "1";
  source_digest: string;
  payload_digest: string;
  build_receipt_digest: string;
  identities: Identities;
  recipe: Recipe;
  obligations: { id: string; decl: string; statement: string; scope: string; axioms: string[]; ok: boolean }[];
  bindings: { export_bound: boolean; fixtures_bound: number };
  replay: { tool: "leanchecker --fresh"; module: "FactoryBridge"; rc: number | null };
  checks: Check[];
  bridge_digest: string;
  log_digests: Record<string, string>;
  outcome: "pass" | "fail" | "inconclusive";
  failure: string | null;
}

export interface TestReport {
  kind: "protected_tests";
  version: "1";
  payload_digest: string;
  binary_digest: string;
  cases: number;
  failures: { index: number; view: PlannerView | null; reason: string }[];
  negative_controls: { name: string; ok: boolean; detail: string }[];
  outcome: "pass" | "fail" | "inconclusive";
  detail: string;
}

export interface VerifierEnv {
  docker: Docker;
  blobs: BlobStore;
  kernel: KernelClient;
  ids: Identities;
  scratch: string;         // host scratch root (never mounted wholesale)
  instance: string;        // label used for reconciliation
  buildTimeoutMs: number;
  proveTimeoutMs: number;
  testTimeoutMs: number;
}

export interface RunHooks {
  name: string;                        // deterministic container name
  labels: Record<string, string>;
  onStarted?: (containerId: string) => Promise<void> | void;
}

const MAX_OUT_FILE = 64 * 1024 * 1024;

/** Trusted collector: read a regular file produced in /out with limits. */
function collect(dir: string, name: string, max = MAX_OUT_FILE): Buffer | null {
  const p = path.join(dir, name);
  let st: fs.Stats;
  try {
    st = fs.lstatSync(p);
  } catch {
    return null;
  }
  if (!st.isFile() || st.nlink > 1 || st.size > max) return null;
  return fs.readFileSync(p);
}

function freshDir(root: string, name: string): string {
  const d = path.join(root, name);
  fs.rmSync(d, { recursive: true, force: true });
  fs.mkdirSync(d, { recursive: true, mode: 0o755 });
  return d;
}

export function prevTransform(_p: string, text: string): string {
  return text.replace(/\bFactoryPkg\b/g, "FactoryPrev");
}

/** Lay out the fixed module structure for the harness. */
function prepareSrc(env: VerifierEnv, src: string, cand: SourceManifest, prev: SourceManifest): void {
  const pkg = path.join(src, "FactoryPkg");
  const prv = path.join(src, "FactoryPrev");
  fs.mkdirSync(pkg, { recursive: true });
  fs.mkdirSync(prv, { recursive: true });
  const leanOnly = (m: SourceManifest, keep: string[]): SourceManifest => ({ files: m.files.filter((f) => keep.includes(f.path)) });
  writeManifestTo(leanOnly(cand, ["Package.lean", "Planner.lean", "Proofs.lean"]), env.blobs, pkg);
  writeManifestTo(leanOnly(prev, ["Package.lean", "Planner.lean"]), env.blobs, prv, prevTransform);
  fs.chmodSync(src, 0o755);
}

function containerSpec(env: VerifierEnv, hooks: RunHooks, cmd: string[], mounts: ContainerSpec["mounts"]): ContainerSpec {
  return {
    name: hooks.name,
    image: env.ids.verifier_image,
    cmd,
    labels: { [`${LABEL_ROOT}.instance`]: env.instance, ...hooks.labels },
    mounts,
    memory: "6g",
    cpus: "4",
    pids: 512,
  };
}

export function lintManifest(env: VerifierEnv, m: SourceManifest): LintFinding[] {
  const out: LintFinding[] = [];
  for (const f of m.files) {
    const text = env.blobs.getText(f.digest);
    if (f.path.endsWith(".lean")) out.push(...lintLean(f.path, text));
    else if (f.path.endsWith(".json")) out.push(...lintJson(f.path, text));
  }
  return out;
}

export function readRecipe(env: VerifierEnv, m: SourceManifest): Recipe | null {
  const t = fileText(m, env.blobs, "migration.json");
  if (t === null) return null;
  try {
    const j = strictParse(t) as Record<string, Json>;
    const keys = Object.keys(j);
    if (keys.length !== 1 || keys[0] !== "recipe") return null;
    const r = j.recipe;
    return r === "pin_only" || r === "ordering_only" || r === "planner_equivalent" ? r : null;
  } catch {
    return null;
  }
}

/** Deterministic protected fixture views derived from the exported workflows. */
export function fixtureViews(exports: WorkflowDef[]): PlannerView[] {
  const views: PlannerView[] = [];
  for (const w of exports) {
    const ids = w.steps.map((s) => s.id);
    const alt = ids.filter((_, i) => i % 2 === 0);
    const dup = [...ids, ...[...ids].reverse()];
    for (const [ready, slots] of [[ids, "0"], [ids, "1"], [ids, "2"], [ids, "5"], [[], "2"], [alt, "3"], [dup, "4"]] as [string[], string][]) {
      views.push({ workflow: w, ready, slots });
    }
  }
  return views;
}

/** Run a built package binary over views in the fixed planner harness. */
export async function runPlanner(env: VerifierEnv, hooks: RunHooks, binary: Buffer, lines: string[]):
  Promise<{ rc: number | null; outputs: string[]; timedOut: boolean; stderr: string }> {
  const work = freshDir(env.scratch, hooks.name);
  const pkgDir = path.join(work, "pkg");
  const inDir = path.join(work, "in");
  const outDir = path.join(work, "out");
  fs.mkdirSync(pkgDir);
  fs.mkdirSync(inDir);
  fs.mkdirSync(outDir, { mode: 0o777 });
  fs.chmodSync(outDir, 0o777);
  fs.writeFileSync(path.join(pkgDir, "package.bin"), binary, { mode: 0o555 });
  fs.writeFileSync(path.join(inDir, "views.jsonl"), lines.join("\n") + "\n");
  const spec = containerSpec(env, hooks, ["sh", "/opt/harness/run-planner.sh"], [
    { host: pkgDir, container: "/pkg", readOnly: true },
    { host: inDir, container: "/in", readOnly: true },
    { host: outDir, container: "/out", readOnly: false },
  ]);
  spec.memory = "1g";
  spec.cpus = "1";
  const r = await runToCompletion(env.docker, spec, env.testTimeoutMs, hooks.onStarted);
  const rcBuf = collect(outDir, "planner.rc", 64);
  const plans = collect(outDir, "plans.jsonl");
  const stderr = collect(outDir, "planner.stderr", 1024 * 1024);
  return {
    rc: rcBuf ? Number(rcBuf.toString().trim()) : null,
    outputs: plans ? plans.toString("utf8").split("\n").filter((l) => l.length > 0) : [],
    timedOut: r.timedOut,
    stderr: stderr ? stderr.toString("utf8") : "",
  };
}

function parsePlan(line: string | undefined): string[] | null {
  if (line === undefined) return null;
  try {
    const j = strictParse(line, { numbers: "reject", maxBytes: 1024 * 1024 });
    if (Array.isArray(j) && j.every((x) => typeof x === "string")) return j as string[];
    return null;
  } catch {
    return null;
  }
}

export function payloadDigestOf(r: Pick<BuildReceipt, "source_digest" | "binary_digest" | "export_digest" | "identities" | "assets">): string {
  return digestOf({
    source_digest: r.source_digest,
    binary_digest: r.binary_digest,
    export_digest: r.export_digest,
    toolchain: r.identities.toolchain,
    verifier_image_id: r.identities.verifier_image_id,
    core_digest: r.identities.core_digest,
    contract_digest: r.identities.contract_digest,
    harness_digest: r.identities.harness_digest,
    assets: r.assets,
  });
}

export async function buildPhase(env: VerifierEnv, hooks: RunHooks, cand: SourceManifest, prev: SourceManifest):
  Promise<{ receipt: BuildReceipt; binary: Buffer | null }> {
  const checks: Check[] = [];
  const receipt: BuildReceipt = {
    kind: "build", version: "1", source_digest: digestOf(cand), prev_source_digest: digestOf(prev),
    identities: env.ids, checks, binary_digest: null, export_digest: null, exports: [], fixtures: [],
    assets: cand.files.filter((f) => f.path.startsWith("prompts/")).map((f) => ({ path: f.path, digest: f.digest })),
    recipe: readRecipe(env, cand), payload_digest: null, build_log_digest: null, outcome: "fail", failure: null,
  };
  const fail = (id: string, detail: string, outcome: "fail" | "inconclusive" = "fail") => {
    checks.push({ id, outcome, detail });
    receipt.outcome = outcome;
    receipt.failure = `${id}: ${detail}`;
    return { receipt, binary: null };
  };
  const findings = lintManifest(env, cand);
  if (findings.length) return fail("lint", findings.map((f) => `${f.file}: ${f.rule} (${f.detail})`).join("; "));
  checks.push({ id: "lint", outcome: "pass", detail: "no forbidden constructs, imports or namespaces" });
  if (!receipt.recipe) return fail("migration_recipe", "migration.json must be {\"recipe\": pin_only|ordering_only|planner_equivalent}");
  checks.push({ id: "migration_recipe", outcome: "pass", detail: receipt.recipe });

  const work = freshDir(env.scratch, hooks.name);
  const src = path.join(work, "in", "src");
  const outDir = path.join(work, "out");
  fs.mkdirSync(src, { recursive: true });
  fs.mkdirSync(outDir, { mode: 0o777 });
  fs.chmodSync(outDir, 0o777);
  prepareSrc(env, src, cand, prev);
  const spec = containerSpec(env, hooks, ["sh", "/opt/harness/build.sh"], [
    { host: path.join(work, "in"), container: "/in", readOnly: true },
    { host: outDir, container: "/out", readOnly: false },
  ]);
  const r = await runToCompletion(env.docker, spec, env.buildTimeoutMs, hooks.onStarted);
  const log = collect(outDir, "build.log");
  if (log) receipt.build_log_digest = env.blobs.put(log);
  if (r.timedOut) return fail("compile", "build timed out (inconclusive)", "inconclusive");
  const rcText = collect(outDir, "build.rc", 64)?.toString().trim();
  if (r.exitCode !== 0) {
    const tail = log ? log.toString("utf8").split("\n").filter((l) => /error/.test(l)).slice(0, 12).join("\n") : "";
    if (r.exitCode === 10 || rcText !== "0") return fail("compile", `lake build failed (rc ${rcText ?? "?"})\n${tail}`);
    return fail("export", `package export failed (container exit ${r.exitCode})`);
  }
  checks.push({ id: "compile", outcome: "pass", detail: "fixed recipe `lake build factory-package` succeeded" });
  const bin = collect(outDir, "package.bin");
  const exp = collect(outDir, "export.json", 4 * 1024 * 1024);
  if (!bin || !exp) return fail("collect", "missing package binary or export");
  receipt.binary_digest = env.blobs.put(bin);
  let exports: WorkflowDef[];
  try {
    exports = strictParse(exp.toString("utf8").trim(), { numbers: "reject" }) as unknown as WorkflowDef[];
    const v = await env.kernel.call({ op: "validate_workflows", workflows: exports as unknown as Json });
    if (v.ok !== true) return fail("export", `export does not decode under the fixed codec: ${String(v.message)}`);
    if (v.exports_ok !== true) return fail("export", `exported workflows fail the fixed well-formedness/mandatory-role check (per-workflow: ${canonicalize(v.each)})`);
  } catch (e) {
    return fail("export", `export not strict JSON: ${(e as Error).message}`);
  }
  receipt.exports = exports;
  receipt.export_digest = env.blobs.put(canonicalize(exports as unknown as Json));
  checks.push({ id: "export", outcome: "pass", detail: "binary export decodes and passes kernel exportsOk" });

  const views = fixtureViews(exports);
  const pr = await runPlanner(env, { ...hooks, name: `${hooks.name}-fx`, onStarted: undefined }, bin,
    views.map((v) => canonicalize(v as unknown as Json)));
  if (pr.timedOut) return fail("fixtures", "planner fixture run timed out (inconclusive)", "inconclusive");
  if (pr.rc !== 0 || pr.outputs.length !== views.length) return fail("fixtures", `planner run rc=${pr.rc}, ${pr.outputs.length}/${views.length} outputs`);
  for (let i = 0; i < views.length; i++) {
    const plan = parsePlan(pr.outputs[i]);
    if (!plan) return fail("fixtures", `fixture ${i}: malformed planner output`);
    const c = await env.kernel.query({ op: "check_plan", view: views[i] as unknown as Json, plan });
    if (c.plan_ok !== true) return fail("fixtures", `fixture ${i}: planner output violates the fixed plan contract`);
    receipt.fixtures.push({ view: views[i], plan });
  }
  checks.push({ id: "fixtures", outcome: "pass", detail: `${views.length} fixture views satisfy planOkB on the built binary` });
  receipt.payload_digest = payloadDigestOf(receipt);
  receipt.outcome = "pass";
  return { receipt, binary: bin };
}

export async function provePhase(env: VerifierEnv, hooks: RunHooks, cand: SourceManifest, prev: SourceManifest,
  build: BuildReceipt, buildDigest: string): Promise<ProveReceipt> {
  const checks: Check[] = [];
  const recipe = build.recipe ?? "pin_only";
  const obs = obligationsFor(recipe);
  const receipt: ProveReceipt = {
    kind: "prove", version: "1", source_digest: digestOf(cand), payload_digest: build.payload_digest ?? "",
    build_receipt_digest: buildDigest, identities: env.ids, recipe,
    obligations: obs.map((o) => ({ id: o.id, decl: o.decl.replace("_root_.", ""), statement: o.statement.replaceAll("_root_.", ""),
      scope: o.scope, axioms: [], ok: false })),
    bindings: { export_bound: false, fixtures_bound: 0 },
    replay: { tool: "leanchecker --fresh", module: "FactoryBridge", rc: null },
    checks, bridge_digest: "", log_digests: {}, outcome: "fail", failure: null,
  };
  const fail = (id: string, detail: string, outcome: "fail" | "inconclusive" = "fail") => {
    checks.push({ id, outcome, detail });
    receipt.outcome = outcome;
    receipt.failure = `${id}: ${detail}`;
    return receipt;
  };
  if (build.outcome !== "pass" || !build.payload_digest) return fail("build_receipt", "build receipt is not a pass");
  if (build.source_digest !== digestOf(cand)) return fail("source_binding", "build receipt is for a different source");
  if (build.prev_source_digest !== digestOf(prev)) return fail("source_binding", "build receipt used a different predecessor");
  if (build.identities.contract_digest !== env.ids.contract_digest || build.identities.harness_digest !== env.ids.harness_digest ||
    build.identities.verifier_image_id !== env.ids.verifier_image_id) {
    return fail("identity_binding", "build receipt identities differ from the installed verifier");
  }
  const { bridge, audit, decls } = bridgeSource({ recipe, exports: build.exports, fixtures: build.fixtures });
  receipt.bridge_digest = env.blobs.put(bridge);

  const work = freshDir(env.scratch, hooks.name);
  const inDir = path.join(work, "in");
  const src = path.join(inDir, "src");
  const outDir = path.join(work, "out");
  fs.mkdirSync(src, { recursive: true });
  fs.mkdirSync(outDir, { mode: 0o777 });
  fs.chmodSync(outDir, 0o777);
  prepareSrc(env, src, cand, prev);
  fs.writeFileSync(path.join(inDir, "FactoryBridge.lean"), bridge);
  fs.writeFileSync(path.join(inDir, "Audit.lean"), audit);
  const spec = containerSpec(env, hooks, ["sh", "/opt/harness/prove.sh"], [
    { host: inDir, container: "/in", readOnly: true },
    { host: outDir, container: "/out", readOnly: false },
  ]);
  const r = await runToCompletion(env.docker, spec, env.proveTimeoutMs, hooks.onStarted);
  for (const f of ["prove.log", "axioms.txt", "leanchecker.log"]) {
    const b = collect(outDir, f);
    if (b) receipt.log_digests[f] = env.blobs.put(b);
  }
  if (r.timedOut) return fail("proof_check", "proof checking timed out (inconclusive, never 'proved')", "inconclusive");
  const proveLog = collect(outDir, "prove.log")?.toString("utf8") ?? "";
  if (r.exitCode === 20) {
    const candFailed = /✖ \[[0-9/]+\] Build(ing)? FactoryPkg\./.test(proveLog) || /FactoryPkg\/[A-Za-z]+\.lean:\d+:\d+: error/.test(proveLog);
    const errs = proveLog.split("\n").filter((l) => /error/.test(l)).slice(0, 12).join("\n");
    if (candFailed) return fail("candidate_proofs", `candidate proof modules do not compile\n${errs}`);
    return fail("statement_bridge", `candidate declarations do not have the frozen statement types, or bound values disagree with the built binary\n${errs}`);
  }
  if (r.exitCode === 21) return fail("axiom_audit", "axiom audit did not run");
  const ax = collect(outDir, "axioms.txt")?.toString("utf8") ?? "";
  const parsed = parseAxioms(ax, decls);
  for (const rep of parsed.reports) {
    const ob = receipt.obligations.find((o) => `FactoryBridge.${o.id}` === rep.decl);
    if (ob) {
      ob.axioms = rep.axioms;
      ob.ok = rep.ok;
    }
  }
  if (parsed.problems.length) return fail("axiom_audit", parsed.problems.join("; "));
  checks.push({ id: "statement_bridge", outcome: "pass", detail: `${obs.length} frozen statements bound to candidate declarations` });
  checks.push({ id: "axiom_audit", outcome: "pass", detail: "only propext, Classical.choice, Quot.sound" });
  receipt.bindings = { export_bound: true, fixtures_bound: build.fixtures.length };
  checks.push({ id: "binary_binding", outcome: "pass", detail: `EXPORT and ${build.fixtures.length} planner fixtures kernel-checked equal to proof-bound definitions` });
  const lrc = collect(outDir, "leanchecker.rc", 64)?.toString().trim();
  receipt.replay.rc = lrc === undefined ? null : Number(lrc);
  if (r.exitCode === 22 || receipt.replay.rc !== 0) return fail("independent_replay", `leanchecker --fresh FactoryBridge failed (rc ${lrc})`);
  if (r.exitCode !== 0) return fail("proof_check", `unexpected harness exit ${r.exitCode}`);
  checks.push({ id: "independent_replay", outcome: "pass", detail: "leanchecker --fresh re-checked FactoryBridge and all dependencies" });
  receipt.outcome = "pass";
  return receipt;
}

/** Protected regression/fault tests run by the workbench itself (reproduction stage). */
export async function protectedTests(env: VerifierEnv, hooks: RunHooks, build: BuildReceipt, cand: SourceManifest): Promise<TestReport> {
  const report: TestReport = {
    kind: "protected_tests", version: "1", payload_digest: build.payload_digest ?? "", binary_digest: build.binary_digest ?? "",
    cases: 0, failures: [], negative_controls: [], outcome: "fail", detail: "",
  };
  if (!build.binary_digest || build.outcome !== "pass") {
    report.detail = "no passing build";
    return report;
  }
  const bin = env.blobs.get(build.binary_digest);
  // deterministic pseudo-random views (LCG with fixed seed) + supplemental views
  let seed = 0x5eed;
  const rnd = (n: number) => {
    seed = (seed * 1103515245 + 12345) & 0x7fffffff;
    return seed % n;
  };
  const views: PlannerView[] = [];
  for (const w of build.exports) {
    const ids = w.steps.map((s) => s.id);
    for (let k = 0; k < 60; k++) {
      const len = rnd(ids.length * 2 + 1);
      const ready = Array.from({ length: len }, () => ids[rnd(ids.length)]);
      views.push({ workflow: w, ready, slots: String(rnd(5)) });
    }
  }
  const sup = fileText(cand, env.blobs, "supplemental-tests/views.json");
  if (sup) {
    try {
      const extra = strictParse(sup, { numbers: "reject" });
      if (Array.isArray(extra)) {
        for (const x of extra.slice(0, 200)) {
          const o = x as Record<string, Json>;
          if (o && Array.isArray(o.ready) && typeof o.slots === "string") {
            for (const w of build.exports) views.push({ workflow: w, ready: o.ready as string[], slots: o.slots });
          }
        }
      }
    } catch {
      /* malformed supplemental tests are ignored; protected suite still runs */
    }
  }
  const negatives = [
    { name: "duplicate_key_rejected", line: '{"workflow":{},"workflow":{},"ready":[],"slots":"1"}' },
    { name: "json_number_rejected", line: '{"workflow":{"kind":"package_audit","steps":[],"max_parallel":"1"},"ready":[],"slots":1}' },
    { name: "extra_field_rejected", line: '{"workflow":{"kind":"package_audit","steps":[],"max_parallel":"1"},"ready":[],"slots":"1","x":"1"}' },
  ];
  const lines = [...views.map((v) => canonicalize(v as unknown as Json)), ...negatives.map((n) => n.line)];
  const pr = await runPlanner(env, hooks, bin, lines);
  if (pr.timedOut) {
    report.outcome = "inconclusive";
    report.detail = "protected tests timed out";
    return report;
  }
  if (pr.rc !== 0 || pr.outputs.length !== lines.length) {
    report.detail = `planner harness rc=${pr.rc} outputs=${pr.outputs.length}/${lines.length}`;
    return report;
  }
  report.cases = views.length;
  for (let i = 0; i < views.length; i++) {
    const plan = parsePlan(pr.outputs[i]);
    if (!plan) {
      report.failures.push({ index: i, view: views[i], reason: "malformed output" });
      continue;
    }
    const c = await env.kernel.query({ op: "check_plan", view: views[i] as unknown as Json, plan });
    if (c.plan_ok !== true) report.failures.push({ index: i, view: views[i], reason: `plan ${canonicalize(plan)} violates contract` });
  }
  negatives.forEach((n, k) => {
    const out = pr.outputs[views.length + k];
    let ok = false;
    try {
      const j = strictParse(out) as Record<string, Json>;
      ok = !!j && typeof j === "object" && !Array.isArray(j) && typeof j.error === "string";
    } catch {
      ok = false;
    }
    report.negative_controls.push({ name: n.name, ok, detail: ok ? "rejected by fixed codec" : `unexpected output ${String(out).slice(0, 80)}` });
  });
  const negFail = report.negative_controls.filter((n) => !n.ok).length;
  report.outcome = report.failures.length === 0 && negFail === 0 ? "pass" : "fail";
  report.detail = `${views.length} views, ${report.failures.length} contract failures, ${negFail} negative-control failures`;
  return report;
}

export function receiptText(r: unknown): string {
  return canonicalize(r as Json);
}

export function receiptDigest(r: unknown): string {
  return sha256Hex(canonicalize(r as Json));
}
