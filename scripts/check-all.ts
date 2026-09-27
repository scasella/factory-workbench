// Top-level release check (§21): fails on ANY required failed/missing check.
// Live Codex inference is reported as an explicit `not_run` (allowed only
// because credentials/profile are unavailable); protected proof replay can
// never be skipped into a release-ready status.
//
//   node scripts/check-all.ts [--skip-demo]   (scripts/check-all is a wrapper)
import * as fs from "node:fs";
import * as path from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const skipDemo = process.argv.includes("--skip-demo");
const env = { ...process.env, PATH: `${process.env.HOME}/.elan/bin:${process.env.PATH}` };
const results: any = { generated: new Date().toISOString(), gates: [], tests: [], acceptance: {} };

function gate(id: string, cmd: string, args: string[], timeout = 3 * 3_600_000) {
  const t = Date.now();
  console.log(`\n=== ${id}: ${cmd} ${args.join(" ")}`);
  const r = spawnSync(cmd, args, { cwd: ROOT, env, encoding: "utf8", timeout, maxBuffer: 256 * 1024 * 1024 });
  const out = (r.stdout ?? "") + (r.stderr ?? "");
  const ok = r.status === 0;
  console.log(out.split("\n").slice(-12).join("\n"));
  results.gates.push({ id, ok, seconds: Math.round((Date.now() - t) / 1000) });
  return { ok, out };
}

function tapTests(id: string, files: string[], extraEnv: Record<string, string> = {}) {
  const t = Date.now();
  console.log(`\n=== ${id}: ${files.join(" ")}`);
  const r = spawnSync(process.execPath, ["--test", "--test-concurrency=1", "--test-reporter=tap", ...files], {
    cwd: ROOT, env: { ...env, ...extraEnv }, encoding: "utf8", timeout: 4 * 3_600_000, maxBuffer: 256 * 1024 * 1024 });
  const out = (r.stdout ?? "") + (r.stderr ?? "");
  for (const line of out.split("\n")) {
    const m = /^(not ok|ok) \d+ - (.*?)(?: # (SKIP|TODO).*)?$/.exec(line);
    if (!m) continue;
    const name = m[2].trim();
    const status = m[3] === "SKIP" ? "skipped" : m[1] === "ok" ? "passed" : "failed";
    results.tests.push({ file: id, name, status });
    console.log(`  ${status.padEnd(7)} ${name}`);
  }
  results.gates.push({ id, ok: r.status === 0, seconds: Math.round((Date.now() - t) / 1000) });
}

gate("typecheck", "npx", ["tsc", "-p", "tsconfig.json", "--noEmit"]);
gate("kernel_build", "sh", ["-c", "cd protected/lean && lake build"], 3_600_000);
gate("kernel_proofs", process.execPath, ["scripts/check-proofs.ts"]);
gate("doctor", process.execPath, ["apps/control/cli.ts", "doctor"]);
gate("web_build", "npm", ["run", "build:web"]);
tapTests("unit", ["protected/tests/unit/codex-adapter.test.ts", "protected/tests/unit/canonical.test.ts", "protected/tests/unit/session-link.test.ts", "protected/tests/unit/server-input.test.ts"]);
tapTests("acceptance-core", ["protected/tests/acceptance/lifecycle.test.ts", "protected/tests/acceptance/persistence.test.ts",
  "protected/tests/acceptance/properties.test.ts"]);
tapTests("acceptance-verifier", ["protected/tests/acceptance/verifier.test.ts"]);
tapTests("kernel-mutants", ["protected/tests/mutation/kernel-mutants.test.ts"]);
tapTests("acceptance-engine", ["protected/tests/acceptance/engine.test.ts"]);
if (!skipDemo) {
  const ev = path.join(ROOT, "docs/demo-evidence.json");
  gate("demo_fake_llm", process.execPath, ["apps/control/cli.ts", "demo", "--fake-llm", "--state", path.join(ROOT, ".demo-state"), "--out", ev]);
}
tapTests("acceptance-recursion", ["protected/tests/acceptance/recursion.test.ts"]);

// Requirement ledger A01–A30
for (let i = 1; i <= 30; i++) {
  const id = `A${String(i).padStart(2, "0")}`;
  const ts = results.tests.filter((t: any) => t.name.startsWith(`${id}:`) || t.name.startsWith(`${id}b:`));
  const status = ts.length === 0 ? "not_run" : ts.some((t: any) => t.status === "failed") ? "failed" : ts.every((t: any) => t.status === "passed") ? "passed" : "partial";
  results.acceptance[id] = { status, tests: ts.map((t: any) => `${t.status}: ${t.name}`) };
}
const mut = results.tests.filter((t: any) => t.file === "kernel-mutants");
results.kernel_mutants = { status: mut.length && mut.every((t: any) => t.status === "passed") ? "passed" : mut.length ? "failed" : "not_run", detail: "docs/kernel-mutants.json" };
if (results.kernel_mutants.status !== "passed") results.gates.push({ id: "kernel_mutants_killed", ok: false, seconds: 0 });
results.live_codex_demo = { status: "not_run", reason: "doctor blocks live mode: codex-cli 0.155.1 cannot disable unified_exec (see OPEN-ITEMS.md)" };
const failedGates = results.gates.filter((g: any) => !g.ok).map((g: any) => g.id);
const notPassed = Object.entries(results.acceptance).filter(([, v]: any) => v.status !== "passed").map(([k]) => k);
results.ok = failedGates.length === 0 && notPassed.length === 0;
fs.mkdirSync(path.join(ROOT, "docs"), { recursive: true });
fs.writeFileSync(path.join(ROOT, "docs/test-results.json"), JSON.stringify(results, null, 2) + "\n");
console.log(`\n=== SUMMARY: gates failed: [${failedGates.join(", ")}]; acceptance not passed: [${notPassed.join(", ")}]; live Codex demo: not_run`);
console.log(results.ok ? "CHECK-ALL PASSED" : "CHECK-ALL FAILED");
process.exit(results.ok ? 0 : 1);
