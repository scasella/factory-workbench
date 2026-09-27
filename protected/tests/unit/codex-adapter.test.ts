// Codex adapter tests: the REAL adapter against the labeled FAKE codex executable,
// plus non-inference doctor probes against the real installed CLI (isolated CODEX_HOME).

import { test } from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, readFileSync, writeFileSync, existsSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { runCodex } from "../../../packages/codex-adapter/adapter.ts";
import { writeProfile, resolveExecutable, FORBIDDEN_FEATURES, buildArgs } from "../../../packages/codex-adapter/profile.ts";
import { roleSchemaPath, validate, loadSchema } from "../../../packages/codex-adapter/schema.ts";
import { probeCodex, liveSmokeTest } from "../../../packages/codex-adapter/doctor.ts";
import { sha256Hex } from "../../../packages/protocol/json.ts";
import type { CodexConfig, LlmRequest, LlmRole } from "../../../packages/codex-adapter/types.ts";

const FAKE = fileURLToPath(new URL("../../../packages/codex-adapter/bin/fake-codex", import.meta.url));

const REVIEW_OK = { verdict: "pass", summary: "Looks consistent.", cited_artifacts: ["sha256:abc"], concerns: [] };
const AUTHOR_OK = {
  outcome: "proposed",
  summary: "Parallelize independent review stages.",
  edits: [{ path: "Planner.lean", operation: "replace", expected_sha256: "a".repeat(64), content: "-- new source\n" }],
  claimed_obligations: ["P01"],
  blockers: [],
};

interface Setup { cfg: CodexConfig; ioDir: string; root: string }

function setup(rules: unknown[], extra: Partial<CodexConfig> = {}, env: Record<string, string> = {}): Setup {
  const root = mkdtempSync(join(tmpdir(), "codex-adapter-test-"));
  const codexHome = join(root, "codex-home");
  writeProfile(codexHome);
  const scenario = join(root, "scenario.json");
  writeFileSync(scenario, JSON.stringify({ rules }));
  const cfg: CodexConfig = {
    executable: FAKE,
    argsPrefix: ["exec"],
    globalArgs: ["--ask-for-approval", "never"],
    codexHome,
    workspaceRoot: join(root, "ws"),
    env: { FAKE_CODEX_SCENARIO: scenario, FAKE_CODEX_NODE: process.execPath, FAKE_CODEX_CALLLOG: join(root, "calls.log"), ...env },
    ...extra,
  };
  return { cfg, ioDir: join(root, "io"), root };
}

function req(role: LlmRole, body = "Review the supplied artifact.", over: Partial<LlmRequest> = {}): LlmRequest {
  return {
    invocationId: `inv-${role}`,
    role,
    contextManifestDigest: "0".repeat(64),
    prompt: `ROLE: ${role}\n${body}\n`,
    outputSchemaPath: roleSchemaPath(role),
    timeoutMs: 20_000,
    maxOutputBytes: 1024 * 1024,
    ...over,
  };
}

function alive(pid: number): boolean {
  try {
    process.kill(pid, 0);
    return true;
  } catch (e) {
    return (e as NodeJS.ErrnoException).code !== "ESRCH";
  }
}

test("A19: happy path review — completed, schema-valid result, usage, digests", async () => {
  const s = setup([{ match: { role: "refute" }, response: { inline: REVIEW_OK } }]);
  const r = await runCodex(req("refute"), s.cfg, { ioDir: s.ioDir });
  assert.equal(r.transport, "completed", JSON.stringify(r.diagnostics));
  assert.deepEqual(r.result, REVIEW_OK);
  assert.equal(r.exitCode, 0);
  assert.ok(r.usage && r.usage.inputTokens! > 0 && r.usage.cachedInputTokens === 0);
  assert.equal(r.transcriptDigest, sha256Hex(readFileSync(join(s.ioDir, "stdout.jsonl"))));
  assert.equal(r.stderrDigest, sha256Hex(readFileSync(join(s.ioDir, "stderr.txt"))));
  // Every fake event is labeled fake.
  for (const line of readFileSync(join(s.ioDir, "stdout.jsonl"), "utf8").trim().split("\n")) assert.equal(JSON.parse(line).fake, true);
  // Prompt is passed only on stdin; argv ends with "-".
  const argv = JSON.parse(readFileSync(join(s.root, "calls.log"), "utf8").trim()) as string[];
  assert.equal(argv.at(-1), "-");
  assert.ok(!argv.some((a) => a.includes("Review the supplied artifact")));
});

test("A19: happy path author (from response file) and proof_repair share the author schema", async () => {
  const s = setup([{ match: { role: "author", promptIncludes: ["Planner"] }, response: { file: "author.json" } }]);
  writeFileSync(join(s.root, "author.json"), JSON.stringify(AUTHOR_OK));
  const r = await runCodex(req("author", "Edit Planner.lean"), s.cfg, { ioDir: s.ioDir });
  assert.equal(r.transport, "completed", JSON.stringify(r.diagnostics));
  assert.deepEqual(r.result, AUTHOR_OK);
  const schema = loadSchema(roleSchemaPath("proof_repair"));
  assert.deepEqual(validate(schema, AUTHOR_OK), []);
});

test("A19: malformed JSONL -> invalid_output", async () => {
  const s = setup([{ match: {}, response: { inline: REVIEW_OK, behavior: "malformed_jsonl" } }]);
  const r = await runCodex(req("reproduce"), s.cfg, { ioDir: s.ioDir });
  assert.equal(r.transport, "invalid_output");
  assert.equal(r.diagnostics.reason, "malformed_jsonl");
  assert.equal(r.result, null);
});

test("A19: truncated final output -> invalid_output", async () => {
  const s = setup([{ match: {}, response: { inline: REVIEW_OK, behavior: "truncated_output" } }]);
  const r = await runCodex(req("reproduce"), s.cfg, { ioDir: s.ioDir });
  assert.equal(r.transport, "invalid_output");
  assert.equal(r.diagnostics.reason, "malformed_final_output");
  assert.equal(r.result, null);
});

test("A19: missing final output file -> invalid_output", async () => {
  const s = setup([{ match: {}, response: { inline: REVIEW_OK, behavior: "missing_output" } }]);
  const r = await runCodex(req("reproduce"), s.cfg, { ioDir: s.ioDir });
  assert.equal(r.transport, "invalid_output");
  assert.equal(r.diagnostics.reason, "missing_final_output");
});

test("A19: no turn.completed event -> invalid_output even with a valid output file", async () => {
  const s = setup([{ match: {}, response: { inline: REVIEW_OK, behavior: "no_turn_completed" } }]);
  const r = await runCodex(req("reproduce"), s.cfg, { ioDir: s.ioDir });
  assert.equal(r.transport, "invalid_output");
  assert.equal(r.diagnostics.reason, "missing_turn_completed");
  assert.equal(r.usage, null, "missing usage is unknown (null), not zero");
});

test("A19: nonzero exit -> failed", async () => {
  const s = setup([{ match: {}, response: { inline: REVIEW_OK, behavior: "nonzero_exit" } }]);
  const r = await runCodex(req("reproduce"), s.cfg, { ioDir: s.ioDir });
  assert.equal(r.transport, "failed");
  assert.equal(r.exitCode, 1);
  assert.equal(r.diagnostics.reason, "nonzero_exit");
  assert.equal(r.result, null);
});

test("A19: no matching scenario rule -> failed (turn.failed + nonzero exit)", async () => {
  const s = setup([{ match: { role: "summarize" }, response: { inline: REVIEW_OK } }]);
  const r = await runCodex(req("reproduce"), s.cfg, { ioDir: s.ioDir });
  assert.equal(r.transport, "failed");
  assert.equal(r.diagnostics.reason, "nonzero_exit");
});

test("A19: output overflow -> failed output_overflow, bounded capture", async () => {
  const s = setup([{ match: {}, response: { inline: REVIEW_OK, behavior: "overflow" } }]);
  const r = await runCodex(req("reproduce", "x", { maxOutputBytes: 64 * 1024 }), s.cfg, { ioDir: s.ioDir });
  assert.equal(r.transport, "failed");
  assert.equal(r.diagnostics.reason, "output_overflow");
  assert.ok(readFileSync(join(s.ioDir, "stdout.jsonl")).length <= 64 * 1024);
  assert.equal(r.diagnostics.stdoutBytes, 64 * 1024);
});

test("A19: unknown telemetry events preserved as diagnostics; still completed", async () => {
  const s = setup([{ match: {}, response: { inline: REVIEW_OK, behavior: "unknown_events" } }]);
  const r = await runCodex(req("reproduce"), s.cfg, { ioDir: s.ioDir });
  assert.equal(r.transport, "completed", JSON.stringify(r.diagnostics));
  assert.deepEqual(r.diagnostics.unknownEventTypes, ["fake.telemetry.v9", "session.rate_limits"]);
  assert.deepEqual(r.result, REVIEW_OK);
});

test("A19: timeout kills the whole process group -> timed_out, no leftover processes", async () => {
  const s = setup([{ match: {}, response: { inline: REVIEW_OK, behavior: "hang" } }]);
  const pidfile = join(s.root, "pids");
  s.cfg.env = { ...s.cfg.env, FAKE_CODEX_PIDFILE: pidfile };
  const r = await runCodex(req("reproduce", "x", { timeoutMs: 1500 }), s.cfg, { ioDir: s.ioDir });
  assert.equal(r.transport, "timed_out");
  assert.equal(r.result, null);
  assert.ok(existsSync(pidfile), "fake wrote its pids before hanging");
  const pids = readFileSync(pidfile, "utf8").trim().split(" ").map(Number);
  assert.equal(pids.length, 2);
  for (const pid of pids) assert.equal(alive(pid), false, `pid ${pid} must be gone`);
});

test("A19: AbortSignal -> cancelled, process group killed", async () => {
  const s = setup([{ match: {}, response: { inline: REVIEW_OK, behavior: "hang" } }]);
  const pidfile = join(s.root, "pids");
  s.cfg.env = { ...s.cfg.env, FAKE_CODEX_PIDFILE: pidfile };
  const ac = new AbortController();
  const p = runCodex(req("reproduce"), s.cfg, { ioDir: s.ioDir, signal: ac.signal });
  const until = Date.now() + 10_000;
  while (!existsSync(pidfile) && Date.now() < until) await new Promise((res) => setTimeout(res, 50));
  ac.abort();
  const r = await p;
  assert.equal(r.transport, "cancelled");
  for (const pid of readFileSync(pidfile, "utf8").trim().split(" ").map(Number)) assert.equal(alive(pid), false);
});

test("A19: auth failure -> failed auth_failure", async () => {
  const s = setup([{ match: {}, response: { inline: REVIEW_OK, behavior: "auth_failure" } }]);
  const r = await runCodex(req("reproduce"), s.cfg, { ioDir: s.ioDir });
  assert.equal(r.transport, "failed");
  assert.equal(r.diagnostics.reason, "auth_failure");
});

test("A20: forbidden tool (command_execution) event fails the attempt despite valid output", async () => {
  const s = setup([{ match: {}, response: { inline: REVIEW_OK, behavior: "forbidden_tool" } }]);
  const r = await runCodex(req("reproduce"), s.cfg, { ioDir: s.ioDir });
  assert.equal(r.transport, "failed");
  assert.equal(r.diagnostics.reason, "forbidden_tool_event");
  assert.deepEqual(r.diagnostics.forbiddenToolEvents, ["item.started:command_execution", "item.completed:command_execution"]);
  assert.equal(r.result, null);
});

test("A19: schema violation (extra model-chosen field) -> invalid_output", async () => {
  const s = setup([{ match: {}, response: { inline: REVIEW_OK, behavior: "schema_violation" } }]);
  const r = await runCodex(req("reproduce"), s.cfg, { ioDir: s.ioDir });
  assert.equal(r.transport, "invalid_output");
  assert.equal(r.diagnostics.reason, "schema_violation");
  assert.match(r.diagnostics.detail!, /unexpected field 'actor'/);
});

test("A19: schema violation (wrong enum) -> invalid_output", async () => {
  const s = setup([{ match: {}, response: { inline: { ...REVIEW_OK, verdict: "maybe" } } }]);
  const r = await runCodex(req("reproduce"), s.cfg, { ioDir: s.ioDir });
  assert.equal(r.transport, "invalid_output");
  assert.match(r.diagnostics.detail!, /verdict: value not in enum/);
});

test("A19: unsupported --exec prefix fails with a CLI usage error; no fallback invocation", async () => {
  const s = setup([{ match: {}, response: { inline: REVIEW_OK } }], { argsPrefix: ["--exec"] });
  const r = await runCodex(req("reproduce"), s.cfg, { ioDir: s.ioDir });
  assert.equal(r.transport, "failed");
  assert.equal(r.exitCode, 2);
  assert.equal(r.diagnostics.reason, "cli_usage_error");
  assert.match(readFileSync(join(s.ioDir, "stderr.txt"), "utf8"), /unexpected argument '--exec' found/);
  assert.equal(readFileSync(join(s.root, "calls.log"), "utf8").trim().split("\n").length, 1, "exactly one CLI invocation");
});

test("A19: output schema path that is not the role's pinned schema is refused before spawn", async () => {
  const s = setup([{ match: {}, response: { inline: REVIEW_OK } }]);
  const r = await runCodex(req("reproduce", "x", { outputSchemaPath: roleSchemaPath("author") }), s.cfg, { ioDir: s.ioDir });
  assert.equal(r.transport, "failed");
  assert.equal(r.diagnostics.reason, "schema_mismatch");
  assert.equal(existsSync(join(s.root, "calls.log")), false);
});

test("A20: tampered CODEX_HOME profile is refused before spawn", async () => {
  const s = setup([{ match: {}, response: { inline: REVIEW_OK } }]);
  writeFileSync(join(s.cfg.codexHome, "config.toml"), "[features]\nshell_tool = true\n");
  const r = await runCodex(req("reproduce"), s.cfg, { ioDir: s.ioDir });
  assert.equal(r.diagnostics.reason, "profile_mismatch");
  assert.equal(existsSync(join(s.root, "calls.log")), false);
});

test("A20: argument array disables every forbidden feature and never carries the prompt", () => {
  const args = buildArgs({ argsPrefix: ["exec"], globalArgs: ["--ask-for-approval", "never"] }, {
    schemaPath: "/io/s.json", outPath: "/io/r.json", workspace: "/ws",
  });
  assert.deepEqual(args.slice(0, 3), ["--ask-for-approval", "never", "exec"]);
  for (const f of FORBIDDEN_FEATURES) assert.ok(args.join(" ").includes(`--disable ${f}`), f);
  assert.equal(args.at(-1), "-");
});

test("A20: role schemas are strict and carry no identity/authority fields", () => {
  const banned = ["actor", "subject", "attempt", "lease", "verifier", "invocation", "timestamp"];
  const walk = (s: Record<string, unknown>, path: string): void => {
    if (s.type === "object" || (Array.isArray(s.type) && s.type.includes("object"))) {
      assert.equal(s.additionalProperties, false, path);
      const props = Object.keys((s.properties ?? {}) as object);
      assert.deepEqual([...(s.required as string[])].sort(), [...props].sort(), `${path}: all properties required`);
      for (const p of props) {
        assert.ok(!banned.some((b) => p.toLowerCase().includes(b)), `${path}.${p}`);
        walk((s.properties as Record<string, Record<string, unknown>>)[p], `${path}.${p}`);
      }
    }
    if (s.items) walk(s.items as Record<string, unknown>, `${path}[]`);
  };
  for (const role of ["author", "reproduce", "summarize"] as const) walk(loadSchema(roleSchemaPath(role)), role);
});

// ---- doctor (non-inference) ----

test("doctor: fake CLI rejects --exec and reports the fake version", async () => {
  const s = setup([]);
  const report = await probeCodex({ ...s.cfg, argsPrefix: ["exec"] });
  const byId = Object.fromEntries(report.checks.map((c) => [c.id, c]));
  assert.equal(byId.executable.ok, true);
  assert.match(byId.version.detail, /fake/);
  assert.equal(byId.exec_flags.ok, true, byId.exec_flags.detail);
  assert.equal(byId.dash_exec_rejected.ok, true, byId.dash_exec_rejected.detail);
  assert.equal(report.ok, false, "fake has no `features list`; doctor must not pass");
});

test("doctor: liveSmokeTest refuses without explicit consent", async () => {
  const s = setup([]);
  await assert.rejects(() => liveSmokeTest(s.cfg, { consent: false as unknown as true }), /consent/);
});

const realCodex = resolveExecutable("codex");
test(
  "A20: doctor against the REAL codex CLI (non-inference probes, isolated CODEX_HOME)",
  { skip: realCodex ? false : "codex is not on PATH" },
  async () => {
    const root = mkdtempSync(join(tmpdir(), "codex-doctor-test-"));
    const report = await probeCodex({
      executable: realCodex!, argsPrefix: ["exec"], globalArgs: ["--ask-for-approval", "never"],
      codexHome: join(root, "codex-home"), workspaceRoot: join(root, "ws"),
    });
    const byId = Object.fromEntries(report.checks.map((c) => [c.id, c]));
    assert.equal(byId.dash_exec_rejected.ok, true, byId.dash_exec_rejected.detail);
    assert.equal(byId.exec_flags.ok, true, byId.exec_flags.detail);
    assert.equal(byId.global_flags.ok, true, byId.global_flags.detail);
    assert.equal(byId.features_recognized.ok, true, byId.features_recognized.detail);
    assert.equal(byId.strict_config_exec_probe.ok, true, byId.strict_config_exec_probe.detail);
    assert.equal(byId.auth_ready.ok, false, "isolated CODEX_HOME has no auth.json");
    // Every forbidden feature is recognized; whatever the CLI still reports enabled must be named and must fail doctor.
    const enabled = (report.features ?? []).filter((f) => f.enabled).map((f) => f.name);
    assert.equal(byId.features_disabled.ok, enabled.length === 0, byId.features_disabled.detail);
    for (const name of enabled) assert.match(byId.features_disabled.detail, new RegExp(`\\b${name}\\b`));
    if (enabled.length > 0) assert.equal(report.ok, false);
    assert.equal(existsSync(join(root, "codex-home", "auth.json")), false);
  },
);
