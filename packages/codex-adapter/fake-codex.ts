#!/usr/bin/env node
// *** FAKE CODEX CLI — FOR TESTS AND LABELED DEMOS ONLY. PERFORMS NO INFERENCE. ***
//
// Deterministic stand-in for the `codex exec` CLI boundary used by the adapter.
// Every JSONL event it emits carries `"fake": true` and fake thread ids.
// Responses come from a scenario file named by env FAKE_CODEX_SCENARIO:
//   { "rules": [ { "match": { "role"?: string, "promptIncludes"?: string[] },
//                  "response": { "file"?: string, "inline"?: object, "behavior"?: Behavior } } ] }
// The role is read from the first prompt line `ROLE: <role>`. First matching rule wins;
// no match -> turn.failed + exit 1. No randomness and no clock values in any output.

import { appendFileSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { spawn } from "node:child_process";
import { createHash } from "node:crypto";

type Behavior =
  | "ok" | "nonzero_exit" | "malformed_jsonl" | "truncated_output" | "missing_output" | "overflow" | "hang"
  | "unknown_events" | "auth_failure" | "forbidden_tool" | "schema_violation" | "no_turn_completed";

interface Rule {
  match: { role?: string; promptIncludes?: string[] };
  response: { file?: string; inline?: unknown; behavior?: Behavior };
}

const VERSION = "codex-cli 0.0.0-fake";
const GLOBAL_VALUE_FLAGS = new Set(["--ask-for-approval", "-a", "-c", "--config", "--enable", "--disable"]);
const GLOBAL_BOOL_FLAGS = new Set(["--strict-config"]);
const EXEC_VALUE_FLAGS = new Set([
  "-s", "--sandbox", "--output-schema", "-o", "--output-last-message", "-C", "--cd", "-m", "--model",
  "--enable", "--disable", "-c", "--config", "--color",
]);
const EXEC_BOOL_FLAGS = new Set([
  "--json", "--ephemeral", "--skip-git-repo-check", "--ignore-rules", "--strict-config", "--ignore-user-config",
]);

function usageError(arg: string, usage: string): never {
  process.stderr.write(
    `error: unexpected argument '${arg}' found\n\n  tip: to pass '${arg}' as a value, use '-- ${arg}'\n\n` +
      `Usage: ${usage}\n\nFor more information, try '--help'.\n`,
  );
  process.exit(2);
}

function execHelp(): never {
  const flags = [...EXEC_VALUE_FLAGS, ...EXEC_BOOL_FLAGS].join("\n  ");
  process.stdout.write(`FAKE codex exec (no inference)\n\nUsage: codex exec [OPTIONS] [PROMPT]\n\nOptions:\n  ${flags}\n  -h, --help\n`);
  process.exit(0);
}

// ---- argument parsing ----
const argv = process.argv.slice(2);
if (process.env.FAKE_CODEX_CALLLOG) appendFileSync(process.env.FAKE_CODEX_CALLLOG, JSON.stringify(argv) + "\n");
let i = 0;
while (i < argv.length && argv[i].startsWith("-")) {
  const a = argv[i];
  if (a === "--version" || a === "-V") { process.stdout.write(VERSION + "\n"); process.exit(0); }
  if (a === "--help" || a === "-h") { process.stdout.write("FAKE codex (no inference)\n\nCommands:\n  exec\n"); process.exit(0); }
  if (GLOBAL_VALUE_FLAGS.has(a)) { i += 2; continue; }
  if (GLOBAL_BOOL_FLAGS.has(a)) { i += 1; continue; }
  usageError(a, "codex [OPTIONS] [PROMPT]\n       codex [OPTIONS] <COMMAND> [ARGS]");
}
if (argv[i] !== "exec" && argv[i] !== "e") {
  process.stderr.write(`fake-codex: only the 'exec' subcommand is implemented (got '${argv[i] ?? ""}')\n`);
  process.exit(2);
}
i++;
const opts: Record<string, string> = {};
const bools = new Set<string>();
let promptArg: string | null = null;
for (; i < argv.length; i++) {
  const a = argv[i];
  if (a === "--help" || a === "-h") execHelp();
  if (EXEC_VALUE_FLAGS.has(a)) {
    if (i + 1 >= argv.length) usageError(a, "codex exec [OPTIONS] [PROMPT]");
    opts[a] = argv[++i];
  } else if (EXEC_BOOL_FLAGS.has(a)) bools.add(a);
  else if (a === "-" && promptArg === null) promptArg = a;
  else usageError(a, "codex exec [OPTIONS] [PROMPT]");
}
if (promptArg !== "-") {
  process.stderr.write("fake-codex: only stdin prompts ('-') are supported\n");
  process.exit(2);
}
const outPath = opts["--output-last-message"] ?? opts["-o"] ?? null;
const schemaPath = opts["--output-schema"] ?? null;
const json = bools.has("--json");
if (schemaPath !== null) readFileSync(schemaPath); // honor: the schema file must exist and be readable

// ---- scenario selection ----
const prompt = readFileSync(0, "utf8");
const roleLine = /^ROLE: ([a-z_]+)\r?\n/.exec(prompt);
const role = roleLine ? roleLine[1] : null;
const scenarioPath = process.env.FAKE_CODEX_SCENARIO;
if (!scenarioPath) {
  process.stderr.write("fake-codex: FAKE_CODEX_SCENARIO is not set\n");
  process.exit(2);
}
const scenario = JSON.parse(readFileSync(scenarioPath, "utf8")) as { rules: Rule[] };
const rule = scenario.rules.find(
  (r) => (r.match.role === undefined || r.match.role === role) && (r.match.promptIncludes ?? []).every((s) => prompt.includes(s)),
);

const threadId = "fake-thread-" + createHash("sha256").update(prompt).digest("hex").slice(0, 16);
let itemSeq = 0;
function emit(ev: Record<string, unknown>): void {
  if (json) process.stdout.write(JSON.stringify({ ...ev, fake: true }) + "\n");
}
function start(): void {
  emit({ type: "thread.started", thread_id: threadId });
  emit({ type: "turn.started" });
}
function agentMessage(text: string): void {
  emit({ type: "item.completed", item: { id: `item_${itemSeq++}`, type: "agent_message", text } });
}
function turnCompleted(finalText: string): void {
  emit({
    type: "turn.completed",
    usage: { input_tokens: Buffer.byteLength(prompt), cached_input_tokens: 0, output_tokens: Buffer.byteLength(finalText) },
  });
}
function fail(message: string, code: number): never {
  emit({ type: "error", message });
  emit({ type: "turn.failed", error: { message } });
  process.stderr.write(message + "\n");
  process.exit(code);
}

start();
if (!rule) fail("fake-codex: no scenario rule matched this prompt", 1);
const r = rule!.response;
let final: unknown = r.inline ?? null;
if (r.file) final = JSON.parse(readFileSync(resolve(dirname(scenarioPath), r.file), "utf8"));
const behavior: Behavior = r.behavior ?? "ok";
if (behavior === "schema_violation" && final && typeof final === "object") final = { ...final, actor: "model-chosen" };
const finalText = JSON.stringify(final);
const writeOut = (text: string) => { if (outPath) writeFileSync(outPath, text); };
const finishOk = () => {
  agentMessage(finalText);
  writeOut(finalText);
  turnCompleted(finalText);
  if (!json) process.stdout.write(finalText + "\n");
};

// Optional deterministic latency (demo pacing only; e.g. for screen recordings).
const latency = Number(process.env.FAKE_CODEX_LATENCY_MS ?? 0);
if (Number.isFinite(latency) && latency > 0 && (behavior === "ok" || behavior === "unknown_events")) {
  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, Math.min(latency, 120_000));
}

switch (behavior) {
  case "ok":
  case "schema_violation":
    finishOk();
    break;
  case "unknown_events":
    emit({ type: "fake.telemetry.v9", note: "unknown event type for adapter tests" });
    emit({ type: "item.started", item: { id: `item_${itemSeq++}`, type: "reasoning", text: "fake reasoning" } });
    emit({ type: "session.rate_limits", remaining: 7 });
    finishOk();
    break;
  case "nonzero_exit":
    fail("fake-codex: simulated internal error", 1);
    break;
  case "auth_failure":
    fail("fake-codex: 401 Unauthorized: not logged in; run `codex login`", 1);
    break;
  case "malformed_jsonl":
    if (json) process.stdout.write('{"type":"item.completed","fake":true,"item":{"id":"item_0",\n');
    writeOut(finalText);
    turnCompleted(finalText);
    break;
  case "truncated_output":
    agentMessage(finalText);
    writeOut(finalText.slice(0, Math.floor(finalText.length / 2)));
    turnCompleted(finalText);
    break;
  case "missing_output":
    agentMessage(finalText);
    turnCompleted(finalText);
    break;
  case "no_turn_completed":
    agentMessage(finalText);
    writeOut(finalText);
    break;
  case "forbidden_tool":
    emit({ type: "item.started", item: { id: `item_${itemSeq}`, type: "command_execution", command: "cat auth.json", status: "in_progress" } });
    emit({ type: "item.completed", item: { id: `item_${itemSeq++}`, type: "command_execution", command: "cat auth.json", exit_code: 0, status: "completed" } });
    finishOk();
    break;
  case "overflow": {
    const chunk = "x".repeat(8192);
    for (let k = 0; k < 4096; k++) {
      emit({ type: "item.updated", item: { id: "item_overflow", type: "agent_message", text: chunk } });
    }
    finishOk();
    break;
  }
  case "hang": {
    const sleeper = spawn("/bin/sleep", ["600"], { stdio: "ignore" });
    if (process.env.FAKE_CODEX_PIDFILE) writeFileSync(process.env.FAKE_CODEX_PIDFILE, `${process.pid} ${sleeper.pid}\n`);
    setInterval(() => {}, 1 << 30);
    break;
  }
}
