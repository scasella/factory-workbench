// The single inference path (SPEC §10): spawn the Codex CLI with an argument array,
// prompt on stdin, bounded concurrent capture, strict JSONL decoding, strict final-output
// validation. Nothing the model or the CLI emits is authority; diagnostics are observations.

import { spawn, type ChildProcess } from "node:child_process";
import { createHash } from "node:crypto";
import { closeSync, existsSync, mkdirSync, mkdtempSync, openSync, readFileSync, rmSync, statSync, writeSync } from "node:fs";
import { join } from "node:path";
import { strictParse, digestOf } from "../protocol/json.ts";
import { buildArgs, childEnv, profileToml, resolveExecutable } from "./profile.ts";
import { loadSchema, roleSchema, validate } from "./schema.ts";
import type { CodexConfig, LlmDiagnostics, LlmRequest, LlmResult, LlmTransport, LlmUsage } from "./types.ts";

export const MAX_LINE_BYTES = 1024 * 1024;
export const KILL_GRACE_MS = 3000;

const KNOWN_EVENTS = new Set([
  "thread.started", "turn.started", "item.started", "item.updated", "item.completed", "turn.completed", "turn.failed", "error",
]);
const ALLOWED_ITEMS = new Set(["agent_message", "reasoning", "todo_list"]);
const AUTH_RE = /\b(401|403)\b|unauthori[sz]ed|not logged in|\blogin\b|authenticat|api[ _-]?key/i;
const EMPTY_DIGEST = createHash("sha256").digest("hex");

/** Bounded capture of one stream into a file, with an incremental digest. */
class Capture {
  bytes = 0;
  overflow = false;
  private fd: number;
  private hash = createHash("sha256");
  private limit: number;
  constructor(path: string, limit: number) {
    this.fd = openSync(path, "w", 0o600);
    this.limit = limit;
  }
  /** Returns the accepted part of the chunk (empty once the limit is hit). */
  push(chunk: Buffer): Buffer {
    if (this.overflow) return Buffer.alloc(0);
    const room = this.limit - this.bytes;
    const take = chunk.length > room ? chunk.subarray(0, room) : chunk;
    if (chunk.length > room) this.overflow = true;
    if (take.length > 0) {
      writeSync(this.fd, take);
      this.hash.update(take);
      this.bytes += take.length;
    }
    return take;
  }
  finish(): string {
    closeSync(this.fd);
    return this.hash.digest("hex");
  }
}

interface EventState {
  events: number;
  malformed: string | null;
  lineOverflow: boolean;
  unknown: string[];
  forbidden: string[];
  turnCompleted: boolean;
  terminalFailure: string | null;
  usage: LlmUsage | null;
}

function nonNegInt(v: unknown): number | undefined {
  return typeof v === "number" && Number.isSafeInteger(v) && v >= 0 ? v : undefined;
}

function parseUsage(u: unknown): LlmUsage | null {
  if (u === null || typeof u !== "object" || Array.isArray(u)) return null;
  const o = u as Record<string, unknown>;
  const usage: LlmUsage = {};
  const inputTokens = nonNegInt(o.input_tokens);
  const outputTokens = nonNegInt(o.output_tokens);
  const cachedInputTokens = nonNegInt(o.cached_input_tokens);
  if (inputTokens !== undefined) usage.inputTokens = inputTokens;
  if (outputTokens !== undefined) usage.outputTokens = outputTokens;
  if (cachedInputTokens !== undefined) usage.cachedInputTokens = cachedInputTokens;
  return Object.keys(usage).length > 0 ? usage : null;
}

const utf8 = new TextDecoder("utf-8", { fatal: true });

function onLine(st: EventState, line: Buffer): void {
  if (line.length === 0 || st.malformed) return;
  let ev: unknown;
  try {
    ev = strictParse(utf8.decode(line));
  } catch (e) {
    st.malformed = `line ${st.events + 1}: ${(e as Error).message}`;
    return;
  }
  if (ev === null || typeof ev !== "object" || Array.isArray(ev) || typeof (ev as { type?: unknown }).type !== "string") {
    st.malformed = `line ${st.events + 1}: event is not an object with a string 'type'`;
    return;
  }
  st.events++;
  const e = ev as Record<string, unknown>;
  const type = e.type as string;
  const known = KNOWN_EVENTS.has(type);
  if (!known && !st.unknown.includes(type)) st.unknown.push(type);
  // Any event that carries an item (known or not) has its item type checked: tool use is never allowed.
  if (type.startsWith("item.") || e.item !== undefined) {
    const item = e.item as Record<string, unknown> | undefined;
    const itemType = item && typeof item === "object" && typeof item.type === "string" ? item.type : "<missing>";
    if (!ALLOWED_ITEMS.has(itemType)) st.forbidden.push(`${type}:${itemType}`);
  }
  if (!known) return;
  if (type === "turn.completed") {
    st.turnCompleted = true;
    st.usage = parseUsage(e.usage);
  } else if (type === "turn.failed" || type === "error") {
    const err = e.error as { message?: unknown } | undefined;
    const msg = typeof e.message === "string" ? e.message : typeof err?.message === "string" ? err.message : "";
    st.terminalFailure = `${type}: ${msg}`.slice(0, 500);
  }
}

function killGroup(child: ChildProcess, sig: NodeJS.Signals): void {
  if (child.pid === undefined) return;
  try {
    process.kill(-child.pid, sig);
  } catch {
    /* ESRCH: group already gone */
  }
}

export interface RunOptions {
  ioDir: string;
  signal?: AbortSignal;
}

export async function runCodex(req: LlmRequest, cfg: CodexConfig, opts: RunOptions): Promise<LlmResult> {
  mkdirSync(opts.ioDir, { recursive: true, mode: 0o700 });
  const diag: LlmDiagnostics = {
    reason: null, detail: null, unknownEventTypes: [], forbiddenToolEvents: [], stdoutBytes: 0, stderrBytes: 0, eventCount: 0,
  };
  const early = (transport: LlmTransport, reason: string, detail: string): LlmResult => ({
    invocationId: req.invocationId, transport, result: null, transcriptDigest: EMPTY_DIGEST, stderrDigest: EMPTY_DIGEST,
    exitCode: null, usage: null, diagnostics: { ...diag, reason, detail },
  });

  // Preconditions: pinned role schema, runner-owned profile, resolvable executable.
  const { schema, digest } = roleSchema(req.role);
  let suppliedDigest: string;
  try {
    suppliedDigest = digestOf(loadSchema(req.outputSchemaPath));
  } catch (e) {
    return early("failed", "schema_unreadable", (e as Error).message);
  }
  if (suppliedDigest !== digest) return early("failed", "schema_mismatch", `outputSchemaPath is not the ${req.role} schema`);
  const profilePath = join(cfg.codexHome, "config.toml");
  if (!existsSync(profilePath) || readFileSync(profilePath, "utf8") !== profileToml()) {
    return early("failed", "profile_mismatch", `${profilePath} is not the runner-owned security profile`);
  }
  const exe = resolveExecutable(cfg.executable);
  if (!exe) return early("failed", "executable_not_found", cfg.executable);
  if (opts.signal?.aborted) return early("cancelled", "cancelled", "aborted before spawn");

  // Sanitized empty workspace and isolated HOME; context travels only as stdin data.
  mkdirSync(cfg.workspaceRoot, { recursive: true, mode: 0o700 });
  const workspace = mkdtempSync(join(cfg.workspaceRoot, "ws-"));
  const home = join(opts.ioDir, "home");
  mkdirSync(home, { recursive: true, mode: 0o700 });
  const outPath = join(opts.ioDir, "result.json");
  rmSync(outPath, { force: true });

  const args = buildArgs(cfg, { schemaPath: req.outputSchemaPath, outPath, workspace, model: req.model ?? cfg.model });
  const out = new Capture(join(opts.ioDir, "stdout.jsonl"), req.maxOutputBytes);
  const err = new Capture(join(opts.ioDir, "stderr.txt"), req.maxOutputBytes);
  const st: EventState = {
    events: 0, malformed: null, lineOverflow: false, unknown: [], forbidden: [], turnCompleted: false, terminalFailure: null, usage: null,
  };

  const child = spawn(exe, args, {
    shell: false, detached: true, cwd: workspace, env: childEnv({ ...cfg, executable: exe }, home), stdio: ["pipe", "pipe", "pipe"],
  });
  let killedAs: "timed_out" | "cancelled" | "overflow" | null = null;
  let graceTimer: NodeJS.Timeout | undefined;
  const terminate = (why: "timed_out" | "cancelled" | "overflow") => {
    if (killedAs) return;
    killedAs = why;
    killGroup(child, "SIGTERM");
    graceTimer = setTimeout(() => killGroup(child, "SIGKILL"), KILL_GRACE_MS);
  };

  let pending = Buffer.alloc(0);
  child.stdout!.on("data", (chunk: Buffer) => {
    const took = out.push(chunk);
    if (out.overflow) return terminate("overflow");
    let buf = pending.length ? Buffer.concat([pending, took]) : took;
    let nl: number;
    while ((nl = buf.indexOf(0x0a)) >= 0) {
      if (nl > MAX_LINE_BYTES) st.lineOverflow = true;
      else onLine(st, buf.subarray(0, nl));
      buf = buf.subarray(nl + 1);
    }
    pending = Buffer.from(buf);
    if (pending.length > MAX_LINE_BYTES) st.lineOverflow = true;
    if (st.lineOverflow) terminate("overflow");
  });
  child.stderr!.on("data", (chunk: Buffer) => {
    err.push(chunk);
    if (err.overflow) terminate("overflow");
  });
  child.stdin!.on("error", () => { /* EPIPE when the CLI exits before reading stdin */ });
  child.stdin!.end(req.prompt, "utf8");

  const timer = setTimeout(() => terminate("timed_out"), req.timeoutMs);
  const onAbort = () => terminate("cancelled");
  opts.signal?.addEventListener("abort", onAbort, { once: true });

  const { code, spawnError } = await new Promise<{ code: number | null; spawnError: string | null }>((res) => {
    child.once("error", (e) => res({ code: null, spawnError: e.message }));
    child.once("close", (c) => res({ code: c, spawnError: null }));
  });
  clearTimeout(timer);
  opts.signal?.removeEventListener("abort", onAbort);
  if (graceTimer) clearTimeout(graceTimer);
  killGroup(child, "SIGKILL"); // sweep any stragglers left in the CLI's process group
  if (pending.length > 0 && !killedAs && !st.malformed) st.malformed = "stdout ended with an unterminated (truncated) JSONL line";

  const transcriptDigest = out.finish();
  const stderrDigest = err.finish();
  diag.stdoutBytes = out.bytes;
  diag.stderrBytes = err.bytes;
  diag.eventCount = st.events;
  diag.unknownEventTypes = st.unknown;
  diag.forbiddenToolEvents = st.forbidden;
  const base = { invocationId: req.invocationId, transcriptDigest, stderrDigest, exitCode: code };
  const done = (transport: LlmTransport, reason: string | null, detail: string | null, result: unknown = null): LlmResult => ({
    ...base, transport, result, usage: st.usage, diagnostics: { ...diag, reason, detail },
  });

  if (spawnError) return done("failed", "spawn_error", spawnError);
  if (killedAs === "cancelled") return done("cancelled", "cancelled", "abort signal");
  if (killedAs === "timed_out") return done("timed_out", "timed_out", `exceeded ${req.timeoutMs} ms`);
  if (killedAs === "overflow") {
    return done("failed", "output_overflow", st.lineOverflow ? `a stdout line exceeded ${MAX_LINE_BYTES} bytes` : `output exceeded ${req.maxOutputBytes} bytes`);
  }
  if (st.forbidden.length > 0) return done("failed", "forbidden_tool_event", st.forbidden.join(", "));
  if (code !== 0) {
    const errText = readFileSync(join(opts.ioDir, "stderr.txt"), "utf8") + "\n" + (st.terminalFailure ?? "");
    if (AUTH_RE.test(errText)) return done("failed", "auth_failure", `exit ${code}`);
    if (code === 2 && /unexpected argument|unrecognized|invalid value/i.test(errText)) {
      return done("failed", "cli_usage_error", errText.trim().split("\n")[0].slice(0, 300));
    }
    return done("failed", "nonzero_exit", `exit ${code}${st.terminalFailure ? `; ${st.terminalFailure}` : ""}`);
  }
  if (st.malformed) return done("invalid_output", "malformed_jsonl", st.malformed);
  if (st.terminalFailure) return done("failed", "terminal_failure_event", st.terminalFailure);
  if (!st.turnCompleted) return done("invalid_output", "missing_turn_completed", "no turn.completed event");
  if (!existsSync(outPath)) return done("invalid_output", "missing_final_output", "output-last-message file absent");
  if (statSync(outPath).size > req.maxOutputBytes) return done("invalid_output", "final_output_too_large", `${statSync(outPath).size} bytes`);
  let final: unknown;
  try {
    final = strictParse(utf8.decode(readFileSync(outPath)));
  } catch (e) {
    return done("invalid_output", "malformed_final_output", (e as Error).message);
  }
  if (final === null || typeof final !== "object" || Array.isArray(final)) return done("invalid_output", "final_output_not_object", typeOfJson(final));
  const violations = validate(schema, final);
  if (violations.length > 0) return done("invalid_output", "schema_violation", violations.slice(0, 5).join("; "));
  return done("completed", null, null, final);
}

function typeOfJson(v: unknown): string {
  return v === null ? "null" : Array.isArray(v) ? "array" : typeof v;
}
