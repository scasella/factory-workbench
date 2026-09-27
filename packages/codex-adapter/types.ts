// Codex CLI adapter types (SPEC §10.1). The adapter is the single inference path.

export type LlmRole = "author" | "proof_repair" | "reproduce" | "refute" | "summarize";

export interface LlmRequest {
  invocationId: string;
  role: LlmRole;
  contextManifestDigest: string;
  prompt: string;
  outputSchemaPath: string;
  timeoutMs: number;
  maxOutputBytes: number;
  model?: string;
}

export type LlmTransport = "completed" | "failed" | "timed_out" | "cancelled" | "invalid_output";

export interface LlmUsage {
  inputTokens?: number;
  outputTokens?: number;
  cachedInputTokens?: number;
}

/** Extra observations about an invocation. Diagnostics are never authority. */
export interface LlmDiagnostics {
  /** Precise failure reason (e.g. "output_overflow", "auth_failure"); null on success. */
  reason: string | null;
  detail: string | null;
  unknownEventTypes: string[];
  forbiddenToolEvents: string[];
  stdoutBytes: number;
  stderrBytes: number;
  eventCount: number;
}

export interface LlmResult {
  invocationId: string;
  transport: LlmTransport;
  result: unknown | null;
  transcriptDigest: string;
  stderrDigest: string;
  exitCode: number | null;
  usage: LlmUsage | null;
  diagnostics: LlmDiagnostics;
}

export interface CodexConfig {
  executable: string;
  /** Default ["exec"]. ["--exec"] only when an operator-verified wrapper accepts it. */
  argsPrefix: string[];
  /** Default ["--ask-for-approval", "never"]; placed BEFORE argsPrefix. */
  globalArgs: string[];
  codexHome: string;
  workspaceRoot: string;
  model?: string;
  /** Explicit allowlist of extra environment variables; nothing is inherited. */
  env?: Record<string, string>;
}

export const DEFAULT_ARGS_PREFIX: readonly string[] = ["exec"];
export const DEFAULT_GLOBAL_ARGS: readonly string[] = ["--ask-for-approval", "never"];
