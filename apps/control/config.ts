// Workbench configuration. All effective limits are exposed via /api/status
// before launch (§11). Defaults are engineering limits, not promises.

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

export const REPO_ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "../..");

export interface Limits {
  llmSlots: number;            // concurrent Codex invocations
  containerSlots: number;      // concurrent proof/build containers
  heartbeatMs: number;
  leaseMs: number;
  llmTimeoutMs: number;
  proofTimeoutMs: number;
  buildTimeoutMs: number;
  testTimeoutMs: number;
  graceSec: number;
  idleWarnMs: number;
  maxOutputBytes: number;
  revisionsPerChange: number;
  attemptsPerChange: number;
  attemptsPerAudit: number;
  maxJobs: number;
  maxSteps: number;
  plannerTimeoutMs: number;
  kernelTimeoutMs: number;
}

export const DEFAULT_LIMITS: Limits = {
  llmSlots: 2,
  containerSlots: 1,
  heartbeatMs: 5_000,
  leaseMs: 30_000,
  llmTimeoutMs: 20 * 60_000,
  proofTimeoutMs: 30 * 60_000,
  buildTimeoutMs: 10 * 60_000,
  testTimeoutMs: 5 * 60_000,
  graceSec: 3,
  idleWarnMs: 5 * 60_000,
  maxOutputBytes: 10 * 1024 * 1024,
  revisionsPerChange: 3,
  attemptsPerChange: 40,
  attemptsPerAudit: 20,
  maxJobs: 10_000,
  maxSteps: 64,
  plannerTimeoutMs: 10_000,
  kernelTimeoutMs: 20_000,
};

export interface CodexSettings {
  mode: "fake" | "live";
  executable: string;
  argsPrefix: string[];
  globalArgs: string[];
  model?: string;
  codexHome: string;          // runner-owned CODEX_HOME (auth provisioned by operator)
  fakeScenario?: string;      // deterministic fake scenario file (fake mode only)
}

export interface Settings {
  stateDir: string;
  instance: string;
  operatorName: string;
  verifierImage: string;
  limits: Limits;
  codex: CodexSettings;
  bind: string;
  port: number;
}

export function defaultStateDir(): string {
  return process.env.FACTORY_STATE_DIR ?? path.join(os.homedir(), ".factory-workbench", "state");
}

export function loadSettings(overrides: Partial<Settings> = {}): Settings {
  const stateDir = overrides.stateDir ?? defaultStateDir();
  const file = path.join(stateDir, "operator", "settings.json");
  let saved: Partial<Settings> = {};
  if (fs.existsSync(file)) saved = JSON.parse(fs.readFileSync(file, "utf8"));
  const codexDefault: CodexSettings = {
    mode: "fake",
    executable: path.join(REPO_ROOT, "packages/codex-adapter/bin/fake-codex"),
    argsPrefix: ["exec"],
    globalArgs: ["--ask-for-approval", "never"],
    codexHome: path.join(stateDir, "operator", "codex-home"),
    fakeScenario: path.join(REPO_ROOT, "protected/tests/fixtures/fake-codex/scenario.json"),
  };
  const s: Settings = {
    stateDir,
    instance: "fw1",
    operatorName: "operator",
    verifierImage: "factory-verifier:dev",
    limits: { ...DEFAULT_LIMITS },
    codex: codexDefault,
    bind: "127.0.0.1",
    port: 4317,
    ...saved,
    ...overrides,
  };
  s.limits = { ...DEFAULT_LIMITS, ...(saved.limits ?? {}), ...(overrides.limits ?? {}) };
  s.codex = { ...codexDefault, ...(saved.codex ?? {}), ...(overrides.codex ?? {}) };
  if (!["127.0.0.1", "::1", "localhost"].includes(s.bind)) {
    throw new Error("refusing non-loopback bind address (remote hosting is outside v1)");
  }
  return s;
}

export function statePaths(stateDir: string) {
  return {
    db: path.join(stateDir, "workbench.sqlite"),
    blobs: path.join(stateDir, "blobs"),
    releases: path.join(stateDir, "releases"),
    attempts: path.join(stateDir, "attempts"),
    staging: path.join(stateDir, "staging"),
    operator: path.join(stateDir, "operator"),
    kernel: path.join(stateDir, "kernel"),
    lock: path.join(stateDir, "controller.lock"),
  };
}

/**
 * How the operator should invoke a CLI subcommand for THIS instance: the
 * repository-relative entry point plus --state/--port when they differ from
 * the defaults (so a hint never points at the wrong state or server).
 */
export function cliHint(settings: Settings, sub: string): string {
  const parts = ["node apps/control/cli.ts", sub];
  if (path.resolve(settings.stateDir) !== path.resolve(defaultStateDir())) parts.push(`--state ${JSON.stringify(settings.stateDir)}`);
  // Only commands that talk to the server need the port.
  if (settings.port !== 4317 && !["bootstrap", "doctor", "journal verify", "journal export"].includes(sub)) parts.push(`--port ${settings.port}`);
  return parts.join(" ");
}
