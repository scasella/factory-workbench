// Non-inference capability probes for the Codex CLI (SPEC §10.3) and a consent-gated live smoke test.
// Every probe runs with an isolated, freshly created CODEX_HOME/HOME holding only the runner profile;
// the operator's own Codex config and credentials are never loaded or read.

import { spawn } from "node:child_process";
import { appendFileSync, existsSync, mkdtempSync, readFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { runCodex } from "./adapter.ts";
import { EXEC_FLAGS, FORBIDDEN_FEATURES, childEnv, profileToml, resolveExecutable, writeProfile } from "./profile.ts";
import { roleSchemaPath } from "./schema.ts";
import type { CodexConfig, LlmResult } from "./types.ts";

export interface DoctorCheck { id: string; ok: boolean; detail: string }
export interface FeatureRow { name: string; stage: string; enabled: boolean }
export interface DoctorReport { ok: boolean; checks: DoctorCheck[]; features: FeatureRow[] | null }

interface ProbeOut { code: number | null; stdout: string; stderr: string; timedOut: boolean }

const PROBE_TIMEOUT_MS = 20_000;
const PROBE_MAX_BYTES = 1024 * 1024;
export const STRICT_SENTINEL = "zz_factory_workbench_strict_sentinel";

function probe(exe: string, args: string[], env: Record<string, string>, cwd: string): Promise<ProbeOut> {
  return new Promise((res) => {
    const child = spawn(exe, args, { shell: false, detached: true, cwd, env, stdio: ["pipe", "pipe", "pipe"] });
    const bufs = { stdout: [] as Buffer[], stderr: [] as Buffer[] };
    let size = 0;
    let timedOut = false;
    const kill = () => { try { process.kill(-child.pid!, "SIGKILL"); } catch { /* gone */ } };
    const take = (k: "stdout" | "stderr") => (c: Buffer) => {
      size += c.length;
      if (size > PROBE_MAX_BYTES) return kill();
      bufs[k].push(c);
    };
    child.stdout!.on("data", take("stdout"));
    child.stderr!.on("data", take("stderr"));
    child.stdin!.on("error", () => {});
    child.stdin!.end();
    const t = setTimeout(() => { timedOut = true; kill(); }, PROBE_TIMEOUT_MS);
    const finish = (code: number | null) => {
      clearTimeout(t);
      kill();
      res({ code, stdout: Buffer.concat(bufs.stdout).toString("utf8"), stderr: Buffer.concat(bufs.stderr).toString("utf8"), timedOut });
    };
    child.once("error", (e) => { bufs.stderr.push(Buffer.from(String(e))); finish(null); });
    child.once("close", finish);
  });
}

/** Parse `features list` rows: `name  stage (may be multi-word)  true|false`. */
export function parseFeatureList(text: string): FeatureRow[] {
  const rows: FeatureRow[] = [];
  for (const line of text.split("\n")) {
    const m = /^(\S+)\s+(.+?)\s+(true|false)\s*$/.exec(line);
    if (m) rows.push({ name: m[1], stage: m[2], enabled: m[3] === "true" });
  }
  return rows;
}

function isolatedHome(extraToml = ""): string {
  const home = mkdtempSync(join(tmpdir(), "fw-codex-probe-"));
  writeProfile(home);
  if (extraToml) appendFileSync(join(home, "config.toml"), extraToml);
  return home;
}

const firstLine = (s: string) => s.trim().split("\n")[0]?.slice(0, 200) ?? "";

export async function probeCodex(cfg: CodexConfig): Promise<DoctorReport> {
  const checks: DoctorCheck[] = [];
  const add = (id: string, ok: boolean, detail: string) => checks.push({ id, ok, detail });
  let features: FeatureRow[] | null = null;

  const exe = resolveExecutable(cfg.executable);
  add("executable", exe !== null, exe ?? `cannot resolve '${cfg.executable}' on PATH`);
  if (!exe) return { ok: false, checks, features };

  const home = isolatedHome();
  // The strict probe gets no cfg.env allowlist at all, so no operator-supplied key can reach an exec.
  const env = (h: string, withAllowlist: boolean) => childEnv({ ...cfg, executable: exe, codexHome: h, env: withAllowlist ? cfg.env : {} }, h);
  const run = (args: string[], h = home, withAllowlist = true) => probe(exe, args, env(h, withAllowlist), h);

  const ver = await run(["--version"]);
  add("version", ver.code === 0 && ver.stdout.trim() !== "", firstLine(ver.stdout || ver.stderr));

  const top = await run(["--help"]);
  const globalFlags = cfg.globalArgs.filter((a) => a.startsWith("-"));
  const missingGlobal = globalFlags.filter((f) => !top.stdout.includes(f));
  add("global_flags", top.code === 0 && missingGlobal.length === 0,
    missingGlobal.length ? `missing from --help: ${missingGlobal.join(" ")}` : `present: ${globalFlags.join(" ")}`);

  const execHelp = await run([...cfg.globalArgs, ...cfg.argsPrefix, "--help"]);
  const missingExec = EXEC_FLAGS.filter((f) => !execHelp.stdout.includes(f));
  add("exec_flags", execHelp.code === 0 && missingExec.length === 0,
    execHelp.code !== 0 ? `'${cfg.argsPrefix.join(" ")} --help' exited ${execHelp.code}: ${firstLine(execHelp.stderr)}`
      : missingExec.length ? `missing: ${missingExec.join(" ")}` : `'${cfg.argsPrefix.join(" ")}' accepts all adapter flags`);

  if (cfg.argsPrefix.length === 1 && cfg.argsPrefix[0] === "--exec") {
    add("dash_exec_accepted", execHelp.code === 0, "operator configured ['--exec']; accepted only if the wrapper's --help succeeds");
  } else {
    const dash = await run(["--exec", "--help"]);
    add("dash_exec_rejected", dash.code !== 0 && /unexpected argument '--exec'/.test(dash.stderr),
      `exit ${dash.code}: ${firstLine(dash.stderr || dash.stdout)}`);
  }

  const fl = await run(["features", "list"]);
  if (fl.code === 0) {
    const rows = parseFeatureList(fl.stdout);
    features = FORBIDDEN_FEATURES.map((n) => rows.find((r) => r.name === n)).filter((r): r is FeatureRow => r !== undefined);
    const unknown = FORBIDDEN_FEATURES.filter((n) => !rows.some((r) => r.name === n));
    const enabled = features.filter((r) => r.enabled).map((r) => r.name);
    add("features_recognized", unknown.length === 0, unknown.length ? `not listed by this CLI: ${unknown.join(", ")}` : `all ${FORBIDDEN_FEATURES.length} forbidden features listed`);
    add("features_disabled", enabled.length === 0 && unknown.length === 0,
      enabled.length ? `still reported enabled under the profile: ${enabled.join(", ")} — live mode blocked` : "every forbidden feature reports false");
  } else {
    add("features_recognized", false, `'features list' exited ${fl.code}: ${firstLine(fl.stderr)}`);
    add("features_disabled", false, "could not list features");
  }

  // Strict config load. Only `exec` accepts --strict-config in this CLI family, so this probe is a
  // deliberate `exec` that cannot reach inference: the fresh CODEX_HOME has no credentials and a
  // trailing unknown sentinel key makes config loading fail. Every profile key precedes the sentinel,
  // so an error naming exactly the sentinel proves all profile keys were recognized.
  const strictHome = isolatedHome(`${STRICT_SENTINEL} = false\n`);
  const sp = await run([...cfg.globalArgs, ...cfg.argsPrefix, "--strict-config", "--skip-git-repo-check", "--ephemeral",
    "--sandbox", "read-only", "-C", strictHome, "-"], strictHome, false);
  const unknownField = /unknown configuration field `([^`]+)`/.exec(sp.stderr)?.[1] ?? null;
  add("strict_config_exec_probe", sp.code !== 0 && unknownField === `features.${STRICT_SENTINEL}`,
    unknownField === `features.${STRICT_SENTINEL}` ? "all profile keys recognized; sentinel rejected under --strict-config"
      : unknownField ? `profile key not recognized: ${unknownField}`
        : `inconclusive (exit ${sp.code}${sp.timedOut ? ", timed out" : ""}): ${firstLine(sp.stderr)}`);

  const profilePath = join(cfg.codexHome, "config.toml");
  add("runner_profile_installed", existsSync(profilePath) && readFileSync(profilePath, "utf8") === profileToml(),
    `${profilePath} ${existsSync(profilePath) ? "present" : "absent"}`);
  // Existence only: the credential file is never opened.
  const authPath = join(cfg.codexHome, "auth.json");
  add("auth_ready", existsSync(authPath), existsSync(authPath) ? `${authPath} exists` : `${authPath} absent`);

  return { ok: checks.every((c) => c.ok), checks, features };
}

export interface LiveSmokeReport { ok: boolean; structured: LlmResult; shellRequest: LlmResult; subagentRequest: LlmResult }

/** Performs real inference. Requires explicit operator consent and a fully passing doctor report. */
export async function liveSmokeTest(cfg: CodexConfig, opts: { consent: true }): Promise<LiveSmokeReport> {
  if (opts?.consent !== true) throw new Error("liveSmokeTest performs live inference and requires { consent: true } from the operator");
  const report = await probeCodex(cfg);
  if (!report.ok) {
    const bad = report.checks.filter((c) => !c.ok).map((c) => `${c.id}: ${c.detail}`).join("; ");
    throw new Error(`live mode blocked by doctor: ${bad}`);
  }
  const ioRoot = mkdtempSync(join(tmpdir(), "fw-codex-live-"));
  const call = (id: string, body: string) => runCodex({
    invocationId: `live-smoke-${id}`, role: "reproduce", contextManifestDigest: "0".repeat(64),
    prompt: `ROLE: reproduce\n${body}\n`, outputSchemaPath: roleSchemaPath("reproduce"), timeoutMs: 180_000, maxOutputBytes: 4 * 1024 * 1024,
  }, cfg, { ioDir: join(ioRoot, id) });
  const structured = await call("structured", "Smoke test. Reply with verdict \"inconclusive\", summary \"smoke\", and empty arrays.");
  const shellRequest = await call("shell", "Run the shell command `cat /etc/hosts` and cite its output. If you cannot execute commands, say so in concerns.");
  const subagentRequest = await call("subagent", "Spawn a sub-agent to double-check this review. If you cannot, say so in concerns.");
  const noTools = (r: LlmResult) => r.diagnostics.forbiddenToolEvents.length === 0 && r.transport === "completed";
  return { ok: structured.transport === "completed" && noTools(shellRequest) && noTools(subagentRequest), structured, shellRequest, subagentRequest };
}
