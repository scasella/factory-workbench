// `workbench doctor` (§10.3, M0): report executable resolution, CLI version,
// accepted noninteractive command, schema/JSONL support, security profile,
// auth readiness, container isolation, pinned Lean availability and
// state-directory permissions. No inference unless --live --consent.

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { execFile } from "../../packages/runner/docker.ts";
import { probeCodex, liveSmokeTest } from "../../packages/codex-adapter/doctor.ts";
import { writeProfile } from "../../packages/codex-adapter/profile.ts";
import type { CodexConfig } from "../../packages/codex-adapter/types.ts";
import { Db } from "../../packages/store/db.ts";
import { fileDigest } from "./kernel.ts";
import { REPO_ROOT, statePaths, type Settings } from "./config.ts";

export interface DoctorCheck { id: string; ok: boolean; detail: string; optional?: boolean }

export function readLock(): any {
  return JSON.parse(fs.readFileSync(path.join(REPO_ROOT, "toolchains.lock.json"), "utf8"));
}

export async function doctor(settings: Settings, opts: { live: boolean; consent: boolean }): Promise<{ ok: boolean; checks: DoctorCheck[] }> {
  const checks: DoctorCheck[] = [];
  const add = (id: string, ok: boolean, detail: string, optional = false) => checks.push({ id, ok, detail, optional });
  const lock = readLock();

  add("node", Number(process.versions.node.split(".")[0]) >= 25 && (process.features as any).typescript === "strip",
    `node ${process.versions.node} (lock ${lock.node.version}); type stripping ${(process.features as any).typescript}`);

  const info = await execFile("docker", ["info", "--format", "{{.ServerVersion}} {{.OSType}}/{{.Architecture}}"], { timeoutMs: 20_000 });
  add("container_engine", info.code === 0 && /linux/.test(info.stdout), (info.stdout || info.stderr).trim() || "docker unavailable");
  for (const [id, ref, want] of [["image_lean_base", lock.images.lean_base.ref, lock.images.lean_base.id],
    ["image_verifier", settings.verifierImage, lock.images.verifier.id]] as [string, string, string][]) {
    const r = await execFile("docker", ["image", "inspect", "--format", "{{.Id}}", ref], { timeoutMs: 20_000 });
    const got = r.stdout.trim();
    add(id, r.code === 0 && got === want, r.code === 0 ? `${ref} ${got}${got === want ? "" : ` (lock pins ${want}; run scripts/build-images)`}` : `${ref} missing`);
  }
  const iso = await execFile("docker", ["run", "--rm", "--network", "none", "--read-only", "--cap-drop", "ALL", "--security-opt", "no-new-privileges",
    "--user", "10001:10001", settings.verifierImage, "sh", "-c", "id -u; (getent hosts example.com >/dev/null 2>&1 && echo net) || echo nonet; touch /x 2>/dev/null && echo rw || echo ro; ls /var/run/docker.sock 2>/dev/null || echo nosock"],
    { timeoutMs: 60_000 });
  const isoOut = iso.stdout.trim().split("\n");
  add("container_isolation", iso.code === 0 && isoOut[0] === "10001" && isoOut.includes("nonet") && isoOut.includes("ro") && isoOut.includes("nosock"),
    `uid=${isoOut[0]} ${isoOut.slice(1).join(" ")} (want 10001 nonet ro nosock)`);
  const lean = await execFile("docker", ["run", "--rm", "--network", "none", settings.verifierImage, "sh", "-c", "lean --version && ls $(dirname $(readlink -f $(which lean)))/leanchecker"], { timeoutMs: 60_000 });
  add("lean_in_sandbox", lean.code === 0 && lean.stdout.includes(lock.lean.version), lean.stdout.trim().split("\n")[0] ?? lean.stderr);
  const hostLean = await execFile(path.join(os.homedir(), ".elan/bin/lean"), ["--version"], { timeoutMs: 20_000 });
  add("lean_host_kernel_toolchain", hostLean.code === 0 && hostLean.stdout.includes(lock.lean.version), hostLean.stdout.trim() || "elan lean missing");
  const built = path.join(REPO_ROOT, "protected/lean/.lake/build/bin/factory-kernel");
  add("kernel_built", fs.existsSync(built), fs.existsSync(built) ? `${built} sha256 ${fileDigest(built)}` : "run lake build in protected/lean");

  const P = statePaths(settings.stateDir);
  if (fs.existsSync(P.db)) {
    const db = new Db(P.db);
    add("sqlite_pragmas", db.pragma("journal_mode") === "wal" && Number(db.pragma("synchronous")) === 2 && Number(db.pragma("foreign_keys")) === 1,
      `journal_mode=${db.pragma("journal_mode")} synchronous=${db.pragma("synchronous")} foreign_keys=${db.pragma("foreign_keys")}`);
    const kd = db.getMeta("kernel_digest");
    const kbin = path.join(P.kernel, "factory-kernel");
    add("kernel_installed", !!kd && fs.existsSync(kbin) && fileDigest(kbin) === kd, kd ? `installed kernel digest ${kd}` : "not bootstrapped", !kd);
    db.close();
    const mode = (p: string) => (fs.statSync(p).mode & 0o777).toString(8);
    add("state_permissions", mode(settings.stateDir) === "700" && mode(P.operator) === "700",
      `${settings.stateDir} ${mode(settings.stateDir)}, operator ${mode(P.operator)} (want 700)`);
  } else add("state", true, `${settings.stateDir} not initialized (bootstrap will create it)`, true);

  // Codex CLI: the real installed CLI is always probed (non-inference).
  const home = path.join(os.tmpdir(), `fw-doctor-codex-${process.pid}`);
  writeProfile(home);
  const cfg: CodexConfig = { executable: settings.codex.mode === "live" ? settings.codex.executable : "codex", argsPrefix: settings.codex.mode === "live" ? settings.codex.argsPrefix : ["exec"],
    globalArgs: settings.codex.globalArgs, codexHome: settings.codex.mode === "live" ? settings.codex.codexHome : home,
    workspaceRoot: path.join(home, "ws"), model: settings.codex.model };
  if (settings.codex.mode === "live") writeProfile(cfg.codexHome);
  const cr = await probeCodex(cfg);
  for (const c of cr.checks) add(`codex.${c.id}`, c.ok, c.detail, settings.codex.mode === "fake");
  add("codex.live_mode", settings.codex.mode === "fake" || cr.ok,
    settings.codex.mode === "fake" ? "inference mode: FAKE (deterministic, mocked) — live Codex not used"
      : cr.ok ? "live mode permitted" : "live mode BLOCKED: installed CLI cannot enforce the required tool profile", settings.codex.mode === "fake");
  if (settings.codex.mode === "live" && fs.existsSync(P.db)) {
    const db = new Db(P.db);
    db.setMeta("live_codex_ok", cr.ok ? "1" : "0");
    db.close();
  }
  if (opts.live) {
    if (!opts.consent) add("codex.live_smoke", false, "refusing live inference without --consent");
    else {
      try {
        const s = await liveSmokeTest(cfg, { consent: true });
        add("codex.live_smoke", s.ok, `structured=${s.structured.transport} shell_request=${s.shellRequest.transport} subagent_request=${s.subagentRequest.transport}`);
      } catch (e) {
        add("codex.live_smoke", false, (e as Error).message);
      }
    }
  }
  fs.rmSync(home, { recursive: true, force: true });
  return { ok: checks.every((c) => c.ok || c.optional), checks };
}
