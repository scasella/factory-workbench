// Container supervisor primitives (§3.2, §7.3, §11).
// Fixed isolation profile: no network, read-only root, all capabilities
// dropped, no-new-privileges, non-root user, pid/memory/cpu limits, only
// explicit bind mounts (inputs read-only). No host control socket is ever
// mounted. Containers carry deterministic names + labels so a restarted
// supervisor can reconcile them instead of blindly relaunching.

import { spawn } from "node:child_process";

export const LABEL_ROOT = "io.factory-workbench";

export interface Mount { host: string; container: string; readOnly: boolean }

export interface ContainerSpec {
  name: string;                 // deterministic, e.g. fw-<instance>-<effecthash>
  image: string;                // pinned image reference (checked by id elsewhere)
  cmd: string[];
  labels: Record<string, string>;
  mounts: Mount[];
  network?: "none";             // only "none" is supported for candidate work
  memory?: string;
  cpus?: string;
  pids?: number;
  user?: string;
  tmpfs?: string[];
  env?: Record<string, string>;
  interactive?: boolean;
}

export interface ExecResult { code: number | null; stdout: string; stderr: string; timedOut: boolean }

export function execFile(cmd: string, args: string[], opts: { timeoutMs?: number; input?: string; maxBytes?: number } = {}): Promise<ExecResult> {
  return new Promise((resolve) => {
    const p = spawn(cmd, args, { stdio: ["pipe", "pipe", "pipe"], shell: false });
    let out = "";
    let err = "";
    const max = opts.maxBytes ?? 32 * 1024 * 1024;
    let timedOut = false;
    const timer = opts.timeoutMs ? setTimeout(() => { timedOut = true; p.kill("SIGKILL"); }, opts.timeoutMs) : null;
    p.stdout.on("data", (d) => { if (out.length < max) out += d.toString(); });
    p.stderr.on("data", (d) => { if (err.length < max) err += d.toString(); });
    p.on("error", (e) => { err += String(e); });
    p.on("close", (code) => {
      if (timer) clearTimeout(timer);
      resolve({ code, stdout: out, stderr: err, timedOut });
    });
    if (opts.input !== undefined) p.stdin.end(opts.input);
    else p.stdin.end();
  });
}

export function dockerArgsCreate(spec: ContainerSpec): string[] {
  if (spec.network && spec.network !== "none") throw new Error("only network=none is permitted");
  const a = ["create", "--name", spec.name, "--network", "none", "--read-only", "--cap-drop", "ALL",
    "--security-opt", "no-new-privileges", "--pids-limit", String(spec.pids ?? 256),
    "--memory", spec.memory ?? "4g", "--cpus", spec.cpus ?? "2", "--user", spec.user ?? "10001:10001"];
  for (const t of spec.tmpfs ?? ["/work:exec,size=2g,uid=10001", "/tmp:exec,size=512m,uid=10001"]) a.push("--tmpfs", t);
  for (const [k, v] of Object.entries(spec.labels)) a.push("--label", `${k}=${v}`);
  for (const m of spec.mounts) {
    if (m.host.includes(",") || m.container.includes(",")) throw new Error("mount path contains ','");
    a.push("--mount", `type=bind,source=${m.host},target=${m.container}${m.readOnly ? ",readonly" : ""}`);
  }
  for (const [k, v] of Object.entries(spec.env ?? {})) a.push("--env", `${k}=${v}`);
  if (spec.interactive) a.push("-i");
  a.push(spec.image, ...spec.cmd);
  return a;
}

export class Docker {
  readonly bin: string;
  constructor(bin = "docker") {
    this.bin = bin;
  }

  async create(spec: ContainerSpec): Promise<string> {
    const r = await execFile(this.bin, dockerArgsCreate(spec), { timeoutMs: 60_000 });
    if (r.code !== 0) {
      if (/already in use/.test(r.stderr)) throw new ContainerExists(spec.name);
      throw new Error(`docker create failed: ${r.stderr.trim()}`);
    }
    return r.stdout.trim();
  }

  async start(id: string): Promise<void> {
    const r = await execFile(this.bin, ["start", id], { timeoutMs: 60_000 });
    if (r.code !== 0) throw new Error(`docker start failed: ${r.stderr.trim()}`);
  }

  /** Wait for exit; returns exit code or null on timeout. */
  async wait(id: string, timeoutMs: number): Promise<number | null> {
    const r = await execFile(this.bin, ["wait", id], { timeoutMs });
    if (r.timedOut) return null;
    if (r.code !== 0) throw new Error(`docker wait failed: ${r.stderr.trim()}`);
    return Number(r.stdout.trim());
  }

  async logs(id: string, maxBytes = 1024 * 1024): Promise<{ stdout: string; stderr: string }> {
    const r = await execFile(this.bin, ["logs", id], { timeoutMs: 30_000, maxBytes });
    return { stdout: r.stdout, stderr: r.stderr };
  }

  /** Graceful stop (grace seconds) then forced removal of the whole container. */
  async terminate(idOrName: string, graceSec = 3): Promise<void> {
    await execFile(this.bin, ["stop", "-t", String(graceSec), idOrName], { timeoutMs: (graceSec + 30) * 1000 });
    await execFile(this.bin, ["rm", "-f", idOrName], { timeoutMs: 30_000 });
  }

  async remove(idOrName: string): Promise<void> {
    await execFile(this.bin, ["rm", "-f", idOrName], { timeoutMs: 30_000 });
  }

  async inspectState(idOrName: string): Promise<{ id: string; running: boolean; exitCode: number; status: string; labels: Record<string, string> } | null> {
    const r = await execFile(this.bin, ["inspect", "--format", "{{json .}}", idOrName], { timeoutMs: 30_000 });
    if (r.code !== 0) return null;
    const j = JSON.parse(r.stdout);
    return { id: j.Id, running: j.State.Running, exitCode: j.State.ExitCode, status: j.State.Status, labels: j.Config.Labels ?? {} };
  }

  /** Inventory of containers carrying the workbench instance label. */
  async inventory(instance: string): Promise<{ id: string; name: string; labels: Record<string, string>; state: string }[]> {
    const r = await execFile(this.bin, ["ps", "-a", "--no-trunc", "--filter", `label=${LABEL_ROOT}.instance=${instance}`,
      "--format", "{{json .}}"], { timeoutMs: 30_000 });
    if (r.code !== 0) throw new Error(`docker ps failed: ${r.stderr.trim()}`);
    const out: { id: string; name: string; labels: Record<string, string>; state: string }[] = [];
    for (const line of r.stdout.split("\n")) {
      if (!line.trim()) continue;
      const j = JSON.parse(line);
      const labels: Record<string, string> = {};
      for (const kv of String(j.Labels ?? "").split(",")) {
        const i = kv.indexOf("=");
        if (i > 0) labels[kv.slice(0, i)] = kv.slice(i + 1);
      }
      out.push({ id: j.ID, name: j.Names, labels, state: j.State });
    }
    return out;
  }

  async inspectImage(ref: string): Promise<{ id: string; labels: Record<string, string> } | null> {
    const r = await execFile(this.bin, ["image", "inspect", "--format", "{{json .}}", ref], { timeoutMs: 30_000 });
    if (r.code !== 0) return null;
    const j = JSON.parse(r.stdout);
    return { id: j.Id, labels: j.Config?.Labels ?? {} };
  }

  async imageId(ref: string): Promise<string | null> {
    const r = await execFile(this.bin, ["image", "inspect", "--format", "{{.Id}}", ref], { timeoutMs: 30_000 });
    return r.code === 0 ? r.stdout.trim() : null;
  }

  async available(): Promise<{ ok: boolean; detail: string }> {
    const r = await execFile(this.bin, ["info", "--format", "{{.ServerVersion}} {{.OSType}}/{{.Architecture}}"], { timeoutMs: 20_000 });
    return { ok: r.code === 0 && /linux/.test(r.stdout), detail: (r.stdout || r.stderr).trim() };
  }
}

export class ContainerExists extends Error {
  readonly containerName: string;
  constructor(name: string) {
    super(`container ${name} already exists`);
    this.containerName = name;
  }
}

/** Run a container to completion with a wall timeout; always removes it. */
export async function runToCompletion(docker: Docker, spec: ContainerSpec, timeoutMs: number,
  onStarted?: (id: string) => Promise<void> | void): Promise<{ id: string; exitCode: number | null; timedOut: boolean; logs: { stdout: string; stderr: string } }> {
  const id = await docker.create(spec);
  try {
    await docker.start(id);
    if (onStarted) await onStarted(id);
    const code = await docker.wait(id, timeoutMs);
    const logs = await docker.logs(id);
    if (code === null) {
      await docker.terminate(id);
      return { id, exitCode: null, timedOut: true, logs };
    }
    return { id, exitCode: code, timedOut: false, logs };
  } finally {
    await docker.remove(id);
  }
}
