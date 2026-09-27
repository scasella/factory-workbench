// Package runtime pool (§3.1, §8.1): one long-lived, network-less, read-only
// container per installed release, serving the package's pure planner over
// JSONL. The planner is an untrusted proposer: its output is checked by the
// kernel (`check_plan`) and every proposed start is re-validated by `apply`.
// A crash, timeout or malformed output blocks scheduling for that job and is
// surfaced as a diagnostic; a pinned job never silently switches planner.

import { spawn, type ChildProcessWithoutNullStreams } from "node:child_process";
import { createHash } from "node:crypto";
import { canonicalize, strictParse, type Json } from "../../packages/protocol/json.ts";
import type { PlannerView } from "../../packages/protocol/kernel-types.ts";
import { dockerArgsCreate, LABEL_ROOT } from "../../packages/runner/docker.ts";
import { bundleDir, verifyBundle } from "./releases.ts";

export class PlannerFault extends Error {
  constructor(msg: string) {
    super(msg);
    this.name = "PlannerFault";
  }
}

interface Proc {
  child: ChildProcessWithoutNullStreams;
  buf: string;
  waiter: ((line: string | null) => void) | null;
  chain: Promise<unknown>;
}

export class PlannerPool {
  private procs = new Map<string, Proc>();
  readonly stateDir: string;
  readonly image: string;
  readonly instance: string;
  readonly timeoutMs: number;
  readonly dockerBin: string;

  constructor(opts: { stateDir: string; image: string; instance: string; timeoutMs: number; dockerBin?: string }) {
    this.stateDir = opts.stateDir;
    this.image = opts.image;
    this.instance = opts.instance;
    this.timeoutMs = opts.timeoutMs;
    this.dockerBin = opts.dockerBin ?? "docker";
  }

  containerName(release: string): string {
    return `fw-${this.instance}-planner-${release.slice(0, 16)}`;
  }

  private start(release: string): Proc {
    verifyBundle(this.stateDir, release); // integrity before executing the binary
    const dir = bundleDir(this.stateDir, release);
    const spec = {
      name: `${this.containerName(release)}-${createHash("sha256").update(String(process.pid) + Date.now()).digest("hex").slice(0, 6)}`,
      image: this.image,
      cmd: ["/pkg/package.bin", "plan"],
      labels: { [`${LABEL_ROOT}.instance`]: this.instance, [`${LABEL_ROOT}.role`]: "planner", [`${LABEL_ROOT}.release`]: release },
      mounts: [{ host: dir, container: "/pkg", readOnly: true }],
      memory: "256m", cpus: "1", pids: 32,
      tmpfs: ["/tmp:size=16m,uid=10001"],
    };
    const args = ["run", "--rm", "-i", ...dockerArgsCreate(spec).slice(1)];
    const child = spawn(this.dockerBin, args, { stdio: ["pipe", "pipe", "pipe"], shell: false });
    const proc: Proc = { child, buf: "", waiter: null, chain: Promise.resolve() };
    child.stdout.setEncoding("utf8");
    child.stdout.on("data", (d: string) => {
      proc.buf += d;
      let nl: number;
      while ((nl = proc.buf.indexOf("\n")) >= 0) {
        const line = proc.buf.slice(0, nl);
        proc.buf = proc.buf.slice(nl + 1);
        const w = proc.waiter;
        proc.waiter = null;
        w?.(line);
      }
    });
    child.stderr.on("data", () => {});
    child.on("exit", () => {
      this.procs.delete(release);
      const w = proc.waiter;
      proc.waiter = null;
      w?.(null);
    });
    this.procs.set(release, proc);
    return proc;
  }

  async plan(release: string, view: PlannerView): Promise<string[]> {
    const proc = this.procs.get(release) ?? this.start(release);
    const run = async (): Promise<string[]> => {
      const line = await new Promise<string | null>((resolve) => {
        const timer = setTimeout(() => {
          proc.waiter = null;
          resolve("__timeout__");
        }, this.timeoutMs);
        proc.waiter = (l) => {
          clearTimeout(timer);
          resolve(l);
        };
        proc.child.stdin.write(canonicalize(view as unknown as Json) + "\n");
      });
      if (line === null) throw new PlannerFault("planner process exited");
      if (line === "__timeout__") {
        this.kill(release);
        throw new PlannerFault(`planner timed out after ${this.timeoutMs} ms`);
      }
      let j: Json;
      try {
        j = strictParse(line, { numbers: "reject", maxBytes: 1024 * 1024 });
      } catch (e) {
        this.kill(release);
        throw new PlannerFault(`malformed planner output: ${(e as Error).message}`);
      }
      if (!Array.isArray(j) || !j.every((x) => typeof x === "string")) {
        throw new PlannerFault(`planner returned a non-plan value: ${line.slice(0, 200)}`);
      }
      return j as string[];
    };
    const r = proc.chain.then(run, run);
    proc.chain = r.catch(() => {});
    return r;
  }

  kill(release: string): void {
    const p = this.procs.get(release);
    if (p) {
      p.child.kill("SIGKILL");
      this.procs.delete(release);
    }
  }

  stopAll(): void {
    for (const r of [...this.procs.keys()]) this.kill(r);
  }
}
