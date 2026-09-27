// Client for the installed, digest-checked Lean kernel executable (§7.1 step 4).
// The coordinator has NO alternative authorization path: every state
// transition is the kernel's `apply` output. Kernel faults (crash, timeout,
// invalid response) disable further mutation until diagnosed.

import { spawn, type ChildProcessWithoutNullStreams } from "node:child_process";
import * as fs from "node:fs";
import { canonicalize, sha256Hex, strictParse, type Json } from "../../packages/protocol/json.ts";

export class KernelFault extends Error {
  constructor(msg: string) {
    super(msg);
    this.name = "KernelFault";
  }
}

export function fileDigest(p: string): string {
  return sha256Hex(fs.readFileSync(p));
}

export class KernelClient {
  readonly bin: string;
  readonly expectedDigest: string;
  readonly timeoutMs: number;
  private proc: ChildProcessWithoutNullStreams | null = null;
  private buf = "";
  private waiter: { resolve: (s: string) => void; reject: (e: Error) => void; timer: NodeJS.Timeout } | null = null;
  private chain: Promise<unknown> = Promise.resolve();
  faulted: string | null = null;
  /** Raw bytes of the most recent response line (for golden-vector checks). */
  lastRaw = "";

  constructor(bin: string, expectedDigest: string, timeoutMs = 15_000) {
    this.bin = bin;
    this.expectedDigest = expectedDigest;
    this.timeoutMs = timeoutMs;
  }

  private ensure(): ChildProcessWithoutNullStreams {
    if (this.faulted) throw new KernelFault(`kernel disabled after fault: ${this.faulted}`);
    if (this.proc) return this.proc;
    const actual = fileDigest(this.bin);
    if (actual !== this.expectedDigest) {
      this.faulted = `kernel binary digest mismatch: expected ${this.expectedDigest}, found ${actual}`;
      throw new KernelFault(this.faulted);
    }
    const p = spawn(this.bin, ["--serve"], { stdio: ["pipe", "pipe", "pipe"], env: { PATH: "/usr/bin:/bin" } });
    p.stdout.setEncoding("utf8");
    p.stdout.on("data", (chunk: string) => {
      this.buf += chunk;
      let nl: number;
      while ((nl = this.buf.indexOf("\n")) >= 0) {
        const line = this.buf.slice(0, nl);
        this.buf = this.buf.slice(nl + 1);
        const w = this.waiter;
        this.waiter = null;
        if (w) {
          clearTimeout(w.timer);
          w.resolve(line);
        }
      }
    });
    p.stderr.on("data", () => {});
    // Spawn failures (EACCES, ENOENT) and broken pipes become kernel faults,
    // never an unhandled 'error' event that would crash the controller.
    const fail = (e: Error) => {
      this.faulted = `kernel process error: ${e.message}`;
      this.proc = null;
      const w = this.waiter;
      this.waiter = null;
      if (w) {
        clearTimeout(w.timer);
        w.reject(new KernelFault(this.faulted));
      }
    };
    p.on("error", fail);
    p.stdin.on("error", fail);
    p.on("exit", (code, sig) => {
      this.proc = null;
      const w = this.waiter;
      this.waiter = null;
      if (w) {
        clearTimeout(w.timer);
        this.faulted = `kernel exited (code ${code}, signal ${sig})`;
        w.reject(new KernelFault(this.faulted));
      }
    });
    this.proc = p;
    return p;
  }

  /** Serialized request/response. Requests must contain no JSON numbers. */
  call(req: Record<string, Json>): Promise<Record<string, Json>> {
    const run = async () => {
      const p = this.ensure();
      const line = canonicalize({ v: "1", ...req });
      const out = await new Promise<string>((resolve, reject) => {
        const timer = setTimeout(() => {
          this.waiter = null;
          this.faulted = `kernel timed out after ${this.timeoutMs} ms`;
          p.kill("SIGKILL");
          reject(new KernelFault(this.faulted));
        }, this.timeoutMs);
        this.waiter = { resolve, reject, timer };
        p.stdin.write(line + "\n");
      });
      this.lastRaw = out;
      let parsed: Json;
      try {
        parsed = strictParse(out, { numbers: "reject", maxBytes: 256 * 1024 * 1024 });
      } catch (e) {
        this.faulted = `invalid kernel response: ${(e as Error).message}`;
        throw new KernelFault(this.faulted);
      }
      if (parsed === null || typeof parsed !== "object" || Array.isArray(parsed) || parsed.v !== "1") {
        this.faulted = "invalid kernel response envelope";
        throw new KernelFault(this.faulted);
      }
      return parsed as Record<string, Json>;
    };
    const r = this.chain.then(run, run);
    this.chain = r.catch(() => {});
    return r;
  }

  /** Like call(), but a kernel-reported bad_request becomes an exception. */
  async query(req: Record<string, Json>): Promise<Record<string, Json>> {
    const r = await this.call(req);
    if (r.ok !== true) throw new Error(`kernel ${String(req.op)} failed: ${String(r.code)} ${String(r.message)}`);
    return r;
  }

  stop(): void {
    this.proc?.kill("SIGTERM");
    this.proc = null;
  }
}
