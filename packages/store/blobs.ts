// Content-addressed immutable blob store (§7.2).
// Write protocol: temp file in the store's tmp dir → enforce size → hash →
// fsync file → atomic rename into sha256/<prefix>/<digest> → fsync directory.
// Only then may a reference be committed. Collisions/mismatches fail closed.

import * as fs from "node:fs";
import * as path from "node:path";
import { createHash, randomBytes } from "node:crypto";
import { isDigest } from "../protocol/json.ts";

export class BlobError extends Error {
  constructor(msg: string) {
    super(msg);
    this.name = "BlobError";
  }
}

/** Test-only fault hooks (A23). Never wired to the production API. */
export interface BlobFaults {
  beforeFsync?: () => void;
  beforeRename?: () => void;
  beforeDirSync?: () => void;
}

export class BlobStore {
  readonly root: string;
  readonly maxBlobBytes: number;
  faults: BlobFaults = {};

  constructor(root: string, maxBlobBytes = 256 * 1024 * 1024) {
    this.root = root;
    this.maxBlobBytes = maxBlobBytes;
    fs.mkdirSync(path.join(root, "sha256"), { recursive: true, mode: 0o700 });
    fs.mkdirSync(path.join(root, "tmp"), { recursive: true, mode: 0o700 });
  }

  pathFor(digest: string): string {
    if (!isDigest(digest)) throw new BlobError(`invalid digest ${digest}`);
    return path.join(this.root, "sha256", digest.slice(0, 2), digest);
  }

  has(digest: string): boolean {
    return fs.existsSync(this.pathFor(digest));
  }

  /** Store bytes; returns the digest. Idempotent for identical content. */
  put(data: Uint8Array | string): string {
    const bytes = typeof data === "string" ? Buffer.from(data, "utf8") : Buffer.from(data);
    if (bytes.length > this.maxBlobBytes) throw new BlobError(`blob exceeds ${this.maxBlobBytes} bytes`);
    const digest = createHash("sha256").update(bytes).digest("hex");
    const final = this.pathFor(digest);
    if (fs.existsSync(final)) {
      this.verifyExisting(final, digest);
      return digest;
    }
    const tmp = path.join(this.root, "tmp", `${digest}.${randomBytes(6).toString("hex")}.tmp`);
    const fd = fs.openSync(tmp, "wx", 0o400);
    try {
      let off = 0;
      while (off < bytes.length) off += fs.writeSync(fd, bytes, off, bytes.length - off);
      this.faults.beforeFsync?.();
      fs.fsyncSync(fd);
    } finally {
      fs.closeSync(fd);
    }
    const dir = path.dirname(final);
    fs.mkdirSync(dir, { recursive: true, mode: 0o700 });
    this.faults.beforeRename?.();
    try {
      fs.linkSync(tmp, final); // fails if exists: never overwrite
    } catch (e: any) {
      fs.rmSync(tmp, { force: true });
      if (e.code === "EEXIST") {
        this.verifyExisting(final, digest);
        return digest;
      }
      throw e;
    }
    fs.rmSync(tmp, { force: true });
    this.faults.beforeDirSync?.();
    const dfd = fs.openSync(dir, "r");
    try {
      fs.fsyncSync(dfd);
    } finally {
      fs.closeSync(dfd);
    }
    return digest;
  }

  /** Import a regular file (no symlinks/devices) by copying its bytes. */
  putFile(file: string): string {
    const st = fs.lstatSync(file);
    if (!st.isFile()) throw new BlobError(`not a regular file: ${file}`);
    if (st.nlink > 1) throw new BlobError(`hard-linked file rejected: ${file}`);
    if (st.size > this.maxBlobBytes) throw new BlobError(`file too large: ${file}`);
    return this.put(fs.readFileSync(file));
  }

  get(digest: string): Buffer {
    const p = this.pathFor(digest);
    const bytes = fs.readFileSync(p);
    const actual = createHash("sha256").update(bytes).digest("hex");
    if (actual !== digest) throw new BlobError(`blob ${digest} is corrupt (hash ${actual})`);
    return bytes;
  }

  getText(digest: string): string {
    return this.get(digest).toString("utf8");
  }

  private verifyExisting(file: string, digest: string): void {
    const actual = createHash("sha256").update(fs.readFileSync(file)).digest("hex");
    if (actual !== digest) throw new BlobError(`existing blob ${digest} mismatches content; failing closed`);
  }

  /** v1 GC: only abandoned temp files older than the grace period. */
  collectTemp(graceMs = 3600_000): number {
    let n = 0;
    const dir = path.join(this.root, "tmp");
    for (const f of fs.readdirSync(dir)) {
      const p = path.join(dir, f);
      if (Date.now() - fs.statSync(p).mtimeMs > graceMs) {
        fs.rmSync(p, { force: true });
        n++;
      }
    }
    return n;
  }
}
