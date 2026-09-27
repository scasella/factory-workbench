// Package source manifests and the trusted materializer (§7.2, §10.5, §12.2).
// Candidate paths are relative artifact names, never filesystem authority.

import * as fs from "node:fs";
import * as path from "node:path";
import { canonicalize, digestOf, isDigest, sha256Hex } from "../../packages/protocol/json.ts";
import type { BlobStore } from "../../packages/store/blobs.ts";

export interface SourceFile { path: string; digest: string }
export interface SourceManifest { files: SourceFile[] }

export const MAX_FILE_BYTES = 256 * 1024;
export const MAX_FILES = 64;
export const MAX_EDITS = 16;

const FIXED_FILES = new Set([
  "Package.lean", "Planner.lean", "Proofs.lean", "migration.json", "package-metadata.json",
]);
const REQUIRED_FILES = ["Package.lean", "Planner.lean", "Proofs.lean", "migration.json", "package-metadata.json"];

export class PathRejected extends Error {
  constructor(msg: string) {
    super(msg);
    this.name = "PathRejected";
  }
}

/** Allowlisted candidate-editable package paths. Everything else (protected/,
 *  build files, lakefile, toolchain, runner profiles, verifier inputs) is rejected. */
export function checkPackagePath(p: string): void {
  if (typeof p !== "string" || p.length === 0 || p.length > 128) throw new PathRejected(`bad path length: ${JSON.stringify(p)}`);
  if (p.normalize("NFC") !== p) throw new PathRejected(`non-NFC path: ${JSON.stringify(p)}`);
  if (!/^[A-Za-z0-9._\/-]+$/.test(p)) throw new PathRejected(`path has disallowed characters: ${JSON.stringify(p)}`);
  if (p.startsWith("/") || p.includes("\\") || p.includes("//")) throw new PathRejected(`absolute/ambiguous path: ${p}`);
  const parts = p.split("/");
  if (parts.some((s) => s === "" || s === "." || s === ".." || s.startsWith("."))) throw new PathRejected(`traversal or hidden component: ${p}`);
  if (FIXED_FILES.has(p)) return;
  if (/^prompts\/[a-z0-9_-]{1,48}\.md$/.test(p)) return;
  if (/^supplemental-tests\/[a-z0-9_-]{1,48}\.json$/.test(p)) return;
  throw new PathRejected(`path outside candidate package allowlist: ${p}`);
}

function checkText(p: string, bytes: Buffer): void {
  if (bytes.length > MAX_FILE_BYTES) throw new PathRejected(`${p}: exceeds ${MAX_FILE_BYTES} bytes`);
  const text = bytes.toString("utf8");
  if (!Buffer.from(text, "utf8").equals(bytes)) throw new PathRejected(`${p}: not valid UTF-8`);
  if (/[\u0000-\u0008\u000b\u000c\u000e-\u001f\u007f‪-‮⁦-⁩]/.test(text)) {
    throw new PathRejected(`${p}: control or bidi characters`);
  }
}

export function sortManifest(files: SourceFile[]): SourceManifest {
  return { files: [...files].sort((a, b) => (a.path < b.path ? -1 : a.path > b.path ? 1 : 0)) };
}

export function sourceDigest(m: SourceManifest): string {
  return digestOf(m);
}

/** Import a package directory (regular files only) into the blob store. */
export function importPackageDir(dir: string, blobs: BlobStore): SourceManifest {
  const files: SourceFile[] = [];
  const walk = (rel: string) => {
    const abs = path.join(dir, rel);
    for (const ent of fs.readdirSync(abs, { withFileTypes: true })) {
      const r = rel ? `${rel}/${ent.name}` : ent.name;
      const st = fs.lstatSync(path.join(dir, r));
      if (st.isSymbolicLink()) throw new PathRejected(`symlink rejected: ${r}`);
      if (st.isDirectory()) walk(r);
      else if (st.isFile()) {
        if (st.nlink > 1) throw new PathRejected(`hard link rejected: ${r}`);
        checkPackagePath(r);
        const bytes = fs.readFileSync(path.join(dir, r));
        checkText(r, bytes);
        files.push({ path: r, digest: blobs.put(bytes) });
      } else throw new PathRejected(`special file rejected: ${r}`);
    }
  };
  walk("");
  return validateManifest(sortManifest(files));
}

export function validateManifest(m: SourceManifest): SourceManifest {
  if (m.files.length > MAX_FILES) throw new PathRejected("too many files");
  const seen = new Set<string>();
  for (const f of m.files) {
    checkPackagePath(f.path);
    if (!isDigest(f.digest)) throw new PathRejected(`bad digest for ${f.path}`);
    if (seen.has(f.path.toLowerCase())) throw new PathRejected(`duplicate/case-colliding path ${f.path}`);
    seen.add(f.path.toLowerCase());
  }
  for (const r of REQUIRED_FILES) if (!seen.has(r.toLowerCase())) throw new PathRejected(`missing required file ${r}`);
  return m;
}

/** Write a manifest's files into a fresh directory (for container input). */
export function writeManifestTo(m: SourceManifest, blobs: BlobStore, dir: string, transform?: (p: string, text: string) => string): void {
  for (const f of m.files) {
    const target = path.join(dir, f.path);
    if (!target.startsWith(path.resolve(dir) + path.sep)) throw new PathRejected(`escape: ${f.path}`);
    fs.mkdirSync(path.dirname(target), { recursive: true });
    let text = blobs.getText(f.digest);
    if (transform) text = transform(f.path, text);
    fs.writeFileSync(target, text, { flag: "wx" });
  }
}

export function fileText(m: SourceManifest, blobs: BlobStore, p: string): string | null {
  const f = m.files.find((x) => x.path === p);
  return f ? blobs.getText(f.digest) : null;
}

// ---------------------------------------------------------------------------
// Trusted materializer: applies author-proposed edits with exact preimages.

export interface Edit {
  path: string;
  operation: "replace" | "create" | "delete";
  expected_sha256: string | null;
  content: string | null;
}

export interface MaterializeResult {
  manifest: SourceManifest;
  changed: string[];
}

export function materialize(base: SourceManifest, edits: Edit[], blobs: BlobStore): MaterializeResult {
  if (!Array.isArray(edits) || edits.length === 0) throw new PathRejected("no edits proposed");
  if (edits.length > MAX_EDITS) throw new PathRejected(`too many edits (${edits.length} > ${MAX_EDITS})`);
  const files = new Map(base.files.map((f) => [f.path, f.digest]));
  const touched = new Set<string>();
  for (const e of edits) {
    checkPackagePath(e.path);
    if (touched.has(e.path)) throw new PathRejected(`multiple edits to ${e.path}`);
    touched.add(e.path);
    const cur = files.get(e.path);
    if (e.operation === "replace") {
      if (cur === undefined) throw new PathRejected(`replace of missing file ${e.path}`);
      if (e.expected_sha256 !== cur) throw new PathRejected(`wrong preimage hash for ${e.path}`);
      if (typeof e.content !== "string") throw new PathRejected(`replace without content: ${e.path}`);
    } else if (e.operation === "create") {
      if (cur !== undefined) throw new PathRejected(`create of existing file ${e.path}`);
      if (e.expected_sha256 !== null) throw new PathRejected(`create must have null preimage: ${e.path}`);
      if (typeof e.content !== "string") throw new PathRejected(`create without content: ${e.path}`);
    } else if (e.operation === "delete") {
      if (cur === undefined) throw new PathRejected(`delete of missing file ${e.path}`);
      if (e.expected_sha256 !== cur) throw new PathRejected(`wrong preimage hash for ${e.path}`);
      if (REQUIRED_FILES.includes(e.path)) throw new PathRejected(`cannot delete required file ${e.path}`);
      if (e.content !== null) throw new PathRejected(`delete must not carry content: ${e.path}`);
    } else throw new PathRejected(`unknown operation`);
  }
  for (const e of edits) {
    if (e.operation === "delete") files.delete(e.path);
    else {
      const bytes = Buffer.from(e.content as string, "utf8");
      checkText(e.path, bytes);
      files.set(e.path, blobs.put(bytes));
    }
  }
  const manifest = validateManifest(sortManifest([...files].map(([p, d]) => ({ path: p, digest: d }))));
  return { manifest, changed: [...touched].sort() };
}

export function manifestText(m: SourceManifest): string {
  return canonicalize(m);
}

export function textDigest(s: string): string {
  return sha256Hex(Buffer.from(s, "utf8"));
}
