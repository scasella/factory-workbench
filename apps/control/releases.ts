// Immutable release bundles (§13). The complete bundle is built and synced
// BEFORE the publication transaction; activation re-verifies its integrity.
//
//   source_digest  = digest(canonical source manifest)
//   payload_digest = digest(source, binary, exports, toolchain/core/contract/harness ids, assets)
//   release_digest = digest(payload, accepted evidence refs, recipe, lineage) — excludes approvals

import * as fs from "node:fs";
import * as path from "node:path";
import { canonicalize, digestOf, sha256Hex, type Json } from "../../packages/protocol/json.ts";
import type { BlobStore } from "../../packages/store/blobs.ts";
import type { Db } from "../../packages/store/db.ts";
import { nowIso } from "../../packages/store/db.ts";
import type { SourceManifest } from "../../protected/verifier/package-source.ts";
import type { BuildReceipt } from "../../protected/verifier/verifier.ts";

export interface EvidenceRef { role: string; job: string | null; step: string | null; gen: string | null; result: string }

export interface ReleaseEnvelope {
  payload_digest: string;
  evidence: EvidenceRef[];
  recipe: string;
  lineage: { parent: string | null; producer: string | null };
}

export interface ReleaseManifest {
  release_digest: string;
  envelope: ReleaseEnvelope;
  source_digest: string;
  binary_digest: string;
  export_digest: string;
  build_receipt: string;
  files: { path: string; digest: string }[];
}

export class BundleError extends Error {
  constructor(msg: string) {
    super(msg);
    this.name = "BundleError";
  }
}

export function releaseDigestOf(env: ReleaseEnvelope): string {
  return digestOf(env as unknown as Json);
}

export function bundleDir(stateDir: string, releaseDigest: string): string {
  return path.join(stateDir, "releases", releaseDigest);
}

function fsyncDir(d: string): void {
  const fd = fs.openSync(d, "r");
  try {
    fs.fsyncSync(fd);
  } finally {
    fs.closeSync(fd);
  }
}

/** Build and durably store a release bundle; returns its digest. Idempotent. */
export function createBundle(stateDir: string, blobs: BlobStore, db: Db, args: {
  source: SourceManifest; build: BuildReceipt; buildReceiptDigest: string; envelope: ReleaseEnvelope;
}): { releaseDigest: string; dir: string } {
  const { source, build, envelope } = args;
  if (build.outcome !== "pass" || !build.binary_digest || !build.export_digest || !build.payload_digest) {
    throw new BundleError("cannot bundle a failed build");
  }
  if (build.payload_digest !== envelope.payload_digest) throw new BundleError("envelope payload differs from build payload");
  if (digestOf(source) !== build.source_digest) throw new BundleError("source manifest differs from build receipt");
  const releaseDigest = releaseDigestOf(envelope);
  const dir = bundleDir(stateDir, releaseDigest);
  if (fs.existsSync(path.join(dir, "manifest.json"))) {
    verifyBundle(stateDir, releaseDigest);
    return { releaseDigest, dir };
  }
  const tmp = `${dir}.tmp-${process.pid}`;
  fs.rmSync(tmp, { recursive: true, force: true });
  fs.mkdirSync(path.join(tmp, "source"), { recursive: true });
  const files: { path: string; digest: string }[] = [];
  const put = (rel: string, bytes: Buffer, mode = 0o444) => {
    const p = path.join(tmp, rel);
    fs.mkdirSync(path.dirname(p), { recursive: true });
    fs.writeFileSync(p, bytes, { mode });
    const fd = fs.openSync(p, "r");
    fs.fsyncSync(fd);
    fs.closeSync(fd);
    files.push({ path: rel, digest: sha256Hex(bytes) });
  };
  put("package.bin", blobs.get(build.binary_digest), 0o555);
  put("export.json", blobs.get(build.export_digest));
  put("build-receipt.json", blobs.get(args.buildReceiptDigest));
  put("source-manifest.json", Buffer.from(canonicalize(source as unknown as Json)));
  for (const f of source.files) put(`source/${f.path}`, blobs.get(f.digest));
  const manifest: ReleaseManifest = {
    release_digest: releaseDigest, envelope, source_digest: build.source_digest, binary_digest: build.binary_digest,
    export_digest: build.export_digest, build_receipt: args.buildReceiptDigest,
    files: files.sort((a, b) => (a.path < b.path ? -1 : 1)),
  };
  fs.writeFileSync(path.join(tmp, "manifest.json"), canonicalize(manifest as unknown as Json), { mode: 0o444 });
  for (const d of [path.join(tmp, "source"), tmp]) fsyncDir(d);
  fs.renameSync(tmp, dir);
  fsyncDir(path.dirname(dir));
  db.db.prepare("INSERT OR IGNORE INTO release_bundles(release_digest, payload_digest, source_digest, envelope_digest, bundle_dir, created) VALUES (?,?,?,?,?,?)")
    .run(releaseDigest, build.payload_digest, build.source_digest, digestOf(envelope as unknown as Json), dir, nowIso());
  verifyBundle(stateDir, releaseDigest);
  return { releaseDigest, dir };
}

/** Re-verify every file of a bundle against its manifest and the release digest. */
export function verifyBundle(stateDir: string, releaseDigest: string): ReleaseManifest {
  const dir = bundleDir(stateDir, releaseDigest);
  let manifest: ReleaseManifest;
  try {
    manifest = JSON.parse(fs.readFileSync(path.join(dir, "manifest.json"), "utf8"));
  } catch {
    throw new BundleError(`bundle ${releaseDigest} missing or unreadable`);
  }
  if (manifest.release_digest !== releaseDigest || releaseDigestOf(manifest.envelope) !== releaseDigest) {
    throw new BundleError(`bundle ${releaseDigest}: release digest does not match its envelope`);
  }
  for (const f of manifest.files) {
    const p = path.join(dir, f.path);
    const st = fs.lstatSync(p);
    if (!st.isFile()) throw new BundleError(`bundle ${releaseDigest}: ${f.path} is not a regular file`);
    if (sha256Hex(fs.readFileSync(p)) !== f.digest) throw new BundleError(`bundle ${releaseDigest}: ${f.path} digest mismatch`);
  }
  const bin = manifest.files.find((f) => f.path === "package.bin");
  if (!bin || bin.digest !== manifest.binary_digest) throw new BundleError(`bundle ${releaseDigest}: binary does not match payload`);
  return manifest;
}

export function bundleSource(stateDir: string, releaseDigest: string): SourceManifest {
  const m = JSON.parse(fs.readFileSync(path.join(bundleDir(stateDir, releaseDigest), "source-manifest.json"), "utf8"));
  return m as SourceManifest;
}

export function bundleBuildReceipt(stateDir: string, releaseDigest: string): BuildReceipt {
  return JSON.parse(fs.readFileSync(path.join(bundleDir(stateDir, releaseDigest), "build-receipt.json"), "utf8"));
}
