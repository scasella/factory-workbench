// Protected identities bound into payloads and receipts (§13.1, §9.3).
//
// core/contract/harness digests describe what the VERIFIER IMAGE actually
// contains: they are computed from the protected sources when the image is
// built (scripts/build-images.sh) and baked in as image labels. The host-side
// verifier code digest is computed from the running tree. Bootstrap records
// all of them; any later drift makes the verifier "unavailable" (A30).
import * as fs from "node:fs";
import * as path from "node:path";
import { digestOf, sha256Hex } from "../../packages/protocol/json.ts";

export interface Identities {
  core_digest: string;          // protected Lean sources + build recipe (in image)
  contract_digest: string;      // frozen statement sources + contracts.json (in image)
  harness_digest: string;       // container harness (in image) + host verifier code
  toolchain: string;            // pinned Lean toolchain id
  verifier_image: string;       // image reference
  verifier_image_id: string;    // observed image id
}

export const LABEL_CORE = "io.factory-workbench.core-digest";
export const LABEL_CONTRACT = "io.factory-workbench.contract-digest";
export const LABEL_HARNESS = "io.factory-workbench.harness-digest";
export const LABEL_TOOLCHAIN = "io.factory-workbench.toolchain";

function filesDigest(root: string, rels: string[]): string {
  return digestOf({ files: [...rels].sort().map((r) => ({ path: r, digest: sha256Hex(fs.readFileSync(path.join(root, r))) })) });
}

/** Digests of protected sources as they are copied into the verifier image. */
export function sourceIdentities(repo: string): { core: string; contract: string; harness: string; toolchain: string } {
  const lean = path.join(repo, "protected/lean");
  const leanFiles = fs.readdirSync(path.join(lean, "Factory")).filter((f) => f.endsWith(".lean")).map((f) => `Factory/${f}`);
  const core = filesDigest(lean, [...leanFiles, "lakefile.toml", "lean-toolchain", "Factory.lean"]);
  const contract = digestOf({
    contracts_json: sha256Hex(fs.readFileSync(path.join(repo, "protected/contracts.json"))),
    lean: filesDigest(lean, ["Factory/Types.lean", "Factory/Workflow.lean", "Factory/PackageContracts.lean"]),
  });
  const harnessDir = path.join(repo, "protected/verifier/harness");
  const harness = filesDigest(harnessDir, fs.readdirSync(harnessDir));
  const toolchain = fs.readFileSync(path.join(lean, "lean-toolchain"), "utf8").trim();
  return { core, contract, harness, toolchain };
}

/** Host verifier/runner code that interprets container results. */
export function hostVerifierDigest(repo: string): string {
  const dirs = ["protected/verifier", "packages/runner"];
  return digestOf(dirs.map((d) => ({ dir: d, digest: filesDigest(path.join(repo, d), fs.readdirSync(path.join(repo, d)).filter((f) => f.endsWith(".ts"))) })));
}

export function computeIdentities(repo: string, image: string, imageId: string, labels: Record<string, string>): Identities {
  const missing = "unavailable";
  return {
    core_digest: labels[LABEL_CORE] ?? missing,
    contract_digest: labels[LABEL_CONTRACT] ?? missing,
    harness_digest: labels[LABEL_HARNESS] ? digestOf({ image_harness: labels[LABEL_HARNESS], host: hostVerifierDigest(repo) }) : missing,
    toolchain: labels[LABEL_TOOLCHAIN] ?? missing,
    verifier_image: image,
    verifier_image_id: imageId,
  };
}
