// Prints `--label k=v` build args with the digests of protected sources that
// go into the verifier image (used by scripts/build-images.sh).
import * as path from "node:path";
import { fileURLToPath } from "node:url";
import { sourceIdentities, LABEL_CORE, LABEL_CONTRACT, LABEL_HARNESS, LABEL_TOOLCHAIN } from "../protected/verifier/identity.ts";
const repo = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const s = sourceIdentities(repo);
console.log([`--label ${LABEL_CORE}=${s.core}`, `--label ${LABEL_CONTRACT}=${s.contract}`, `--label ${LABEL_HARNESS}=${s.harness}`, `--label ${LABEL_TOOLCHAIN}=${s.toolchain}`].join(" "));
