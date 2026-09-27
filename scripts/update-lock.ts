// Records observed toolchain/image identities into toolchains.lock.json.
import * as fs from "node:fs";
import { execFileSync } from "node:child_process";
const lockPath = new URL("../toolchains.lock.json", import.meta.url);
const lock = JSON.parse(fs.readFileSync(lockPath, "utf8"));
const id = (ref: string) => execFileSync("docker", ["image", "inspect", "--format", "{{.Id}}", ref]).toString().trim();
lock.images.lean_base.id = id(lock.images.lean_base.ref);
lock.images.verifier.id = id(lock.images.verifier.ref);
fs.writeFileSync(lockPath, JSON.stringify(lock, null, 2) + "\n");
console.log("lock updated:", lock.images);
