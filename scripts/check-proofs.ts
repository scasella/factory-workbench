// Checks the protected KERNEL theorems (K01–K12) against protected/contracts.json:
//   1. `lake build` of the protected library (includes Factory.Proofs if imported);
//   2. every advertised theorem exists, and its axiom closure is within the
//      approved set (#print axioms, parsed strictly);
//   3. independent replay: `lake env leanchecker --fresh Factory.Proofs`.
// Writes docs/proof-status.json. Exit 1 if any advertised theorem is missing,
// uses unapproved axioms, or replay fails.
import * as fs from "node:fs";
import * as path from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const LEAN = path.join(ROOT, "protected/lean");
const env = { ...process.env, PATH: `${process.env.HOME}/.elan/bin:${process.env.PATH}` };
const contracts = JSON.parse(fs.readFileSync(path.join(ROOT, "protected/contracts.json"), "utf8"));
const approved = new Set<string>(contracts.approved_axioms);

const run = (cmd: string, args: string[], timeout = 3_600_000) => {
  const r = spawnSync(cmd, args, { cwd: LEAN, env, encoding: "utf8", timeout, maxBuffer: 64 * 1024 * 1024 });
  return { code: r.status, out: (r.stdout ?? "") + (r.stderr ?? "") };
};

const status: any = { generated: new Date().toISOString(), toolchain: fs.readFileSync(path.join(LEAN, "lean-toolchain"), "utf8").trim(), properties: [], build: null, replay: null };
const b = run("lake", ["build"]);
status.build = { ok: b.code === 0, tail: b.out.split("\n").slice(-5) };
const proofsImported = fs.readFileSync(path.join(LEAN, "Factory.lean"), "utf8").includes("import Factory.Proofs");
status.proofs_module_in_library = proofsImported;
const names: string[] = [...new Set<string>(contracts.kernel.flatMap((k: any) => k.theorems))];
const probe = path.join(LEAN, ".lake", "ProofProbe.lean");
fs.mkdirSync(path.dirname(probe), { recursive: true });
const found: Record<string, { axioms: string[] } | null> = {};
const bp = fs.existsSync(path.join(LEAN, "Factory/Proofs.lean")) ? run("lake", ["build", "Factory.Proofs"]) : { code: 1, out: "missing" };
status.proofs_build = { ok: bp.code === 0, tail: bp.out.split("\n").slice(-8) };
if (b.code === 0 && bp.code === 0) {
  for (const n of names) {
    fs.writeFileSync(probe, `import Factory.Proofs\n#print axioms ${n}\n`);
    const r = run("lake", ["env", "lean", probe], 600_000);
    const m = /depends on axioms: \[(.*)\]/.exec(r.out);
    if (r.code === 0 && m) found[n] = { axioms: m[1].split(",").map((s) => s.trim()).filter(Boolean) };
    else if (r.code === 0 && /does not depend on any axioms/.test(r.out)) found[n] = { axioms: [] };
    else found[n] = null;
  }
  const rp = run("lake", ["env", "leanchecker", "--fresh", "Factory.Proofs"]);
  status.replay = { tool: "leanchecker --fresh Factory.Proofs", ok: rp.code === 0, tail: rp.out.split("\n").slice(-5) };
} else {
  for (const n of names) found[n] = null;
  status.replay = { tool: "leanchecker --fresh Factory.Proofs", ok: false, tail: ["Factory/Proofs.lean missing or library build failed"] };
}
let ok = status.build.ok && status.replay.ok;
for (const k of contracts.kernel) {
  const th = k.theorems.map((n: string) => {
    const f = found[n];
    const bad = f ? f.axioms.filter((a) => !approved.has(a)) : [];
    if (!f || bad.length) ok = false;
    return { name: n, present: !!f, axioms: f?.axioms ?? null, approved_axioms_only: !!f && bad.length === 0 };
  });
  status.properties.push({ id: k.id, title: k.title, definition: k.definition, theorems: th,
    status: th.every((t: any) => t.present && t.approved_axioms_only) && status.replay.ok ? "proof replay passed" : th.some((t: any) => t.present) ? "partial" : "not proved" });
}
status.ok = ok;
fs.mkdirSync(path.join(ROOT, "docs"), { recursive: true });
fs.writeFileSync(path.join(ROOT, "docs/proof-status.json"), JSON.stringify(status, null, 2) + "\n");
for (const p of status.properties) console.log(`${p.id.padEnd(4)} ${p.status.padEnd(20)} ${p.theorems.map((t: any) => `${t.name.split(".").pop()}${t.present ? "" : "(missing)"}`).join(", ")}`);
console.log(`build ${status.build.ok ? "ok" : "FAILED"}; replay ${status.replay.ok ? "ok" : "FAILED"}; overall ${ok ? "OK" : "INCOMPLETE"}`);
process.exit(ok ? 0 : 1);
