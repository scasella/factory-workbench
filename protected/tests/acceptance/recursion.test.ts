// A26, A27 — assertions over the evidence produced by an actual run of
// `workbench demo --fake-llm` (inference mocked; everything else real).
// scripts/check-all runs the demo immediately before this file.
import { test } from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { REPO_ROOT } from "../../../apps/control/config.ts";

const FILE = process.env.DEMO_EVIDENCE ?? path.join(REPO_ROOT, "docs/demo-evidence.json");

function load(): any {
  assert.ok(fs.existsSync(FILE), `demo evidence missing: ${FILE} (run workbench demo --fake-llm)`);
  const ev = JSON.parse(fs.readFileSync(FILE, "utf8"));
  assert.equal(ev.result, "completed", `demo did not complete: ${ev.result}`);
  return ev;
}
const step = (ev: any, name: string) => ev.steps.find((s: any) => s.step === name);

test("A26: real recursion — P0 produces P1, P1 produces P2; executed planner hashes change; evidence bound; no external patch", () => {
  const ev = load();
  const P0 = step(ev, "bootstrap").genesis_release;
  const cr1 = step(ev, "cr1");
  const cr2 = step(ev, "cr2");
  assert.ok(cr1.governed_by.every((j: any) => j.pinned_release === P0), "P1 was authored and evaluated by jobs pinned to P0");
  assert.equal(cr2.governed_by, cr1.release, "P2 was evaluated by a job pinned to P1");
  assert.equal(cr2.governed_by_is_P1, true);
  assert.ok(cr1.binary && cr2.binary_P2 && cr2.binary_P1, "binary digests recorded");
  assert.notEqual(cr2.binary_P1, cr2.binary_P2, "the executed planner binary changed P1 → P2");
  const bootstrapActive = step(ev, "status").active;
  assert.equal(bootstrapActive, P0);
  assert.ok(cr1.proof_obligations.every((o: any) => o.ok), "P1 obligations checked");
  assert.ok(cr2.obligations.every((o: any) => o.ok), "P2 obligations checked");
  assert.equal(cr1.reviews_under_P0.concurrent_authority, false, "under P0 the reviews were serial");
  assert.equal(cr2.reviews_under_P1.concurrent_authority, true, "under P1 the independent reviews held authority concurrently");
  const act = step(ev, "activate_p1");
  assert.ok(act.approval, "activation used a recorded operator approval via the product API");
  const fin = step(ev, "final");
  assert.equal(fin.active, cr2.release, "P2 is active at the end");
  assert.ok(cr1.rejected_candidates.length >= 1, "the first P1 candidate failed a real check and was preserved");
  assert.ok(cr1.revisions.some((r: any) => r.status === "revised"), "bounded repair created a recorded revision");
  const bypass = step(ev, "bypass_attempts");
  assert.deepEqual(bypass.remove_refutation.releases, [], "refutation-removal candidate was not published");
  assert.match(String(bypass.remove_refutation.build_failure), /mandatory-role|well-formedness/);
  assert.deepEqual(bypass.protected_edit.releases, []);
  assert.ok(bypass.protected_edit.rejected.some((r: any) => /allowlist|traversal/.test(r.reason)));
  const jv = step(ev, "journal_verify");
  assert.equal(jv.ok, true);
});

test("A27: equivalence improvement — general P05 theorem checked; fixtures agree; benchmark measured and recorded", () => {
  const ev = load();
  const cr2 = step(ev, "cr2");
  const p05 = cr2.obligations.find((o: any) => o.id === "P05");
  assert.ok(p05, "P05 obligation present");
  assert.equal(p05.ok, true);
  assert.equal(p05.scope, "general");
  assert.match(p05.statement, /P05 FactoryPrev.plan FactoryPkg.plan/);
  assert.ok(p05.axioms.every((a: string) => ["propext", "Classical.choice", "Quot.sound"].includes(a)));
  assert.equal(cr2.recipe, "planner_equivalent");
  const bench = step(ev, "benchmark");
  assert.equal(bench.identical_outputs, true, "P1 and P2 binaries produce identical plans on the benchmark set");
  assert.ok(Number.isFinite(bench.results.P1.large_views_ms_median) && Number.isFinite(bench.results.P2.large_views_ms_median));
});
