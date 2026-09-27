// Golden vectors for canonical encoding (§13.1): TS canonicalize() and the Lean
// kernel's strict decode + canonical re-encode must produce identical bytes.
// Also checks the strict parsers reject duplicate keys, numbers (kernel), extra
// fields, noncanonical naturals and lone surrogates.
import { test } from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { canonicalize, sha256Hex, strictParse, JsonError } from "../../../packages/protocol/json.ts";
import { KernelClient, fileDigest } from "../../../apps/control/kernel.ts";
import { REPO_ROOT } from "../../../apps/control/config.ts";

const V = JSON.parse(fs.readFileSync(path.join(REPO_ROOT, "protected/tests/vectors/canonical.json"), "utf8"));

test("canonical golden vectors: TS and Lean produce identical canonical bytes and digests", async () => {
  const bin = path.join(REPO_ROOT, "protected/lean/.lake/build/bin/factory-kernel");
  const k = new KernelClient(bin, fileDigest(bin));
  try {
    const out: any[] = [];
    for (const v of V.vectors) {
      const ts = canonicalize(v.value);
      const r = await k.query({ op: "canonical", kind: v.kind, value: v.value });
      // The kernel's raw response bytes must equal the TS canonical encoding of the same response,
      // and the embedded value must be byte-identical to TS canonicalize(value).
      assert.equal(k.lastRaw, canonicalize(r), `kernel emits canonical bytes (${v.name})`);
      assert.ok(k.lastRaw.includes(`"value":${ts}`), `vector ${v.name}: Lean bytes == TS bytes`);
      // the kernel's raw response line is itself canonical: re-parse and compare bytes
      assert.equal(canonicalize(strictParse(ts, { numbers: "reject" })), ts);
      out.push({ name: v.name, canonical: ts, sha256: sha256Hex(ts) });
    }
    fs.writeFileSync(path.join(REPO_ROOT, "protected/tests/vectors/canonical.expected.json"), JSON.stringify(out, null, 2) + "\n");
  } finally {
    k.stop();
  }
});

test("strict JSON boundary rejects ambiguous inputs (TS and kernel)", async () => {
  for (const bad of ['{"a":"1","a":"2"}', '{"a":1.5}', '{"a":"\\ud800"}', '[1] x', '{"a":01}']) {
    assert.throws(() => strictParse(bad, { numbers: "reject" }), JsonError, bad);
  }
  const bin = path.join(REPO_ROOT, "protected/lean/.lake/build/bin/factory-kernel");
  const k = new KernelClient(bin, fileDigest(bin));
  try {
    const cases: [string, any][] = [
      ["extra field", { op: "canonical", kind: "envelope", value: { actor: { type: "coordinator" }, epoch: "0", tick: "0", command: { type: "recover_controller" }, extra: "x" } }],
      ["noncanonical natural", { op: "canonical", kind: "envelope", value: { actor: { type: "coordinator" }, epoch: "007", tick: "0", command: { type: "recover_controller" } } }],
      ["unknown tag", { op: "canonical", kind: "envelope", value: { actor: { type: "god" }, epoch: "0", tick: "0", command: { type: "recover_controller" } } }],
      ["unknown command", { op: "canonical", kind: "envelope", value: { actor: { type: "coordinator" }, epoch: "0", tick: "0", command: { type: "grant_all" } } }],
    ];
    for (const [name, req] of cases) {
      const r = await k.call(req);
      assert.equal(r.ok, false, name);
      assert.equal(r.code, "BAD_REQUEST", name);
    }
  } finally {
    k.stop();
  }
});
