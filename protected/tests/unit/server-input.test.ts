// Operator input validation at the HTTP boundary: malformed numbers are a 400
// for that request, never a kernel fault that disables the coordinator.
import { test } from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { buildServer } from "../../../apps/control/server.ts";
import { openCopy } from "../harness.ts";

test("malformed naturals are rejected per request and leave the coordinator writable", async () => {
  const { wb, settings } = await openCopy("server-input");
  const app = await buildServer(wb);
  const token = fs.readFileSync(path.join(settings.stateDir, "operator/token"), "utf8").trim();
  const headers = { host: `127.0.0.1:${settings.port}`, "content-type": "application/json", authorization: `Bearer ${token}`, "x-factory-request": "1" };
  try {
    for (const bad of ["07", "-1", "1.5", "NaN", "", "1e3"]) {
      const r = await app.inject({ method: "POST", url: "/api/jobs/nope/migrations/apply", headers,
        payload: { target: "a".repeat(64), expected_revision: bad, command_id: `bad-rev-${bad.length}-${bad.replace(/[^a-z0-9]/gi, "x")}` } });
      assert.equal(r.statusCode, 400, `expected_revision ${JSON.stringify(bad)} → ${r.statusCode} ${r.body}`);
    }
    for (const bad of [0, -2, "3x", "007"]) {
      const r = await app.inject({ method: "POST", url: "/api/changes", headers,
        payload: { request: "a valid improvement request", revisions: bad, command_id: `bad-revs-${String(bad).replace(/[^a-z0-9]/gi, "x")}` } });
      assert.equal(r.statusCode, 400, `revisions ${JSON.stringify(bad)} → ${r.statusCode} ${r.body}`);
    }
    const unknownApi = await app.inject({ method: "GET", url: "/api/no-such-route", headers: { host: headers.host, authorization: headers.authorization } });
    assert.equal(unknownApi.statusCode, 404);
    const badPath = await app.inject({ method: "GET", url: "/%E0%A4%A", headers: { host: headers.host } });
    assert.ok(badPath.statusCode === 400 || badPath.statusCode === 404, `malformed path → ${badPath.statusCode}`);
    // Still writable: a valid audit submission is accepted.
    const ok = await app.inject({ method: "POST", url: "/api/jobs", headers, payload: { fixture: "genesis-package", command_id: "after-bad-input" } });
    assert.equal(ok.statusCode, 200, ok.body);
    const unknownFixture = await app.inject({ method: "POST", url: "/api/jobs", headers, payload: { fixture: "nope", command_id: "unknown-fixture" } });
    assert.match(unknownFixture.json().message, /registered: genesis-package/);
  } finally {
    await app.close();
    await wb.close();
  }
});
