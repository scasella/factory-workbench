// One-time sign-in links (apps/control/server.ts LoginLinks + /api/session/claim, /api/session/link).
import { test } from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { buildServer, LINK_TTL_MS, LoginLinks } from "../../../apps/control/server.ts";
import { openCopy } from "../harness.ts";

test("LoginLinks: single use, expiry, replacement", () => {
  let now = 1_000;
  const links = new LoginLinks(() => now);
  const a = links.mint();
  assert.match(a, /^[A-Za-z0-9_-]{43}$/);
  assert.equal(links.claim("wrong"), false);
  assert.equal(links.claim(a), true, "a wrong guess must not burn the live link");
  assert.equal(links.claim(a), false, "second use rejected");
  const b = links.mint();
  const c = links.mint();
  assert.equal(links.claim(b), false, "minting a new link invalidates the previous one");
  now += LINK_TTL_MS + 1;
  assert.equal(links.claim(c), false, "expired");
});

test("claim endpoint: CSRF required, one cookie per link, mint is Bearer-only", async () => {
  const { wb, settings } = await openCopy("session-link");
  const links = new LoginLinks();
  const app = await buildServer(wb, links);
  const host = `127.0.0.1:${settings.port}`;
  const token = fs.readFileSync(path.join(settings.stateDir, "operator/token"), "utf8").trim();
  const json = { host, "content-type": "application/json" };
  try {
    const nonce = links.mint();
    const noCsrf = await app.inject({ method: "POST", url: "/api/session/claim", headers: json, payload: { nonce } });
    assert.equal(noCsrf.statusCode, 403);

    const ok = await app.inject({ method: "POST", url: "/api/session/claim", headers: { ...json, "x-factory-request": "1" }, payload: { nonce } });
    assert.equal(ok.statusCode, 200);
    const cookie = String(ok.headers["set-cookie"]);
    assert.match(cookie, /^fw_session=[0-9a-f]{64}; HttpOnly; SameSite=Strict; Path=\//);
    const sid = cookie.split(";")[0];

    const again = await app.inject({ method: "POST", url: "/api/session/claim", headers: { ...json, "x-factory-request": "1" }, payload: { nonce } });
    assert.equal(again.statusCode, 401);
    assert.equal(again.json().code, "LINK_USED_OR_EXPIRED");

    const status = await app.inject({ method: "GET", url: "/api/status", headers: { host, cookie: sid } });
    assert.equal(status.statusCode, 200, "claimed session authenticates");

    const mintByCookie = await app.inject({ method: "POST", url: "/api/session/link", headers: { ...json, cookie: sid, "x-factory-request": "1" }, payload: {} });
    assert.equal(mintByCookie.statusCode, 401, "a browser session cannot mint sign-in links");

    const mint = await app.inject({ method: "POST", url: "/api/session/link", headers: { ...json, authorization: `Bearer ${token}`, "x-factory-request": "1" }, payload: {} });
    assert.equal(mint.statusCode, 200);
    const url = String(mint.json().url);
    assert.match(url, new RegExp(`^http://127\\.0\\.0\\.1:${settings.port}/#login=[A-Za-z0-9_-]{43}$`), "nonce travels only in the fragment");
    assert.ok(!url.includes(token), "the operator token never appears in a link");
    const fresh = url.split("#login=")[1];
    const claimed = await app.inject({ method: "POST", url: "/api/session/claim", headers: { ...json, "x-factory-request": "1" }, payload: { nonce: fresh } });
    assert.equal(claimed.statusCode, 200);

    const extra = await app.inject({ method: "POST", url: "/api/session/claim", headers: { ...json, "x-factory-request": "1" }, payload: { nonce: fresh, token } });
    assert.equal(extra.statusCode, 400, "exact field set");
  } finally {
    await app.close();
    await wb.close();
  }
});
