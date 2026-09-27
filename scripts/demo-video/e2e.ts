// Browser end-to-end check of the operator UI against a running workbench:
// one-time sign-in link → home → release review → approve (typed confirm,
// mocked-review acknowledgement) → activate. Mutates the given state.
//   node scripts/demo-video/e2e.ts <stateDir> [baseUrl]
import fs from "node:fs";
import path from "node:path";
import assert from "node:assert/strict";
import { chromium } from "playwright";

const [STATE, BASE = "http://127.0.0.1:4317"] = process.argv.slice(2);
const token = fs.readFileSync(path.join(STATE, "operator/token"), "utf8").trim();
const H = { Authorization: `Bearer ${token}`, "Content-Type": "application/json", "X-Factory-Request": "1" };
const api = async (m: string, p: string, body?: unknown) => (await fetch(BASE + p, { method: m, headers: H, body: body === undefined ? undefined : JSON.stringify(body) })).json();

const browser = await chromium.launch();
const ctx = await browser.newContext({ viewport: { width: 1280, height: 900 } });
const page = await ctx.newPage();
const errors: string[] = [];
page.on("pageerror", (e) => errors.push(String(e)));
page.on("console", (m) => { if (m.type() === "error") errors.push(m.text()); });

// 1. Sign-in link: lands signed in, fragment removed from the address bar.
const { url } = await api("POST", "/api/session/link", {});
await page.goto(url);
await page.getByRole("heading", { name: "What should the workbench improve?" }).waitFor();
assert.ok(!page.url().includes("login="), `nonce left in URL: ${page.url()}`);
console.log("ok  sign-in link → home, fragment stripped");

// 2. Reusing the link fails with the expired message (fresh context, no cookie).
const ctx2 = await browser.newContext();
const p2 = await ctx2.newPage();
await p2.goto(url);
await p2.getByRole("heading", { name: "This sign-in link has expired" }).waitFor();
await ctx2.close();
console.log("ok  reused link refused");

// 3. Mock disclosure present; find a release awaiting review.
await page.getByText("Mocked inference.").first().waitFor();
const rels: any[] = await api("GET", "/api/releases");
const cand = rels.find((r) => !r.active && !r.activated);
assert.ok(cand, "no unactivated release to review");
const d8 = cand.digest.slice(0, 8);
await page.getByRole("link", { name: /Review|Activate/ }).first().click();
await page.getByRole("heading", { name: `Release ${d8}` }).waitFor();
console.log("ok  needs-you → release review");

// 4. Approve: needs typed prefix + acknowledgement.
if (!cand.approved) {
  await page.getByRole("button", { name: "Approve…" }).click();
  const confirm = page.getByRole("button", { name: `Record approval of ${d8}` });
  assert.equal(await confirm.isDisabled(), true, "confirm enabled before typing");
  await page.getByLabel("Type the first 8 characters of the release ID to confirm").fill("deadbeef");
  assert.equal(await confirm.isDisabled(), true, "confirm enabled with wrong prefix");
  await page.getByLabel("Type the first 8 characters of the release ID to confirm").fill(d8);
  const ack = page.getByRole("checkbox", { name: /scripted by fake inference/ });
  if (await ack.count()) {
    assert.equal(await confirm.isDisabled(), true, "confirm enabled before acknowledging mocked reviews");
    await ack.check();
  }
  await confirm.click();
  await page.getByText("Approval recorded.").waitFor();
  console.log("ok  approved with typed confirmation");
}

// 5. Activate.
await page.getByRole("button", { name: "Activate…" }).waitFor();
for (let i = 0; i < 20 && (await page.getByRole("button", { name: "Activate…" }).isDisabled()); i++) await page.waitForTimeout(500);
await page.getByRole("button", { name: "Activate…" }).click();
await page.getByLabel("Type the first 8 characters of the release ID to confirm").fill(d8);
await page.getByRole("button", { name: `Activate ${d8}` }).click();
await page.getByText(`Activated. New jobs now use ${d8}.`).waitFor();
const st = await api("GET", "/api/status");
assert.equal(st.active_release, cand.digest);
console.log("ok  activated; kernel reports it active");

// 6. Every page renders without script errors.
for (const h of ["#/", "#/releases", "#/assurance", "#/journal", `#/changes/${cand.change}`]) {
  await page.goto(`${BASE}/${h}`);
  await page.locator("main h1").waitFor();
}
assert.deepEqual(errors, [], `console errors: ${errors.join("\n")}`);
console.log("ok  all pages render, no console errors");
await browser.close();
