// Capture full-page screenshots of every UI route (design review aid).
//   node scripts/demo-video/shots.ts <stateDir> <outDir> [baseUrl]
import fs from "node:fs";
import path from "node:path";
import { chromium } from "playwright";

const [STATE, OUT, BASE = "http://127.0.0.1:4317"] = process.argv.slice(2);
const token = fs.readFileSync(path.join(STATE, "operator/token"), "utf8").trim();
const auth = { Authorization: `Bearer ${token}` };
const j = async (p: string) => (await fetch(BASE + p, { headers: auth })).json();

const browser = await chromium.launch();
for (const scheme of ["light", "dark"] as const) {
  const ctx = await browser.newContext({ viewport: { width: 1440, height: 900 }, colorScheme: scheme });
  const page = await ctx.newPage();
  await page.goto(BASE + "/");
  await page.screenshot({ path: path.join(OUT, `${scheme}-00-login.png`), fullPage: true });
  await ctx.request.post(`${BASE}/api/session`, { data: { token }, headers: { "Content-Type": "application/json", "X-Factory-Request": "1" } });
  const jobs: any[] = await j("/api/jobs");
  const changes: any[] = await j("/api/changes");
  const rels: any[] = await j("/api/releases");
  const routes: [string, string][] = [
    ["01-home", "#/"], ["02-improve", "#/improve"], ["05-releases", "#/releases"], ["07-assurance", "#/assurance"], ["08-journal", "#/journal"],
  ];
  if (jobs[0]) routes.push(["03-job", `#/jobs/${jobs[0].id}`]);
  if (changes[0]) routes.push(["04-change", `#/changes/${changes[0].id}`]);
  const nonGenesis = rels.find((r) => !r.active) ?? rels[0];
  if (nonGenesis) routes.push(["06-release", `#/releases/${nonGenesis.digest}`]);
  for (const [name, hash] of routes) {
    await page.goto(`${BASE}/${hash}`);
    await page.reload();
    await page.waitForTimeout(1500);
    await page.screenshot({ path: path.join(OUT, `${scheme}-${name}.png`), fullPage: true });
  }
  await ctx.close();
}
await browser.close();
console.log("ok");
