// Records the critical operator flow by driving the REAL workbench UI.
//
//   node scripts/demo-video/record.ts [--out DIR]
//
// Off camera: a fresh state directory is bootstrapped (real sandboxed genesis
// verification) and the real server is started. On camera, a scripted browser
// performs the operator flow; frames come from the Chrome screencast protocol
// with their wall-clock timestamps. Timeline markers (caption + playback speed)
// are written to timeline.json for edit.py. Inference is the deterministic fake
// Codex CLI, and the video says so.
import * as fs from "node:fs";
import * as path from "node:path";
import { spawn, spawnSync, type ChildProcess } from "node:child_process";
import { fileURLToPath } from "node:url";
import { chromium, type Locator, type Page } from "playwright";

const HERE = path.dirname(fileURLToPath(import.meta.url));
const REPO = path.resolve(HERE, "../..");
const args = process.argv.slice(2);
const OUT = path.resolve(args[args.indexOf("--out") + 1] && args.includes("--out") ? args[args.indexOf("--out") + 1] : path.join(REPO, ".video-build"));
const STATE = path.join(OUT, "state");
const FRAMES = path.join(OUT, "frames");
const PORT = 4411;
const BASE = `http://127.0.0.1:${PORT}`;
const W = 1280, H = 720, DSF = 1.5; // → 1920×1080 frames

const REQUEST = "Parallelize the independent reproduction and refutation reviews: remove the incidental ordering edge between reproduction and refutation and let the planner dispatch both, while keeping both publication gates mandatory and bound to the same frozen candidate.";

const sleep = (ms: number) => new Promise((r) => setTimeout(r, ms));
const log = (m: string) => console.log(`[${new Date().toISOString().slice(11, 19)}] ${m}`);

// ---------------------------------------------------------------- timeline
interface Mark { t: number; scene: string; caption: string; sub?: string; speed: number }
const marks: Mark[] = [];
function mark(scene: string, caption: string, speed = 1, sub = "") {
  marks.push({ t: Date.now() / 1000, scene, caption, sub, speed });
  log(`mark ${scene} x${speed}: ${caption}`);
}

// ---------------------------------------------------------------- server
function cli(argv: string[], opts: { stdio?: "inherit" | "pipe" } = {}) {
  return spawnSync(process.execPath, [path.join(REPO, "apps/control/cli.ts"), ...argv, "--state", STATE, "--port", String(PORT)],
    { stdio: opts.stdio ?? "inherit", encoding: "utf8", env: { ...process.env, PATH: `${process.env.HOME}/.elan/bin:${process.env.PATH}` } });
}

async function startServer(): Promise<ChildProcess> {
  // The fake model answers in milliseconds; a fixed 6 s latency makes concurrent
  // review attempts visible on screen. Disclosed in the video and docs/video/README.md.
  const p = spawn(process.execPath, [path.join(REPO, "apps/control/cli.ts"), "serve", "--state", STATE, "--port", String(PORT)],
    { stdio: ["ignore", "pipe", "pipe"], env: { ...process.env, FAKE_CODEX_LATENCY_MS: "6000" } });
  let buf = "";
  p.stdout!.on("data", (d) => (buf += d));
  p.stderr!.on("data", (d) => (buf += d));
  for (let i = 0; i < 120 && !buf.includes("serving on"); i++) await sleep(500);
  if (!buf.includes("serving on")) throw new Error(`server did not start: ${buf}`);
  return p;
}

let TOKEN = "";
async function api(route: string): Promise<any> {
  const r = await fetch(`${BASE}${route}`, { headers: { Authorization: `Bearer ${TOKEN}` } });
  return r.json();
}
async function until(label: string, pred: () => Promise<boolean>, timeoutMs = 20 * 60_000): Promise<void> {
  const end = Date.now() + timeoutMs;
  while (Date.now() < end) {
    if (await pred()) return;
    await sleep(500);
  }
  throw new Error(`timeout waiting for ${label}`);
}

// ---------------------------------------------------------------- cursor
const CURSOR_JS = `
(() => {
  if (window.__fwCursor) return;
  window.__fwCursor = true;
  const add = () => {
    const c = document.createElement('div');
    c.id = '__fw_cursor';
    c.innerHTML = '<svg width="26" height="26" viewBox="0 0 24 24"><path d="M4 2 L4 19 L8.5 14.8 L11.4 21.4 L14.2 20.2 L11.3 13.7 L17.5 13.7 Z" fill="white" stroke="black" stroke-width="1.4" stroke-linejoin="round"/></svg>';
    Object.assign(c.style, { position: 'fixed', left: '-40px', top: '-40px', zIndex: 2147483647, pointerEvents: 'none', transition: 'transform 60ms', filter: 'drop-shadow(0 2px 3px rgba(0,0,0,.45))' });
    document.documentElement.appendChild(c);
    addEventListener('mousemove', (e) => { c.style.left = e.clientX - 3 + 'px'; c.style.top = e.clientY - 2 + 'px'; }, true);
    addEventListener('mousedown', (e) => {
      c.style.transform = 'scale(.85)';
      const r = document.createElement('div');
      Object.assign(r.style, { position: 'fixed', left: e.clientX - 18 + 'px', top: e.clientY - 18 + 'px', width: '36px', height: '36px', borderRadius: '50%',
        border: '3px solid #f5a524', zIndex: 2147483646, pointerEvents: 'none', transition: 'all 450ms ease-out', opacity: '0.95' });
      document.documentElement.appendChild(r);
      requestAnimationFrame(() => { r.style.transform = 'scale(1.8)'; r.style.opacity = '0'; });
      setTimeout(() => r.remove(), 500);
    }, true);
    addEventListener('mouseup', () => { c.style.transform = 'scale(1)'; }, true);
  };
  if (document.readyState === 'loading') addEventListener('DOMContentLoaded', add); else add();
})();`;

let mouse = { x: W / 2, y: H / 2 };
async function moveTo(page: Page, loc: Locator, ms = 650): Promise<{ x: number; y: number }> {
  await loc.scrollIntoViewIfNeeded();
  const b = await loc.boundingBox();
  if (!b) throw new Error("element not visible");
  const x = b.x + b.width / 2, y = b.y + b.height / 2;
  const steps = Math.max(8, Math.round(ms / 16));
  for (let i = 1; i <= steps; i++) {
    const k = i / steps, e = k < 0.5 ? 2 * k * k : 1 - Math.pow(-2 * k + 2, 2) / 2;
    await page.mouse.move(mouse.x + (x - mouse.x) * e, mouse.y + (y - mouse.y) * e);
    await sleep(ms / steps);
  }
  mouse = { x, y };
  return mouse;
}
async function click(page: Page, loc: Locator, pause = 350) {
  await moveTo(page, loc);
  await sleep(pause);
  await loc.click({ delay: 90 }); // real click at the element centre (cursor is already there)
  await sleep(250);
}
async function typeInto(page: Page, loc: Locator, text: string, delay = 28) {
  await click(page, loc);
  await page.keyboard.type(text, { delay });
}
async function scrollTo(page: Page, loc: Locator, block: "start" | "center" = "start") {
  await loc.evaluate((el, b) => el.scrollIntoView({ behavior: "smooth", block: b as ScrollLogicalPosition }), block);
  await sleep(900);
}
async function scrollBy(page: Page, dy: number, ms = 1400) {
  await page.evaluate(([d]) => window.scrollBy({ top: d, behavior: "smooth" }), [dy]);
  await sleep(ms);
}
async function hover(page: Page, loc: Locator, hold = 1200) {
  await moveTo(page, loc);
  await sleep(hold);
}

// ---------------------------------------------------------------- main
async function main() {
  fs.rmSync(OUT, { recursive: true, force: true });
  fs.mkdirSync(FRAMES, { recursive: true });
  log("bootstrapping a fresh workbench (off camera; real sandboxed genesis verification)…");
  const b = cli(["bootstrap"], { stdio: "pipe" });
  if (b.status !== 0) throw new Error(`bootstrap failed:\n${b.stdout}\n${b.stderr}`);
  const P0 = /genesis release ([0-9a-f]{64})/.exec(b.stdout)![1];
  TOKEN = fs.readFileSync(path.join(STATE, "operator/token"), "utf8").trim();
  const server = await startServer();
  log(`server up; P0 = ${P0}`);

  const browser = await chromium.launch();
  const context = await browser.newContext({ viewport: { width: W, height: H }, deviceScaleFactor: DSF, colorScheme: "dark" });
  await context.addInitScript(CURSOR_JS);
  // Recording-only layout aid: extra space below the page so any focused section can be
  // scrolled to the top of the frame, clear of the caption band added in editing.
  await context.addInitScript(`addEventListener('DOMContentLoaded', () => { const s = document.createElement('style'); s.textContent = 'body{padding-bottom:70vh !important}'; document.head.appendChild(s); });`);
  // Sign in exactly as an operator would: a one-time link minted like `workbench login` prints.
  // Headless frames have no address bar, so the nonce never appears on screen.
  const link = await fetch(`${BASE}/api/session/link`, { method: "POST", headers: { Authorization: `Bearer ${TOKEN}`, "Content-Type": "application/json", "X-Factory-Request": "1" }, body: "{}" }).then((r) => r.json());
  const page = await context.newPage();
  await page.goto("about:blank");

  // Screencast capture with wall-clock timestamps.
  const cdp = await context.newCDPSession(page);
  const frames: { f: string; t: number }[] = [];
  let n = 0;
  cdp.on("Page.screencastFrame", async (ev: any) => {
    const f = `f${String(n++).padStart(6, "0")}.jpg`;
    fs.writeFileSync(path.join(FRAMES, f), Buffer.from(ev.data, "base64"));
    frames.push({ f, t: ev.metadata.timestamp });
    cdp.send("Page.screencastFrameAck", { sessionId: ev.sessionId }).catch(() => {});
  });
  await cdp.send("Page.startScreencast", { format: "jpeg", quality: 95, maxWidth: Math.round(W * DSF), maxHeight: Math.round(H * DSF), everyNthFrame: 1 });
  const h1 = () => page.locator("main h1");
  const section = (name: string) => page.getByRole("heading", { name, exact: true });
  const fold = (name: string) => page.locator("details.fold > summary", { hasText: name }).first();

  try {
    // 1. Sign in -----------------------------------------------------------
    mark("signin", "`workbench serve` prints a one-time sign-in link. Open it, and you're in", 1, "Single use, expires in 5 minutes, never sent to the server in a URL; no token to copy");
    await page.goto(link.url);
    await page.getByRole("heading", { name: "What should the workbench improve?" }).waitFor();
    await page.mouse.move(mouse.x, mouse.y);
    await sleep(2500);

    // 2. Home --------------------------------------------------------------
    mark("home", "Home asks one question. Everything else is one step away", 1, "Genesis release P0 was installed and verified at setup");
    await sleep(2000);
    await hover(page, page.getByText("Mocked inference.").first(), 1500);
    mark("home", "Honest by default: this recording uses a deterministic fake model", 1, "Kernel, database, sandboxed builds, Lean proofs and release gates are all real");
    await sleep(2500);
    await hover(page, page.locator("footer.foot"), 1500);
    mark("home", "System facts sit in one quiet line: checker, protected components, sandbox", 1);
    await sleep(2500);

    // 3. A normal job --------------------------------------------------------
    mark("job", "Run a real job: audit a package with build, proof and two reviews", 1);
    await click(page, page.getByRole("button", { name: "Run an audit" }));
    await sleep(1200);
    await click(page, page.getByRole("button", { name: "Start audit" }));
    await page.getByRole("heading", { name: "Package audit" }).waitFor();
    const jobId = decodeURIComponent(page.url().split("#/jobs/")[1]);
    mark("job", "A job is pinned to the release that was active when it started", 1, "Steps show what each waits for and whose output it uses");
    await sleep(2500);
    mark("job", "Pause stops new work; anything running settles first", 1);
    await click(page, page.getByRole("button", { name: "Pause" }));
    await sleep(800);
    await scrollTo(page, section("Steps"));
    mark("job", "Each try shows five separate facts: allowed to run, what the machine saw, model call, result kept, cleanup", 3, "Time compressed 3×");
    await until("audit job paused", async () => (await api(`/api/jobs/${jobId}`)).status === "paused", 5 * 60_000);
    await sleep(2500);
    await page.evaluate(() => window.scrollTo({ top: 0, behavior: "smooth" }));
    mark("job", "Paused: completed work is kept; this job stays on P0", 1);
    await sleep(3000);

    // 4. Improve this workbench ---------------------------------------------
    mark("improve", "Now ask the workbench to improve its own orchestration", 1);
    await click(page, page.getByRole("link", { name: "Home", exact: true }));
    await page.getByRole("heading", { name: "What should the workbench improve?" }).waitFor();
    await sleep(800);
    mark("improve", "A plain-language request, bound to the active release and a fixed budget", 2);
    await typeInto(page, page.locator("#request"), REQUEST, 14);
    await sleep(600);
    await click(page, page.getByRole("button", { name: "Adjust" }));
    await typeInto(page, page.getByLabel("Drafts"), "3", 60);
    mark("improve", "Start: the current release (P0) writes and checks its own successor", 1);
    await click(page, page.getByRole("button", { name: /^Start/ }));
    await page.waitForURL(/#\/changes\//);
    const changeId = decodeURIComponent(page.url().split("#/changes/")[1]);
    await h1().waitFor();

    // 5. Evaluation ------------------------------------------------------------
    mark("evaluate", "Every improvement shows where it is: requested, written, checked, published, approved, active", 8, "Codex (mocked) proposes exact file edits · time compressed 8×");
    await until("first evaluation failed", async () => (await api(`/api/changes/${changeId}`)).rejected.length > 0);
    await scrollTo(page, section("Attempts"));
    mark("evaluate", "The first attempt had a real proof error — the fixed verifier rejected it", 1, "Lean's actual diagnostic is shown; no model can override it");
    await sleep(5000);
    mark("evaluate", "The diagnostic went back to the author as a recorded new draft; the second attempt is checked", 10, "Sandboxed build, proof replay, protected tests, two independent reviews · time compressed 10×");
    await until("candidate evaluated (graph)", async () => (await api(`/api/changes/${changeId}`)).graph_changes.some((g: any) => g.available));
    await scrollTo(page, section("What it changes"));
    mark("evaluate", "What changes, in plain words: refute no longer waits for reproduce", 1, "No data dependency between them, so both may run at once; both gates are still required");
    await sleep(6000);
    mark("evaluate", "Publication waits until every required gate passes", 10, "Time compressed 10×");
    await until("release published", async () => (await api(`/api/changes/${changeId}`)).releases.length > 0);
    await page.evaluate(() => window.scrollTo({ top: 0, behavior: "smooth" }));
    const review = page.getByRole("link", { name: "Review release" });
    await review.waitFor();
    mark("release", "Release P1 was published by the protected kernel. It's waiting for you", 1);
    await sleep(2500);
    const P1 = (await api(`/api/changes/${changeId}`)).releases[0];

    // 6. Release review ----------------------------------------------------------
    await click(page, review);
    await page.getByRole("heading", { name: `Release ${P1.slice(0, 8)}` }).waitFor();
    mark("release", "The decision comes first: the exact release, what it replaces, and the evidence", 1, "Full digests, grouped for reading");
    await sleep(4000);
    await scrollTo(page, section("Evidence"));
    mark("release", "Each fact keeps its own label. There is no single 'verified' badge", 1, "Model reviews are judgments, not proofs, and here they are marked as mocked");
    await sleep(6000);
    await scrollTo(page, fold("Proofs"), "center");
    await click(page, fold("Proofs"));
    mark("release", "Details are one click away: every proof obligation, general or finite, re-checked from scratch", 1);
    await sleep(5000);
    await click(page, fold("Proofs"));
    await scrollTo(page, section("Decision"));
    await sleep(800);

    // 7. Activation ----------------------------------------------------------------
    await scrollTo(page, page.getByRole("button", { name: "Approve…" }), "center");
    mark("activate", "Activation never moves existing jobs: they stay on P0 unless explicitly migrated", 1);
    await sleep(3000);
    mark("activate", "Approve: type the release's first 8 characters and acknowledge the mocked reviews", 1, "Approval binds this exact digest to the current active release");
    await click(page, page.getByRole("button", { name: "Approve…" }));
    await sleep(1500);
    await typeInto(page, page.getByLabel("Type the first 8 characters of the release ID to confirm"), P1.slice(0, 8), 90);
    await click(page, page.getByRole("checkbox", { name: /scripted by fake inference/ }));
    await sleep(800);
    await click(page, page.getByRole("button", { name: `Record approval of ${P1.slice(0, 8)}` }));
    await page.getByText("Approval recorded.").waitFor();
    await sleep(1500);
    mark("activate", "Activate is a separate step: a compare-and-swap on the expected active release", 1);
    await click(page, page.getByRole("button", { name: "Activate…" }));
    await sleep(1500);
    await typeInto(page, page.getByLabel("Type the first 8 characters of the release ID to confirm"), P1.slice(0, 8), 90);
    await sleep(600);
    await click(page, page.getByRole("button", { name: `Activate ${P1.slice(0, 8)}` }));
    await page.getByText(`Activated. New jobs now use ${P1.slice(0, 8)}.`).waitFor();
    await sleep(2000);

    // 8. After -----------------------------------------------------------------------
    mark("after", "P1 is now the default for new jobs; the paused job is still pinned to P0", 1);
    await click(page, page.getByRole("link", { name: "Home", exact: true }));
    await page.getByRole("heading", { name: "What should the workbench improve?" }).waitFor();
    await sleep(1000);
    await scrollTo(page, section("Jobs"));
    await hover(page, page.locator(`a[href="#/jobs/${jobId}"]`).first(), 3000);
    mark("after", "A new job runs on P1", 1);
    await click(page, page.getByRole("button", { name: "Run an audit" }));
    await sleep(1000);
    await click(page, page.getByRole("button", { name: "Start audit" }));
    await page.getByRole("heading", { name: "Package audit" }).waitFor();
    const job2 = decodeURIComponent(page.url().split("#/jobs/")[1]);
    mark("after", "Build and proof run first…", 10, "Time compressed 10×");
    await scrollTo(page, section("Steps"));
    await until("both reviews authorized concurrently", async () => {
      const j = await api(`/api/jobs/${job2}`);
      const live = (id: string) => j.attempts.some((a: any) => a.step === id && ["authorized", "starting", "running"].includes(a.status));
      return live("reproduce") && live("refute");
    }, 15 * 60_000);
    // The UI polls; wait until the page itself shows both reviews running before captioning it.
    await page.waitForFunction(() => ["reproduce", "refute"].every((id) => [...document.querySelectorAll(".steps > li")]
      .some((li) => li.querySelector(".sid")?.textContent?.trim() === id && (li.querySelector("summary")?.textContent ?? "").includes("running"))), null, { timeout: 15_000 });
    mark("after", "…then reproduction and refutation run at the same time under P1", 1, "Both publication gates are still mandatory and bound to the same payload");
    await sleep(6500);
    mark("after", "Both reviews passed; the summary step combines them", 1);
    await until("job2 done", async () => (await api(`/api/jobs/${job2}`)).status === "succeeded", 5 * 60_000);
    await sleep(2500);
    mark("end", "", 1);
    await sleep(300);
  } finally {
    await cdp.send("Page.stopScreencast").catch(() => {});
    await sleep(500);
    fs.writeFileSync(path.join(OUT, "timeline.json"), JSON.stringify({ viewport: [W, H], dsf: DSF, marks, frames, P0 }, null, 2));
    await browser.close();
    server.kill("SIGTERM");
    log(`captured ${frames.length} frames; timeline at ${path.join(OUT, "timeline.json")}`);
  }
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
