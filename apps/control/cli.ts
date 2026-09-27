#!/usr/bin/env node
// Product CLI (§16). These are Factory Workbench commands, not Codex subcommands.
//
// Run as `node apps/control/cli.ts <command>` (or `npm run workbench -- <command>`).
// The usage text below is also what `--help` prints.

import * as fs from "node:fs";
import * as path from "node:path";
import { randomBytes } from "node:crypto";
import { spawnSync } from "node:child_process";
import { DatabaseSync } from "node:sqlite";
import { cliHint, loadSettings, REPO_ROOT, statePaths } from "./config.ts";

function parse(argv: string[]) {
  const pos: string[] = [];
  const flags: Record<string, string | true> = {};
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a.startsWith("--")) {
      const k = a.slice(2);
      const n = argv[i + 1];
      if (n !== undefined && !n.startsWith("--")) {
        flags[k] = n;
        i++;
      } else flags[k] = true;
    } else pos.push(a);
  }
  return { pos, flags };
}

const USAGE = `usage: node apps/control/cli.ts <command> [--state DIR] [--port N]

  doctor [--live --consent]           check host, Docker, images, toolchain
  bootstrap                           build the kernel, verify genesis, create the trust root
  serve                               start the local server (prints a one-time sign-in link)
  login                               print a fresh one-time sign-in link (server must be running)
  job submit --fixture NAME [--release D] | list | fixtures | show ID | pause ID | resume ID | cancel ID
  change propose "TEXT" [--revisions N] | list | show ID | revise ID --note TEXT
  release list | show D | preview D | approve D --expected-base D
          | activate D --expected-active D --approval ID | revoke APPROVAL
  migrate preview JOB --target D | apply JOB --target D --expected-revision N
  journal verify | export [--out FILE]
  recovery pause-all
  demo --fake-llm | --live-codex --consent --budget N

  D = a release digest or a unique prefix (at least 6 hex characters).
  --state defaults to $FACTORY_STATE_DIR or ~/.factory-workbench/state; --port defaults to 4317.`;

const { pos, flags } = parse(process.argv.slice(2));
if (flags.help || flags.h || pos[0] === "help" || pos.length === 0) {
  console.log(USAGE);
  process.exit(pos.length === 0 && !flags.help && !flags.h ? 1 : 0);
}
const settings = loadSettings({
  ...(typeof flags.state === "string" ? { stateDir: path.resolve(flags.state) } : {}),
  ...(typeof flags.port === "string" ? { port: Number(flags.port) } : {}),
});
const P = statePaths(settings.stateDir);

function out(v: unknown): void {
  console.log(typeof v === "string" ? v : JSON.stringify(v, null, 2));
}

function die(msg: string, code = 1): never {
  console.error(`workbench: ${msg}`);
  process.exit(code);
}

async function api(method: string, route: string, body?: unknown): Promise<any> {
  let token: string;
  try {
    token = fs.readFileSync(path.join(P.operator, "token"), "utf8").trim();
  } catch {
    die(`not set up yet. Run: ${cliHint(settings, "bootstrap")}`);
  }
  const res = await fetch(`http://127.0.0.1:${settings.port}${route}`, {
    method,
    headers: { Authorization: `Bearer ${token}`, "Content-Type": "application/json", "X-Factory-Request": "1" },
    body: body === undefined ? undefined : JSON.stringify(body),
  }).catch(() => die(`cannot reach the workbench server on 127.0.0.1:${settings.port}. Start it with: ${cliHint(settings, "serve")}`));
  const text = await res.text();
  let j: any;
  try {
    j = JSON.parse(text);
  } catch {
    j = text;
  }
  if (!res.ok) die(`${res.status} ${j?.code ?? ""}: ${j?.message ?? text}`);
  return j;
}

const cid = () => (typeof flags["command-id"] === "string" ? flags["command-id"] : `cli-${Date.now()}-${randomBytes(3).toString("hex")}`);
const natFlag = (k: string, min = 0): number => {
  const v = flags[k];
  if (typeof v !== "string" || !/^(0|[1-9][0-9]{0,8})$/.test(v) || Number(v) < min) die(`--${k} must be a whole number ≥ ${min}`);
  return Number(v);
};
const need = (k: string): string => (typeof flags[k] === "string" ? (flags[k] as string) : die(`--${k} is required`));

async function main() {
  const [cmd, sub, arg] = pos;
  switch (cmd) {
    case "doctor": {
      const { doctor } = await import("./doctor.ts");
      const r = await doctor(settings, { live: !!flags.live, consent: !!flags.consent });
      for (const c of r.checks) console.log(`${c.ok ? "ok  " : c.optional ? "warn" : "FAIL"} ${c.id.padEnd(28)} ${c.detail}`);
      process.exit(r.ok ? 0 : 1);
    }
    case "bootstrap": {
      const { Workbench } = await import("./workbench.ts");
      const lean = path.join(REPO_ROOT, "protected/lean");
      console.log("building protected Lean kernel (lake build)...");
      const b = spawnSync("lake", ["build"], { cwd: lean, stdio: "inherit", env: { ...process.env, PATH: `${process.env.HOME}/.elan/bin:${process.env.PATH}` } });
      if (b.status !== 0) die("lake build failed");
      const wb = await Workbench.open(settings);
      try {
        const d = await wb.bootstrap(path.join(REPO_ROOT, "orchestration/genesis"), (m) => console.log(`  ${m}`));
        console.log(`genesis release ${d} installed and activated (trust root).`);
        console.log(`operator token: ${path.join(P.operator, "token")}`);
        console.log(`next: ${cliHint(settings, "serve")}   (prints a one-time sign-in link)`);
      } finally {
        await wb.close();
      }
      return;
    }
    case "serve": {
      const { Workbench } = await import("./workbench.ts");
      const { buildServer, LoginLinks, loginUrl, LINK_TTL_MS } = await import("./server.ts");
      if (!fs.existsSync(path.join(P.operator, "token"))) die(`not set up yet. Run: ${cliHint(settings, "bootstrap")}`);
      const wb = await Workbench.open(settings);
      await wb.start();
      const links = new LoginLinks();
      const app = await buildServer(wb, links);
      await app.listen({ host: settings.bind, port: settings.port });
      console.log(`workbench serving on http://${settings.bind}:${settings.port} (inference: ${settings.codex.mode === "fake" ? "FAKE (mocked)" : "live Codex"})`);
      // The link is a short-lived credential: print it only to an interactive
      // terminal, never into a redirected log.
      if (process.stdout.isTTY && process.env.FACTORY_NO_LOGIN_LINK !== "1") {
        console.log(`\n  Sign in: ${loginUrl(settings.bind, settings.port, links.mint())}`);
        console.log(`  (one-time link, expires in ${LINK_TTL_MS / 60000} min; for a new one: ${cliHint(settings, "login")})\n`);
      } else console.log(`  sign in: run ${cliHint(settings, "login")} for a one-time link`);
      const stop = async () => {
        await app.close();
        await wb.close();
        process.exit(0);
      };
      process.on("SIGINT", stop);
      process.on("SIGTERM", stop);
      return;
    }
    case "login": {
      const r = await api("POST", "/api/session/link", {});
      if (!process.stdout.isTTY) console.error("note: this link is a sign-in credential for the next few minutes; don't keep it in logs");
      console.log(`Sign in: ${r.url}`);
      console.log(`(one-time link, expires in ${Math.round(Number(r.expires_in_s) / 60)} min)`);
      return;
    }
    case "job":
      if (sub === "submit") return out(await api("POST", "/api/jobs", { fixture: need("fixture"), command_id: cid(), ...(typeof flags.release === "string" ? { release: flags.release } : {}) }));
      if (sub === "list") return out(await api("GET", "/api/jobs"));
      if (sub === "fixtures") return out(await api("GET", "/api/fixtures"));
      if (sub === "show") return out(await api("GET", `/api/jobs/${encodeURIComponent(arg ?? die("job show ID"))}`));
      if (["pause", "resume", "cancel"].includes(sub)) return out(await api("POST", `/api/jobs/${encodeURIComponent(arg ?? die(`job ${sub} ID`))}/${sub}`, { command_id: cid() }));
      return die("job submit|list|fixtures|show|pause|resume|cancel");
    case "change":
      if (sub === "propose") return out(await api("POST", "/api/changes", { request: arg ?? die("request text required"), command_id: cid(),
        ...(flags.revisions !== undefined ? { revisions: natFlag("revisions", 1) } : {}) }));
      if (sub === "show") return out(await api("GET", `/api/changes/${arg}`));
      if (sub === "list") return out(await api("GET", "/api/changes"));
      if (sub === "revise") return out(await api("POST", `/api/changes/${arg}/revise`, { note: need("note"), command_id: cid() }));
      return die("change propose|show|list|revise");
    case "release":
      if (sub === "show") return out(await api("GET", `/api/releases/${arg}`));
      if (sub === "list") return out(await api("GET", "/api/releases"));
      if (sub === "preview") return out(await api("GET", `/api/releases/${arg}/activation-preview`));
      if (sub === "approve") return out(await api("POST", `/api/releases/${arg}/approve`, { expected_base: need("expected-base"), command_id: cid() }));
      if (sub === "activate") return out(await api("POST", `/api/releases/${arg}/activate`, { expected_active: need("expected-active"), approval: need("approval"), command_id: cid() }));
      if (sub === "revoke") return out(await api("POST", `/api/approvals/${arg}/revoke`, { command_id: cid() }));
      return die("release show|list|preview|approve|activate|revoke");
    case "migrate":
      if (sub === "preview") return out(await api("POST", `/api/jobs/${arg}/migrations/preview`, { target: need("target") }));
      if (sub === "apply") return out(await api("POST", `/api/jobs/${arg}/migrations/apply`, { target: need("target"), expected_revision: String(natFlag("expected-revision")), command_id: cid() }));
      return die("migrate preview|apply");
    case "journal": {
      if (sub === "verify") {
        if (!fs.existsSync(P.db)) die(`not set up yet. Run: ${cliHint(settings, "bootstrap")}`);
        const { Workbench } = await import("./workbench.ts");
        const wb = await Workbench.open(settings, { inspectOnly: true });
        let ok = false;
        try {
          const r = await wb.coord.verifyJournal();
          out(r);
          ok = r.ok;
        } finally {
          await wb.close();
        }
        process.exit(ok ? 0 : 1);
      }
      if (sub === "export") {
        if (!fs.existsSync(P.db)) die(`not set up yet. Run: ${cliHint(settings, "bootstrap")}`);
        const db = new DatabaseSync(P.db, { readOnly: true });
        const rows = db.prepare("SELECT * FROM journal ORDER BY seq").all();
        const text = rows.map((r) => JSON.stringify(r)).join("\n") + (rows.length ? "\n" : "");
        if (typeof flags.out === "string") {
          fs.mkdirSync(path.dirname(path.resolve(flags.out)), { recursive: true });
          fs.writeFileSync(flags.out, text);
          console.error(`wrote ${rows.length} journal ${rows.length === 1 ? "entry" : "entries"} to ${flags.out}`);
        } else process.stdout.write(text);
        return;
      }
      return die("journal verify|export");
    }
    case "recovery":
      if (sub === "pause-all") return out(await api("POST", "/api/recovery/pause-all", { command_id: cid() }));
      return die("recovery pause-all");
    case "demo": {
      const { runDemo } = await import("./demo.ts");
      if (flags["live-codex"]) {
        const { runLiveDemo } = await import("./demo.ts");
        return runLiveDemo(settings, { consent: !!flags.consent, budget: Number(flags.budget ?? 0) });
      }
      if (!flags["fake-llm"]) die("demo requires --fake-llm or --live-codex");
      return runDemo({ stateDir: typeof flags.state === "string" ? path.resolve(flags.state) : path.join(REPO_ROOT, ".demo-state"),
        ...(typeof flags.port === "string" ? { port: natFlag("port", 1) } : {}),
        out: typeof flags.out === "string" ? flags.out : path.join(REPO_ROOT, "docs/demo-evidence.json") });
    }
    default:
      console.error(USAGE);
      process.exit(1);
  }
}

main().catch((e) => {
  // Expected operator mistakes read as one line; anything else keeps its stack.
  const msg = String(e?.message ?? e);
  if (/already bootstrapped|state not initialized|refusing to wipe/.test(msg)) die(msg);
  die(e?.stack ?? msg);
});
