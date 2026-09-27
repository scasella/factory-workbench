// Operator HTTP API (§16). Loopback only; operator token (CLI, Bearer) or an
// HttpOnly SameSite=Strict session cookie (UI). State-changing requests need
// the X-Factory-Request header (CSRF: no CORS is enabled, so browsers cannot
// send it cross-origin) plus Host/Origin validation. Bodies are strict JSON
// (duplicate keys rejected) with exact field sets. The UI never decides
// authorization: every write becomes a kernel command.

import Fastify, { type FastifyReply, type FastifyRequest } from "fastify";
import * as fs from "node:fs";
import * as path from "node:path";
import { createHash, randomBytes, timingSafeEqual } from "node:crypto";
import { canonicalize, exactFields, isDigest, strictParse, type Json } from "../../packages/protocol/json.ts";
import { CommandConflict } from "./coordinator.ts";
import { KernelFault } from "./kernel.ts";
import * as ops from "./ops.ts";
import { OpError } from "./ops.ts";
import type { Workbench } from "./workbench.ts";
import { cliHint } from "./config.ts";

const WEB_DIST = path.resolve(path.dirname(new URL(import.meta.url).pathname), "../web/dist");

export function readToken(wb: Workbench): string {
  return fs.readFileSync(path.join(wb.paths.operator, "token"), "utf8").trim();
}

function eq(a: string, b: string): boolean {
  const x = Buffer.from(a);
  const y = Buffer.from(b);
  return x.length === y.length && timingSafeEqual(x, y);
}

/**
 * One-time sign-in links. A link carries a random nonce in the URL *fragment*
 * (never sent to the server, so never in request lines or logs); the page
 * strips it from history and POSTs it to /api/session/claim. The nonce is not
 * the operator token: it is held only as a hash in memory, is single-use,
 * expires after LINK_TTL_MS, dies with the process, and minting a new link
 * invalidates the previous one.
 */
export const LINK_TTL_MS = 5 * 60 * 1000;
export class LoginLinks {
  private current: { hash: Buffer; expires: number } | null = null;
  private readonly now: () => number;
  constructor(now: () => number = Date.now) {
    this.now = now;
  }
  mint(): string {
    const nonce = randomBytes(32).toString("base64url");
    this.current = { hash: createHash("sha256").update(nonce).digest(), expires: this.now() + LINK_TTL_MS };
    return nonce;
  }
  /** True exactly once for the live nonce; any claim attempt on a mismatch leaves the live link intact. */
  claim(nonce: string): boolean {
    const c = this.current;
    if (!c || this.now() > c.expires) {
      this.current = null;
      return false;
    }
    const h = createHash("sha256").update(nonce).digest();
    if (!timingSafeEqual(h, c.hash)) return false;
    this.current = null;
    return true;
  }
}

export function loginUrl(host: string, port: number, nonce: string): string {
  const h = host.includes(":") ? `[${host}]` : host;
  return `http://${h}:${port}/#login=${nonce}`;
}

function body(req: FastifyRequest, fields: string[], optional: string[] = []): Record<string, Json> {
  const b = (req.body ?? {}) as Record<string, Json>;
  const present = Object.keys(b);
  for (const k of present) if (!fields.includes(k) && !optional.includes(k)) throw new OpError("BAD_REQUEST", `unexpected field '${k}'`);
  for (const f of fields) if (!(f in b)) throw new OpError("BAD_REQUEST", `missing field '${f}'`);
  return b;
}

function str(v: Json | undefined, name: string, max = 200): string {
  if (typeof v !== "string" || v.length === 0 || v.length > max) throw new OpError("BAD_REQUEST", `field '${name}' must be a non-empty string`);
  return v;
}

/** A natural number in canonical decimal form (a JSON number or string). Rejects NaN, signs, fractions and leading zeros. */
function nat(v: Json | undefined, name: string, min = 0): number | undefined {
  if (v === undefined) return undefined;
  const t = typeof v === "number" ? String(v) : v;
  if (typeof t !== "string" || !/^(0|[1-9][0-9]{0,8})$/.test(t) || Number(t) < min) throw new OpError("BAD_REQUEST", `field '${name}' must be a whole number ≥ ${min}`);
  return Number(t);
}

function cmdId(b: Record<string, Json>): string {
  const id = str(b.command_id, "command_id");
  if (!/^[A-Za-z0-9._:\-]{1,120}$/.test(id)) throw new OpError("BAD_REQUEST", "invalid command_id");
  return `op:${id}`;
}

export async function buildServer(wb: Workbench, links: LoginLinks = new LoginLinks()) {
  const token = readToken(wb);
  const sessions = new Set<string>();
  const port = wb.settings.port;
  const allowedHosts = new Set([`127.0.0.1:${port}`, `localhost:${port}`, `[::1]:${port}`]);
  const app = Fastify({ bodyLimit: 1024 * 1024, logger: false, forceCloseConnections: true }); // SSE streams must not block shutdown

  app.removeAllContentTypeParsers();
  app.addContentTypeParser("application/json", { parseAs: "string" }, (_req, text, done) => {
    try {
      done(null, strictParse(String(text), { maxBytes: 1024 * 1024 }));
    } catch (e) {
      const err = new OpError("BAD_JSON", (e as Error).message);
      done(err, undefined);
    }
  });

  const bearer = (req: FastifyRequest): boolean => {
    const h = req.headers.authorization;
    return !!h && h.startsWith("Bearer ") && eq(h.slice(7), token);
  };
  const authed = (req: FastifyRequest): boolean => {
    if (bearer(req)) return true;
    const cookie = String(req.headers.cookie ?? "").split(";").map((s) => s.trim()).find((s) => s.startsWith("fw_session="));
    return !!cookie && sessions.has(cookie.slice("fw_session=".length));
  };

  app.addHook("onRequest", async (req, reply) => {
    reply.header("X-Content-Type-Options", "nosniff");
    reply.header("Referrer-Policy", "no-referrer");
    reply.header("Content-Security-Policy", "default-src 'self'; script-src 'self'; style-src 'self' 'unsafe-inline'; img-src 'self' data:; connect-src 'self'; frame-ancestors 'none'; base-uri 'none'; form-action 'self'");
    if (!allowedHosts.has(String(req.headers.host ?? ""))) {
      reply.code(421).send({ code: "BAD_HOST", message: "Host header not allowed" });
      return reply;
    }
    const origin = req.headers.origin;
    if (origin && !allowedHosts.has(origin.replace(/^https?:\/\//, ""))) {
      reply.code(403).send({ code: "BAD_ORIGIN", message: "cross-origin request refused" });
      return reply;
    }
    if (!req.url.startsWith("/api/")) return;
    if (req.url === "/api/session" && req.method === "POST") return;
    if (req.url === "/api/signin-hint" && req.method === "GET") return;
    if (req.url === "/api/session/claim" && req.method === "POST") {
      // Unauthenticated by design (the nonce is the credential), but still a
      // state change: require the CSRF header like every other write.
      if (req.headers["x-factory-request"] !== "1") {
        reply.code(403).send({ code: "CSRF", message: "missing X-Factory-Request header" });
        return reply;
      }
      return;
    }
    if (!authed(req)) {
      reply.code(401).send({ code: "UNAUTHENTICATED", message: "operator token or session required" });
      return reply;
    }
    if (req.method !== "GET" && req.headers["x-factory-request"] !== "1") {
      reply.code(403).send({ code: "CSRF", message: "missing X-Factory-Request header" });
      return reply;
    }
  });

  app.setErrorHandler((err: any, _req, reply) => {
    const cur = wb.coord.state();
    if (err instanceof OpError) return reply.code(err.status).send({ code: err.code, message: err.message, current_revision: cur.seq, controller_epoch: cur.state.ctrl_epoch });
    if (err instanceof CommandConflict) return reply.code(409).send({ code: err.code, message: err.message });
    if (err instanceof KernelFault) return reply.code(503).send({ code: "KERNEL_FAULT", message: err.message });
    if (err.code === "BAD_JSON") return reply.code(400).send({ code: "BAD_JSON", message: err.message });
    if (err.statusCode === 413) return reply.code(413).send({ code: "TOO_LARGE", message: "request body too large" });
    return reply.code(500).send({ code: "INTERNAL", message: String(err.message ?? err) });
  });

  app.post("/api/session", async (req, reply) => {
    const b = body(req, ["token"]);
    if (!eq(str(b.token, "token", 200), token)) throw new OpError("UNAUTHENTICATED", "bad token", 401);
    const sid = randomBytes(32).toString("hex");
    sessions.add(sid);
    reply.header("Set-Cookie", `fw_session=${sid}; HttpOnly; SameSite=Strict; Path=/`);
    return { ok: true };
  });

  const newSession = (reply: FastifyReply) => {
    const sid = randomBytes(32).toString("hex");
    sessions.add(sid);
    reply.header("Set-Cookie", `fw_session=${sid}; HttpOnly; SameSite=Strict; Path=/`);
  };
  // Unauthenticated (loopback + Host-checked): tells the sign-in page which
  // command prints a link for this instance and where the token file lives.
  app.get("/api/signin-hint", async () => ({
    login: cliHint(wb.settings, "login"),
    token_file: path.join(wb.paths.operator, "token"),
  }));
  app.post("/api/session/claim", async (req, reply) => {
    const b = body(req, ["nonce"]);
    if (!links.claim(str(b.nonce, "nonce", 100))) throw new OpError("LINK_USED_OR_EXPIRED", "this sign-in link was already used, has expired, or was replaced by a newer one", 401);
    newSession(reply);
    return { ok: true };
  });
  // Mint a fresh sign-in link (`workbench login`). Bearer only: a browser
  // session must not be able to mint links.
  app.post("/api/session/link", async (req) => {
    if (!bearer(req)) throw new OpError("UNAUTHENTICATED", "operator token required", 401);
    body(req, []);
    return { url: loginUrl(wb.settings.bind, port, links.mint()), expires_in_s: String(LINK_TTL_MS / 1000) };
  });

  app.get("/api/status", async () => ops.statusView(wb));
  app.get("/api/fixtures", async () => wb.db.db.prepare("SELECT name, digest, created FROM fixtures").all());
  app.get("/api/jobs", async () => ops.jobsList(wb));
  app.post("/api/jobs", async (req) => {
    const b = body(req, ["fixture", "command_id"], ["release", "attempts"]);
    const release = b.release === undefined || b.release === null ? null : str(b.release, "release", 64);
    const attempts = nat(b.attempts, "attempts", 1);
    return ops.submitAudit(wb, { fixture: str(b.fixture, "fixture"), release, commandId: cmdId(b), attempts });
  });
  app.get("/api/jobs/:id", async (req) => {
    const id = (req.params as any).id as string;
    const j = wb.state().jobs.find((x) => x.id === id);
    if (!j) throw new OpError("UNKNOWN_JOB", "unknown job", 404);
    return ops.jobView(wb, j);
  });
  for (const act of ["pause", "resume", "cancel"] as const) {
    app.post(`/api/jobs/:id/${act}`, async (req) => {
      const b = body(req, ["command_id"]);
      const id = (req.params as any).id as string;
      const f = act === "pause" ? ops.pauseJob : act === "resume" ? ops.resumeJob : ops.cancelJob;
      return f(wb, id, cmdId(b));
    });
  }
  app.get("/api/jobs/:id/events", async (req, reply) => sse(wb, req, reply, (req.params as any).id));
  app.get("/api/journal", async (req) => {
    const after = Number((req.query as any).after ?? 0);
    const rows = wb.db.db.prepare("SELECT seq, command_id, accepted, reject_code, events, effects, envelope, wall_time FROM journal WHERE seq > ? ORDER BY seq LIMIT 500").all(after) as any[];
    return rows.map((r) => ({ ...r, events: JSON.parse(r.events), effects: JSON.parse(r.effects), envelope: JSON.parse(r.envelope) }));
  });
  app.get("/api/journal/verify", async () => wb.coord.verifyJournal());
  app.get("/api/artifacts/:digest", async (req, reply) => {
    const d = (req.params as any).digest as string;
    if (!isDigest(d)) throw new OpError("BAD_DIGEST", "not a digest");
    if (!wb.blobs.has(d)) throw new OpError("UNKNOWN_ARTIFACT", "unknown artifact", 404);
    const bytes = wb.blobs.get(d);
    if (bytes.length > 8 * 1024 * 1024) throw new OpError("TOO_LARGE", "artifact too large to display; export it via the CLI");
    const text = bytes.toString("utf8");
    const isText = Buffer.from(text, "utf8").equals(bytes);
    reply.header("Content-Disposition", "inline");
    if (!isText) {
      reply.type("application/octet-stream");
      return { digest: d, binary: true, size: bytes.length };
    }
    try {
      return { digest: d, json: strictParse(text), size: bytes.length };
    } catch {
      return { digest: d, text, size: bytes.length };
    }
  });
  app.get("/api/changes", async () => {
    // Kernel change records plus read-only presentation fields for the list view.
    const st = wb.state();
    const meta = wb.db.db.prepare("SELECT change_id, request_text, created FROM changes_meta").all() as { change_id: string; request_text: string; created: string }[];
    const m = new Map(meta.map((r) => [r.change_id, r]));
    return st.changes.map((c) => ({ ...c, request_text: m.get(c.id)?.request_text?.slice(0, 400) ?? null, created: m.get(c.id)?.created ?? null,
      releases: st.releases.filter((r) => r.evidence_job && c.jobs.includes(r.evidence_job)).map((r) => r.digest) }));
  });
  app.post("/api/changes", async (req) => {
    const b = body(req, ["request", "command_id"], ["attempts", "revisions"]);
    return ops.proposeChange(wb, { request: str(b.request, "request", 8000), commandId: cmdId(b),
      attempts: nat(b.attempts, "attempts", 1), revisions: nat(b.revisions, "revisions", 1) });
  });
  app.get("/api/changes/:id", async (req) => ops.changeView(wb, (req.params as any).id));
  app.post("/api/changes/:id/revise", async (req) => {
    const b = body(req, ["note", "command_id"]);
    return ops.reviseChange(wb, { change: (req.params as any).id, note: str(b.note, "note", 4000), commandId: cmdId(b) });
  });
  app.get("/api/releases", async () => {
    const st = wb.state();
    return st.releases.map((r) => ({ digest: r.digest, payload: r.payload, source: r.source, parent: r.parent, producer: r.producer,
      evidence_job: r.evidence_job, active: st.active === r.digest, activated: st.activations.some((a) => a.release === r.digest),
      approved: st.approvals.some((a) => a.release === r.digest && !a.revoked),
      change: st.changes.find((c) => r.evidence_job && c.jobs.includes(r.evidence_job))?.id ?? null }));
  });
  app.get("/api/releases/:digest", async (req) => ops.releaseView(wb, (req.params as any).digest));
  app.get("/api/releases/:digest/activation-preview", async (req) => ops.activationPreview(wb, (req.params as any).digest));
  app.post("/api/releases/:digest/approve", async (req) => {
    const b = body(req, ["expected_base", "command_id"]);
    return ops.approveRelease(wb, { release: (req.params as any).digest, expectedBase: str(b.expected_base, "expected_base", 64), commandId: cmdId(b) });
  });
  app.post("/api/releases/:digest/activate", async (req) => {
    const b = body(req, ["expected_active", "approval", "command_id"]);
    return ops.activateRelease(wb, { release: (req.params as any).digest, expectedActive: str(b.expected_active, "expected_active", 64),
      approval: str(b.approval, "approval"), commandId: cmdId(b) });
  });
  app.post("/api/approvals/:id/revoke", async (req) => {
    const b = body(req, ["command_id"]);
    return ops.revokeApproval(wb, (req.params as any).id, cmdId(b));
  });
  app.post("/api/jobs/:id/migrations/preview", async (req) => {
    const b = body(req, ["target"]);
    return ops.migrationPreview(wb, (req.params as any).id, ops.resolveRelease(wb, str(b.target, "target", 64)));
  });
  app.post("/api/jobs/:id/migrations/apply", async (req) => {
    const b = body(req, ["target", "expected_revision", "command_id"]);
    return ops.migrationApply(wb, { job: (req.params as any).id, target: ops.resolveRelease(wb, str(b.target, "target", 64)),
      expectedRevision: String(nat(str(b.expected_revision, "expected_revision", 20), "expected_revision")), commandId: cmdId(b) });
  });
  app.post("/api/recovery/pause-all", async (req) => {
    const b = body(req, ["command_id"]);
    return ops.pauseAll(wb, cmdId(b));
  });
  app.get("/api/logs", async () => wb.logs.slice(-300));
  app.get("/api/assurance", async () => {
    const read = (rel: string) => {
      const f = path.join(wb.repo, rel);
      return fs.existsSync(f) ? JSON.parse(fs.readFileSync(f, "utf8")) : null;
    };
    return {
      contracts: read("protected/contracts.json"),
      kernel_proofs: read("docs/proof-status.json"),
      tests: read("docs/test-results.json"),
      trust: wb.trustStatus(),
      verifier: wb.verifierAvailable(),
      inference: { mode: wb.settings.codex.mode, mocked: wb.settings.codex.mode === "fake", live_blocked: wb.codexConfig().blocked },
      assumptions: ops.TRUSTED_ASSUMPTIONS,
    };
  });

  // Static operator UI (protected build output; never candidate HTML).
  app.get("/*", async (req, reply) => {
    if (req.url.startsWith("/api/")) {
      reply.code(404);
      return { code: "NOT_FOUND", message: "unknown API route" };
    }
    let rel: string;
    try {
      rel = decodeURIComponent(req.url.split("?")[0]).replace(/^\/+/, "");
    } catch {
      throw new OpError("BAD_PATH", "bad path", 404);
    }
    if (rel === "" || !/\.[a-z0-9]+$/.test(rel)) rel = "index.html";
    if (rel.includes("..") || rel.includes("\0")) throw new OpError("BAD_PATH", "bad path", 404);
    const file = path.join(WEB_DIST, rel);
    if (!file.startsWith(WEB_DIST + path.sep) || !fs.existsSync(file) || !fs.lstatSync(file).isFile()) {
      reply.code(404).type("text/plain");
      return fs.existsSync(WEB_DIST) ? "not found" : "UI not built: run `npm run build:web`";
    }
    const types: Record<string, string> = { ".html": "text/html; charset=utf-8", ".js": "text/javascript", ".css": "text/css", ".svg": "image/svg+xml", ".json": "application/json" };
    reply.type(types[path.extname(file)] ?? "application/octet-stream");
    return fs.readFileSync(file);
  });

  return app;
}

/** Journal SSE for one job: sequence ids, reconnect via Last-Event-ID. */
async function sse(wb: Workbench, req: FastifyRequest, reply: FastifyReply, job: string) {
  let last = Number(req.headers["last-event-id"] ?? (req.query as any).after ?? 0) || 0;
  reply.raw.writeHead(200, { "Content-Type": "text/event-stream", "Cache-Control": "no-store", Connection: "keep-alive" });
  const needle = `"job":${JSON.stringify(job)}`;
  // Whole-token match on command ids so job "j1" does not also stream "j10".
  const idRe = new RegExp(`(^|[^A-Za-z0-9_-])${job.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}([^A-Za-z0-9_-]|$)`);
  const push = () => {
    const rows = wb.db.db.prepare("SELECT seq, command_id, accepted, reject_code, events, wall_time FROM journal WHERE seq > ? ORDER BY seq LIMIT 200").all(last) as any[];
    for (const r of rows) {
      last = r.seq;
      if (!String(r.events).includes(needle) && !idRe.test(String(r.command_id))) continue;
      reply.raw.write(`id: ${r.seq}\nevent: journal\ndata: ${canonicalize({ seq: r.seq, command_id: r.command_id, accepted: r.accepted === 1,
        reject_code: r.reject_code, events: JSON.parse(r.events), wall_time: r.wall_time } as unknown as Json)}\n\n`);
    }
  };
  push();
  const t = setInterval(push, 500);
  req.raw.on("close", () => clearInterval(t));
  return reply;
}

export { exactFields };
