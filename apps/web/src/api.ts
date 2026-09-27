// Thin client for the operator API (apps/control/server.ts). The UI never
// decides authorization: every write is sent to the server, which turns it
// into a kernel command. The operator token is only ever sent once, in the
// body of POST /api/session; afterwards the HttpOnly cookie authenticates.

export class ApiError extends Error {
  readonly code: string;
  readonly status: number;
  readonly currentRevision: unknown;
  constructor(status: number, code: string, message: string, currentRevision?: unknown) {
    super(message);
    this.status = status;
    this.code = code;
    this.currentRevision = currentRevision;
  }
}

type Listener = () => void;
const unauthListeners = new Set<Listener>();
export function onUnauthenticated(fn: Listener): () => void {
  unauthListeners.add(fn);
  return () => unauthListeners.delete(fn);
}

async function handle<T>(res: Response): Promise<T> {
  let data: unknown = null;
  const text = await res.text();
  if (text) {
    try {
      data = JSON.parse(text);
    } catch {
      data = { code: "BAD_RESPONSE", message: text.slice(0, 500) };
    }
  }
  if (!res.ok) {
    const d = (data ?? {}) as Record<string, unknown>;
    const code = typeof d.code === "string" ? d.code : `HTTP_${res.status}`;
    const message = typeof d.message === "string" ? d.message : res.statusText;
    if (res.status === 401 && code === "UNAUTHENTICATED") unauthListeners.forEach((f) => f());
    throw new ApiError(res.status, code, message, d.current_revision);
  }
  return data as T;
}

export async function get<T = any>(path: string): Promise<T> {
  const res = await fetch(path, { method: "GET", credentials: "same-origin", headers: { Accept: "application/json" } });
  return handle<T>(res);
}

export async function post<T = any>(path: string, body: Record<string, unknown>): Promise<T> {
  // Content-Type must be exactly application/json (the server registers only
  // that parser); X-Factory-Request is the CSRF guard for state changes.
  const res = await fetch(path, {
    method: "POST",
    credentials: "same-origin",
    headers: { "Content-Type": "application/json", "X-Factory-Request": "1", Accept: "application/json" },
    body: JSON.stringify(body),
  });
  return handle<T>(res);
}

export function login(token: string): Promise<{ ok: boolean }> {
  return post("/api/session", { token });
}

/** Redeem a one-time sign-in link nonce for the same HttpOnly session cookie. */
export function claimLink(nonce: string): Promise<{ ok: boolean }> {
  return post("/api/session/claim", { nonce });
}

/** Fresh, unique command id for an operator write (server prefixes "op:"). */
export function commandId(): string {
  const rnd = new Uint32Array(2);
  crypto.getRandomValues(rnd);
  return `ui-${Date.now()}-${rnd[0].toString(36)}${rnd[1].toString(36)}`;
}

// ---------------------------------------------------------------- untrusted text

// ANSI CSI / OSC / other escape sequences and C0/C1 controls (except \n, \t).
const ANSI = /\u001b\[[0-9;?]*[ -/]*[@-~]|\u001b\][^\u0007\u001b]*(?:\u0007|\u001b\\)|\u001b[@-Z\\-_]|\u009b[0-9;?]*[ -/]*[@-~]/g;
const CTRL = /[\u0000-\u0008\u000b-\u001f\u007f-\u009f]/g;

/** Make untrusted text safe for display as plain text (React escapes HTML). */
export function clean(v: unknown, max = 200_000): string {
  if (v === null || v === undefined) return "";
  const s = typeof v === "string" ? v : JSON.stringify(v, null, 2) ?? String(v);
  const out = s.replace(ANSI, "").replace(/\r\n?/g, "\n").replace(CTRL, "");
  return out.length > max ? `${out.slice(0, max)}\n… (truncated, ${out.length - max} more characters)` : out;
}

/** Pretty JSON of an untrusted value, cleaned. */
export function pretty(v: unknown): string {
  try {
    return clean(JSON.stringify(v, null, 2));
  } catch {
    return clean(String(v));
  }
}

export const isDigest = (s: unknown): s is string => typeof s === "string" && /^[0-9a-f]{64}$/.test(s);
export const short = (d: unknown): string => (typeof d === "string" && d.length > 16 ? `${d.slice(0, 12)}…` : typeof d === "string" ? d : "—");

export function errText(e: unknown): { code: string; message: string } {
  if (e instanceof ApiError) return { code: e.code, message: e.message };
  if (e instanceof Error) return { code: "CLIENT_ERROR", message: e.message };
  return { code: "CLIENT_ERROR", message: String(e) };
}

/** Parse SQLite-ish booleans (0/1, "0"/"1", true/false). */
export const truthy = (v: unknown): boolean => v === true || v === 1 || v === "1" || v === "true";

export const TERMINAL_JOB = new Set(["blocked", "succeeded", "failed", "cancelled"]);
export const LIVE_ATTEMPT = new Set(["authorized", "starting", "running"]);
