// Shared primitives. All server values render as React text nodes (escaped);
// nothing uses dangerouslySetInnerHTML.

import { createContext, useCallback, useContext, useEffect, useId, useLayoutEffect, useRef, useState, type ReactNode } from "react";
import { clean, errText, get, isDigest } from "./api.ts";

export type Err = { code: string; message: string } | null;

// ---------------------------------------------------------------- data

export function usePoll<T>(path: string | null, intervalMs = 2500) {
  const [data, setData] = useState<T | null>(null);
  const [error, setError] = useState<Err>(null);
  const [loading, setLoading] = useState(true);
  const alive = useRef(true);
  const reload = useCallback(async () => {
    if (!path) return;
    try {
      const d = await get<T>(path);
      if (!alive.current) return;
      setData(d);
      setError(null);
    } catch (e) {
      if (alive.current) setError(errText(e));
    } finally {
      if (alive.current) setLoading(false);
    }
  }, [path]);
  useEffect(() => {
    alive.current = true;
    setLoading(true);
    setData(null);
    void reload();
    if (!intervalMs) return () => { alive.current = false; };
    const t = setInterval(() => void reload(), intervalMs);
    return () => {
      alive.current = false;
      clearInterval(t);
    };
  }, [reload, intervalMs]);
  return { data, error, loading, reload };
}

/** System status (/api/status), polled once by the shell and shared. */
export const StatusCtx = createContext<any>(null);
export const useSystem = () => useContext(StatusCtx);

export function arr<T = any>(v: unknown): T[] {
  return Array.isArray(v) ? (v as T[]) : [];
}

// ---------------------------------------------------------------- time

export function fmtTime(v: unknown): string {
  if (typeof v !== "string" || !v) return "—";
  const d = new Date(v);
  return Number.isNaN(d.getTime()) ? clean(v) : d.toLocaleString();
}

export function ago(v: unknown): string {
  if (typeof v !== "string" || !v) return "—";
  const t = new Date(v).getTime();
  if (Number.isNaN(t)) return clean(v);
  const s = Math.max(0, Math.round((Date.now() - t) / 1000));
  if (s < 45) return "just now";
  if (s < 90) return "1 min ago";
  if (s < 3600) return `${Math.round(s / 60)} min ago`;
  if (s < 5400) return "1 hour ago";
  if (s < 86400) return `${Math.round(s / 3600)} hours ago`;
  return new Date(t).toLocaleDateString();
}

export function When({ t }: { t: unknown }) {
  if (typeof t !== "string" || !t) return <span className="muted">—</span>;
  return <time dateTime={t} title={fmtTime(t)}>{ago(t)}</time>;
}

// ---------------------------------------------------------------- page

let lastFocused: string | null = null;

/** Page heading: sets document.title and takes focus on navigation. */
export function Page({ title, eyebrow, back, children, actions }: {
  title: string; eyebrow?: ReactNode; back?: [string, string]; children?: ReactNode; actions?: ReactNode;
}) {
  const sys = useSystem();
  const h1 = useRef<HTMLHeadingElement>(null);
  useEffect(() => {
    document.title = `${title}${sys?.inference?.mocked ? " (mocked)" : ""} · Factory Workbench`;
  }, [title, sys?.inference?.mocked]);
  useLayoutEffect(() => {
    // Take focus once per navigation (a loading and a loaded heading must not both grab it).
    if (lastFocused === window.location.hash) return;
    lastFocused = window.location.hash;
    h1.current?.focus({ preventScroll: true });
  }, []);
  return (
    <header className="page-head">
      {back ? <a className="back" href={back[0]}>← {back[1]}</a> : null}
      {eyebrow ? <div className="eyebrow">{eyebrow}</div> : null}
      <div className="section-head">
        <h1 tabIndex={-1} ref={h1}>{title}</h1>
        {actions ? <div className="row">{actions}</div> : null}
      </div>
      {children}
    </header>
  );
}

export function Section({ title, children, action, id }: { title: string; children: ReactNode; action?: ReactNode; id?: string }) {
  const hid = id ?? `s-${title.toLowerCase().replace(/[^a-z0-9]+/g, "-")}`;
  return (
    <section className="section" aria-labelledby={hid}>
      <div className="section-head">
        <h2 id={hid}>{title}</h2>
        {action}
      </div>
      {children}
    </section>
  );
}

/** Progressive disclosure. `attention` opens it by default and marks the title. */
export function Fold({ title, meta, attention = false, open, children }: {
  title: string; meta?: ReactNode; attention?: boolean; open?: boolean; children: ReactNode;
}) {
  return (
    <details className={`fold${attention ? " attention" : ""}`} open={open ?? attention}>
      <summary>
        <span className="fold-title">{attention ? <span className="attn" aria-hidden="true">⚠ </span> : null}{title}</span>
        {attention ? <span className="fold-meta attn-word">needs a look ·</span> : null}
        {meta ? <span className="fold-meta">{meta}</span> : null}
      </summary>
      <div className="fold-body">{children}</div>
    </details>
  );
}

export function Facts({ rows }: { rows: [ReactNode, ReactNode][] }) {
  return (
    <dl className="facts">
      {rows.map(([k, v], i) => (
        <div key={i}>
          <dt>{k}</dt>
          <dd>{v}</dd>
        </div>
      ))}
    </dl>
  );
}

export function ErrorBox({ error }: { error: Err }) {
  if (!error) return null;
  return (
    <div className="error" role="alert">
      {/^UNKNOWN_|NOT_FOUND|BAD_DIGEST/.test(error.code) ? "Not found: " : "Couldn’t do that: "}{clean(error.message)} <code>({clean(error.code)})</code>
    </div>
  );
}

export function Loading({ what }: { what: string }) {
  return <p className="muted" role="status">Loading {what}…</p>;
}

/** Candidate or model text: escaped, boxed, labelled untrusted. */
export function Untrusted({ children, caption = "untrusted text" }: { children: unknown; caption?: ReactNode }) {
  return (
    <div className="untrusted">
      <div className="cap">{caption}</div>
      <pre>{clean(children)}</pre>
    </div>
  );
}

export function MockTag() {
  return <span className="tag" title="Produced by the scripted fake, not a real model">mocked</span>;
}

// ---------------------------------------------------------------- status

type Tone = "ok" | "bad" | "warn" | "info" | "muted";
const S: Record<string, [string, Tone, string?]> = {
  succeeded: ["✓", "ok"], pass: ["✓", "ok", "passed"], ok: ["✓", "ok"], done: ["✓", "ok"], published: ["✓", "ok"], accepted: ["✓", "ok"],
  running: ["●", "info"], starting: ["●", "info"], authorized: ["●", "info", "allowed to run"], active: ["▶", "info"], open: ["●", "info", "in progress"],
  queued: ["○", "muted"], pending: ["○", "muted"], ready: ["○", "muted"], none: ["–", "muted"],
  paused: ["‖", "warn"], pause_requested: ["‖", "warn", "pausing"], inconclusive: ["?", "warn"], unknown: ["?", "muted"], revised: ["↻", "muted"],
  not_run: ["–", "muted", "not run"], closed: ["–", "muted"],
  failed: ["✕", "bad"], fail: ["✕", "bad", "failed"], blocked: ["✕", "bad"], expired: ["✕", "bad"], lost: ["✕", "bad"], exhausted: ["✕", "bad", "out of budget"],
  cancelled: ["⊘", "muted"], rejected: ["✕", "bad"], revoked: ["⊘", "muted"],
};

export function statusTone(s: unknown): Tone {
  return S[String(s ?? "unknown")]?.[1] ?? "muted";
}

/** Glyph + word; the glyph is decorative, the word carries the meaning. */
export function Status({ s, label, glyph, tone }: { s?: unknown; label?: string; glyph?: string; tone?: Tone }) {
  const v = s === null || s === undefined ? "unknown" : clean(String(s));
  const d = S[v] ?? ["·", "muted" as Tone];
  return (
    <span className={`st t-${tone ?? d[1]}`}>
      <span className="g" aria-hidden="true">{glyph ?? d[0]}</span>
      <span>{label ?? d[2] ?? v.replaceAll("_", " ")}</span>
    </span>
  );
}

// ---------------------------------------------------------------- digests

function CopyButton({ value, what }: { value: string; what: string }) {
  const [done, setDone] = useState(false);
  return (
    <>
    <button type="button" className="copy" aria-label={`Copy full ${what} ID`}
      onClick={(e) => {
        e.preventDefault();
        e.stopPropagation();
        void navigator.clipboard?.writeText(value).then(() => {
          setDone(true);
          setTimeout(() => setDone(false), 1400);
        });
      }}>
      {done ? "copied" : "copy"}
    </button>
    <span className="sr" role="status">{done ? "Copied" : ""}</span>
    </>
  );
}

export const shortD = (s: string) => (s.length > 16 ? `${s.slice(0, 8)}…${s.slice(-4)}` : s);

/** Short digest with the full value in the DOM (screen readers, copy, search). */
export function Digest({ d, link = false, copy = true, what = "digest" }: { d: unknown; link?: boolean | "release"; copy?: boolean; what?: string }) {
  if (d === null || d === undefined || d === "") return <span className="muted">none</span>;
  const s = clean(d);
  const body = <><span aria-hidden="true">{shortD(s)}</span><span className="sr">{s}</span></>;
  const href = link && isDigest(s) ? (link === "release" ? `#/releases/${s}` : `#/artifacts/${s}`) : null;
  return (
    <span className="dg" title={s}>
      {href ? <a href={href}>{body}</a> : <span>{body}</span>}
      {copy && isDigest(s) ? <CopyButton value={s} what={what} /> : null}
    </span>
  );
}

/** Full digest grouped in fours; the first eight characters are bold. */
export function FullDigest({ d, what = "digest" }: { d: unknown; what?: string }) {
  const s = clean(d);
  if (!s) return <span className="muted">none</span>;
  const groups = s.match(/.{1,4}/g) ?? [s];
  return (
    <span className="row" style={{ gap: 6, alignItems: "baseline" }}>
      <span className="dg-full">
        <span aria-hidden="true">{groups.map((g, i) => (i < 2 ? <b key={i}>{g} </b> : <span key={i}>{g} </span>))}</span>
        <span className="sr">{s}</span>
      </span>
      {isDigest(s) ? <CopyButton value={s} what={what} /> : null}
    </span>
  );
}

// ---------------------------------------------------------------- confirmation

/**
 * Two-step confirmation. The trigger opens an inline panel that states exactly
 * what will be sent; the action button is never auto-focused. Optional
 * safeguards: typing the first 8 characters of a digest, and an explicit
 * acknowledgement checkbox. If `guard` changes while open, the panel resets.
 */
export function Confirm({ label, heading, details, action, onConfirm, danger = false, disabled = false, why, match, ack, guard, primary = false, cancelLabel = "Cancel" }: {
  label: string; heading: string; details: ReactNode; action: string; onConfirm: () => Promise<string | void>;
  danger?: boolean; disabled?: boolean; why?: string; match?: string; ack?: string; guard?: string; primary?: boolean; cancelLabel?: string;
}) {
  const [open, setOpen] = useState(false);
  const [busy, setBusy] = useState(false);
  const [error, setError] = useState<Err>(null);
  const [done, setDone] = useState<string | null>(null);
  const [typed, setTyped] = useState("");
  const [acked, setAcked] = useState(false);
  const [reset, setReset] = useState<string | null>(null);
  const panel = useRef<HTMLDivElement>(null);
  const trigger = useRef<HTMLButtonElement>(null);
  const openGuard = useRef<string | undefined>(undefined);
  const result = useRef<HTMLParagraphElement>(null);
  const uid = useId();
  const close = (refocus = true) => {
    setOpen(false);
    setTyped("");
    setAcked(false);
    if (refocus) setTimeout(() => trigger.current?.focus(), 0);
  };
  useEffect(() => {
    if (open) {
      openGuard.current = guard;
      panel.current?.focus();
    }
  }, [open]);
  useEffect(() => {
    if (open && guard !== openGuard.current) {
      setReset("Something changed while this was open (the active release or approvals). Review again.");
      close();
    }
  }, [guard]);
  const want = match ? match.slice(0, 8) : "";
  const ready = (!match || typed.trim().toLowerCase() === want) && (!ack || acked);
  const go = async () => {
    setBusy(true);
    setError(null);
    try {
      const msg = await onConfirm();
      setDone(msg || `${label}: recorded`);
      close(false);
      // Keep keyboard and screen-reader users on the outcome, not on <body>.
      // After the reload() re-render settles (folds may open and shift layout).
      const show = () => {
        result.current?.focus({ preventScroll: true });
        result.current?.scrollIntoView({ block: "center" });
      };
      setTimeout(show, 0);
      setTimeout(show, 400);
    } catch (e) {
      setError(errText(e));
    } finally {
      setBusy(false);
    }
  };
  return (
    <div>
      <button type="button" ref={trigger} className={`btn${primary ? " primary" : ""}${danger ? " danger" : ""}`} disabled={disabled || busy}
        aria-expanded={open} onClick={() => { setOpen(!open); setDone(null); setError(null); setReset(null); }}>
        {label}…
      </button>
      {disabled && why ? <p className="why" style={{ marginTop: 8 }}>{why}</p> : null}
      {open && (
        <div className="confirm-panel" role="group" aria-labelledby={`${uid}h`} tabIndex={-1} ref={panel}
          onKeyDown={(e) => { if (e.key === "Escape") close(); }}>
          <h3 id={`${uid}h`}>{heading}</h3>
          <div>{details}</div>
          {match ? (
            <div className="row" style={{ marginTop: 10 }}>
              <label htmlFor={`${uid}m`}>Type the first 8 characters of the release ID to confirm</label>
              <input id={`${uid}m`} className="match" autoComplete="off" spellCheck={false} maxLength={8} value={typed}
                onChange={(e) => setTyped(e.target.value)} onKeyDown={(e) => { if (e.key === "Enter") e.preventDefault(); }}
                aria-invalid={typed.length === 8 && typed.trim().toLowerCase() !== want} />
            </div>
          ) : null}
          {ack ? (
            <label className="ack"><input type="checkbox" checked={acked} onChange={(e) => setAcked(e.target.checked)} /> <span>{ack}</span></label>
          ) : null}
          <div className="confirm-actions">
            <button type="button" className={`btn ${danger ? "danger solid" : "primary"}`} disabled={busy || !ready} aria-describedby={`${uid}r`} onClick={() => void go()}>
              {busy ? "Sending…" : action}
            </button>
            <button type="button" className="btn" onClick={() => close()}>{cancelLabel}</button>
          </div>
          <p id={`${uid}r`} className="why" style={{ margin: "8px 0 0" }}>
            {ready ? "" : [match && typed.trim().toLowerCase() !== want ? "type the 8 characters" : "", ack && !acked ? "tick the box" : ""].filter(Boolean).join(" and ").replace(/^./, (c) => `To continue, ${c}`) + (ready ? "" : ".")}
          </p>
        </div>
      )}
      <p role="status" ref={result} tabIndex={-1} className={done ? "result-ok" : "why"} style={done || reset ? undefined : { margin: 0 }}>{done ? `✓ ${done}` : reset ?? ""}</p>
      <ErrorBox error={error} />
    </div>
  );
}

// ---------------------------------------------------------------- brand

export function Mark({ size = 18 }: { size?: number }) {
  return (
    <svg width={size} height={size} viewBox="0 0 24 24" aria-hidden="true" fill="none" stroke="currentColor" strokeWidth="2" strokeLinejoin="round">
      <path d="M12 2.5 21 7.5v9L12 21.5 3 16.5v-9L12 2.5Z" />
      <path d="M12 12 21 7.5M12 12 3 7.5M12 12v9.5" />
    </svg>
  );
}

// ---------------------------------------------------------------- plain words

export const KIND: Record<string, string> = {
  package_audit: "Package audit",
  change_author: "Write the change",
  change_evaluate: "Check the change",
};
export const kindName = (k: unknown) => KIND[String(k)] ?? clean(k);
