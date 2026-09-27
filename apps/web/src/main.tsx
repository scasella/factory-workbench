import { StrictMode, useEffect, useRef, useState, type FormEvent } from "react";
import { createRoot } from "react-dom/client";
import { ApiError, claimLink, clean, errText, get, login, onUnauthenticated } from "./api.ts";
import { ErrorBox, Mark, StatusCtx, usePoll, type Err } from "./ui.tsx";
import { Home } from "./pages/Home.tsx";
import { JobDetail } from "./pages/Job.tsx";
import { ChangeDetail } from "./pages/Improve.tsx";
import { ReleaseReview, Releases } from "./pages/Releases.tsx";
import { Assurance } from "./pages/Assurance.tsx";
import { ArtifactView, Journal } from "./pages/Misc.tsx";
import "./styles.css";

// A one-time sign-in link carries its nonce in the URL fragment. Remove it
// from the address bar and history before anything renders, then redeem it.
let claim: Promise<unknown> | null = null;
/** If the URL carries a sign-in nonce, strip it from the address bar/history and redeem it. */
function takeLoginFragment(): Promise<unknown> | null {
  const m = /^#login=([A-Za-z0-9_-]{16,100})$/.exec(window.location.hash);
  if (!m) return null;
  let back = "#/";
  try {
    back = sessionStorage.getItem("fw.lastRoute") || "#/";
  } catch {
    /* default route */
  }
  history.replaceState(null, "", `${window.location.pathname}${back}`);
  const p = claimLink(m[1]);
  p.catch(() => undefined);
  return p;
}
claim = takeLoginFragment();

// Remember (per tab) that this browser had a session, so a later 401 can be
// explained as "the workbench restarted" rather than a bare sign-in page.
const HAD = "fw.hadSession";
const mark = () => {
  try {
    sessionStorage.setItem(HAD, "1");
  } catch {
    /* storage unavailable: no hint */
  }
};
const hadSession = () => {
  try {
    return sessionStorage.getItem(HAD) === "1";
  } catch {
    return false;
  }
};

function useHash(): string {
  const [hash, setHash] = useState(() => window.location.hash || "#/");
  useEffect(() => {
    const f = () => setHash(window.location.hash || "#/");
    window.addEventListener("hashchange", f);
    return () => window.removeEventListener("hashchange", f);
  }, []);
  return hash;
}

function route(hash: string) {
  const parts = hash.replace(/^#\/?/, "").split("?")[0].split("/").filter(Boolean).map((p) => {
    try {
      return decodeURIComponent(p);
    } catch {
      return p;
    }
  });
  const [a, b] = parts;
  switch (a) {
    case undefined: return { key: "home", nav: "home", el: <Home /> };
    case "improve": return { key: "home", nav: "home", el: <Home /> };
    case "jobs": return b ? { key: `job:${b}`, nav: "home", el: <JobDetail id={b} /> } : { key: "home", nav: "home", el: <Home /> };
    case "changes": return b ? { key: `chg:${b}`, nav: "home", el: <ChangeDetail id={b} /> } : { key: "home", nav: "home", el: <Home /> };
    case "releases": return b ? { key: `rel:${b}`, nav: "releases", el: <ReleaseReview digest={b} /> } : { key: "releases", nav: "releases", el: <Releases /> };
    case "assurance": return { key: "assurance", nav: "assurance", el: <Assurance /> };
    case "artifacts": return { key: `art:${b}`, nav: "", el: <ArtifactView digest={b ?? ""} /> };
    case "journal": return { key: "journal", nav: "journal", el: <Journal /> };
    default: return { key: "404", nav: "", el: <p>That page doesn’t exist. <a href="#/">Go home</a></p> };
  }
}

// ---------------------------------------------------------------- sign in

function SignIn({ onDone, linkError, restarted }: { onDone: () => void; linkError: Err; restarted: boolean }) {
  const [token, setToken] = useState("");
  const [hint, setHint] = useState<{ login: string; token_file: string } | null>(null);
  useEffect(() => {
    get<{ login: string; token_file: string }>("/api/signin-hint").then(setHint, () => undefined);
  }, []);
  const loginCmd = hint?.login ?? "node apps/control/cli.ts login";
  const [busy, setBusy] = useState(false);
  const [error, setError] = useState<Err>(null);
  useEffect(() => {
    document.title = "Sign in · Factory Workbench";
  }, []);
  const submit = async (e: FormEvent) => {
    e.preventDefault();
    setBusy(true);
    setError(null);
    try {
      await login(token.trim());
      setToken(""); // never stored; the HttpOnly cookie authenticates from here on
      onDone();
    } catch (err) {
      setError(err instanceof ApiError && err.status === 401 ? { code: err.code, message: "that token didn’t match" } : errText(err));
    } finally {
      setBusy(false);
    }
  };
  const used = linkError?.code === "LINK_USED_OR_EXPIRED";
  return (
    <main id="main" className="signin">
      <div className="signin-card">
        <div className="mark"><Mark size={22} /> Factory Workbench</div>
        {used ? (
          <>
            <h1>This sign-in link no longer works</h1>
            <p>Links work once, last five minutes, and a newer link replaces older ones. Get a fresh one by running this in the repository folder:</p>
            <p><code className="wrap">{loginCmd}</code></p>
            <p className="small">You can paste the new link into this tab.</p>
          </>
        ) : restarted ? (
          <>
            <h1>Sign in again</h1>
            <p>The workbench server restarted, which ends every session. Get a new sign-in link by running this in the repository folder:</p>
            <p><code className="wrap">{loginCmd}</code></p>
          </>
        ) : (
          <>
            <h1>Sign in</h1>
            <p>Open the sign-in link the server printed in your terminal, or get a new one by running this in the repository folder:</p>
            <p><code className="wrap">{loginCmd}</code></p>
          </>
        )}
        {linkError && !used ? <ErrorBox error={linkError} /> : null}
        <details open={!!error}>
          <summary>Sign in with the operator token instead</summary>
          <form onSubmit={(e) => void submit(e)}>
            <label htmlFor="token">Operator token</label>
            <input id="token" type="password" autoComplete="off" spellCheck={false} value={token} aria-describedby="token-hint"
              onChange={(e) => setToken(e.target.value)} required />
            <p className="small muted" id="token-hint" style={{ margin: 0 }}>
              It’s the file <code className="wrap">{hint?.token_file ?? "<state directory>/operator/token"}</code>. Sent once; not stored by this page.
            </p>
            <button type="submit" className="btn primary" disabled={busy || !token.trim()}>{busy ? "Signing in…" : "Sign in"}</button>
            <ErrorBox error={error} />
          </form>
        </details>
      </div>
    </main>
  );
}

// ---------------------------------------------------------------- shell

const NAV: [string, string, string][] = [["home", "#/", "Home"], ["releases", "#/releases", "Releases"], ["assurance", "#/assurance", "Assurance"], ["journal", "#/journal", "Journal"]];

const SHORTCUTS_KEY = "fw.shortcuts";
function shortcutsOn(): boolean {
  try {
    return localStorage.getItem(SHORTCUTS_KEY) !== "off";
  } catch {
    return true;
  }
}

function Shortcuts({ open, onClose }: { open: boolean; onClose: () => void }) {
  const [on, setOn] = useState(shortcutsOn);
  const ref = useRef<HTMLDialogElement>(null);
  useEffect(() => {
    const d = ref.current;
    if (!d) return;
    if (open && !d.open) d.showModal();
    if (!open && d.open) d.close();
  }, [open]);
  return (
    <dialog ref={ref} onClose={onClose} aria-labelledby="kb-h">
      <h2 id="kb-h" style={{ margin: 0 }}>Keyboard shortcuts</h2>
      <dl>
        <dt><kbd>/</kbd></dt><dd>Write an improvement request</dd>
        <dt><kbd>g</kbd> <kbd>h</kbd></dt><dd>Home</dd>
        <dt><kbd>g</kbd> <kbd>r</kbd></dt><dd>Releases</dd>
        <dt><kbd>g</kbd> <kbd>a</kbd></dt><dd>Assurance</dd>
        <dt><kbd>g</kbd> <kbd>j</kbd></dt><dd>Journal</dd>
        <dt><kbd>?</kbd></dt><dd>This list</dd>
        <dt><kbd>⌘</kbd> <kbd>↵</kbd></dt><dd>Start the improvement you’re writing</dd>
      </dl>
      <label className="ack" style={{ display: "flex", gap: 8, fontWeight: 400, marginBottom: 16 }}>
        <input type="checkbox" checked={on} style={{ minHeight: 0 }} onChange={(e) => {
          setOn(e.target.checked);
          try {
            localStorage.setItem(SHORTCUTS_KEY, e.target.checked ? "on" : "off");
          } catch {
            /* per-viewer convenience only */
          }
        }} /> Single-key shortcuts on
      </label>
      <button type="button" className="btn" onClick={onClose}>Close</button>
    </dialog>
  );
}

function useShortcuts(setHelp: (f: (v: boolean) => boolean) => void) {
  useEffect(() => {
    let g = 0;
    const onKey = (e: KeyboardEvent) => {
      const t = e.target as HTMLElement;
      if (e.metaKey || e.ctrlKey || e.altKey || t.closest("input, textarea, select, [contenteditable], dialog")) return;
      if (e.key === "?") {
        // "?" stays available so shortcuts can always be turned back on.
        e.preventDefault();
        setHelp((v) => !v);
        return;
      }
      if (!shortcutsOn()) return;
      if (e.key === "/") {
        e.preventDefault();
        const focus = () => document.getElementById("request")?.focus();
        if (document.getElementById("request")) focus();
        else {
          window.location.hash = "#/";
          setTimeout(focus, 60);
        }
        return;
      }
      if (e.key === "g") {
        g = Date.now();
        return;
      }
      if (Date.now() - g < 900) {
        const to = ({ h: "#/", r: "#/releases", a: "#/assurance", j: "#/journal" } as Record<string, string>)[e.key];
        if (to) window.location.hash = to;
        g = 0;
      }
    };
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [setHelp]);
}

function SystemLine({ st, onHelp }: { st: any; onHelp: () => void }) {
  if (!st) return null;
  const trust = Array.isArray(st.trust) ? st.trust : [];
  const cap = st.capacity ?? {};
  const iso = st.isolation ?? {};
  return (
    <footer className="foot" aria-label="System">
      {st.verifier?.ok ? "Checker available" : "Checker unavailable"} · {trust.filter((t: any) => t.ok).length} of {trust.length} protected components unchanged
      {" · "}model slots {clean(cap.llm?.live ?? "?")}/{clean(cap.llm?.limit ?? "?")} · container slots {clean(cap.container?.live ?? "?")}/{clean(cap.container?.limit ?? "?")}
      {" · "}sandbox: network {clean(iso.network)}, {clean(iso.root_fs)} root · <a href="#/assurance">Assurance</a>
      {" · "}<button type="button" className="copy" style={{ fontSize: 13, padding: 0, textDecoration: "underline", textUnderlineOffset: 3 }} onClick={onHelp}>Keyboard shortcuts</button>
    </footer>
  );
}

function Shell() {
  const hash = useHash();
  const [help, setHelp] = useState(false);
  const sys = usePoll<any>("/api/status", 3000);
  useShortcuts(setHelp);
  const r = route(hash);
  const st = sys.data;
  useEffect(() => {
    // Remember where this tab was, so signing in again returns here.
    try {
      sessionStorage.setItem("fw.lastRoute", hash.startsWith("#login=") ? "#/" : hash);
    } catch {
      /* per-tab convenience only */
    }
  }, [hash]);
  return (
    <StatusCtx.Provider value={st}>
      <a className="skip" href="#main" onClick={(e) => { e.preventDefault(); document.querySelector<HTMLElement>("main h1")?.focus(); }}>Skip to content</a>
      {st?.inference?.mocked ? (
        <div className="mock" role="note">
          <strong>Mocked inference.</strong> Authored code and reviews are scripted, not from a real model.
        </div>
      ) : st?.inference?.live_blocked ? (
        <div className="mock" role="note"><strong>Live inference blocked:</strong> {clean(st.inference.live_blocked)}</div>
      ) : null}
      {st?.mutation_disabled ? <div className="note bad" role="alert" style={{ margin: 0, borderRadius: 0, textAlign: "center" }}>Changes are disabled: {clean(st.mutation_disabled)}</div> : null}
      <header className="top">
        <a className="mark" href="#/"><Mark /> Factory Workbench</a>
        <nav aria-label="Primary">
          <ul>
            {NAV.map(([k, href, label]) => <li key={k}><a href={href} aria-current={r.nav === k ? "page" : undefined}>{label}</a></li>)}
          </ul>
        </nav>
      </header>
      <main id="main">
        <div key={r.key}>{r.el}</div>
      </main>
      <SystemLine st={st} onHelp={() => setHelp(true)} />
      <Shortcuts open={help} onClose={() => setHelp(false)} />
    </StatusCtx.Provider>
  );
}

function App() {
  const [auth, setAuth] = useState<"unknown" | "yes" | "no">("unknown");
  const [linkError, setLinkError] = useState<Err>(null);
  const [restarted, setRestarted] = useState(false);
  const signedIn = () => {
    mark();
    setLinkError(null);
    setRestarted(false);
    setAuth("yes");
  };
  const signedOut = () => {
    // Keep the flag: a reload of this tab should still explain the restart.
    if (hadSession()) setRestarted(true);
    setAuth("no");
  };
  useEffect(() => onUnauthenticated(signedOut), []);
  // A sign-in link pasted into an already-open tab only changes the fragment,
  // which does not reload the page: redeem it here.
  useEffect(() => {
    const f = () => {
      const p = takeLoginFragment();
      if (p) p.then(signedIn, (e) => setLinkError(errText(e)));
    };
    window.addEventListener("hashchange", f);
    return () => window.removeEventListener("hashchange", f);
  }, []);
  useEffect(() => {
    const check = () => get("/api/status").then(signedIn, (e) => (e instanceof ApiError && e.status === 401 ? signedOut() : signedIn()));
    if (claim) claim.then(signedIn, (e) => {
      setLinkError(errText(e));
      void check();
    });
    else void check();
  }, []);
  if (auth === "unknown") return <p role="status" className="signin muted">Signing you in…</p>;
  if (auth === "no") return <SignIn onDone={signedIn} linkError={linkError} restarted={restarted} />;
  return <Shell />;
}

createRoot(document.getElementById("root")!).render(
  <StrictMode>
    <App />
  </StrictMode>,
);
