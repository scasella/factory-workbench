import { useState, type FormEvent, type KeyboardEvent, type ReactNode } from "react";
import { clean, commandId, errText, isDigest, post, TERMINAL_JOB } from "../api.ts";
import { arr, Digest, ErrorBox, kindName, Loading, Page, Section, shortD, Status, useSystem, usePoll, When, type Err } from "../ui.tsx";

// ---------------------------------------------------------------- composer

function Composer() {
  const sys = useSystem();
  const [request, setRequest] = useState("");
  const [adjust, setAdjust] = useState(false);
  const [attempts, setAttempts] = useState("");
  const [revisions, setRevisions] = useState("");
  const [busy, setBusy] = useState(false);
  const [error, setError] = useState<Err>(null);
  const lim = sys?.limits ?? {};
  const posInt = (s: string) => s.trim() === "" || /^[1-9][0-9]{0,5}$/.test(s.trim());
  const valid = request.trim().length >= 8 && posInt(attempts) && posInt(revisions);
  const submit = async (e?: FormEvent) => {
    e?.preventDefault();
    if (!valid || busy) return;
    setBusy(true);
    setError(null);
    try {
      const body: Record<string, unknown> = { request, command_id: commandId() };
      if (attempts.trim()) body.attempts = Number(attempts);
      if (revisions.trim()) body.revisions = Number(revisions);
      const r = await post<any>("/api/changes", body);
      window.location.hash = `#/changes/${encodeURIComponent(clean(r?.change))}`;
    } catch (err) {
      setError(errText(err));
      setBusy(false);
    }
  };
  const onKey = (e: KeyboardEvent) => {
    if (e.key === "Enter" && (e.metaKey || e.ctrlKey)) void submit();
  };
  return (
    <form onSubmit={(e) => void submit(e)} style={{ marginTop: 20 }}>
      <div className="composer">
        <label htmlFor="request" className="sr">Improvement request</label>
        <textarea id="request" rows={3} maxLength={8000} value={request} onChange={(e) => setRequest(e.target.value)} onKeyDown={onKey}
          placeholder="e.g. Let the reproduce and refute reviews run at the same time. Both must still pass." aria-describedby="request-how" />
        {adjust ? (
          <div className="budget">
            <label>Tries <input inputMode="numeric" value={attempts} onChange={(e) => setAttempts(e.target.value)} placeholder={clean(lim.attemptsPerChange ?? "")} aria-invalid={!posInt(attempts)} aria-describedby="budget-hint" /></label>
            <label>Drafts <input inputMode="numeric" value={revisions} onChange={(e) => setRevisions(e.target.value)} placeholder={clean(lim.revisionsPerChange ?? "")} aria-invalid={!posInt(revisions)} aria-describedby="budget-hint" /></label>
            <span id="budget-hint" className={`field-hint${posInt(attempts) && posInt(revisions) ? "" : " bad"}`}>Whole numbers, 1 or more. Leave empty for the default.</span>
          </div>
        ) : null}
        <div className="composer-bar">
          <span className="meta">
            Builds on {sys?.active_release ? <Digest d={sys.active_release} link="release" copy={false} /> : "the active release"}
            {" · "}up to {clean(attempts || lim.attemptsPerChange || "?")} tries, {clean(revisions || lim.revisionsPerChange || "?")} drafts
            {" · "}<button type="button" className="btn quiet" style={{ minHeight: 24, padding: "0 4px", fontSize: 13 }} aria-expanded={adjust} onClick={() => setAdjust(!adjust)}>{adjust ? "Done" : "Adjust"}</button>
          </span>
          <button type="submit" className="btn primary" disabled={!valid || busy} aria-describedby="request-need">{busy ? "Starting…" : "Start"}</button>
        </div>
      </div>
      <p className="hint-line" id="request-how">
        <span id="request-need" className={request.length > 0 && request.trim().length < 8 ? "field-hint bad" : undefined}>{request.trim().length < 8 ? "Describe it in at least 8 characters. " : ""}</span>
        It’s written, built, proved and reviewed first. Nothing changes until you approve and activate the result.
      </p>
      <ErrorBox error={error} />
    </form>
  );
}

// ---------------------------------------------------------------- needs you

function NeedsYou({ jobs, changes, releases }: { jobs: any[]; changes: any[]; releases: any[] }) {
  const items: { key: string; text: ReactNode; href: string; cta: string; tone: string; glyph: string; label: string }[] = [];
  for (const r of releases) {
    if (r.active || r.activated) continue;
    items.push({
      key: `r${r.digest}`, href: `#/releases/${r.digest}`, cta: r.approved ? "Activate" : "Review", label: `release ${shortD(clean(r.digest))}`,
      glyph: r.approved ? "●" : "○", tone: "info",
      text: r.approved ? <>Release <b className="mono">{shortD(clean(r.digest))}</b> is approved and ready to activate</> : <>Release <b className="mono">{shortD(clean(r.digest))}</b> is ready for your review</>,
    });
  }
  for (const c of changes) {
    if (c.status === "exhausted") items.push({ key: `c${c.id}`, href: `#/changes/${c.id}`, cta: "Open", label: `improvement ${clean(c.id)}`, glyph: "✕", tone: "bad", text: <>An improvement stopped: it ran out of budget</> });
  }
  for (const j of jobs) {
    if (j.change) continue;
    if (j.status === "failed" || j.status === "blocked") items.push({ key: `j${j.id}`, href: `#/jobs/${j.id}`, cta: "Open", label: `job ${clean(j.id)}`, glyph: "✕", tone: "bad", text: <>{kindName(j.kind)} <span className="mono">{clean(j.id)}</span> {clean(j.status)}</> });
    else if (j.status === "paused") items.push({ key: `j${j.id}`, href: `#/jobs/${j.id}`, cta: "Open", label: `job ${clean(j.id)}`, glyph: "‖", tone: "warn", text: <>{kindName(j.kind)} <span className="mono">{clean(j.id)}</span> is paused</> });
    if (Number(j.cleanup_pending) > 0) items.push({ key: `cl${j.id}`, href: `#/jobs/${j.id}`, cta: "Open", label: `job ${clean(j.id)}`, glyph: "○", tone: "warn", text: <>Cleanup still running for <span className="mono">{clean(j.id)}</span></> });
  }
  if (!items.length) return null;
  return (
    <Section title="Needs you">
      <ul className="list">
        {items.map((i) => (
          <li key={i.key} className="row" style={{ justifyContent: "space-between" }}>
            <span className={`st t-${i.tone}`} style={{ whiteSpace: "normal", fontSize: 15, color: "var(--fg)" }}>
              <span className="g" aria-hidden="true">{i.glyph}</span><span>{i.text}</span>
            </span>
            <a className="btn" href={i.href} aria-label={`${i.cta} ${i.label}`}>{i.cta}</a>
          </li>
        ))}
      </ul>
    </Section>
  );
}

// ---------------------------------------------------------------- improvements

function Improvements({ changes }: { changes: any[] }) {
  if (!changes.length) return null;
  const sorted = [...changes].sort((a, b) => String(b.created ?? "").localeCompare(String(a.created ?? "")));
  const label = (c: any) => {
    if (c.status === "published") return arr(c.releases).length ? "release published" : "published";
    if (c.status === "open") return "in progress";
    return undefined;
  };
  return (
    <Section title="Improvements">
      <ul className="list">
        {sorted.map((c) => (
          <li key={clean(c.id)}>
            <a className="item-title clamp" href={`#/changes/${encodeURIComponent(c.id)}`}>{clean(c.request_text) || clean(c.id)}</a>
            <div className="meta-line" style={{ marginTop: 4 }}>
              <Status s={c.status} label={label(c)} />
              <span className="mono">{clean(c.id)}</span>
              <span>{`${clean(c.revisions)} of ${clean(c.revision_limit)} drafts`}</span>
              <When t={c.created} />
            </div>
          </li>
        ))}
      </ul>
    </Section>
  );
}

// ---------------------------------------------------------------- jobs

const FILTERS = [["all", "All"], ["active", "Running"], ["paused", "Paused"], ["terminal", "Finished"]] as const;

function RunAudit({ onClose }: { onClose: () => void }) {
  const fixtures = usePoll<any[]>("/api/fixtures", 0);
  const releases = usePoll<any[]>("/api/releases", 0);
  const [fixture, setFixture] = useState("");
  const [release, setRelease] = useState("");
  const [busy, setBusy] = useState(false);
  const [error, setError] = useState<Err>(null);
  const fx = fixture || clean(arr(fixtures.data)[0]?.name ?? "");
  const activated = arr(releases.data).filter((r: any) => r.activated);
  const submit = async (e: FormEvent) => {
    e.preventDefault();
    setBusy(true);
    setError(null);
    try {
      const body: Record<string, unknown> = { fixture: fx, command_id: commandId() };
      if (release) body.release = release;
      const r = await post<any>("/api/jobs", body);
      window.location.hash = `#/jobs/${encodeURIComponent(clean(r?.job))}`;
    } catch (err) {
      setError(errText(err));
      setBusy(false);
    }
  };
  return (
    <form onSubmit={(e) => void submit(e)} className="confirm-panel" style={{ marginBottom: 16 }}>
      <h3>Run a package audit</h3>
      <p className="small muted">Builds, proves and reviews a registered package with a release’s workflow. The job keeps that release even if you activate a newer one.</p>
      <div className="row" style={{ alignItems: "flex-end", gap: 16 }}>
        <label style={{ display: "grid", gap: 4 }}>Package
          <select value={fx} onChange={(e) => setFixture(e.target.value)} required>
            {arr(fixtures.data).map((f: any) => <option key={clean(f.digest)} value={clean(f.name)}>{clean(f.name)}</option>)}
          </select>
        </label>
        <label style={{ display: "grid", gap: 4 }}>Release
          <select value={release} onChange={(e) => setRelease(e.target.value)}>
            <option value="">Active release</option>
            {activated.filter((r: any) => !r.active).map((r: any) => <option key={clean(r.digest)} value={clean(r.digest)}>{shortD(clean(r.digest))} (earlier)</option>)}
          </select>
        </label>
        <div className="row">
          <button type="button" className="btn" onClick={onClose}>Cancel</button>
          <button type="submit" className="btn primary" disabled={busy || !fx || (release !== "" && !isDigest(release))}>{busy ? "Starting…" : "Start audit"}</button>
        </div>
      </div>
      <ErrorBox error={fixtures.error ?? error} />
    </form>
  );
}

function progress(steps: any[]): string {
  if (!steps.length) return "—";
  const done = steps.filter((s) => s.status === "succeeded").length;
  const failed = steps.filter((s) => s.status === "failed").length;
  return `${done} of ${steps.length} steps${failed ? ` · ${failed} failed` : ""}`;
}

function Jobs({ jobs, loading }: { jobs: any[]; loading: boolean }) {
  const [filter, setFilter] = useState<(typeof FILTERS)[number][0]>("all");
  const [withChanges, setWithChanges] = useState(false);
  const [audit, setAudit] = useState(false);
  const internal = jobs.filter((j) => j.change).length;
  const shown = jobs
    .filter((j) => withChanges || !j.change)
    .filter((j) => {
      if (filter === "all") return true;
      if (filter === "terminal") return TERMINAL_JOB.has(j.status);
      if (filter === "paused") return j.status === "paused" || j.status === "pause_requested";
      return !TERMINAL_JOB.has(j.status) && j.status !== "paused";
    })
    .sort((a, b) => String(b.created ?? "").localeCompare(String(a.created ?? "")));
  return (
    <Section title="Jobs" action={!audit ? <button type="button" className="btn" onClick={() => setAudit(true)}>Run an audit</button> : undefined}>
      {audit ? <RunAudit onClose={() => setAudit(false)} /> : null}
      <div className="row" style={{ justifyContent: "space-between", marginBottom: 8 }}>
        <div className="seg" role="group" aria-label="Filter jobs by state">
          {FILTERS.map(([k, l]) => <button key={k} type="button" aria-pressed={filter === k} onClick={() => setFilter(k)}>{l}</button>)}
        </div>
        {internal ? (
          <label className="small muted" style={{ fontWeight: 400, display: "inline-flex", gap: 6, alignItems: "center" }}>
            <input type="checkbox" checked={withChanges} onChange={(e) => setWithChanges(e.target.checked)} style={{ minHeight: 0 }} /> Include improvement jobs ({internal})
          </label>
        ) : null}
      </div>
      {loading ? <Loading what="jobs" /> : !shown.length ? (
        <p className="empty">{jobs.length ? "No jobs match this filter." : "No jobs yet. Run an audit to see a job’s steps, tries and evidence."}</p>
      ) : (
        <div className="scroll" role="region" aria-label="Jobs" tabIndex={0}>
          <table>
            <caption className="sr">Jobs, newest first</caption>
            <thead>
              <tr>
                <th scope="col">Job</th><th scope="col">Status</th><th scope="col" className="hide-sm">Release</th><th scope="col">Progress</th>
                <th scope="col" className="hide-sm">Tries</th><th scope="col" className="hide-sm">Last activity</th><th scope="col" className="hide-sm">Started</th>
              </tr>
            </thead>
            <tbody>
              {shown.map((j) => (
                <tr key={clean(j.id)} className="link-row" onClick={(e) => { if (!(e.target as HTMLElement).closest("a,button")) window.location.hash = `#/jobs/${encodeURIComponent(j.id)}`; }}>
                  <th scope="row">
                    <a className="item-title" href={`#/jobs/${encodeURIComponent(j.id)}`}>{kindName(j.kind)}</a>
                    <div className="meta mono">{clean(j.id)}</div>
                  </th>
                  <td>
                    <Status s={j.status} />
                    {Number(j.cleanup_pending) > 0 ? <div className="meta">cleanup: {clean(j.cleanup_pending)} pending</div> : null}
                    {Number(j.live) > 0 ? <div className="meta">{clean(j.live)} running now</div> : null}
                  </td>
                  <td className="hide-sm"><Digest d={j.release} link="release" copy={false} what="release" /></td>
                  <td className="small">{progress(arr(j.steps))}</td>
                  <td className="small hide-sm">{j.budget ? `${clean(j.budget.used)} of ${clean(j.budget.limit)}` : "—"}</td>
                  <td className="small hide-sm">{j.last_progress ? <When t={j.last_progress} /> : <span className="muted">none yet</span>}</td>
                  <td className="small hide-sm"><When t={j.created} /></td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      )}
    </Section>
  );
}

// ---------------------------------------------------------------- page

export function Home() {
  const jobs = usePoll<any[]>("/api/jobs", 2500);
  const changes = usePoll<any[]>("/api/changes", 3000);
  const releases = usePoll<any[]>("/api/releases", 4000);
  return (
    <>
      <Page title="What should the workbench improve?" />
      <Composer />
      <ErrorBox error={jobs.error ?? changes.error ?? releases.error} />
      <NeedsYou jobs={arr(jobs.data)} changes={arr(changes.data)} releases={arr(releases.data)} />
      <Improvements changes={arr(changes.data)} />
      <Jobs jobs={arr(jobs.data)} loading={!jobs.data && !jobs.error} />
    </>
  );
}
