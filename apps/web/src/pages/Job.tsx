import { useEffect, useState } from "react";
import { clean, commandId, errText, LIVE_ATTEMPT, post, pretty, TERMINAL_JOB, truthy } from "../api.ts";
import { arr, Confirm, Digest, ErrorBox, Facts, Fold, kindName, Loading, MockTag, Page, Section, shortD, Status, Untrusted, usePoll, When, type Err } from "../ui.tsx";

function parseUsage(u: unknown): string {
  if (u === null || u === undefined || u === "" || u === "null") return "unknown";
  let v: any = u;
  if (typeof u === "string") {
    try {
      v = JSON.parse(u);
    } catch {
      return clean(u);
    }
  }
  if (!v || typeof v !== "object") return "unknown";
  const part = (k: string, label: string) => (typeof v[k] === "number" ? `${v[k]} ${label}` : `? ${label}`);
  return [part("inputTokens", "in"), part("outputTokens", "out"), part("cachedInputTokens", "cached")].join(" · ");
}

const MODEL_ROLES = ["author", "reproduce", "refute", "summarize"];

// ---------------------------------------------------------------- attempts

/** The five facts about an attempt are independent and always shown separately. */
function Attempt({ a, job }: { a: any; job: any }) {
  const o = a.observation;
  const inv = arr(job.invocations).filter((i: any) => String(i.step) === String(a.step) && String(i.gen) === String(a.gen));
  const acc = arr(job.steps).find((s: any) => s.id === a.step)?.accepted;
  const accepted = acc && String(acc.gen) === String(a.gen);
  return (
    <div className="attempt">
      <h4>Try #{clean(a.gen)} <span className="meta" style={{ fontWeight: 400 }}>{clean(a.role)}</span></h4>
      <Facts rows={[
        ["Allowed to run", <>
          <Status s={a.status} /> · {LIVE_ATTEMPT.has(a.status) ? "holds live authority" : "no authority now"}
          <div className="meta">authorization (kernel) · job epoch {clean(a.job_epoch)}, controller epoch {clean(a.ctrl_epoch)}, deadline tick {clean(a.deadline)}</div>
        </>],
        ["Machine saw", o ? <>
          phase <strong>{clean(o.phase ?? "unknown")}</strong>{o.container ? <> · container <span className="mono">{clean(o.container).slice(0, 12)}</span></> : null} · <When t={o.updated} />
          <div className="meta">OS observation (supervisor)</div>
          {o.detail ? <details className="inline"><summary>detail</summary><Untrusted>{o.detail}</Untrusted></details> : null}
          {o.last_output ? <details className="inline"><summary>last output</summary><Untrusted caption="process output">{o.last_output}</Untrusted></details> : null}
        </> : <span className="muted">nothing observed</span>],
        ["Model call", inv.length === 0 ? <span className="muted">{MODEL_ROLES.includes(a.role) ? "no call recorded" : "none (checker step)"}</span> : inv.map((i: any) => (
          <div key={clean(i.id)}>
            {clean(i.transport ?? "unknown")}{truthy(i.fake) ? <> <MockTag /></> : null} · exit {i.exit_code === null || i.exit_code === undefined ? "unknown" : clean(i.exit_code)} · {parseUsage(i.usage)}
            {i.transcript_digest ? <> · transcript <Digest d={i.transcript_digest} link copy={false} /></> : null}
            <div className="meta">transport outcome (adapter)</div>
          </div>
        ))],
        ["Result kept", accepted ? <><Status s="accepted" label="accepted" /> <Digest d={acc.result} link /></> : <span className="muted">not accepted</span>],
        ["Cleanup", <Status s={o?.cleanup ?? "none"} label={o?.cleanup === "pending" ? "still running" : o?.cleanup ? undefined : "nothing to clean up"} />],
      ]} />
    </div>
  );
}

function Steps({ job }: { job: any }) {
  const specs = arr(job.workflow?.steps);
  const states = arr(job.steps);
  const ids = specs.length ? specs.map((s: any) => s.id) : states.map((s: any) => s.id);
  const attempts = arr(job.attempts);
  return (
    <ul className="steps">
      {ids.map((id: string) => {
        const spec = specs.find((s: any) => s.id === id) ?? {};
        const st = states.find((s: any) => s.id === id) ?? {};
        const mine = attempts.filter((a: any) => a.step === id);
        const busy = mine.some((a: any) => LIVE_ATTEMPT.has(a.status));
        const failed = st.status === "failed" || st.status === "blocked";
        const waits = arr(spec.after).map((x) => clean(x));
        const uses = arr(spec.inputs).filter((i: any) => i.source?.type === "step_output").map((i: any) => clean(i.source.step));
        return (
          <li key={clean(id)}>
            <details open={busy || failed}>
              <summary>
                <span className="sid">{clean(id)}</span>
                <span className="small muted role">
                  {[spec.role && spec.role !== id ? clean(spec.role) : "", waits.length ? `waits for ${waits.join(", ")}` : ""].filter(Boolean).join(" · ")}
                  {uses.length ? `${spec.role !== id || waits.length ? " · " : ""}uses output of ${uses.join(", ")}` : ""}
                  {mine.length > 1 ? ` · ${mine.length} tries` : ""}
                </span>
                <Status s={busy ? "running" : job.status === "cancelled" && st.status !== "succeeded" ? "cancelled" : st.status} />
              </summary>
              <div style={{ paddingBottom: 8 }}>
                {st.accepted ? (
                  <p className="small" style={{ marginLeft: 16 }}>
                    Result <Digest d={st.accepted.result} link /> · outcome <Status s={st.accepted.outcome} /> · made by release <Digest d={st.accepted.release} link="release" copy={false} />
                    <span className="meta"> · fingerprint {shortD(clean(st.accepted.fingerprint))}, accepted at tick {clean(st.accepted.accepted_at)}</span>
                  </p>
                ) : null}
                {arr(spec.inputs).length ? <p className="small muted" style={{ marginLeft: 16 }}>Reads: {arr(spec.inputs).map((i: any) => `${clean(i.name)} ← ${i.source?.type === "step_output" ? `output of ${clean(i.source.step)}` : "job input"}`).join("; ")}</p> : null}
                {mine.length === 0 ? <p className="small muted" style={{ marginLeft: 16 }}>Not started. A step isn’t running until a try is allowed and observed.</p> : mine.map((a: any) => <Attempt key={`${a.step}#${a.gen}`} a={a} job={job} />)}
              </div>
            </details>
          </li>
        );
      })}
    </ul>
  );
}

// ---------------------------------------------------------------- journal

interface JEntry { seq: number; command_id: string; accepted: boolean; reject_code: string | null; events: unknown; wall_time?: string }

export function JournalTable({ rows }: { rows: JEntry[] }) {
  if (!rows.length) return <p className="empty">No entries.</p>;
  return (
    <div className="scroll" role="region" aria-label="Journal entries" tabIndex={0}>
      <table>
        <thead><tr><th scope="col">#</th><th scope="col">Decision</th><th scope="col">What happened</th><th scope="col" className="hide-sm">Record ID</th><th scope="col" className="hide-sm">When</th></tr></thead>
        <tbody>
          {rows.map((r) => (
            <tr key={r.seq}>
              <th scope="row" className="mono">{r.seq}</th>
              <td>{r.accepted ? <Status s="accepted" /> : <><Status s="rejected" /> <code>{clean(r.reject_code)}</code></>}</td>
              <td className="small">
                {arr(r.events).length ? (
                  <details className="inline"><summary style={{ color: "var(--fg-2)" }}>{arr(r.events).map((e: any) => clean(e?.type ?? "event").replaceAll("_", " ")).join(", ")}</summary><Untrusted caption="events">{pretty(r.events)}</Untrusted></details>
                ) : <span className="muted">no events</span>}
              </td>
              <td className="hide-sm"><code className="wrap small muted">{clean(r.command_id)}</code></td>
              <td className="small hide-sm"><When t={r.wall_time} /></td>
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  );
}

function LiveJournal({ id }: { id: string }) {
  const [entries, setEntries] = useState<Map<number, JEntry>>(new Map());
  const [conn, setConn] = useState<"connecting" | "open" | "reconnecting" | "closed">("connecting");
  useEffect(() => {
    // Cookie-authenticated; no token in the URL. EventSource resumes with
    // Last-Event-ID; entries are also deduplicated by sequence number.
    const es = new EventSource(`/api/jobs/${encodeURIComponent(id)}/events`);
    es.onopen = () => setConn("open");
    es.onerror = () => setConn(es.readyState === EventSource.CLOSED ? "closed" : "reconnecting");
    es.addEventListener("journal", (ev) => {
      let d: any;
      try {
        d = JSON.parse((ev as MessageEvent).data);
      } catch {
        return;
      }
      const seq = Number(d?.seq ?? (ev as MessageEvent).lastEventId);
      if (!Number.isFinite(seq)) return;
      setEntries((m) => {
        if (m.has(seq)) return m;
        const n = new Map(m);
        n.set(seq, { seq, command_id: d.command_id, accepted: truthy(d.accepted), reject_code: d.reject_code ?? null, events: d.events, wall_time: d.wall_time });
        return n;
      });
    });
    return () => es.close();
  }, [id]);
  const rows = [...entries.values()].sort((a, b) => a.seq - b.seq);
  return (
    <Fold title="Activity log" meta={`${rows.length} entries · stream ${conn}`}>
      <p className="small muted">Live, in journal order; reconnects resume without duplicates.</p>
      <JournalTable rows={rows} />
    </Fold>
  );
}

// ---------------------------------------------------------------- migration

function Migration({ job }: { job: any }) {
  const releases = usePoll<any[]>("/api/releases", 0);
  const [target, setTarget] = useState("");
  const [preview, setPreview] = useState<any>(null);
  const [error, setError] = useState<Err>(null);
  const [busy, setBusy] = useState(false);
  const [applied, setApplied] = useState<string | null>(null);
  const options = arr(releases.data).filter((r: any) => r.activated && r.digest !== job.release);
  const doPreview = async () => {
    setBusy(true);
    setError(null);
    setPreview(null);
    try {
      setPreview(await post("/api/jobs/" + encodeURIComponent(job.id) + "/migrations/preview", { target }));
    } catch (e) {
      setError(errText(e));
    } finally {
      setBusy(false);
    }
  };
  const list = (v: unknown) => (arr(v).length ? arr(v).map((x) => clean(x)).join(", ") : "none");
  return (
    <Fold title="Move to another release" meta="checked migration">
      {job.kind !== "package_audit" ? <p className="small muted">Improvement jobs are never moved between releases.</p> : null}
      <p className="small muted">A preview changes nothing. The job stays on its release unless you apply a migration, and only a paused job can move.</p>
      <div className="row">
        <label htmlFor="mig-target" className="sr">Target release</label>
        <select id="mig-target" value={target} onChange={(e) => { setTarget(e.target.value); setPreview(null); }}>
          <option value="">Choose a release…</option>
          {options.map((r: any) => <option key={clean(r.digest)} value={clean(r.digest)}>{shortD(clean(r.digest))}{r.active ? " (active)" : ""}</option>)}
        </select>
        <button type="button" className="btn" disabled={!target || busy} onClick={() => void doPreview()}>Preview</button>
      </div>
      <ErrorBox error={error} />
      <p role="status" className="result-ok" style={applied ? undefined : { margin: 0 }}>{applied ? `✓ ${applied}` : ""}</p>
      {preview ? (
        <div className="confirm-panel">
          <Facts rows={[
            ["Can move", <Status s={preview.can_migrate ? "ok" : "failed"} label={preview.can_migrate ? "yes" : "no"} />],
            ["From → to", <><Digest d={preview.from} link="release" copy={false} /> → <Digest d={preview.to} link="release" copy={false} /></>],
            ["Kept (identical)", list(preview.kept)],
            ["Redone", list(preview.reset)],
            ["Retired", list(preview.retired)],
            ["Reasons", arr(preview.reasons).length ? arr(preview.reasons).map((r, i) => <div key={i}>{clean(r)}</div>) : "none"],
            ["Job revision", clean(preview.revision)],
          ]} />
          <Confirm label="Apply migration" heading="Move this job?" action="Apply migration" disabled={!preview.can_migrate} why={preview.can_migrate ? undefined : "The preview says this job can’t move."}
            details={<p className="small">Move <span className="mono">{clean(job.id)}</span> to release <span className="mono wrap">{clean(preview.to)}</span> at job revision {clean(preview.revision)}. Rejected if the job changed since this preview.</p>}
            onConfirm={() => post("/api/jobs/" + encodeURIComponent(job.id) + "/migrations/apply", { target: String(preview.to ?? target), expected_revision: String(preview.revision), command_id: commandId() }).then(() => { setApplied(`Moved to release ${shortD(clean(preview.to))}. The job is still paused: resume it to continue on the new release.`); setPreview(null); return "Migration applied."; })} />
        </div>
      ) : null}
    </Fold>
  );
}

// ---------------------------------------------------------------- page

function Controls({ job, reload }: { job: any; reload: () => void }) {
  const [error, setError] = useState<Err>(null);
  const act = async (a: "pause" | "resume") => {
    setError(null);
    try {
      await post(`/api/jobs/${encodeURIComponent(job.id)}/${a}`, { command_id: commandId() });
      reload();
    } catch (e) {
      setError(errText(e));
    }
  };
  if (TERMINAL_JOB.has(job.status)) return null;
  const paused = job.status === "paused" || job.status === "pause_requested";
  return (
    <div>
      <div className="row" style={{ alignItems: "flex-start" }}>
        {paused ? <button type="button" className="btn" onClick={() => void act("resume")}>Resume</button> : <button type="button" className="btn" onClick={() => void act("pause")}>Pause</button>}
        <Confirm label="Cancel job" danger heading="Cancel this job?" action="Cancel job" cancelLabel="Keep running"
          details={<p className="small">Cancelling takes away every try’s authority immediately, so no later result can be accepted. Container cleanup may continue afterwards and stays visible here.</p>}
          onConfirm={() => post(`/api/jobs/${encodeURIComponent(job.id)}/cancel`, { command_id: commandId() }).then(() => { reload(); return "Cancelled."; })} />
      </div>
      <ErrorBox error={error} />
    </div>
  );
}

export function JobDetail({ id }: { id: string }) {
  const { data: job, error, reload } = usePoll<any>(`/api/jobs/${encodeURIComponent(id)}`, 2000);
  if (!job) return <><Page title="Job" back={["#/", "Home"]} /><ErrorBox error={error} />{!error && <Loading what="job" />}</>;
  const obs = arr(job.attempts).map((a: any) => a.observation).filter(Boolean);
  const pendingCleanup = obs.filter((o: any) => o.cleanup === "pending").length;
  const live = arr(job.attempts).filter((a: any) => LIVE_ATTEMPT.has(a.status)).length;
  const b = job.budget_detail;
  const back: [string, string] = job.change ? [`#/changes/${encodeURIComponent(job.change)}`, "Improvement"] : ["#/", "Home"];
  return (
    <>
      <Page title={kindName(job.kind)} back={back} eyebrow={<span className="mono">{clean(job.id)}</span>} actions={<Controls job={job} reload={reload} />}>
        <div className="meta-line">
          <Status s={job.status} />
          <span>on release <Digest d={job.release} link="release" copy={false} what="release" /></span>
          {b ? <span>{clean(b.used)} of {clean(b.limit)} tries used</span> : null}
          {live ? <span>{live} running now</span> : null}
          {job.report ? <span>report <Digest d={job.report.digest} link copy={false} /></span> : null}
        </div>
      </Page>
      <ErrorBox error={error} />
      {job.status === "cancelled" ? (
        <div className="note warn" role="note">
          <strong>Cancelled — effective immediately.</strong> Tries holding authority: {live}. {pendingCleanup > 0 ? <>Cleanup still running for {pendingCleanup}.</> : <>No cleanup pending.</>}
        </div>
      ) : null}
      {job.ready_diagnostic ? <div className="note warn" role="note"><strong>Why nothing is running:</strong><Untrusted caption="planner diagnostic">{job.ready_diagnostic}</Untrusted></div> : null}

      <Section title="Steps" action={<span className="meta">{job.workflow ? `up to ${clean(job.workflow.max_parallel)} at once` : ""}</span>}>
        <Steps job={job} />
      </Section>

      <div className="section">
        {arr(job.diagnostics).length ? (
          <Fold title="Diagnostics" meta={`latest ${arr(job.diagnostics).length}`}>
            <ul className="list">{arr(job.diagnostics).map((d: any, i) => <li key={i}><div className="meta"><When t={d.created} /> · {clean(d.kind)}</div><Untrusted>{d.detail}</Untrusted></li>)}</ul>
          </Fold>
        ) : null}
        <Fold title="Identifiers" meta="subject, input, revision">
          <Facts rows={[
            ["Kind", <span className="mono">{clean(job.kind)}</span>],
            ["Runs on (pinned)", <Digest d={job.release} link="release" what="release" />],
            ["Subject", <Digest d={job.subject} link />],
            ["Input", <Digest d={job.input} link />],
            ["Job epoch / revision", `${clean(job.epoch)} / ${clean(job.revision)}`],
            ["Improvement", job.change ? <a href={`#/changes/${encodeURIComponent(job.change)}`}>{clean(job.change)}</a> : "—"],
          ]} />
        </Fold>
        <Migration job={job} />
        <LiveJournal id={id} />
      </div>
    </>
  );
}
