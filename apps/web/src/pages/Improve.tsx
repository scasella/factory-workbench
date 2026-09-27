import { useState, type FormEvent, type ReactNode } from "react";
import { clean, commandId, errText, post } from "../api.ts";
import { arr, Digest, ErrorBox, Facts, Fold, kindName, Loading, MockTag, Page, Section, shortD, Status, Untrusted, useSystem, usePoll, When, type Err } from "../ui.tsx";

// Improvement (change) page: the request, where it is in its lifecycle, what
// it changes, and every attempt — rejected ones with their real diagnostics.

function Lifecycle({ stages }: { stages: [string, "done" | "now" | "todo"][] }) {
  return (
    <ol className="life" aria-label="Progress">
      {stages.map(([name, s]) => (
        <li key={name} className={s} aria-current={s === "now" ? "step" : undefined}>
          <span className="g" aria-hidden="true">{s === "done" ? "✓" : s === "now" ? "●" : "○"}</span>
          {name}<span className="sr">{s === "done" ? " (done)" : s === "now" ? " (current)" : " (not yet)"}</span>
        </li>
      ))}
    </ol>
  );
}

function sentenceFor(c: any): string[] {
  const out: string[] = [];
  for (const e of arr(c.ordering_edges)) {
    if (e.removed_after) out.push(`${clean(e.step)} no longer waits for ${clean(e.removed_after)}`);
    else if (e.added_after) out.push(`${clean(e.step)} now waits for ${clean(e.added_after)}`);
    else out.push(`${clean(e.step)}: ${clean(e.change)}`);
  }
  for (const s of arr(c.removed_steps)) out.push(`step ${clean(s)} removed`);
  if (arr(c.semantic_input_changes).length) out.push(`${arr(c.semantic_input_changes).length} change(s) to what steps read`);
  const b = c.max_parallel?.before, a = c.max_parallel?.after;
  if (b !== undefined && a !== undefined && String(a) !== String(b)) out.push(`up to ${clean(a)} steps at once (was ${clean(b)})`);
  return out;
}

function WhatChanged({ g }: { g: any }) {
  if (!g) return <p className="empty">Nothing to compare yet: no attempt has built successfully.</p>;
  const changed = arr(g.changes).filter((c: any) => sentenceFor(c).length || arr(c.semantic_input_changes).length);
  const same = arr(g.changes).length - changed.length;
  return (
    <div className="stack">
      {changed.map((c: any, i) => (
        <div key={i}>
          <h3>{kindName(c.kind)} <span className="meta mono" style={{ fontWeight: 400 }}>{clean(c.kind)}</span></h3>
          <ul style={{ listStyle: "disc", paddingLeft: 20, marginTop: 4 }}>
            {sentenceFor(c).map((s, k) => <li key={k}>{s}</li>)}
          </ul>
          {arr(c.newly_parallel).map((p: string, k) => <p key={k} className="small muted" style={{ margin: "6px 0 0" }}>Why this is safe: {clean(p)}</p>)}
          {arr(c.semantic_input_changes).length ? <Untrusted caption="changes to step inputs">{JSON.stringify(c.semantic_input_changes, null, 1)}</Untrusted> : null}
        </div>
      ))}
      {same > 0 ? <p className="small muted">{same} other workflow{same === 1 ? "" : "s"} unchanged.</p> : null}
      <p className="small muted">
        Still required before any release: {arr(g.retained_gates).map((x) => clean(x)).join(", ")} (fixed by the kernel). Migration recipe: <span className="mono">{clean(g.recipe)}</span>.
      </p>
    </div>
  );
}

function Attempts({ data, rels }: { data: any; rels: any[] }) {
  const cands = arr(data.candidates);
  const rejected = arr(data.rejected);
  const jobs = arr(data.jobs);
  if (!cands.length && !rejected.length) return <p className="empty">The first attempt is being written.</p>;
  const authorJobs = jobs.filter((j: any) => j.kind === "change_author");
  return (
    <ol className="list">
      {authorJobs.map((aj: any, i) => {
        const cand = cands.find((c: any) => c.author_job === aj.id);
        const rej = rejected.find((r: any) => r.author_job === aj.id);
        const evalJob = jobs.find((j: any) => j.kind === "change_evaluate" && cand && j.subject === cand.source_digest);
        const rel = evalJob ? rels.find((r: any) => r.evidence_job === evalJob.id)?.digest : undefined;
        let status;
        if (rej) status = <Status s="rejected" label={`rejected at ${clean(rej.stage)}`} />;
        else if (evalJob?.status === "succeeded") status = <Status s="succeeded" label="evaluation passed" />;
        else if (evalJob) status = <Status s={evalJob.status} label={evalJob.status === "running" || evalJob.status === "queued" ? "being checked" : undefined} />;
        else status = <Status s={aj.status} label={aj.status === "running" || aj.status === "queued" ? "being written" : undefined} />;
        return (
          <li key={clean(aj.id)}>
            <div className="row" style={{ justifyContent: "space-between" }}>
              <strong>Attempt {cand ? clean(cand.revision) : i + 1}</strong>
              {status}
            </div>
            <div className="meta-line">
              <span>written by <a href={`#/jobs/${encodeURIComponent(aj.id)}`}>{clean(aj.id)}</a></span>
              {evalJob ? <span>checked by <a href={`#/jobs/${encodeURIComponent(evalJob.id)}`}>{clean(evalJob.id)}</a></span> : null}
              {cand ? <span>source <Digest d={cand.source_digest} link what="source" /></span> : null}
              {rel ? <span>published as <Digest d={rel} link="release" what="release" /></span> : null}
            </div>
            {rej ? <Untrusted caption={<>What failed — actual diagnostic{rej.detail_digest ? <> · <Digest d={rej.detail_digest} link copy={false} /></> : null}</>}>{rej.reason}</Untrusted> : null}
          </li>
        );
      })}
    </ol>
  );
}

function Rewrite({ id, left, reload }: { id: string; left: number; reload: () => void }) {
  const [note, setNote] = useState("");
  const [busy, setBusy] = useState(false);
  const [error, setError] = useState<Err>(null);
  const [ok, setOk] = useState(false);
  const submit = async (e: FormEvent) => {
    e.preventDefault();
    setBusy(true);
    setError(null);
    setOk(false);
    try {
      await post(`/api/changes/${encodeURIComponent(id)}/revise`, { note, command_id: commandId() });
      setOk(true);
      setNote("");
      reload();
    } catch (err) {
      setError(errText(err));
    } finally {
      setBusy(false);
    }
  };
  return (
    <form onSubmit={(e) => void submit(e)} className="stack">
      <label htmlFor="note">Note to the author</label>
      <textarea id="note" rows={3} maxLength={4000} value={note} onChange={(e) => setNote(e.target.value)} required />
      <div className="row">
        <button type="submit" className="btn" disabled={busy || !note.trim() || left <= 0}>{busy ? "Sending…" : "Ask for another draft"}</button>
        <span className="why">Uses one of {left} remaining draft{left === 1 ? "" : "s"}.</span>
      </div>
      {ok ? <p role="status" className="result-ok">✓ Another draft requested.</p> : null}
      <ErrorBox error={error} />
    </form>
  );
}

export function ChangeDetail({ id }: { id: string }) {
  const sys = useSystem();
  const { data, error, reload } = usePoll<any>(`/api/changes/${encodeURIComponent(id)}`, 2500);
  const rels = usePoll<any[]>("/api/releases", 4000);
  if (!data) return <><Page title="Improvement" back={["#/", "Home"]} /><ErrorBox error={error} />{!error && <Loading what="improvement" />}</>;
  const c = data.change ?? {};
  const jobs = arr(data.jobs);
  const releases = arr<string>(data.releases);
  const relInfo = arr(rels.data).filter((r: any) => releases.includes(r.digest));
  const latest = relInfo[relInfo.length - 1];
  const authored = jobs.some((j: any) => j.kind === "change_author" && j.status === "succeeded");
  const evalPassed = jobs.some((j: any) => j.kind === "change_evaluate" && j.status === "succeeded");
  const running = jobs.some((j: any) => !["succeeded", "failed", "cancelled", "blocked"].includes(j.status));
  const flags = [true, authored, evalPassed, releases.length > 0, relInfo.some((r: any) => r.approved || r.activated), relInfo.some((r: any) => r.active || r.activated)];
  const names = ["Requested", "Written", "Checked", "Published", "Approved", "Active"];
  const firstTodo = flags.indexOf(false);
  const stages = names.map((n, i): [string, "done" | "now" | "todo"] => [n, flags[i] ? "done" : i === firstTodo && (running || i >= 4) && c.status !== "exhausted" ? "now" : "todo"]);
  const graph = arr(data.graph_changes).filter((g: any) => g.available);
  const lastGraph = graph[graph.length - 1];
  const revLeft = Number(c.revision_limit ?? 0) - Number(c.revisions ?? 0);
  const req = clean(data.request ?? "");
  const firstLine = req.split("\n")[0];
  const cut = firstLine.length > 160 || req.includes("\n");
  const title = !req ? "Improvement" : firstLine.length > 160 ? `${firstLine.slice(0, 120).replace(/\s+\S*$/, "")}…` : firstLine;
  return (
    <>
      <Page title={title} back={["#/", "Home"]}
        eyebrow={<>Improvement <span className="mono">{clean(c.id ?? id)}</span> · <Status s={c.status} label={c.status === "open" ? "in progress" : undefined} /></>}>
        {cut ? <p className="lede">{req}</p> : null}
        <Lifecycle stages={stages} />
      </Page>
      <ErrorBox error={error} />

      {latest && !latest.active && !latest.activated ? (
        <div className="next">
          <span>Release <b className="mono">{shortD(clean(latest.digest))}</b> {latest.approved ? "is approved. Activate it when you’re ready." : "passed every check. It’s waiting for your review."}</span>
          <a className="btn primary" href={`#/releases/${latest.digest}`}>{latest.approved ? "Go to activation" : "Review release"}</a>
        </div>
      ) : latest?.active ? (
        <div className="note">This improvement is live: release <Digest d={latest.digest} link="release" /> is the active release.</div>
      ) : c.status === "exhausted" ? (
        <div className="note bad">This improvement stopped: it used its whole budget without producing a release.</div>
      ) : null}

      <Section title="What it changes">
        <WhatChanged g={lastGraph} />
      </Section>

      <Section title="Attempts" action={sys?.inference?.mocked ? <span className="meta">authored by <MockTag /> inference</span> : undefined}>
        <Attempts data={data} rels={relInfo} />
      </Section>

      <Section title="Budget">
        <Facts rows={[
          ["Tries", data.budget ? `${clean(data.budget.used)} of ${clean(data.budget.limit)} used` : "unknown"],
          ["Drafts", `${clean(c.revisions)} of ${clean(c.revision_limit)} used (the first draft counts)`],
          ["Based on", <Digest d={c.base} link="release" what="release" />],
        ]} />
      </Section>

      <div className="section">
        {c.status === "open" ? <Fold title="Ask for another draft" meta={`${revLeft} left`}><Rewrite id={id} left={revLeft} reload={reload} /></Fold> : null}
        <Fold title="Details" meta="jobs, source IDs, draft history">
          <h3 style={{ marginBottom: 8 }}>Jobs</h3>
          <div className="scroll">
            <table>
              <thead><tr><th scope="col">Job</th><th scope="col">Status</th><th scope="col">Steps</th></tr></thead>
              <tbody>
                {jobs.map((j: any) => (
                  <tr key={clean(j.id)}>
                    <th scope="row"><a href={`#/jobs/${encodeURIComponent(j.id)}`}>{kindName(j.kind)}</a><div className="meta mono">{clean(j.id)}</div></th>
                    <td><Status s={j.status} /></td>
                    <td className="small">{arr(j.steps).map((s: any) => <div key={clean(s.id)}>{clean(s.id)}: <Status s={s.status} />{s.result ? <> <Digest d={s.result} link copy={false} /></> : null}</div>)}</td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
          <h3 style={{ margin: "24px 0 8px" }}>Draft history</h3>
          {arr(data.revisions).length === 0 ? <p className="muted small">Only the first draft so far.</p> : (
            <ul className="small">
              {arr(data.revisions).map((x: any, i) => (
                <li key={i}><When t={x.created} />: {x.from_job ? clean(x.from_job) : "—"} → {x.new_job ? <a href={`#/jobs/${encodeURIComponent(x.new_job)}`}>{clean(x.new_job)}</a> : "—"} (<Status s={x.status} />)</li>
              ))}
            </ul>
          )}
          <h3 style={{ margin: "24px 0 8px" }}>Identifiers</h3>
          <Facts rows={[
            ["Request", <Digest d={c.request} link what="request" />],
            ...arr(data.candidates).map((x: any): [string, ReactNode] => [`Attempt ${clean(x.revision)} source`, <Digest d={x.source_digest} link what="source" />]),
          ]} />
        </Fold>
      </div>
    </>
  );
}
