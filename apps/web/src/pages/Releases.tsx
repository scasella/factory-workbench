import { useEffect, type ReactNode } from "react";
import { clean, commandId, post, truthy } from "../api.ts";
import { arr, Confirm, Digest, ErrorBox, Facts, Fold, FullDigest, kindName, Loading, Page, Status, Untrusted, useSystem, usePoll } from "../ui.tsx";

// ---------------------------------------------------------------- list

function releaseState(r: any): ReactNode {
  if (r.active) return <Status s="active" label="active" />;
  if (r.activated) return <Status s="closed" glyph="◌" label="previously active" />;
  if (r.approved) return <Status s="authorized" glyph="●" label="approved, not active" tone="info" />;
  return <Status s="pending" label="awaiting review" />;
}

export function Releases() {
  const { data, error } = usePoll<any[]>("/api/releases", 4000);
  const rows = [...arr(data)].reverse();
  return (
    <>
      <Page title="Releases">
        <p className="lede" style={{ fontSize: 15 }}>Each release is a complete, checked orchestration package. New jobs use the active release; running jobs keep the one they started with.</p>
      </Page>
      <ErrorBox error={error} />
      <div className="section">
        {!data ? <Loading what="releases" /> : (
          <div className="scroll" role="region" aria-label="Releases" tabIndex={0}>
            <table>
              <thead><tr><th scope="col">Release</th><th scope="col">State</th><th scope="col">From</th><th scope="col" className="hide-sm">Built on</th></tr></thead>
              <tbody>
                {rows.map((r: any) => (
                  <tr key={clean(r.digest)} className="link-row" onClick={(e) => { if (!(e.target as HTMLElement).closest("a,button")) window.location.hash = `#/releases/${r.digest}`; }}>
                    <th scope="row"><Digest d={r.digest} link="release" what="release" /></th>
                    <td>{releaseState(r)}</td>
                    <td className="small">{r.change ? <a href={`#/changes/${encodeURIComponent(r.change)}`}>improvement {clean(r.change)}</a> : r.evidence_job ? clean(r.evidence_job) : <span className="muted">setup (trust root)</span>}</td>
                    <td className="hide-sm">{r.parent ? <Digest d={r.parent} link="release" copy={false} /> : <span className="muted">—</span>}</td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        )}
      </div>
    </>
  );
}

// ---------------------------------------------------------------- evidence

function checkLabel(id: string, outcome: string): string {
  if (outcome === "not_run") return "not run";
  if (outcome === "inconclusive") return "inconclusive";
  if (id === "independent_replay") return outcome === "pass" ? "proof replay passed" : "proof replay failed";
  return outcome === "pass" ? "checked: pass" : `checked: ${outcome}`;
}

const passed = (o: unknown) => o === "pass";

function ChecksTable({ checks, caption }: { checks: unknown; caption: string }) {
  const rows = arr(checks);
  if (!rows.length) return <p className="muted small">{caption}: not available / not run.</p>;
  return (
    <table>
      <caption>{caption}</caption>
      <thead><tr><th scope="col">Check</th><th scope="col">Result</th><th scope="col">Detail</th></tr></thead>
      <tbody>
        {rows.map((c: any, i) => (
          <tr key={i}>
            <th scope="row" className="mono">{clean(c.id)}</th>
            <td><Status s={c.outcome} label={checkLabel(String(c.id), String(c.outcome))} /></td>
            <td className="small">{clean(c.detail)}</td>
          </tr>
        ))}
      </tbody>
    </table>
  );
}

function scopeLabel(s: unknown): string {
  if (s === "general") return "general";
  if (s === "finite-kernel-reduced") return "finite (kernel-reduced)";
  return clean(s) || "unknown";
}

interface Line { name: string; status: ReactNode; detail?: ReactNode; bad: boolean; mocked?: boolean }

function evidenceLines(v: any, mocked: boolean): Line[] {
  const b = v.build_receipt, p = v.prove_receipt, t = v.protected_tests;
  const lines: Line[] = [];
  const bc = arr(b?.checks);
  lines.push({
    name: "Build",
    status: b ? <Status s={b.outcome} label={passed(b.outcome) ? "checked: pass" : `checked: ${clean(b.outcome)}`} /> : <Status s="not_run" />,
    detail: b ? <>{bc.filter((c: any) => passed(c.outcome)).length} of {bc.length} checks · build <Digest d={b.binary_digest} link copy={false} what="build" /></> : null,
    bad: !b || !passed(b.outcome),
  });
  const obl = arr(p?.obligations);
  const replay = arr(p?.checks).find((c: any) => c.id === "independent_replay");
  lines.push({
    name: "Proofs",
    status: !p ? <Status s="not_run" />
      : !passed(p.outcome) ? <Status s="failed" label={`prove: ${clean(p.outcome)}${p.failure ? ` — ${clean(p.failure)}` : ""}`} />
      : <Status s={replay?.outcome ?? p.outcome} label={replay ? checkLabel("independent_replay", String(replay.outcome)) : "prove: pass"} />,
    detail: p ? <>{obl.map((o: any) => clean(o.id)).join(", ")} — {obl.filter((o: any) => o.ok).length} of {obl.length} statements checked{replay ? <> · replay {checkLabel("independent_replay", String(replay.outcome))}</> : null}{p.replay ? <> · <span className="mono">{clean(p.replay.tool)}</span></> : null}</> : null,
    bad: !p || !passed(p.outcome) || (replay && !passed(replay.outcome)),
  });
  const neg = arr(t?.negative_controls);
  lines.push({
    name: "Protected tests",
    status: t ? <Status s={t.outcome} label={passed(t.outcome) ? "integration test passed" : `integration test: ${clean(t.outcome)}`} /> : <Status s="not_run" />,
    detail: t ? <>{clean(t.cases ?? "?")} cases, {arr(t.failures).length} failures · {neg.filter((n: any) => n.ok).length} of {neg.length} bad inputs rejected</> : null,
    bad: !t || !passed(t.outcome),
  });
  lines.push({
    name: "Supplemental tests",
    status: <Status s="not_run" label="not reported separately" />,
    detail: "Candidate-supplied planner cases, if any, run inside the protected suite above; the verifier does not report them on their own.",
    bad: false,
  });
  const reviews = arr(v.reviews);
  const byRole = (role: string) => reviews.find((r: any) => r.role === role);
  const rv = ["reproduce", "refute"].map((role) => {
    const r = byRole(role);
    const verdict = r?.verdict ?? "not_run";
    return { role, verdict, fake: truthy(r?.fake) };
  });
  const fakeRoles = rv.filter((r) => r.fake).map((r) => r.role);
  const anyFake = fakeRoles.length > 0 || (mocked && reviews.length > 0);
  lines.push({
    name: "Model reviews",
    status: (
      <span className="row" style={{ gap: 14 }}>
        {rv.map((r) => (
          <Status key={r.role} s={r.verdict === "pass" ? "open" : r.verdict} glyph={r.verdict === "pass" ? (anyFake ? "⚠" : "◐") : undefined}
            tone={r.verdict === "pass" ? (anyFake ? "warn" : "info") : undefined}
            label={r.verdict === "not_run" ? `${r.role}: not run` : `${r.role}: model review: ${clean(r.verdict)}`} />
        ))}
      </span>
    ),
    detail: <>Judgments, not proofs.{anyFake ? <> <strong>Mocked:</strong> {fakeRoles.length ? `the ${fakeRoles.join(" and ")} review${fakeRoles.length > 1 ? "s were" : " was"}` : "reviews in this system are"} scripted by fake inference, not a real model.</> : null}</>,
    bad: rv.some((r) => r.verdict !== "pass"),
    mocked: anyFake,
  });
  lines.push({
    name: "Assumed",
    status: <Status s="none" glyph="◇" label={`${arr(v.assumptions).length} outside verified boundary`} />,
    detail: "Lean toolchain, codec, SHA-256, SQLite, Docker isolation, supervisor reports, and the reviews themselves.",
    bad: false,
  });
  lines.push({
    name: "Bundle",
    status: v.integrity === "ok" ? <Status s="ok" label="runtime guard checked: bundle integrity ok" /> : <Status s="failed" glyph="⚠" label={`integrity failure: ${clean(v.integrity)}`} />,
    bad: v.integrity !== "ok",
  });
  return lines;
}

function Evidence({ lines }: { lines: Line[] }) {
  return (
    <dl className="evidence">
      {lines.map((l) => (
        <div key={l.name}>
          <dt>{l.name}</dt>
          <dd>{l.status}{l.detail ? <div className="detail">{l.detail}</div> : null}</dd>
        </div>
      ))}
    </dl>
  );
}

// ---------------------------------------------------------------- decision

function Decision({ digest, v, active, preview, previewError, reload, lines, mocked }: {
  digest: string; v: any; active: string | null; preview: any[] | null; previewError: boolean; reload: () => void; lines: Line[]; mocked: boolean;
}) {
  const r = v.release ?? {};
  const approvals = arr(v.approvals);
  const usable = approvals.filter((a: any) => !a.revoked);
  const latest = usable[usable.length - 1];
  const s8 = digest.slice(0, 8);
  const unfinished = preview ? preview.length : null;
  const jobsSentence = previewError
    ? "Effect on existing jobs: unknown (the preview failed to load)."
    : unfinished === null ? "Checking existing jobs…"
    : `${unfinished === 0 ? "No unfinished jobs" : `${unfinished} unfinished job${unfinished === 1 ? "" : "s"}`}. Existing jobs stay on the release they started with; none move unless you migrate them.`;
  const guard = `${active}|${latest?.id ?? ""}|${approvals.length}|${v.active}|${v.integrity}|${lines.map((l) => (l.bad ? 1 : 0)).join("")}`;
  const baseMatches = !!latest && latest.expected_base === active;
  const intact = v.integrity === "ok";
  const reviewMocked = mocked || arr(v.reviews).some((x: any) => truthy(x.fake));
  return (
    <section className="decision" aria-labelledby="decide-h">
      <h2 id="decide-h">Decision</h2>
      <div className="part">
        <Facts rows={[
          ["Release", <FullDigest d={digest} what="release" />],
          v.active
            ? ["Built on", r.parent ? <FullDigest d={r.parent} what="parent release" /> : <span className="muted">nothing (setup release)</span>]
            : ["Replaces", active ? <><FullDigest d={active} what="active release" /><div className="small muted">{arr(v.activations).length ? "↩ Rollback: this release was active before. Approving and activating makes it the default again for new jobs." : r.parent === active ? "✓ This release was built on the active release." : "≠ This release was built on a different release; approval will bind to the current active release."}</div></> : <span className="muted">no active release</span>],
          ["State", v.active ? <Status s="active" label="active: new jobs use it" /> : arr(v.activations).length ? <Status s="closed" glyph="◌" label="previously active" /> : latest ? <Status s="authorized" glyph="●" tone="info" label={`approved (${clean(latest.id)}), not active`} /> : <Status s="pending" label="published, not approved, not active" />],
        ]} />
      </div>
      <div className="part">
        <h2>Evidence</h2>
        <Evidence lines={lines} />
      </div>
      <div className="part">
        <p style={{ margin: 0 }}>{jobsSentence}</p>
      </div>
      <div className="part steps2">
        <div className="stepcard">
          <h3><span className="num">1</span> Approve</h3>
          <p className="small muted">Records that you reviewed this exact release against the active one. It doesn’t change what runs.</p>
          {latest ? <p className="small"><Status s="ok" label={`Approved: ${clean(latest.id)}`} /></p> : null}
          <Confirm label="Approve" heading={`Approve release ${s8}?`} primary={!latest && !v.active && intact} disabled={!active || v.active || !intact} guard={guard}
            why={v.active ? "This release is already active." : !intact ? "The release bundle failed its integrity check." : !active ? "There is no active release to approve against." : undefined}
            match={digest}
            ack={reviewMocked ? "I understand the model reviews for this release were scripted by fake inference, not a real model." : undefined}
            details={<>
              <p className="small">You’re approving this exact release against the release that is active now.</p>
              <Facts rows={[
                ["Release", <span className="mono wrap">{digest}</span>],
                ["Payload", <span className="mono wrap">{clean(r.payload)}</span>],
                ["Source", <span className="mono wrap">{clean(r.source)}</span>],
                ["Active base", <span className="mono wrap">{active ?? "none"}</span>],
              ]} />
              <Evidence lines={lines} />
            </>}
            action={`Record approval of ${s8}`}
            onConfirm={() => post(`/api/releases/${encodeURIComponent(digest)}/approve`, { expected_base: active ?? "", command_id: commandId() }).then(() => { reload(); return "Approval recorded. It appears above with its ID."; })} />
        </div>
        <div className="stepcard">
          <h3><span className="num">2</span> Activate</h3>
          <p className="small muted">Makes this the release new jobs use. Running jobs keep theirs.</p>
          <Confirm label="Activate" heading={`Activate release ${s8}?`} guard={guard}
            primary={!!latest && !v.active && intact && baseMatches && !previewError && preview !== null}
            disabled={!latest || !active || v.active || !intact || !baseMatches || previewError || preview === null}
            why={v.active ? "Already the active release." : !intact ? "The release bundle failed its integrity check." : !latest ? "Needs an approval first." : !baseMatches ? "The approval was for a different active release. Approve again." : previewError ? "The effect on existing jobs couldn’t be checked." : preview === null ? "Checking existing jobs…" : undefined}
            match={digest}
            details={<>
              <p className="small">New jobs will use this release. {jobsSentence}</p>
              <Facts rows={[
                ["Release", <span className="mono wrap">{digest}</span>],
                ["Replaces", <span className="mono wrap">{active ?? "none"}</span>],
                ["Approval", <>{clean(latest?.id)} {baseMatches ? <Status s="ok" label="base matches the active release" /> : <Status s="failed" label="base differs from the active release" />}</>],
              ]} />
            </>}
            action={`Activate ${s8}`}
            onConfirm={() => post(`/api/releases/${encodeURIComponent(digest)}/activate`, { expected_active: active ?? "", approval: String(latest?.id ?? ""), command_id: commandId() }).then(() => { reload(); return `Activated. New jobs now use ${s8}.`; })} />
        </div>
      </div>
      {!v.active && !arr(v.activations).length && !latest ? (
        <p className="small muted" style={{ margin: "16px 0 0" }}>To reject: leave it unapproved. Nothing ever runs an unapproved release. (A recorded “reject” is not available yet.)</p>
      ) : null}
    </section>
  );
}

// ---------------------------------------------------------------- page

export function ReleaseReview({ digest: ref }: { digest: string }) {
  const sys = useSystem();
  const { data: v, error, reload } = usePoll<any>(`/api/releases/${encodeURIComponent(ref)}`, 4000);
  // The URL may carry a short prefix; everything below uses the full digest the server resolved.
  const digest: string = v?.release?.digest ?? ref;
  useEffect(() => {
    if (v?.release?.digest && v.release.digest !== ref) history.replaceState(null, "", `#/releases/${v.release.digest}`);
  }, [v?.release?.digest, ref]);
  const pv = usePoll<any[]>(`/api/releases/${encodeURIComponent(digest)}/activation-preview`, 5000);
  const s8 = digest.slice(0, 8);
  if (!v) return <><Page title={`Release ${s8}`} back={["#/releases", "Releases"]} /><ErrorBox error={error} />{!error && <Loading what="release" />}</>;
  const r = v.release ?? {};
  const active: string | null = sys?.active_release ?? null;
  const mocked = !!sys?.inference?.mocked;
  const lines = evidenceLines(v, mocked);
  const p = v.prove_receipt, b = v.build_receipt, t = v.protected_tests;
  const obl = arr(p?.obligations);
  const bc = arr(b?.checks);
  const neg = arr(t?.negative_controls);
  const genesis = !r.parent;
  return (
    <>
      <Page title={`Release ${s8}`} back={["#/releases", "Releases"]}
        eyebrow={genesis ? "Setup release: checked by the fixed verifier during bootstrap and installed as the trust root" : <>From {r.evidence_job ? <a href={`#/jobs/${encodeURIComponent(r.evidence_job)}`}>{clean(r.evidence_job)}</a> : "—"}</>} />
      <ErrorBox error={error} />
      <Decision digest={digest} v={v} active={active} preview={pv.data ? arr(pv.data) : null} previewError={!!pv.error} reload={reload} lines={lines} mocked={mocked} />

      <div className="section">
        <Fold title="Proofs" meta={p ? `${obl.length} statements · ${obl.filter((o: any) => o.ok).length} checked · axioms ${[...new Set(obl.flatMap((o: any) => arr(o.axioms)))].map((x) => clean(x)).join(", ") || "none"}` : "not run"} attention={lines[1].bad}>
          {!p ? <p className="muted">No proof receipt.</p> : (
            <>
              {p.failure ? <p className="t-bad">{clean(p.failure)}</p> : null}
              <div className="scroll">
                <table>
                  <caption>Frozen statements bound to this release’s declarations</caption>
                  <thead><tr><th scope="col">Id</th><th scope="col">Statement</th><th scope="col">Scope</th><th scope="col">Axioms</th><th scope="col">Result</th></tr></thead>
                  <tbody>
                    {obl.map((o: any) => (
                      <tr key={clean(o.id)}>
                        <th scope="row">{clean(o.id)}</th>
                        <td><code className="wrap">{clean(o.statement)}</code><div className="meta mono">{clean(o.decl)}</div></td>
                        <td className="small">{scopeLabel(o.scope)}</td>
                        <td className="small">{arr(o.axioms).map((x) => clean(x)).join(", ") || "none"}</td>
                        <td><Status s={o.ok ? "ok" : "failed"} label={o.ok ? "statement checked" : "failed"} /></td>
                      </tr>
                    ))}
                  </tbody>
                </table>
              </div>
              <div style={{ marginTop: 20 }}><ChecksTable checks={p.checks} caption="Proof checks" /></div>
            </>
          )}
        </Fold>
        <Fold title="Build checks" meta={b ? `${bc.filter((c: any) => passed(c.outcome)).length} of ${bc.length} passed` : "not run"} attention={lines[0].bad}>
          {b?.failure ? <p className="t-bad">{clean(b.failure)}</p> : null}
          <ChecksTable checks={b?.checks} caption="Build checks" />
        </Fold>
        <Fold title="Tests" meta={t ? `${clean(t.cases ?? "?")} cases · ${arr(t.failures).length} failures · ${neg.filter((n: any) => n.ok).length} of ${neg.length} bad inputs rejected` : "not run"} attention={lines[2].bad}>
          {!t ? <p className="muted">No protected test result.</p> : (
            <>
              <p><Status s={t.outcome} label={passed(t.outcome) ? "integration test passed" : `integration test: ${clean(t.outcome)}`} /> <span className="small muted">{clean(t.detail)}</span></p>
              {arr(t.failures).length ? <Untrusted caption="failures">{JSON.stringify(t.failures, null, 2)}</Untrusted> : null}
              {neg.length ? (
                <table>
                  <caption>Bad inputs the harness must reject (negative controls)</caption>
                  <thead><tr><th scope="col">Control</th><th scope="col">Result</th><th scope="col">Detail</th></tr></thead>
                  <tbody>{neg.map((n: any, i) => <tr key={i}><th scope="row" className="mono">{clean(n.name)}</th><td><Status s={n.ok ? "ok" : "failed"} label={n.ok ? "rejected as expected" : "NOT rejected"} /></td><td className="small">{clean(n.detail)}</td></tr>)}</tbody>
                </table>
              ) : null}
              <p className="small muted" style={{ marginTop: 16 }}>Supplemental tests: not reported separately by the verifier.</p>
            </>
          )}
        </Fold>
        <Fold title="Model reviews" meta={`${arr(v.reviews).length} reviews · untrusted model text`} attention={(lines[4].bad && !genesis) || !!lines[4].mocked}>
          {arr(v.reviews).length === 0 ? <p className="muted">Not run.</p> : arr(v.reviews).map((rv: any, i) => (
            <div key={i} style={{ marginBottom: 20 }}>
              <div className="row">
                <strong>{rv.role === "reproduce" ? "Does it work?" : rv.role === "refute" ? "Can we break it?" : clean(rv.role)}</strong>
                <span className="meta mono">{clean(rv.role)}</span>
                <Status s={rv.verdict ?? "inconclusive"} glyph={rv.verdict === "pass" ? "◐" : undefined} tone={rv.verdict === "pass" ? "info" : undefined} label={`model review: ${clean(rv.verdict ?? "inconclusive")}`} />
                {truthy(rv.fake) ? <span className="tag">mocked</span> : null}
              </div>
              <Untrusted caption={truthy(rv.fake) ? "untrusted model text · scripted by fake inference" : "untrusted model text"}>{rv.summary ?? ""}</Untrusted>
              {arr(rv.concerns).length ? <Untrusted caption="concerns">{arr(rv.concerns).map((x) => clean(x)).join("\n")}</Untrusted> : <p className="small muted" style={{ marginTop: 6 }}>No concerns raised.</p>}
              {rv.test_report ? <p className="small">Test report <Digest d={rv.test_report} link /></p> : null}
            </div>
          ))}
        </Fold>
        <Fold title="Trusted assumptions" meta={`${arr(v.assumptions).length} · outside verified boundary`}>
          <ul className="list">{arr(v.assumptions).map((a, i) => <li key={i}><Status s="none" glyph="◇" label="outside verified boundary" /><div>{clean(a)}</div></li>)}</ul>
        </Fold>
        <Fold title="Existing jobs" meta={pv.error ? "preview failed" : pv.data ? `${arr(pv.data).length} unfinished · all stay pinned` : "checking…"} attention={!!pv.error}>
          <ErrorBox error={pv.error} />
          {!pv.data ? null : arr(pv.data).length === 0 ? <p className="muted">No unfinished jobs.</p> : (
            <table>
              <thead><tr><th scope="col">Job</th><th scope="col">Status</th><th scope="col">Runs on</th><th scope="col">If activated</th></tr></thead>
              <tbody>
                {arr(pv.data).map((j: any) => (
                  <tr key={clean(j.job)}>
                    <th scope="row"><a href={`#/jobs/${encodeURIComponent(j.job)}`}>{kindName(j.kind)}</a><div className="meta mono">{clean(j.job)}</div></th>
                    <td><Status s={j.status} /></td>
                    <td><Digest d={j.pinned} link="release" copy={false} /></td>
                    <td className="small">{clean(j.disposition)}{arr(j.reasons).length ? <div className="muted">{arr(j.reasons).map((x) => clean(x)).join("; ")}</div> : null}</td>
                  </tr>
                ))}
              </tbody>
            </table>
          )}
        </Fold>
        <Fold title="Exact IDs" meta="release, payload, source, build, contract, lineage">
          <Facts rows={[
            ["Release", <span className="mono wrap">{clean(r.digest ?? digest)}</span>],
            ["Payload", <span className="mono wrap">{clean(r.payload)}</span>],
            ["Source", <Digest d={r.source} link what="source" />],
            ["Build", b?.binary_digest ? <Digest d={b.binary_digest} link what="build" /> : <span className="muted">unknown</span>],
            ["Contract", <Digest d={r.contract} what="contract" />],
            ["Built on", <Digest d={r.parent} link="release" />],
            ["Produced by", <Digest d={r.producer} link="release" />],
            ["Evidence job", r.evidence_job ? <a href={`#/jobs/${encodeURIComponent(r.evidence_job)}`}>{clean(r.evidence_job)}</a> : "none"],
          ]} />
        </Fold>
        <Fold title="Workflows" meta={arr(r.workflows).map((w: any) => `${kindName(w.kind)} (${arr(w.steps).length} steps, up to ${clean(w.max_parallel)} at once)`).join(" · ")}>
          {arr(r.workflows).map((w: any) => (
            <div key={clean(w.kind)} style={{ marginBottom: 20 }}>
              <h3>{kindName(w.kind)} <span className="meta mono" style={{ fontWeight: 400 }}>{clean(w.kind)}</span></h3>
              <table>
                <thead><tr><th scope="col">Step</th><th scope="col">Role</th><th scope="col">Waits for</th><th scope="col">Uses</th></tr></thead>
                <tbody>
                  {arr(w.steps).map((s: any) => (
                    <tr key={clean(s.id)}>
                      <th scope="row">{clean(s.id)}</th><td className="small">{clean(s.role)}</td>
                      <td className="small">{arr(s.after).map((x) => clean(x)).join(", ") || "—"}</td>
                      <td className="small">{arr(s.inputs).map((i: any) => `${clean(i.name)} ← ${i.source?.type === "step_output" ? clean(i.source.step) : "job input"}`).join("; ") || "—"}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
          ))}
        </Fold>
        <Fold title="Approvals and activations" meta={`${arr(v.approvals).length} approval${arr(v.approvals).length === 1 ? "" : "s"} · ${arr(v.activations).length} activation${arr(v.activations).length === 1 ? "" : "s"}`}>
          {arr(v.approvals).length === 0 ? <p className="muted">No approvals recorded.</p> : (
            <ul className="list">
              {arr(v.approvals).map((a: any) => (
                <li key={clean(a.id)}>
                  <div className="row" style={{ justifyContent: "space-between" }}>
                    <span><strong className="mono">{clean(a.id)}</strong> · base <Digest d={a.expected_base} link="release" copy={false} /> · by {clean(a.operator)} · tick {clean(a.at)}</span>
                    {a.revoked ? <Status s="revoked" /> : <Status s="ok" label="valid" />}
                  </div>
                  <div style={{ marginTop: 8 }}>
                    {/* Stays mounted after revoking so its result (and focus) survive the row's state change. */}
                    <Confirm label="Revoke" danger heading={`Revoke approval ${clean(a.id)}?`} action="Revoke approval" disabled={!!a.revoked} why={a.revoked ? "Already revoked." : undefined}
                      details={<p className="small">This stops the approval from being used again. It doesn’t undo an activation that already happened.</p>}
                      onConfirm={() => post(`/api/approvals/${encodeURIComponent(a.id)}/revoke`, { command_id: commandId() }).then(() => { reload(); return "Approval revoked."; })} />
                  </div>
                </li>
              ))}
            </ul>
          )}
          {arr(v.activations).length ? (
            <ul className="small" style={{ marginTop: 12 }}>
              {arr(v.activations).map((a: any, i) => <li key={i}>Activated at tick {clean(a.at)} replacing <Digest d={a.base} link="release" copy={false} />, approval {clean(a.approval ?? "none")}</li>)}
            </ul>
          ) : null}
        </Fold>
      </div>
      <p className="small muted" style={{ marginTop: 24 }}>There is no single “verified” verdict: each line above is a separate fact with its own label. <a href="#/assurance">What the labels mean</a>.</p>
    </>
  );
}

