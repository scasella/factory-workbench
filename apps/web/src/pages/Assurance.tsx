import { clean, pretty } from "../api.ts";
import { arr, ErrorBox, Fold, Loading, Page, Section, Status, Untrusted, usePoll } from "../ui.tsx";

const LEGEND: [string, string, string, string][] = [
  ["✓", "ok", "proof replay passed", "A Lean proof of the stated theorem was re-checked from scratch (leanchecker --fresh)."],
  ["✓", "ok", "runtime guard checked", "Checked by host code while running, e.g. comparing protected components to their setup identities. Not a proof."],
  ["✓", "ok", "integration test passed", "An operator-owned test suite passed against the built artifact."],
  ["◐", "info", "model review: pass", "A model judged it acceptable. An opinion, not a proof."],
  ["?", "warn", "inconclusive", "There is evidence, but it doesn’t settle the question either way."],
  ["–", "muted", "not run", "No evidence was produced."],
  ["◇", "muted", "outside verified boundary", "Assumed, not checked by anything in this system."],
];

function proofStatus(doc: any, id: string, theorems: string[]): { label: string; s: string; glyph?: string; detail?: string } {
  if (!doc) return { label: "not run", s: "not_run" };
  const candidates: any[] = [];
  if (doc[id] !== undefined) candidates.push(doc[id]);
  for (const key of ["contracts", "kernel", "results", "theorems"]) {
    const v = doc[key];
    if (v && !Array.isArray(v) && typeof v === "object" && v[id] !== undefined) candidates.push(v[id]);
    if (Array.isArray(v)) for (const e of v) if (e && (e.id === id || theorems.includes(e.name) || theorems.includes(e.theorem))) candidates.push(e);
  }
  if (!candidates.length) return { label: "not run", s: "not_run" };
  const c = candidates[0];
  const raw = typeof c === "string" || typeof c === "boolean" ? c : c.status ?? c.outcome ?? c.ok ?? c.replay;
  const ok = raw === true || raw === "pass" || raw === "ok" || raw === "passed" || raw === "proved" || raw === "replayed";
  if (ok) return { label: "proof replay passed", s: "ok", detail: typeof c === "object" ? pretty(c) : undefined };
  if (raw === "inconclusive") return { label: "inconclusive", s: "inconclusive" };
  return { label: `proof status: ${clean(String(raw ?? "unknown"))}`, s: "failed", detail: typeof c === "object" ? pretty(c) : undefined };
}

function scopeLabel(s: unknown): string {
  return s === "finite-kernel-reduced" ? "finite (kernel-reduced)" : s === "general" ? "general" : clean(s) || "unknown";
}

export function Assurance() {
  const { data, error } = usePoll<any>("/api/assurance", 10000);
  if (!data) return <><Page title="What’s checked, and how" /><ErrorBox error={error} />{!error && <Loading what="assurance" />}</>;
  const c = data.contracts;
  const trust = arr(data.trust);
  return (
    <>
      <Page title="What’s checked, and how">
        <p className="lede" style={{ fontSize: 15 }}>Assurance here is a set of separate facts, each with its own label. There is no single “formally verified” status.</p>
      </Page>
      <ErrorBox error={error} />

      <Section title="Labels">
        <dl className="evidence">
          {LEGEND.map(([g, tone, l, m]) => (
            <div key={l}><dt><Status s={tone === "ok" ? "ok" : "none"} glyph={g} tone={tone as any} label={l} /></dt><dd className="small muted">{m}</dd></div>
          ))}
        </dl>
      </Section>

      <Section title="Core guarantees (K01–K12)">
        <p className="small muted">Proved in Lean about the kernel that actually decides every command.</p>
        {!c ? <p className="muted">Contracts file not available.</p> : (
          <div className="scroll" role="region" aria-label="Core guarantees" tabIndex={0}>
            <table>
              <thead><tr><th scope="col">Id</th><th scope="col">Guarantee</th><th scope="col">Status</th></tr></thead>
              <tbody>
                {arr(c.kernel).map((k: any) => {
                  const ps = proofStatus(data.kernel_proofs, String(k.id), arr(k.theorems));
                  return (
                    <tr key={clean(k.id)}>
                      <th scope="row" className="mono">{clean(k.id)}</th>
                      <td>
                        {clean(k.title)}
                        <details className="inline"><summary>definition and theorems</summary>
                          <p className="small mono wrap" style={{ margin: "6px 0" }}>{clean(k.definition)}</p>
                          <p className="small mono">{arr(k.theorems).map((x) => clean(x)).join(", ")}</p>
                          {ps.detail ? <Untrusted caption="proof-status entry">{ps.detail}</Untrusted> : null}
                        </details>
                      </td>
                      <td><Status s={ps.s} label={ps.label} /></td>
                    </tr>
                  );
                })}
              </tbody>
            </table>
          </div>
        )}
      </Section>

      <Section title="Package checks (P01–P05)">
        <p className="small muted">Checked for every candidate release by the protected prove step. Each release page shows its own results.</p>
        {c ? (
          <div className="scroll" role="region" aria-label="Package checks" tabIndex={0}>
            <table>
              <thead><tr><th scope="col">Id</th><th scope="col">Statement</th><th scope="col">Scope</th><th scope="col">Required</th></tr></thead>
              <tbody>
                {arr(c.package).map((p: any) => (
                  <tr key={clean(p.id)}>
                    <th scope="row" className="mono">{clean(p.id)}</th>
                    <td><code className="wrap">{clean(p.statement)}</code><div className="meta mono">{clean(p.decl)}</div></td>
                    <td className="small">{scopeLabel(p.scope)}</td>
                    <td className="small">{clean(p.required)}</td>
                  </tr>
                ))}
              </tbody>
            </table>
            <p className="small muted" style={{ marginTop: 12 }}>
              Allowed logic axioms: {arr(c.approved_axioms).map((x) => clean(x)).join(", ") || "none"}. A release needs evidence from: {arr(c.publication_roles).map((x) => clean(x)).join(", ") || "—"}.
            </p>
          </div>
        ) : null}
      </Section>

      <Section title="Trusted assumptions">
        <ul className="list">{arr(data.assumptions).map((a, i) => <li key={i}><Status s="none" glyph="◇" label="outside verified boundary" /><div>{clean(a)}</div></li>)}</ul>
      </Section>

      <div className="section">
        <Fold title="Protected components" meta={`${trust.filter((t: any) => t.ok).length} of ${trust.length} unchanged since setup · checker ${data.verifier?.ok ? "available" : "unavailable"}`} attention={trust.some((t: any) => !t.ok) || !data.verifier?.ok}>
          <p className="small muted">Each match is a runtime guard checked by host code against identities recorded at setup. {clean(data.verifier?.detail)}</p>
          <table>
            <thead><tr><th scope="col">Component</th><th scope="col">State</th><th scope="col">Detail</th></tr></thead>
            <tbody>
              {trust.map((t: any) => (
                <tr key={clean(t.id)}>
                  <th scope="row" className="mono">{clean(t.id)}</th>
                  <td><Status s={t.ok ? "ok" : "failed"} glyph={t.ok ? "✓" : "⚠"} label={t.ok ? "runtime guard checked: matches" : "changed since setup"} /></td>
                  <td><code className="wrap small">{clean(t.detail)}</code></td>
                </tr>
              ))}
            </tbody>
          </table>
        </Fold>
        <Fold title="Kernel proof status" meta="raw document">
          {data.kernel_proofs ? <Untrusted caption="docs/proof-status.json">{pretty(data.kernel_proofs)}</Untrusted> : <p><Status s="not_run" /> Not available.</p>}
        </Fold>
        <Fold title="Test results" meta="raw document">
          {data.tests ? <Untrusted caption="docs/test-results.json">{pretty(data.tests)}</Untrusted> : <p><Status s="not_run" /> Not available.</p>}
        </Fold>
      </div>
    </>
  );
}
