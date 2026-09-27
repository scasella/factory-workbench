import { useState } from "react";
import { clean, isDigest, pretty, truthy } from "../api.ts";
import { arr, ErrorBox, Facts, FullDigest, Loading, Page, Untrusted, usePoll } from "../ui.tsx";
import { JournalTable } from "./Job.tsx";

export function ArtifactView({ digest }: { digest: string }) {
  const ok = isDigest(digest);
  const { data, error } = usePoll<any>(ok ? `/api/artifacts/${digest}` : null, 0);
  return (
    <>
      <Page title={`Artifact ${clean(digest).slice(0, 8)}`} back={["#/", "Home"]}>
        <div style={{ marginTop: 12 }}><FullDigest d={digest} what="artifact" /></div>
      </Page>
      {!ok ? <ErrorBox error={{ code: "BAD_DIGEST", message: "not a digest" }} /> : null}
      <ErrorBox error={error} />
      {ok && !data && !error ? <Loading what="artifact" /> : null}
      {data ? (
        <div className="section">
          <Facts rows={[["Size", `${clean(data.size)} bytes`], ["Kind", data.binary ? "binary" : data.json !== undefined ? "JSON" : "text"]]} />
          {data.binary ? <p style={{ marginTop: 16 }}>Binary artifact — not shown. Export it with the CLI.</p>
            : <Untrusted caption="untrusted content · shown as plain text; links and markup are not rendered">{data.json !== undefined ? pretty(data.json) : data.text ?? ""}</Untrusted>}
        </div>
      ) : null}
    </>
  );
}

export function Journal() {
  const [after, setAfter] = useState(0);
  const [history, setHistory] = useState<number[]>([]);
  const { data, error } = usePoll<any[]>(`/api/journal?after=${after}`, 0);
  const rows = arr(data).map((r: any) => ({ ...r, seq: Number(r.seq), accepted: truthy(r.accepted) }));
  const last = rows.length ? rows[rows.length - 1].seq : after;
  return (
    <>
      <Page title="Journal">
        <p className="lede" style={{ fontSize: 15 }}>Every command the kernel accepted or rejected, in order. Nothing here is ever edited.</p>
      </Page>
      <nav aria-label="Journal pages" className="row" style={{ margin: "28px 0 12px" }}>
        <button type="button" className="btn" disabled={!history.length} onClick={() => { const h = [...history]; setAfter(h.pop() ?? 0); setHistory(h); }}>← Earlier</button>
        <span className="small muted">{rows.length ? `Entries ${rows[0].seq}–${last}` : `After #${after}`}</span>
        <button type="button" className="btn" disabled={rows.length < 500} onClick={() => { setHistory([...history, after]); setAfter(last); }}>Later →</button>
      </nav>
      <ErrorBox error={error} />
      {!data && !error ? <Loading what="journal" /> : <JournalTable rows={rows} />}
    </>
  );
}
