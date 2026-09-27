# Operator walkthrough video

| File | What |
|---|---|
| `factory-workbench-demo.mp4` | 2:34, 1920×1080, 30 fps, H.264 + silent AAC track, captions burned in |
| `factory-workbench-demo.srt` | the same captions as a subtitle track (for platforms and screen readers) |
| `factory-workbench-demo-chapters.txt` | chapter timestamps |
| `factory-workbench-demo-poster.png` | thumbnail frame (both reviews running in parallel under P1) |

## Suggested publishing copy

**Title:** Factory Workbench: a workbench that builds, proves and activates its own orchestration upgrades

**Description:**
Factory Workbench runs durable, reviewed jobs and can improve the orchestration code it uses to run them.
In this walkthrough the operator signs in with a one-time link and asks for a change in plain language. The running release (P0) authors and
evaluates its successor (P1). The first candidate has a real proof error, the fixed verifier rejects it, and a
repair is recorded as a new revision. The repaired candidate passes a sandboxed build, Lean proof replay,
protected tests and two independent reviews. The operator reviews the exact release, approves its digest
(typing its first eight characters and acknowledging that the reviews were mocked), and activates it. Existing jobs stay pinned to P0, and new jobs run with the reviews in parallel.

Recorded from the real running system. Model inference is mocked by a deterministic fake Codex CLI, and every
model output is labelled as mocked on screen.

**Chapters:**
```
0:00 Introduction
0:06 One-click sign-in
0:08 The workbench
0:20 A durable, reviewed job
0:41 Improve this workbench
0:50 P0 builds and verifies its successor
1:06 Release review
1:33 Approval and activation
1:55 After activation: pinning and parallel reviews
2:25 Summary
```

## Disclosures (keep these with the video)

- **Real:** the Lean 4 kernel admitting every state change, the SQLite journal, sandboxed (network-less)
  container builds, the proof bridge, axiom audit, `leanchecker --fresh` replay, protected tests, the
  publication gate, approval and activation. Nothing on screen was staged or edited into the UI.
- **Mocked:** all model output (author proposals, reviews, summaries) comes from the deterministic fake
  Codex CLI (`packages/codex-adapter/fake-codex.ts`). The UI's persistent banner and a corner tag in the video say so.
  Live Codex inference was not used (it is blocked in this environment; see `OPEN-ITEMS.md`).
- **Recording aids:**
  - The fake model is given a fixed 6-second response time (`FAKE_CODEX_LATENCY_MS=6000`) so running work
    stays on screen long enough to see.
  - Segments marked "N× TIME-LAPSE" are sped up.
  - The mouse pointer is an overlay drawn by the recorder.
  - The recorder adds blank space below each page so sections can scroll clear of the captions.
  - The operator signs in through a real one-time sign-in link (minted the way `workbench login` does).
    Headless frames have no address bar, so the link's nonce never appears on screen.
- The flow, digests and outcomes are specific to this recording; a re-recording produces different digests.

## Reproduce

Requires the built images and toolchain from the main README, plus Python 3 with Pillow ≥ 10.1
(`pip install pillow`) and `ffmpeg` on PATH for the editing step. Captions use Avenir Next on macOS;
elsewhere set `VIDEO_FONT=/path/to/font.ttf`.

```bash
npm install --prefix scripts/demo-video && npx --prefix scripts/demo-video playwright install chromium
```

```bash
node scripts/demo-video/record.ts
```

```bash
python3 scripts/demo-video/edit.py
```

`record.ts` bootstraps a fresh state in `.video-build/` (off camera), starts the real server, drives the
UI and captures frames plus a timeline of captions and speeds. `edit.py` renders the MP4, SRT, and chapters.
