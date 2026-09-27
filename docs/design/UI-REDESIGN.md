# Operator UI redesign — panel synthesis

A five-persona panel reviewed the original UI (screenshots of every page, light and dark, plus source and
SPEC §17): an industrial minimalist, a first-run/onboarding specialist, a high-assurance/safety interface
designer, a developer-tools product designer, and an accessibility/plain-language designer. This document
records what they agreed, where they disagreed, and what was decided.

## Diagnosis (unanimous)

- The UI was honest but built like a spreadsheet: every fact had equal weight (10-column bordered tables,
  a pill on every cell), so nothing stood out.
- Onboarding: a login wall asking to paste a secret from `<stateDir>/operator/token` (placeholder path,
  implementation jargon), nothing in `serve`'s output pointing to it, and sessions lost on each restart.
- Home opened on diagnostics (controller epoch, kernel clock, capacities, isolation, trust anchors) before
  any action. The two actions that matter sat top-right and at the very bottom.
- Release review buried the decision (approve/activate) ~2,700 px down, after ~15 evidence sections.
- Overclaim found: the change page said "Candidate verified: yes". Renamed to "Evaluation passed".
- The mocked-inference disclosure appeared on some pages only; nothing repeated it at the moment of approval.

## Organizing idea

**One calm column. Each page answers "what state is it in, and what do I do next?" in its first screen;
every required fact is still there, one disclosure away, and anything that failed opens itself.**

## Decisions

| Topic | Decision | Why / dissent |
|---|---|---|
| Shell | Top bar: wordmark · Home · Releases · Assurance · Journal. No sidebar. Single reading column (max 880 px; lists 960). | Minimalist + a11y over dev-tools sidebar; four destinations don't need one. |
| Mock disclosure | Thin, non-dismissable strip on every page while inference is fake; `(mocked)` in `document.title`; inline `mocked` tag on every model-authored text; an explicit acknowledgement in the approve step. | Safety red line: never dismissible, never only on one page. Onboarding preferred a header badge; outvoted. |
| Sign-in | `serve` prints a **one-time sign-in link** `http://127.0.0.1:PORT/#login=<nonce>`. Nonce ≠ operator token; 32 random bytes, in memory only (hash), single use, 5 min, dies on restart; new link invalidates the previous. The page strips the fragment with `history.replaceState` before rendering, then POSTs it (CSRF header, Host/Origin checks unchanged) to `/api/session/claim` for the same HttpOnly SameSite=Strict cookie. `workbench login` mints a fresh link (Bearer-authenticated). Paste-token remains the fallback, with the real resolved path. | Fragment never reaches the server or logs; token never in a URL. Residual: link sits in terminal scrollback until used — single use + 5 min bounds it. Auto-open not added (argv exposure). |
| Home | Request box first ("What should the workbench improve?"). Then **Needs you** (releases awaiting approval/activation, failed/paused jobs, pending cleanup), **Changes**, **Jobs** as one-line rows with a quiet second line carrying §17 job fields (pinned release, steps, progress, cleanup, budget, created). "Run an audit" is a small inline disclosure. System facts become one footer sentence linking to Assurance. | All five. |
| Status | Glyph + word, glyph colored, no background pills. Fixed vocabulary: `✓` passed/checked, `✕` failed, `●` running, `○` pending/queued, `‖` paused, `–` not run, `?` inconclusive, `◇` outside verified boundary, `⚠` mocked/integrity. **Model reviews never get ✓** — `◐ model review: pass`. Exact §17 labels kept verbatim. | Safety + minimalist; works in grayscale and forced-colors. |
| Release review | Top: title + state + **decision block** (full release digest grouped in 4s, replaces-active relation, 5-line evidence summary in fixed order, existing-jobs impact sentence always shown, Approve/Activate). Below: disclosures with counts in the summary — proofs, build checks, tests, reviews (untrusted text boxed), assumptions, exact IDs, workflows, approvals history. Any non-pass disclosure opens by default. No roll-up line anywhere. | Safety's Band A/B/C adopted wholesale. |
| Approve / activate | Two separate inline confirm panels (not modals), each restating full digests and effects, requiring the operator to **type the first 8 characters of the release digest**; approve in fake mode also needs "I understand the reviews were scripted" ticked. Confirm button never auto-focused; Esc cancels and returns focus. Panel resets if the active release or approval changes while open. Result persists inline with the approval id. | Safety (8 chars) vs dev-tools (4): 8 chosen — this is the one place friction is the feature. |
| Reject | Not added: the kernel has no reject-release command, and adding one is a kernel/contract change outside a UI redesign. Recorded as an open item. Not approving is the current "reject"; revoking an approval remains. | Safety flagged §17 gap; deferred honestly. |
| Change page | Request as the lede. Lifecycle line `Requested → Written → Checked → Published → Approved → Active` with the one next action. "What changed" as sentences per changed workflow ("refute no longer waits for reproduce → up to 2 at once") plus why-parallel. Candidates: rejected ones show the actual diagnostic, open. Jobs/revisions/digests in "Details". Revise shows remaining budget. | Minimalist + dev-tools. |
| Job page | Header sentence (status, kind, pinned release, tries used). Step list; each step expands to its attempts, each attempt always showing five labelled facts in order: Allowed to run (authorization) · Machine saw (OS observation) · Model call (transport) · Result kept (accepted) · Cleanup. Cancelled banner: "effective now" + cleanup. Migration and live journal as disclosures. | Spec-required separations kept; tables → rows. |
| Words | Plain first, exact term second (mono, muted): e.g. "Checked the change" over `change_evaluate`; "5 of 20 tries". "Release", "approve", "activate" kept (they match the CLI). | a11y panelist's table, applied selectively. |
| Type & color | System UI font; 15 px body / 13 px meta / 12.5 px mono; titles 26/600; sections 13 px letterspaced caps. One accent (ink blue) for action/focus/links only. Status glyph colors are reinforcement. Hairlines, no boxed tables; 8 px spacing grid; 8 px radius on inputs/buttons, 14 px on the composer and decision panel. Light + dark. | Minimalist base, dev-tools tokens. |
| Accessibility | Focus moves to the page `<h1>` on navigation; `document.title` per page; one polite live region announcing state changes only (not counters); `prefers-reduced-motion`; targets ≥ 24 px, primary buttons ≥ 40 px; muted text ≥ 4.5:1; real `<table>` kept for tabular detail (journal, obligations); digests have "Copy" buttons and full values in the DOM. | a11y panelist. |
| Keyboard | `/` focuses the request box; `g h`, `g r`, `g a`, `g j` navigate; `?` shows the list. No command palette (not minimal). | Dev-tools set, trimmed. |

## Review round 2 (panel audited the implementation)

Adopted:
- **Safety:** the Proofs line could read "proof replay passed" while the prove receipt failed. It now shows
  the prove failure first. Other safety fixes:
  - "Replaces" is shown for every non-active release, including rollbacks.
  - Mocked roles are named rather than assumed ("both").
  - Approve and Activate are disabled, with the reason, on an integrity failure; Activate is also disabled
    on an approval/base mismatch.
  - An open confirm resets if the evidence changes.
  - The reject hint appears only where it applies.
  - A disabled Activate is no longer styled as primary.
  - `serve` prints the sign-in link only to a TTY.
- **Accessibility:**
  - Confirm ids use `useId`, so there are no duplicate or broken names.
  - The dark-mode danger button text meets contrast.
  - Links are underlined.
  - Single-key shortcuts can be turned off (WCAG 2.1.4).
  - The copy button no longer uses opacity, and "Copied" is announced.
  - Live regions stay mounted, so result messages are announced.
  - The composer has a 2 px focus ring.
  - Field hints and errors are shown as text.
  - Focus moves once per navigation.
  - Link names carry context, and full digests are exposed as real text.
- **Minimalist:**
  - Shadows are removed from content.
  - The logo is no longer in the accent colour.
  - Disabled primary buttons read as disabled.
  - Font weights are normalised to 400/600.
  - Section labels are sentence case instead of tracked caps.
  - Attention folds use ⚠ plus the words "needs a look" instead of red headings.
  - The shortcut button moved to the footer, and the keyboard hint left the Start button.
  - The mock-banner copy is shorter.

Declined, with reasons:
- *Turn the jobs table into a list.* §17 asks for a "readable table", so it stays a `<table>` styled as
  hairline rows.
- *Fold each evidence line into its own disclosure and delete the detail folds.* The safety panelist
  requires the evidence summary to stay visible, unexpanded, at the moment of decision. The folds below
  hold the detail.
- *Add a Reject button.* The kernel has no reject-release command. This is recorded in OPEN-ITEMS §22,
  and the page says how to reject: leave the release unapproved.
