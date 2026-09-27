# Open items

Each item states its exact consequence for activation or assurance. Status as of 2026-09-26.

## Blockers for live inference

1. **Live Codex mode is blocked: `unified_exec` cannot be disabled in codex-cli 0.155.1.**
   Under the runner-owned profile, `codex features list` reports every forbidden capability `false`
   except `unified_exec`, which stays `true` whether set via `[features] unified_exec = false`,
   `--disable unified_exec`, or `-c features.unified_exec=false` (`--strict-config` confirms all
   profile keys are recognized). §3.2/§10.3 require stopping live execution when the profile cannot be
   enforced, so `workbench doctor` fails `codex.features_disabled`, the engine refuses live
   invocations (`live_blocked`), and `demo --live-codex` exits with a diagnostic instead of
   substituting a canned run.
   *Consequence:* **no live inference was run.** All delivered evidence uses the deterministic fake
   Codex CLI (labeled in every event/artifact). Whether `shell_tool=false` alone removes the exec tool
   can only be established by the consent-gated `doctor --live --consent` smoke test (structured
   response + forbidden shell/subagent requests), which was not run (no operator consent was
   requested/given in this build session, and the operator's personal `~/.codex` credentials were
   deliberately never read or copied).
2. **The LLM runner is a host process, not a container.** The adapter spawns the CLI with an argument
   array, no shell, a minimal environment, a runner-owned `CODEX_HOME` with the security profile, an
   empty workspace and a killable process group; no candidate code ever runs there. §3.2 asks for an
   isolated Linux container for LLM calls. *Consequence:* must be implemented (image with the pinned
   Linux Codex CLI, `CODEX_HOME` mounted, outbound network to the model API only) before live mode is
   enabled, in addition to item 1. Fake-mode runs are unaffected (the fake performs no inference and
   reads no credentials).
3. **Operator-provisioned Codex auth.** Live mode expects `auth.json` in `<state>/operator/codex-home`
   (e.g. `CODEX_HOME=<that dir> codex login`). ChatGPT-mode token refresh behaviour under this layout
   is untested.

## Assurance scope (by design, recorded honestly)

4. **K08 statement was corrected during the build.** The first draft of `PinningPreserved` scoped
   `∀ jid tgt r` outside the `≠ migrateJob` premise, making it false for every accepted migration
   (found by the proof effort with a formal refutation and a concrete kernel trace). The corrected
   statement expresses the intended property and is strictly broader (it adds "a migration does not
   change any other job's pin"). It is proved (`k08_pinning`). See `protected/lean/PROOF-NOTES.md`.
4b. **K04 and K06 statements were strengthened during the build.** Kernel mutation testing showed a
   mutant that checked `.reproduce` twice (instead of `.refute`) in the publication gate still
   compiled against the proofs, because K06 was stated via the kernel's own `gatesPass`; K04 had the
   same shape (`prereqsDone`/`bindInputs`). Both are now explicit and re-proved (`k04_dependency`,
   `k06_gated`); see `docs/kernel-mutants.json` for the proof-kill result.
5. **Codec, executable wrapper, harness wrapper, predecessor-rename transform are trusted**, not proved.
   Consequence: a codec bug could make the kernel act on a different state than the coordinator
   stored; mitigated by strict decoding, canonical re-encoding and journal replay checks, not
   eliminated.
6. **P01/P03/P04 are finite kernel-reduced checks** (`decide`) of fixed Boolean functions on concrete
   exports (labelled `finite (kernel-reduced)`); P02/P05 are general. The general soundness of the
   runtime migration check is kernel theorem K09; prompt-byte identity for migration is a runtime check
   (asset digests), not part of P04.
7. **A24 coverage.** Random traces (40 seeds × ~170 commands, with a valid publication prefix on half
   of them) exercise acceptance of every command kind except `migrate_job`, which needs a paused,
   quiescent job with compatible completed steps and an activated target; migration is covered by
   directed tests (A15/A16), kernel mutants and the K09 proof. Coverage: `docs/a24-coverage.json`.
8. **Model review independence** is process/context separation with recorded provenance, not
   statistical independence (§12.2).

## Engineering limitations

9. **Controller lock** is a pid file (`controller.lock`) with liveness check, not an OS advisory lock;
   a reused pid of an unrelated live process would block startup (fails safe, operator removes it).
10. **Planner runtime** uses a long-lived `docker run -i` per release. Killing the CLI closes stdin and
    the planner exits; containers are additionally reconciled by label at startup.
11. **Operator authentication** is a single local bearer token / session cookie: no expiry, rotation or
    logout route (sessions are in memory and end when `serve` restarts; `serve`/`workbench login` print a
    one-time sign-in link whose nonce lives only in the URL fragment, is single-use and expires in 5 min); there are no cryptographic approval signatures (a local authenticated channel, per
    §13.1 "do not add decorative signatures").
12. **Budgets** limit attempts and revisions; optional reported-token limits (§11) are not implemented.
13. **Garbage collection** only removes abandoned temp blobs (`BlobStore.collectTemp`), and nothing
    schedules it; referenced blobs/releases are never deleted.
14. **Base image provenance.** `factory-lean-base` was built from `debian:bookworm-slim` by tag; the
    Dockerfile now pins `@sha256:3783cc01…` for rebuilds, and the built image id is locked in
    `toolchains.lock.json`.
15. **Proof checking cost.** `leanchecker --fresh` re-checks from `Init` (~40 s per candidate on the
    build host), dominating evaluation time.
16. **`demo --live-codex`** only performs the doctor gate; an automated live script beyond that is not
    written (it would be the fake-LLM demo driver with `codex.mode=live`), because live mode is blocked.
17. **UI**: activation uses the newest unrevoked approval for a release (no picker); no logout.
18. **Windows** is out of scope (§0.3).
19. **Progress vs. health.** Process health comes from supervisor heartbeats and container state;
    last-output/progress tracking (`attempt_obs.last_output`) is not populated and the five-minute
    idle warning (§11) is not implemented. Consequence: a silent-but-alive attempt is shown as
    running until its wall timeout or cancellation.
20. **Context size (§10.6).** Author/review prompts carry whole package files and receipts; there is no
    explicit "insufficient context → split/report" check before invocation (packages are small; the
    adapter bounds output, not input). Must be added before large packages or live inference.
21. **Remaining implementation-referential contract definitions** (audit in `protected/lean/PROOF-NOTES.md`):
    state-level K06 via `gatesPass`, K10 via `liveOfClass`, and lookups via `findJob?`/`findStep?`/
    `findAttempt?`/`workflowOf` inside several predicates. Consequence: a mutation of those helpers
    could make the corresponding statement weaker without breaking its proof; the transition-level
    K04/K06 and the directed tests/mutants cover the most important cases. Proposed explicit
    restatements are estimated as modest effort.
22. **No "reject release" control (§17 asks for approve/reject/activate).** The kernel has no
    reject-release command, and adding one is a kernel/contract change, so the redesigned release page
    offers approve and activate only and says so ("leave it unapproved — nothing runs an unapproved
    release"). Revoking an approval is available.
23. **Supplemental tests are not reported separately (§17 "protected versus supplemental").** Candidate
    supplemental planner views (`supplemental-tests/views.json`) run inside the protected suite; the
    verifier's receipt does not break them out, and the release page states "not reported separately".
