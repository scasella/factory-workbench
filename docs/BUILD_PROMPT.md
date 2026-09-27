# Coding-agent handoff

Read `SPEC.md` completely, then build the specified Factory Workbench in a new repository. `SPEC.md` is the source of truth. It is a proposed design, not a claim that implementation, proofs, or runtime checks already exist.

## The outcome

Deliver a running local workbench that executes durable reviewed jobs, uses Codex CLI for every real LLM call, and builds and activates its own executable orchestration successors under a protected, source-connected verification and approval process.

The mandatory demonstration is P0 → P1 → P2: serial independent reviews become parallel while both gates remain mandatory; then the upgraded product builds a source-level planner improvement with a general equivalence proof. Show old jobs pinned, an eligible paused audit job explicitly migrated, crash recovery, stale-result rejection, and a failed attempt to remove refutation.

## Start here

1. Implement M0 from §20. Record tool versions and test the real environment; do not guess CLI flags or silently loosen isolation.
2. Establish the actual executable Lean transition boundary early. Implement M1 before building a separate workflow engine in TypeScript.
3. Continue through M2–M6, maintaining passing tests and an explicit requirement-status ledger. Build the UI after the lifecycle and persistence paths work.

The documented noninteractive command is `codex exec`, not `codex --exec`. Keep the configured executable/argument prefix and startup checks specified in §10. Never replace the required CLI path with an SDK or direct inference API.

## Constraints you must preserve

- The Lean definitions used for proofs must be on the real runtime admission path. No parallel TS authority or unused formal model.
- Candidate packages may change orchestration source, prompts, and additive tests. They cannot modify the protected kernel, proof targets, verifier, fixed test suite, build recipe, credentials, or release gate.
- Codex v1 is a constrained structured proposal/review process. Candidate code and proof compilation run separately, without its credentials. Do not enable an unrestricted nested tool loop for convenience.
- Persist accepted commands/results and committed effect intents. Reconcile process identity; do not recover by replaying all LLM calls.
- Bind code, proof, tests, reviews, migrations, and approvals to the right immutable digests. A model-supplied success flag is never a verifier attestation.
- New default versions do not alter existing jobs. Migration is explicit, quiescent, checked, and revision-bound; completed evidence keeps its original provenance.
- Missing tools, failed proofs, timeouts, and inconclusive reviews cannot be turned into a release-ready status. Human approval cannot override mandatory failed gates.

## During implementation

Treat concrete design choices in the spec as settled. Resolve incidental details with small recorded decisions rather than redesigning the product. Record contradictions or environment blockers in `OPEN-ITEMS.md` with their exact impact. Preserve the protected properties while addressing them.

Implement real behavior rather than placeholder verifiers, canned live demos, or functions returning `true`. A deterministic fake Codex adapter is required for integration testing and must be clearly labeled; it does not mock Lean, persistence, isolation, or activation. Live inference results must be reported only when actually run.

Create the documentation and evidence artifacts in §21. Use the A01–A30 identifiers in executable tests and the final status report. Record which tests ran, which proofs replayed, and which remain blocked. Do not represent unexecuted tests as passing.

## Final handoff

Provide the runnable repository, exact setup/run/check/demo commands, pinned dependencies, proof sources and replay scripts, UI and CLI, recovery procedures, `ASSURANCE.md`, `DEMO-RESULTS.md`, and `OPEN-ITEMS.md`.

Summarize what actually works, which formal statements were checked, what remains trusted, whether live Codex was exercised, and every material outstanding acceptance failure. The criterion is controlled self-improvement of real executable orchestration—not the volume of generated code or proofs.
