# Notes for coding agents working on this repository

This file is for humans/agents maintaining the workbench itself (a maintenance upgrade), not for the
in-product Codex author. The in-product author's rules are in `orchestration/genesis/prompts/author.md`
and enforced by the materializer, lint and verifier — not by this file.

## Invariants you must not break

- **One authority.** Every state change goes through `Coordinator.submit` → installed Lean kernel
  `apply`. Do not add TypeScript paths that decide success, eligibility, publication or activation.
  The engine only turns committed effect intents into supervised work and reports observations.
- **Proofs are about executed code.** `Factory.apply` (protected/lean/Factory/Kernel.lean) is what the
  `factory-kernel` executable runs; `Factory.Contracts` states K01–K12 over it and over the Boolean
  checkers in `Check.lean`. Never "simplify" a statement in `Contracts.lean`/`PackageContracts.lean` to
  make a proof pass. If a statement is false, the kernel has a bug.
- **Protected vs. evolvable.** Candidate packages may change only `Package.lean`, `Planner.lean`,
  `Proofs.lean`, `prompts/*.md`, `supplemental-tests/*.json`, `migration.json`,
  `package-metadata.json` (`protected/verifier/package-source.ts: checkPackagePath`). Everything else is
  protected and changes only by an external maintenance upgrade (rebuild images, re-bootstrap).
- **Evidence binding.** Receipts come from the fixed verifier's observations; model output never
  selects actor/role/subject/lease; approvals bind the exact release digest and expected base.
- **Fail closed.** Missing tools, failed proofs, timeouts and inconclusive reviews never become
  release-ready. Do not add an "accept anyway" path.

## Workflow

- Node 25 runs `.ts` directly: use only erasable TypeScript syntax and explicit `.ts` import suffixes.
  `npx tsc -p tsconfig.json --noEmit` must stay clean.
- Lean: `cd protected/lean && lake build` (host kernel). Kernel proofs: `node scripts/check-proofs.ts`.
- After changing anything under `protected/` rebuild images (`./scripts/build-images.sh`); existing
  bootstrapped states will (correctly) report verifier drift.
- Tests: `./scripts/check-all` (full), or individual files with
  `node --test --test-concurrency=1 protected/tests/acceptance/<file>.test.ts`. Acceptance tests are
  named `Axx: ...` and feed the ledger in `docs/test-results.json`.
- Never run live Codex inference or read `~/.codex` without explicit operator consent.
