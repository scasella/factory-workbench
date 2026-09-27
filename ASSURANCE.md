# Assurance

This document separates what is **proved** (Lean theorems about the executed kernel definitions,
independently replayed), what is **runtime-checked** (guards and fixed-harness observations), what is
**tested**, what is **model judgment**, and what is **assumed**. Nothing here says the system as a
whole is "formally verified". Current machine-generated status: `docs/proof-status.json` (kernel
theorems) and `docs/test-results.json` (acceptance ledger), both produced by `scripts/check-all`.

## Identities

| Item | Value / where |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.34.1` (`protected/lean/lean-toolchain`) |
| Independent checker | `leanchecker --fresh` from the same toolchain (re-checks proof objects of the module and every import from `Init` with the kernel type checker; not a different logic) |
| Approved axioms | `propext`, `Classical.choice`, `Quot.sound` (`protected/contracts.json`) |
| Kernel executable | `factory-kernel` built from `protected/lean` (`Factory.Main`); installed copy digest-pinned at bootstrap (`<state>/kernel/factory-kernel`, meta `kernel_digest`), re-checked before every spawn |
| Verifier image | `factory-verifier:dev`, id in `toolchains.lock.json`; labels carry `core-digest`, `contract-digest`, `harness-digest` of the protected sources baked in |
| Contract identity | `contract_digest` = digest(contracts.json, Types.lean, Workflow.lean, PackageContracts.lean); stored in kernel state at bootstrap and required on build/prove evidence and approvals |

## Kernel properties (K01–K12)

All statements live in `protected/lean/Factory/Contracts.lean` and quantify over **every**
authenticated envelope and **arbitrary** finite states — no bounded model checking. `Safe` is
`K01 ∧ K02 ∧ K03 ∧ K05 ∧ K06 ∧ K07 ∧ K10`, stated over the *same Boolean functions* the runtime
invariant checker executes (`Factory.Check`), so the runtime oracle and the theorem agree by
construction. Proofs: `Factory/Proofs.lean` (+ `ProofLemmas`, `ProofJob`, `ProofState`,
`ProofHandlers`, `ProofTransitions`). Runtime callsite for all of them: `Factory.apply`, executed by
`factory-kernel --serve`, called only from `Coordinator.submit` (`apps/control/coordinator.ts`) inside
`BEGIN IMMEDIATE`; the coordinator persists exactly the returned transition.

| ID | Definition (Contracts.lean) | Theorems (Proofs.lean) | Tests | Notes / boundary |
|---|---|---|---|---|
| K01 well-formed state | `K01` (idsUnique, releasesOk, changesOk, jobPinned, attemptsConsistent, acceptedConsistent) | `initial_safe`, `apply_preserves`, `reachable_safe`, `steps_safe` | A24 (kernel `invariants` op after every generated step), startup check in `Workbench.recover` | Well-typedness of the decoded state is the codec's job (audited, not proved) |
| K02 single accepted completion | `K02` (step-ID `Nodup` per job) + `AcceptedStable` | `k02_stable`, `k02_trace`, `k02_reachable`, `k02_trace_reachable` | A04, A05, A24 oracle | Retries may compute repeatedly; only acceptance is unique |
| K03 fenced results | `K03` (acceptedAt < leaseDeadline) + `FencedAcceptance` | `k03_fenced`, `k03_reachable` | A03, A07, A08, A23 | Acceptance-time epoch/gen/lease are recorded and never rewritten (incl. migration) |
| K04 dependency/input safety | `DependencySafe` (explicit: every ordering edge and semantic producer is `StepDone`; per-index input = job input or the producer's accepted result digest) | `k04_dependency`, `k04_reachable` | A15, A24 | **Restated during the build** (strengthened): the first draft referred to the kernel's own `prereqsDone`/`bindInputs`, so weakening those would have weakened the theorem |
| K05 cancellation | `K05` (terminal ⇒ no live authority) + `CancellationFinal` | `k05_final`, `k05_reachable` | A06 (kernel + container), A24 oracle | Physical OS start is not atomic with SQLite; the supervisor terminates and the kernel rejects late results |
| K06 required evidence | `K06` (`releasesEvidenced`) + `PublicationGated` (explicit `RequiredEvidence`: passing build/prove/reproduce/refute evidence whose roles come from the pinned workflow; build bound to the job subject; prove/reproduce/refute bound to the payload; contract ids; covers `publishRelease` **and** `publishReport`) | `k06_gated`, `k06_reachable` | A01, A09, A10, demo bypass, mutant `publish_without_refutation` | **Restated during the build** (strengthened) after a kernel mutant that checked `.reproduce` twice instead of `.refute` still compiled against the proofs, because the first draft was stated via the kernel's own `gatesPass`. Proves the *gate*, not the truth of model judgments |
| K07 release binding | `K07` (`activationsApproved`) + `ActivationBound` | `k07_bound`, `k07_reachable` | A13, A29 | Operator identity is the authenticated actor; there is no cryptographic signature (v1 local channel) |
| K08 version pinning | `PinningPreserved` | `k08_pinning`, `k08_reachable` (+ `k08_nonmigrate_jobs`, `k08_migrate_others`, `k08_activation`) | A14, A17, A18, mutant `activation_mutates_pinned_jobs` | **Statement corrected** during the build: the first draft's quantifier scope made it false for every migration (found by the proof effort, see `protected/lean/PROOF-NOTES.md`); the corrected statement also covers jobs not named by a migration |
| K09 migration preservation | `MigrationPreserving` | `k09_migration`, `k09_reachable` | A15, A16, mutant `drop_evidence_on_migration` | Concrete `canMigrateB` check runs on the exact state in the same transition |
| K10 resource authority | `K10` (`resourcesOk`: budgets, class slots, per-job maxParallel) | via `apply_preserves` | A28, A24 | Token/monetary limits are not modelled |
| K11 replay determinism | `Factory.replay` | `k11_replay_nil/cons_ok/cons_err/append/reachable/deterministic` | A22, `journal verify` | Determinism is definitional (pure function); the theorems make journal semantics explicit. **Not** a filesystem durability theorem |
| K12 effect causality | `EffectCausality` | `k12_causality`, `k12_reachable` | A23, A24 oracle | The host enforces commit-before-execute (outbox written in the same transaction) |

### Statement audit: remaining implementation-referential definitions

After the K04/K06 restatements, the proof effort audited every contract for the same flaw (full list
and proposed explicit restatements in `protected/lean/PROOF-NOTES.md`). We distinguish:

- **Definitional references** — functions that *are* the property's definition and are protected
  contract material: `wellFormedWorkflow`/`exportsOk`/`requiredRoles` (fixed well-formedness),
  `Role.resource` (role→resource table), `stepStatusOf`, `JobStatus.terminal`, `AttemptStatus.live`.
  Changing them is a contract change, visible in the contract/core digests.
- **Decision-function references** (the flaw class) that remain: the *state-level* K06 invariant
  `releasesEvidenced` still goes through `gatesPass`; K10's `resourcesOk` counts via `liveOfClass`;
  several predicates read state through lookup helpers (`findJob?`, `findStep?`, `findAttempt?`,
  `workflowOf`), so a mutant lookup could make a statement vacuous. The *transition-level* K04/K06 are
  explicit and mutation-verified; the listed items are documented, not yet restated (OPEN-ITEMS 21).

Kernel mutants (§9.4) are in `protected/tests/mutation/kernel-mutants.test.ts`; results in
`docs/kernel-mutants.json` record, per mutant, whether the targeted test killed it and whether the
kernel proofs stop compiling against it (a proof kill). A compile error is never counted as a
semantic kill.

## Package obligations (P01–P05)

Frozen statement types: `protected/lean/Factory/PackageContracts.lean`. The fixed verifier generates a
**trusted statement bridge** (`protected/verifier/bridge.ts`) that re-states each obligation with the
frozen type against a fully qualified candidate declaration (`_root_.FactoryPkg.pNN`), audits the
axiom closure of every bridge theorem (strict parser, approved set only), and replays the bridge with
`leanchecker --fresh` in a network-less container. The predecessor (`FactoryPrev`) is the **actual**
previous release's source, supplied read-only by the verifier (mechanical `FactoryPkg`→`FactoryPrev`
rename; recorded decision, trusted transform).

| ID | Statement | Scope | Required |
|---|---|---|---|
| P01 | `exportsOk workflows = true` (fixed well-formedness, mandatory roles, subject/independence bindings) | finite, kernel-reduced (`decide`) | always |
| P02 | `∀ v, PlanOk v (plan v)` (order-preserving sublist of ready, no duplicates, ≤ slots, nonvacuous) | **general** | always |
| P03 | `gatesRetained prev new = true` | finite, kernel-reduced | always |
| P04 | `exportsOrderingOnlyCompatible prev new` (ordering-only) or `new = prev` (planner-only) | finite, kernel-reduced | per `migration.json` |
| P05 | `∀ v, plan v = prevPlan v` | **general** | recipe `planner_equivalent` (P2) |

Source-to-binary binding: the harness builds the package binary with a fixed recipe; the bridge also
proves, by kernel reduction, that the proof-bound `FactoryPkg.workflows` **equals** the export the
built binary printed and that `FactoryPkg.plan` agrees with the binary's output on every fixture
view. A replaced/`implemented_by` planner, a lying export, or a source/receipt mismatch fails
(A12). Protected tests then execute the binary on 180+ deterministic views plus negative controls,
checked by the kernel's `planOkB` (reproduction stage; exit status is never supplied by a model).

## Runtime checks (not proofs)

- Coordinator: strict JSON (duplicate keys, extra fields, numbers rejected at the kernel boundary),
  command-ID idempotency/conflict detection, size bounds, kernel digest check, kernel timeout ⇒
  mutation disabled.
- Engine/supervisor: planner output checked by kernel `check_plan` before any start; the kernel
  re-checks every start. Container labels + deterministic names for reconciliation.
- Verifier: lint (forbidden tokens/attributes/imports/namespaces), exact-preimage materializer and
  path allowlist, export decoding + `exportsOk`, fixture plan checks, axiom audit, replay exit codes.
- Activation: bundle re-verification (every file digest, binary = payload) before the kernel CAS.
- Startup: state/journal digest agreement, kernel invariant diagnostics, genesis bundle integrity.

## Model judgments

Reproduction/refutation/summary verdicts are model judgments recorded as `model review: pass|fail|inconclusive`.
A `fail` fails the job; `inconclusive` blocks it; neither is retried until it says pass. Distinct
invocations with separate contexts (refutation never sees the reproduction verdict) are enforced;
statistical independence of reasoning is **not** claimed. In the delivered runs inference was
**mocked** by the deterministic fake Codex CLI.

## Trusted base (outside the verified boundary)

Lean kernel/checker/compiler/runtime; the codec (`Factory.Json`, `Factory.Codec`) and executable
wrapper (`Factory.Main`); the harness package wrapper (`FactoryExport.lean`); the namespace-rename
transform for the predecessor; SHA-256; SQLite transaction durability; Node.js; the coordinator's
persistence of kernel outputs; Docker/Linux isolation and the host OS/hardware; the authenticity of
supervisor observations (container ids, exit codes, monotonic clock ticks); the operator's
authentication (local token, no signatures); the Codex CLI's enforcement of its own tool profile
(currently **not** enforceable for `unified_exec` in 0.155.1 — live mode blocked).

## Explicit exclusions

No proof of LLM correctness, of liveness/deadlock freedom, of exactly-once external execution, of
container isolation, of the compiler, or of the TypeScript host. A24 is a property test over random
traces, not a proof; A25 is a nonvacuity test, not a liveness proof. See `OPEN-ITEMS.md` for
incomplete items and their consequences.
