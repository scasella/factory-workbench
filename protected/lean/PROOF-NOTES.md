# Proof notes: kernel safety proofs

All theorems are about the executed kernel (`Factory.apply`, `Factory.replay`) and the
protected statements in `Factory/Contracts.lean`. None of those statements, and none of the
definitions in `Factory/Check.lean`, were changed.

- Toolchain: Lean 4.34.1. Core Lean and Std only.
- `lake build` is green. `Factory.lean` now ends with `import Factory.Proofs`.
- There is no `sorry`, `admit`, new `axiom`, `native_decide`, `implemented_by`, `extern` or
  `unsafe` in the proof files. For every theorem, `#print axioms` lists only
  `[propext, Classical.choice, Quot.sound]` (see `Scratch/ax.lean`).
- No kernel file was edited (Types, Workflow, Access, Migration, Kernel, Check, Contracts,
  Codec, Json, Main, PackageContracts). Nothing was refactored.

## Files (all new)

| File | Contents |
|---|---|
| `Factory/ProofLemmas.lean` | Except-monad plumbing (`bind_eq_ok`, `check_eq_ok`, `need_eq_ok`, `ok_eq_ok`), list and `find?` lemmas, key-preserving replacement lemmas (`findJob?_putJob`, `findStep?_setStep`, `findAttempt?_setAttempt`). |
| `Factory/ProofJob.lean` | The job-intrinsic invariant `JInv` (Prop form of attemptsConsistent, acceptedConsistent, acceptedFenced, terminalQuiet and step-id Nodup), with preservation lemmas for each job operation: start, modify, retire (settle or fail), revoke, finalizeJob, migrate, recover. |
| `Factory/ProofState.lean` | `SafeP` (a structured form of `Safe`) and `safe_iff : Safe s ↔ SafeP s`, plus generic transfer lemmas for the three job-list shapes: replace one job, append one job, jobs unchanged. |
| `Factory/ProofHandlers.lean` | One characterization lemma (`doX_ok`) and one `SafeP` preservation lemma per command handler (all 24 commands). |
| `Factory/ProofExplicit.lean` | Bridges from kernel decision functions to the explicit contract statements: `mapM_option_spec`, `stepDone_of_prereq`, `dep_explicit` (from `prereqsDone`/`bindInputs` to the explicit K04 conditions), `gateEvidence_explicit`, `gatesPass_explicit` (from `gatesPass = .ok (p, ws)` to `RequiredEvidence s j w p ws`), `doPublishReport_gate`. |
| `Factory/ProofTransitions.lean` | `JobsShape` (the four ways a command can change the job list), `dispatch_shape`, and the `dispatch`-level proofs of K02, K03, K04, K05, K08 (the intended form) and K12. |
| `Factory/Proofs.lean` | The requested top-level theorems and reachable-state corollaries. |
| `Scratch/k08_counterexample.lean` | Not part of the build. An executable concrete witness for the K08 finding below. |

## Proved theorems (namespace `Factory.Contracts`)

These use the exact statements requested. `s e t` are implicit.

- `initial_safe : Safe emptyState`
- `apply_preserves (h : Safe s) (hs : apply s e = .ok t) : Safe t.state`
- `reachable_safe (h : Reachable s) : Safe s`
- `k02_stable (h : Safe s) (hs : apply s e = .ok t) : AcceptedStable s t.state`
- `k02_trace (h : Safe s) (hst : Steps s u) : AcceptedStable s u`
- `k03_fenced (h : Safe s) (hs : apply s e = .ok t) : FencedAcceptance s e t.state`
- `k04_dependency (h : Safe s) (hs : apply s e = .ok t) : DependencySafe s t.state`
- `k05_final (h : Safe s) (hs : apply s e = .ok t) : CancellationFinal s t.state`
- `k06_gated (h : Safe s) (hs : apply s e = .ok t) : PublicationGated s e t` (the proof does not use `h`)
- `k07_bound (hs : apply s e = .ok t) : ActivationBound s e t` (no `Safe` hypothesis)
- `k09_migration (h : Safe s) (hs : apply s e = .ok t) : MigrationPreserving s e t` (the proof does not use `h`)
- K11:
  - `k11_replay_nil : replay s [] = s`
  - `k11_replay_cons_ok (h : apply s e = .ok t) : replay s (e :: es) = replay t.state es`
  - `k11_replay_cons_err (h : apply s e = .error r) : replay s (e :: es) = replay s es`
  - `k11_replay_append : replay s (es ++ fs) = replay (replay s es) fs`
  - `k11_replay_reachable (h : Reachable s) : Reachable (replay s es)`
  - `k11_replay_deterministic`: any function that satisfies the three journal equations equals `replay`.
- `k12_causality (h : Safe s) (hs : apply s e = .ok t) : EffectCausality s t`
- Reachable-state corollaries: `k02_reachable`, `k02_trace_reachable`, `k03_reachable`,
  `k04_reachable`, `k05_reachable`, `k06_reachable`, `k07_reachable`, `k09_reachable`,
  `k12_reachable`, `k08_reachable`, `k08_activation_reachable`, and
  `steps_safe (h : Safe s) (hst : Steps s u) : Safe u`.

K08 (the coordinator applied the fix proposed below, and strengthened it with a clause for the jobs a migration does not name):

- `k08_pinning (h : Safe s) (hs) : PinningPreserved s e t` and `k08_reachable`. The pieces are
  `k08_nonmigrate_jobs`, `k08_migrate_others` and `k08_activation`.

K04 and K06 were restated in Contracts.lean (2026-09-26 follow-up) so that they do not
depend on kernel decision functions. The proofs were updated, and the statements were not weakened:

- `k04_dependency` proves the new explicit `DependencySafe`: `StepDone` for every ordering
  edge, the input count, and a per-index binding for every input (the job input for `jobInput`;
  for `stepOutput p`, `StepDone j p` and the producer's accepted `result`). It is derived from
  the kernel's `prereqsDone`/`bindInputs` checks by `dep_explicit`. That lemma uses `Safe` for
  the step-id Nodup and for `acceptedConsistent`, which gives "succeeded ⇒ accepted".
- `k06_gated` proves both conjuncts of the new `PublicationGated` (`publishRelease` and
  `publishReport`) with the explicit `RequiredEvidence`. It uses `gatesPass_explicit`: the
  spec that `uniqueRole` returns is a member of `w.steps` with the queried role.
- Both statements are true. There is no counterexample.

## Finding (resolved): K08 was false as originally stated

This section describes the earlier statement. The current statement in Contracts.lean is fixed
and proved.

## Proof architecture (for maintainers)

1. **`apply` factors through `dispatch`.** `apply_dispatch` shows every accepted transition is
   `dispatch {s with clock := c} e` for some `c`, plus the permission and epoch facts from
   `admit`. No invariant or contract mentions `clock`, so every property transfers by
   definitional unfolding.
2. **Handlers.** `doX_ok` lemmas turn each `do` block into explicit facts and the explicit
   post-state. The `unfold_ok` macro rewrites with `bind_eq_ok`, `check_eq_ok` and `need_eq_ok`.
3. **Safe preservation.** `safe_putJob`, `safe_addJob`, `safe_sameJobs` and `safe_doRecover`
   reduce every handler to a job-local `JInv` proof plus resource accounting. For resources, the
   job list is split as `s.jobs = l1 ++ j :: l2` (unique ids), so the per-class live-attempt sum
   changes by exactly that job's delta.
4. **K06 invariant.** Evidence jobs are `.succeeded`, which is terminal. Every job mutation is
   guarded by non-terminality, and `gatesPass` depends on the state only through `contract`,
   which only bootstrap changes and only when `releases = []`.
5. **Transition contracts.** `dispatch_shape` classifies every command into four shapes: jobs
   unchanged, one fresh job appended, one non-terminal job replaced (with `AccMono`,
   `FenceNew`, `DepNew` and release facts), or controller recovery. K02, K03, K04, K05 and K08
   are proved once per shape.

## Audit: contracts whose meaning depends on a kernel decision function

The flaw is this: if a contract is stated through a function that the kernel also uses to
decide, then weakening that function weakens the theorem too. For example, a mutant
`findStep?` that always returns `none` would make `AcceptedStable` vacuously true. The list
below covers the remaining statements. I changed none of them.

"Effort" is my estimate. Each one needs a bridge lemma of the kind in
`Factory/ProofExplicit.lean`, usually "`find?` with a unique key ↔ list membership", which
already exists as `find?_id_eq_some_iff`, `findAttempt?_eq_some` and `findJob?_eq_some`.

| # | Statement | Kernel function(s) it depends on | Proposed explicit restatement | Provable? |
|---|---|---|---|---|
| 1 | `K06` state invariant (`releasesEvidenced`) | `gatesPass`, `gateEvidence`, `uniqueRole`, `State.findJob?`, `State.workflowOf` | `∀ r ∈ s.releases, ∀ jid, r.evidenceJob = some jid → ∃ j ∈ s.jobs, j.id = jid ∧ j.kind = .changeEvaluate ∧ j.status = .succeeded ∧ ∃ w, PinnedWorkflow s j w ∧ RequiredEvidence s j w r.payload r.workflows ∧ r.source = j.subject` | Yes, modest. It follows from `releasesEvidenced` via `gatesPass_explicit` and `findJob?` ⇒ membership. It needs no induction because it follows from the proved Bool invariant. |
| 2 | `K10` (`resourcesOk`) | `State.liveOfClass`, `Job.liveOfClass`, `Job.liveAttempts`, `AttemptStatus.live`, `Role.resource`, `State.workflowOf` | Let `Live a := a.status = .authorized ∨ a.status = .starting ∨ a.status = .running`, and `Res r` be the fixed table (author/reproduce/refute/summarize ↦ llm, others ↦ container). Then: `(∀ b ∈ s.budgets, b.used ≤ b.limit) ∧ ((s.jobs.flatMap (·.attempts)).filter (fun a => Live a ∧ Res a.role = .llm)).length ≤ s.config.llmSlots ∧ (the same for container) ∧ ∀ j ∈ s.jobs, ∀ w, PinnedWorkflow s j w → (j.attempts.filter Live).length ≤ w.maxParallel` | Yes, modest. It needs sum-of-filter-lengths = length-of-flatMap-filter, plus `live ↔ Live` and `resource ↔ Res` by `cases`. |
| 3 | `K05` state and `CancellationFinal` (`terminalQuiet`, `JobStatus.terminal`, `liveAttempts`) | `JobStatus.terminal`, `AttemptStatus.live` (Types.lean), `Job.liveAttempts`, `Job.findStep?` | Let `Terminal st := st ∈ [.blocked, .succeeded, .failed, .cancelled]`. Then `∀ j ∈ s.jobs, Terminal j.status → ∀ a ∈ j.attempts, ¬ Live a`. In `CancellationFinal`, replace `findStep?` with membership (see row 4). | Yes, easy (`cases` on the status). |
| 4 | `AcceptedStable`, `FencedAcceptance` (via `acceptedAt`), `MigrationPreserving` and `CancellationFinal` (via `findStep?`) | `State.findJob?`, `Job.findStep?` | `AccIn s jid sid a := ∃ j ∈ s.jobs, j.id = jid ∧ ∃ st ∈ j.steps, st.id = sid ∧ st.accepted = some a`, and use `AccIn` / `¬ ∃ a, AccIn …` instead of `acceptedAt … = some/none`. | Yes, modest. Under `Safe` (unique job ids and step ids) `AccIn ↔ acceptedAt = some`. For the post-state use `apply_preserves`. |
| 5 | `DependencySafe` (premise `attemptIn … = none` / `some a`), `EffectCausality` (launch clause) | `Job.findAttempt?`, `State.findJob?` | `AttIn s jid sid g a := ∃ j ∈ s.jobs, j.id = jid ∧ a ∈ j.attempts ∧ a.step = sid ∧ a.gen = g`. | Yes, modest. It uses `findAttempt?_eq_some`, which needs the gen-Nodup that `Safe` provides. |
| 6 | `DependencySafe`, `PublicationGated` (via `s.workflowOf j`), `K01.jobPinned` | `State.workflowOf`, `State.findRelease?`, `workflowFor` | `PinnedWorkflow s j w := ∃ r ∈ s.releases, r.digest = j.release ∧ w ∈ r.workflows ∧ w.kind = j.kind ∧ ∀ w' ∈ r.workflows, w'.kind = j.kind → w' = w` | Yes, modest. Uniqueness comes from `exportsOk` (exactly one workflow per kind) plus unique release digests. |
| 7 | `K01` (`jobPinned`, `releasesOk`) | `wellFormedWorkflow`, `topoOk`, `exportsOk`, `requiredRoles`, `allowedRoles`, `bindingsOk` (Workflow.lean, used by the kernel at runtime) | Restate well-formedness explicitly: steps non-empty; `maxParallel ≥ 1`; `(steps.map id).Nodup`; `∀ i, ∀ p ∈ steps[i].prereqs, p ∈ (steps.take i).map id`; `role ∈ allowedRoles kind`, with that table restated inline; exactly one step per required role; and the evaluation/author binding facts written out. `exportsOk` becomes "for each kind exactly one workflow, and each is well-formed". | Provable, moderate. `topoOk ⇒` topological order is an induction, and `topoOk_nodup` already does half of it. The binding facts need unfolding `uniqueRole` as in `gateEvidence_explicit`. |
| 8 | `K01` (`acceptedConsistent`) | `stepStatusOf` (Access.lean, kernel) | `st.accepted = some a → st.current = none ∧ (a.outcome = .pass ∧ st.status = .succeeded ∨ a.outcome = .fail ∧ st.status = .failed ∨ a.outcome = .inconclusive ∧ st.status = .blocked)` | Yes, easy (`cases a.outcome`). |
| 9 | `K01` (`attemptsConsistent`, `changesOk`, `releasesOk`) | `findAttempt?`, `findStep?`, `findBudget?`, `findRelease?`, `wasActivated` | Replace each lookup with membership plus key equality, as in rows 4 and 5. `ac_iff` in `ProofJob.lean` already proves this for `attemptsConsistent` (the `AC` structure). | Yes, modest. `AC` / `SafeP` / `JInv` are already the explicit forms internally. |
| 10 | `ActivationBound` | `Actor.isOperator` (defined in Kernel.lean) | `(∃ n, e.actor = .operator n)` instead of `e.actor.isOperator = true` | Yes, trivial. |
| 11 | `Reachable`, `Steps`, `replay` (K11) | `apply` | None needed. `apply` is the object under verification. | n/a |
| 12 | `AcceptedStable`/`K02`/`K03` state parts (`acceptedFenced`, step-id Nodup) | `acceptedFenced` is Check.lean-only and uses no kernel function | None needed (only row 4 applies to the transition parts). | n/a |

Two caveats:
- Rows 3 and 8 depend on functions in Types.lean/Access.lean (`JobStatus.terminal`,
  `AttemptStatus.live`, `Role.resource`, `stepStatusOf`). The kernel uses these tables for its
  own decisions, so a mutant that edits a table weakens the matching contract. Restating the
  tables inline in Contracts.lean is cheap and removes that dependency.
- The mutation-testing gap the coordinator found for K04/K06 would also apply to rows 1, 2
  and 6. Rows 1 and 6 are the most important, because the K06 state invariant is the one
  advertised for releases.

## What remains

Nothing requested is unproved. The audit items above are proposals only. No statement in
Contracts.lean was changed by me.
