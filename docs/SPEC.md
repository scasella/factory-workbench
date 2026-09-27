# Factory Workbench — Greenfield Build Specification

**Version:** 1.0  
**Status:** Proposed implementation contract; not an existing or verified implementation.  
**Date:** 2026-09-26  
**Audience:** The coding agent building the first working system and the human accepting it.

## 0. Read this first

Build a local, single-operator agent workbench that runs durable, reviewed jobs and can change **the executable orchestration packages it uses to run those jobs**, from inside the product. A proposed change must bring its implementation, checked proof obligations, tests, review evidence, and an explicit disposition for existing jobs. The running version builds and evaluates its successor. A small protected control plane admits releases; the candidate cannot authorize itself.

This is not a chat interface over an external coding service, a collection of proofs about an unused model, or an unrestricted agent that rewrites its own server.

The founding demonstration is:

1. Run a real multistage job with independent reviews, durable artifacts, cancellation, and recovery.
2. Ask the product to parallelize two independent review stages while retaining both publication prerequisites.
3. Have Codex generate the changed package and its proof source. Build and independently verify the exact candidate.
4. Activate it through the existing release mechanism. Keep old jobs pinned unless an explicit, checked migration succeeds.
5. Use the upgraded workbench to build another improvement. Demonstrate recovery and rejection of an attempted review bypass.

### 0.1 Source basis versus new decisions

The behavior above comes from the concept selected in the (private) design conversation that produced this specification. A (private, unpublished) CPython verification methods report motivates durable journals, process-tree cleanup, proof replay, negative controls, and scrutiny of model–implementation gaps. It does **not** prescribe this architecture. All stack choices, interfaces, proof targets, limits, and implementation milestones below are new design decisions for this greenfield build. See §24 for source notes.

### 0.2 Codex command correction

All production LLM inference must use the **Codex CLI**, not an SDK or direct model HTTP client. The requested `codex --exec` spelling is not the documented noninteractive command. The official spelling checked for this specification is **`codex exec`** [S1, S2].

Use a configurable executable plus argument-prefix array, defaulting to `codex` and `["exec"]`. Support `["--exec"]` only as an explicit operator configuration for a locally installed wrapper/version that actually accepts it. `doctor` must validate the installed CLI and configuration; never silently assume the flag works, or silently switch providers.

### 0.3 Binding scope decisions

| Decision | Required v1 choice |
|---|---|
| Deployment | Single operator, single host, local browser interface; Linux execution environment. macOS may host the required Linux containers. No Windows-native execution requirement. |
| Control plane | TypeScript, Node.js, Fastify; one authoritative write coordinator. |
| UI | React, TypeScript, Vite; ordinary accessible forms and tables. No visual workflow editor required. |
| Persistence | SQLite plus a content-addressed local artifact store. No Redis, external queue, or cloud database. |
| Formal/runtime core | Lean 4 executable pure transition functions, with proofs about those same definitions. |
| Evolvable code | Versioned Lean workflow/planner packages, prompts, and candidate-owned supplemental tests. |
| Immutable during self-update | Kernel, contracts, authentication, runner isolation, verifier, release gate, schema, control-plane/UI binaries, fixed test harness, and build configuration. |
| LLM boundary | Codex CLI subprocesses returning structured proposals/reviews. v1 disables autonomous shell/subagent execution within the LLM process. |
| Generated-code execution | Separate credential-free, network-disabled containers using fixed build/test commands. |
| Approval | Human approval required for every activation. Approval cannot override a failed proof or missing review. |
| External publication | None. “Publish” means registering a locally verified release; no git push, issue filing, email, or external deployment. |

Pin exact working versions in lockfiles and `toolchains.lock.json` during bootstrap. Do not select unspecified “latest” versions on every build. Do not replace Lean with tests, a second handwritten TypeScript model, or a boolean supplied by an agent.

## 1. Product goals and exclusions

### 1.1 Required outcomes

**G1 — Durable work.** A user can submit a job, observe its actual execution, pause/cancel it, restart the workbench, and recover from its journal without recomputing committed stages.

**G2 — Controlled self-improvement.** The user can request an orchestration change inside the workbench. The current package conducts the author/build/proof/review workflow that produces its successor.

**G3 — Source-connected guarantees.** The authoritative admission/lifecycle logic runs the same Lean definitions that are proved. A candidate's executable planner is built from the source covered by its proof package, and is also treated as an untrusted proposer by the kernel.

**G4 — Safe coexistence.** Different jobs can use different immutable package versions. Activation changes the default for new jobs, not the meaning of old jobs.

**G5 — Honest assurance.** The UI separates proved properties, runtime checks, tests, model judgments, and assumptions. A passing proof does not imply correct model judgments or safe arbitrary software.

### 1.2 Explicit non-goals

No autonomous modification of the protected control plane; arbitrary live database migrations; arbitrary workflow scripting; dynamic dependencies; external side effects; multi-user/multi-tenant hosting; distributed workers; automatic spending commitments; claims of exactly-once external execution; proof of LLM correctness; general deadlock/liveness guarantees; unrestricted repository execution; or a universal application builder.

The first system need not regenerate its entire stack. Bootstrap is human-authorized. Thereafter it must genuinely build and activate its **own orchestration code**, not merely produce patches that someone applies outside the product.

## 2. The first user experience

The home screen shows jobs, the active orchestration release, worker health, and an **Improve this workbench** action.

A job detail page shows its pinned release, DAG as a simple step list with dependencies, attempts, source/artifact identifiers, accepted results, live process observations, budget, and journal. A pending step is not “running” merely because a database row says so. Distinguish authorized, starting, observed-running, and cleanup-pending attempts.

The improvement flow accepts a plain-language request and a bounded budget. It shows the proposed source changes, changed scheduling/data dependencies, proof obligations, reviews, test results, expected impact on existing jobs, and any uncertainty. The user can reject or approve the **exact release digest**. Approval and activation are separate recorded operations, though a single UI action may request both with explicit confirmation.

The activation preview lists each unfinished job as **remains pinned**, **eligible for checked migration**, or **ineligible**, with reasons. The default is to leave all existing jobs pinned. No job moves versions merely because the default changes.

## 3. Architecture and trust boundaries

### 3.1 Components

- **Protected kernel:** Lean library and executable defining typed state, commands, guards, transitions, workflow validation, migration checks, and release/publication conditions.
- **Coordinator:** fixed TypeScript service authenticating requests, serializing state transitions, persisting their results, and executing only committed effect intents.
- **Package runtime:** immutable Lean executable per orchestration release. Exports workflow definitions and a pure planner. Runs outside the coordinator's privilege domain.
- **Runner supervisor:** owns containers/process groups, timers, output limits, heartbeats, and artifact collection. Workers never open the authoritative database.
- **Codex adapter:** the only production LLM inference adapter. It does not have release credentials or direct state-write privileges.
- **Verifier:** fixed harness, frozen contract source, pinned compiler, proof replay, statement/axiom inspection, source-to-binary binding, and protected tests. Candidate scripts cannot define “pass.”
- **Artifact store:** immutable blobs addressed by verified digest, separate from mutable attempt scratch spaces.
- **Web interface:** reads projections and sends authenticated commands; it never determines authorization.

All mutation paths, including recovery, cancellation, lease expiry, publication, and activation, must go through the coordinator and kernel. No admin endpoint may directly patch a job row into success.

### 3.2 Process and credential isolation

Use isolated Linux containers for LLM calls, compilation/proof elaboration, tests, and candidate planner execution. Use non-root users, resource limits, read-only inputs, minimal writable scratch/output directories, and no host control sockets. No candidate sees the controller's database, artifact-store write root, signing material, operator session, host home directory, or container-engine socket.

Codex authentication is provisioned by the operator into the **LLM runner only**. Build/test/planner containers receive no Codex credentials and have no network. A candidate's code, build hook, proof elaborator extension, or test must never execute in the credential-bearing LLM runner.

The LLM runner is for proposal generation and review, not autonomous execution. Use a sanitized, minimal Git workspace; supply source/context as data in the prompt, not as executable repository configuration. Disable shell/unified execution, nested agents, web tools, apps/connectors, MCP, user/project hooks, and automatic dependency installation. Verify these restrictions against the pinned CLI. See §10.

Do not claim a CLI sandbox alone protects credentials. The constrained tool profile, absence of candidate execution, outer isolation, and trusted CLI are explicit security assumptions. Unsupported tool restriction/isolation configurations must stop live execution rather than silently degrade.

### 3.3 Formal trust boundary

The proved claims cover well-typed internal state and the Lean transition functions. Deployment relies on the Lean checker, compiler/runtime, approved imports, JSON boundary, host authentication and effect executor, SQLite durability, digest implementation, container isolation, OS, and hardware.

Digest collision resistance and authentic provenance of host observations are assumptions, not Lean theorems about SHA-256 or the operating system. A diagram or trace comparison is not a substitute for this inventory.

The planner is defense-in-depth: even a malformed/malicious planner response cannot authorize an unsafe transition, because the fixed kernel recomputes eligibility and checks every proposed start.

## 4. Repository and runtime layout

Implement this layout or a mechanically equivalent one without changing privilege boundaries:

```text
apps/control/                  # fixed Fastify coordinator/API
apps/web/                      # fixed operator UI
packages/protocol/             # transport schemas and generated TS types
packages/codex-adapter/         # real CLI adapter + deterministic fake
packages/runner/                # container/process supervisor
packages/store/                 # SQLite + immutable blob store
protected/lean/Factory/
  Types.lean
  Workflow.lean
  Kernel.lean
  Migration.lean
  Contracts.lean
  Proofs.lean
  Codec.lean
  Main.lean                    # fixed executable wrapper
protected/verifier/            # fixed build/check/attestation harness
protected/tests/               # acceptance, mutation and fault-injection tests
protected/contracts.json       # property IDs and expected theorem types
protected/runner-profiles/     # version-pinned profiles; not candidate-editable
orchestration/genesis/
  Package.lean                 # workflow exports
  Planner.lean                 # executable planner
  Proofs.lean
  prompts/
  supplemental-tests/
schemas/
scripts/                       # bootstrap, doctor, dev, checks, demos
AGENTS.md
README.md
ASSURANCE.md
TOOLCHAIN.md
toolchains.lock.json
```

Runtime state lives **outside the source tree**:

```text
state/workbench.sqlite
state/blobs/sha256/<prefix>/<digest>
state/releases/<release_digest>/
state/attempts/<attempt_id>/
state/staging/<candidate_id>/
state/operator/                # restrictive permissions, never mounted in workers
```

Path protection is enforced through separate mounts/identities and allowlisted materialization, not only a Git diff check. Candidate output cannot edit its own allowlist or build recipe.

## 5. Domain model

Use stable identifiers independent of task launch order. JSON integers that can exceed safe JavaScript precision are decimal strings, decoded to checked natural numbers. Do not wrap counters. Runtime resource limits reject oversized requests; they do not turn the general proof into a bounded model check.

### 5.1 Core records

| Record | Essential fields |
|---|---|
| `Release` | release digest, payload digest, source digest, parent release, contract digest, toolchain/build identity, binary digest, workflow exports, evidence references, status |
| `Job` | job ID, kind, pinned release, immutable input digest, subject digest, epoch, status, step states, required gates, budget, revision |
| `StepSpec` | stable ID, runner kind, role, ordering prerequisites, semantic input bindings, prompt/schema refs, retry class, resource class |
| `StepState` | pending/active/succeeded/failed/blocked; current attempt; immutable accepted result reference; semantic fingerprint |
| `Attempt` | attempt ID, job/step IDs, monotonic generation, job epoch, controller epoch, lease, process/container identity, timestamps, transport outcome |
| `Evidence` | evidence ID, subject payload digest, producer attempt, role, semantic fingerprint, input digests, outcome, output digests, verifier/harness identity where applicable |
| `ChangeRequest` | ID, user request, base release, total revision budget, author/evaluation jobs, candidate revisions, disposition |
| `Approval` | operator identity, exact release digest, expected base release, contract digest, approval time, revocation state |
| `MigrationPlan` | old/new release, recipe digest, job ID, observed job revision, proposed reuse/reset mapping, compatibility proof reference, reasoned preview |
| `CommandReceipt` | command ID, actor, canonical request digest, accepted/rejected result, associated journal range |
| `EffectIntent` | deterministic effect ID, originating committed command, action, scope, state, dispatch attempt, fencing identity |

Distinguish an attempt's transport success from the task's business result. A CLI process exiting successfully may return `fail`, `inconclusive`, or invalid JSON. Those are not successful review gates.

### 5.2 Status semantics

Job statuses: `queued`, `running`, `pause_requested`, `paused`, `blocked`, `succeeded`, `failed`, `cancelled`.

Terminal job statuses never reopen. An explicit rerun creates a new job with a link to its predecessor. Cancellation revokes authority immediately in the committed state; process cleanup may continue afterward and is shown separately.

Attempt statuses: `authorized`, `starting`, `running`, `succeeded`, `failed`, `expired`, `cancelled`, `lost`. Keep cleanup status separate; an expired attempt may still have an OS process requiring termination.

A step can have several recorded attempts but at most one accepted successful completion. Transport failures may retry according to frozen policy. A negative or inconclusive review blocks publication; do not repeatedly ask the reviewer until it says “pass.” A new candidate revision or explicit operator-requested investigation is a separate recorded action.

### 5.3 Semantic identity and reuse

Compute a step fingerprint from runner implementation identity, role, prompt bytes, result schema, actual semantic input digests, behavioral options/model configuration, and relevant fixed harness/contract versions.

Keep **ordering edges** separate from **semantic inputs**. Removing an unnecessary ordering edge can permit parallelism without changing a task's inputs. An actual input dependency cannot be removed just to obtain parallelism.

Do not include incidental array order or attempt IDs in semantic fingerprints. Record the producer release separately: reuse across versions requires a compatibility check, not deletion of its origin.

Reviews bind to an immutable candidate **payload digest**, never a branch name or mutable worktree. Changing code, proof source, prompts, result schemas, compiler configuration, or required assumptions creates a new payload and invalidates previous candidate-level evidence.

## 6. Executable core and command semantics

### 6.1 Required API shape

The following Lean sketch defines the architectural boundary, not final type-checked source:

```lean
-- All arguments are explicit. No clock, database, LLM, filesystem or network here.
def apply (state : State) (command : AuthenticatedCommand)
    : Except RejectReason Transition

structure Transition where
  state   : State
  events  : List DomainEvent
  effects : List EffectIntent

def wellFormedWorkflow (w : WorkflowDef) : Bool
def readySteps (s : State) (j : JobId) : List StepId
def canMigrate (s : State) (p : MigrationPlan) : Bool
```

Compile these definitions into the kernel executable used by the coordinator. The coordinator must not implement an alternative success/authorization path in TypeScript. `Codec` and the IO wrapper are audited boundaries; they are not automatically covered merely because `apply` is proved.

The executable must support versioned request/response messages for `apply`, workflow validation, export/decoding checks, invariant diagnostics, and offline journal replay. Reject unknown tags, duplicate object keys, extra fields, invalid digests, noncanonical integers, and oversized inputs.

### 6.2 Commands

Implement at least:

`CreateJob`, `StartAttempt`, `ObserveProcessStarted`, `Heartbeat`, `CommitResult`, `FailAttempt`, `ExpireAttempt`, `PauseJob`, `AcknowledgeQuiescence`, `ResumeJob`, `CancelJob`, `RegisterCandidate`, `RecordVerification`, `RecordApproval`, `RevokeApproval`, `PublishReport`, `PublishRelease`, `ActivateRelease`, `MigrateJob`, and `RecoverController`.

Only authenticated controller/verifier/supervisor envelopes can record authoritative observations. Agent result JSON cannot select its actor, role, subject, lease, or verifier identity. Human-only commands are never exposed as model tools. Verification and review receipts from work done by an attempt must settle through that attempt's current fencing/lease checks; `RecordVerification` is not a back door for a late, expired worker to create admissible evidence. The trusted verifier records what it observed, and the kernel separately decides whether that observation can be accepted for this job.

### 6.3 Transition guards

| Command | Essential guards and result |
|---|---|
| `CreateJob` | Approved installed release; valid typed input and DAG; capture the selected/default release atomically with creation. |
| `StartAttempt` | Job dispatchable; step eligible; no accepted completion or active authority; all required inputs present; budget/slots available. Allocate fresh generation and commit launch intent. |
| `Heartbeat` | Current job/controller epochs and generation; unexpired current lease; authenticated supervisor. A late heartbeat cannot resurrect expired authority. |
| `CommitResult` | Current unexpired attempt; matching subject/fingerprint; authenticated supervisor; valid outputs already durably stored; job not cancelled; step has no conflicting accepted completion. |
| `ExpireAttempt` | Trusted monotonic-time observation passes lease deadline. Revoke generation, request cleanup, and make eligible for policy-controlled retry only when safe. |
| `PauseJob` | Stop new dispatch; allow authorized work to settle; transition to paused only after quiescence is acknowledged. |
| `CancelJob` | Increment job epoch; revoke all outstanding attempt authority; cancel unsent launch intents; request process-tree termination. |
| `PublishRelease` | Exact successful proof/build/protected-test and required review evidence for the payload; current contract and approved verifier; no failed mandatory gate. |
| `ActivateRelease` | Published, intact, compatible release; live exact-digest human approval; compare-and-swap expected active release. No implicit job migration. |
| `MigrateJob` | Paused/quiescent job; expected revision unchanged; approved target; supported recipe and compatibility evidence; current state passes migration guards. |
| `RecoverController` | Advance controller epoch before redispatch; fence all old authority; preserve committed results; reconcile/terminate old processes. |

These summaries do not override the more detailed rules below.

### 6.4 Linearization, fencing, and duplicates

Every authority-changing command linearizes at its SQLite commit. The attempt identity is at least `(job_id, step_id, job_epoch, controller_epoch, generation)`. A worker must carry that identity through its supervisor; it is not copied from model output.

The trusted coordinator attaches monotonic clock ticks and its controller epoch to time-sensitive commands. Within an epoch, ticks never decrease; accept a lease-bearing action only while `now < deadline`, and treat equality as expired. A new controller epoch fences all old leases before its new monotonic clock origin is used. Wall-clock timestamps are display metadata, not lease authority. Journal the injected ticks so replay never consults the live clock. The clock implementation/observation is a trusted host boundary.

A duplicate command ID with the same request digest returns its original result. Reuse with different request bytes returns a conflict. A repeated identical already-accepted completion is idempotent; a conflicting completion is rejected and audited. Neither creates a second accepted result.

An expired/replaced worker cannot commit even if its output is useful or arrives before its replacement finishes. Keep such output as an unaccepted diagnostic artifact if desired, never silently promote it.

**Cancellation guarantee:** after cancellation commits, no new work authorization or result acceptance occurs for that job. A process launch authorized before cancellation may cross the physical cancellation instant; the supervisor must cancel it and reject its result. Do not claim physical OS starts are transactionally atomic with SQLite, or that an already-running external action has been undone.

## 7. Durable journal and effect execution

### 7.1 Persistence contract

Use SQLite WAL, foreign keys, durable synchronization, and a single serialized writer. Explicitly implement and test busy/error handling; do not infer transaction success from an HTTP response timeout. SQLite's transaction semantics are part of the trusted persistence boundary [S5].

For every mutating request:

1. Authenticate it, bound its size, and assign/check a command ID.
2. Enter the write coordinator and `BEGIN IMMEDIATE`.
3. Resolve idempotency; load authoritative state and expected revision.
4. Call the **installed, digest-checked kernel** on that state and authenticated command.
5. Validate the response envelope. On success, atomically append the canonical command/events, update state and projections, insert effect intents, and store the receipt.
6. Commit. Only then can effect dispatch occur. Return the committed receipt.

Use a canonical kernel-state blob with revision as the v1 write model; normalized tables are projections. This is intentionally a small-system tradeoff. They must not become a second authority. Enforce configured state-size limits rather than introducing an unproved alternative writer.

Rejected commands receive an audit/receipt entry without changing domain state. Replay uses accepted commands plus their explicit nondeterministic observations, not wall time or LLM re-execution.

Do not run LLMs, builds, filesystem copying, or long proof checks inside database transactions. Kernel calls have a short bounded timeout; a crash/invalid response aborts the transaction and disables further mutation until diagnosed.

### 7.2 Artifact durability

Materialize artifacts into a temporary file, enforce size/type/path rules, compute the digest, flush, atomically rename into the content-addressed store, and sync its directory before committing a reference. On collision/mismatch, fail closed. An unreferenced blob is safe; a committed reference to incomplete bytes is not.

Only the trusted collector writes the store. Candidate paths are relative artifact names, not filesystem authority. Reject absolute paths, traversal, symlinks, hard links, device files, and ambiguous Unicode/path representations in candidate output. Runtime release bundles contain regular files from an allowlist.

Do not delete referenced blobs, active/pinned releases, proof receipts, or replay dependencies. v1 garbage collection may delete only expired unreferenced scratch/uncommitted blobs after a grace period.

### 7.3 Outbox and uncertain launches

Use a transactional outbox for launch/termination intents. The runner maintains a durable launch registry keyed by effect ID and container identity. Duplicate delivery must reconcile with the existing container, not start another blindly.

A crash between spawning and recording a PID is inherently an uncertainty window. Reconcile by deterministic container labels/IDs and supervisor records. On restart, first fence old authority, then terminate/reconcile uncertain containers before retrying. Never mark an uncertain execution “succeeded.” Duplicate computation is possible; duplicate accepted commits are not.

Container inventory and process birth identity matter. A reused PID is not evidence that the original worker is alive. Terminate the complete container/process tree, not only the immediate Codex or prover process.

## 8. Orchestration packages: what the product changes

### 8.1 Package contents and interface

A candidate package includes:

```text
Package.lean             # actual finite workflow definitions
Planner.lean             # actual pure scheduling implementation
Proofs.lean              # proofs against frozen protected contract types
prompts/*.md
supplemental-tests/*     # additive only
migration.json          # supported declarative recipe or explicit pin-only
package-metadata.json   # description; not a self-issued attestation
```

The fixed harness supplies all build files, imports, codecs, entrypoints, and dependencies. Candidate files cannot change the build program, compiler flags, trust policy, proof targets, or protected tests.

The package runtime accepts a `PlannerView` containing the pinned workflow, current ready candidates, resource slots, and stable scheduling metadata, and returns a list of stable step IDs. It cannot spawn work or mutate state. The trusted kernel independently validates every proposed dispatch.

The package's workflow export comes from the **same Lean definition** imported by its proofs. The fixed wrapper exports it through the shared codec; the verifier checks structural/canonical equality with the installed manifest. A separately hand-maintained JSON DAG is not acceptable.

### 8.2 Planner requirements

For every well-formed planner view, prove that the plan has no duplicate IDs, contains only eligible steps, obeys the effective concurrency bound, and respects any declared priority policy. Provide a nonvacuity/completeness statement for dispatchable work; an implementation that always returns an empty list cannot pass by proving only safety.

Use general lemmas over finite lists/sets, not only a proof of one sample DAG. Package-specific finite well-formedness checks may use kernel-reduced computation, but label them honestly.

A planner crash, malformed output, timeout, or failure to propose required available work blocks scheduling and surfaces a diagnostic. Do not silently switch a pinned job to a different planner. A recorded rollback/migration may recover it.

### 8.3 Genesis, v1, and v2

**Genesis (P0):** serial review ordering and a simple stable-ID planner. Already supports general DAGs, resource slots, durable results, pause, and pinning. The serial behavior is an evolvable policy, not a limitation patched into the kernel later.

**First successor (P1):** removes an incidental ordering edge between reproduction and refutation and uses the available planner capacity to dispatch both. Both still receive the same frozen candidate, and neither receives the other's judgment. Publication still requires both.

**Second successor (P2):** optimize the executable planner's ready-list filtering/deduplication while proving its output equivalent to P1 for every well-formed view. Keep workflows and task semantic fingerprints unchanged. A benchmark must report the measured result; do not promise a speedup. A useful simplification with no material regression is acceptable if documented.

P1 must be authored and evaluated through P0. P2 must be authored and evaluated through P1. Record the producer release on every job and evidence item.

## 9. Required formal obligations

### 9.1 Kernel theorems

Define each property precisely in `protected/lean/Factory/Contracts.lean`. Prove initialization, preservation by every accepted transition, and reachable-state corollaries for the following IDs. Auxiliary invariants may evolve during the initial build; the advertised targets must not be weakened to make proofs pass.

| ID | Property and boundary |
|---|---|
| K01 | **Well-formed state:** unique IDs, valid references, consistent status/attempt relationships, and well-formed installed workflows. |
| K02 | **Single accepted completion:** no logical step has two different accepted successful completions. Retries may compute repeatedly. |
| K03 | **Fenced results:** at acceptance, completion belongs to the currently authorized job/controller epoch and generation with a valid lease. |
| K04 | **Dependency/input safety:** a newly authorized step has satisfied prerequisites and the exact required semantic input bindings. |
| K05 | **Cancellation:** a cancelled job admits no subsequent new launch authority or result acceptance; terminal state is irreversible. |
| K06 | **Required evidence:** publication implies successful required evidence, correct roles/provenance classes, and matching payload/contract identifiers. This does not prove model judgments true. |
| K07 | **Release binding:** at activation, the exact published release has an unrevoked matching operator approval against the expected base. |
| K08 | **Version pinning:** changing the default release does not change any existing job's pinned release or completed artifacts. |
| K09 | **Migration preservation:** successful supported migration preserves completed evidence/history, required gates, subject identity, and fencing; it never invents success. |
| K10 | **Resource authority:** active authorized attempts and reserved launches respect configured concurrency and attempt budgets. |
| K11 | **Replay determinism:** identical initial state and recorded authenticated command sequence produce identical logical state/effects. This is not a filesystem durability theorem. |
| K12 | **Effect causality:** returned launch/publication intents correspond to an accepted authorized transition; the host additionally enforces commit-before-execute. |

A schematic statement structure is:

```lean
theorem initial_safe : Safe initialState := ...

theorem apply_preserves
    (h : Safe s)
    (hstep : apply s c = .ok t) : Safe t.state := ...

theorem reachable_safe
    (h : Reachable initialState s) : Safe s := ...
```

Use explicit general parameters for finite collections and arbitrary traces. Do not advertise an exhaustive test over a small trace bound as an unbounded theorem.

### 9.2 Package and migration theorems

Every release supplies checked declarations for:

- P01: exported workflows satisfy the fixed well-formedness and mandatory-role requirements.
- P02: planner eligibility, uniqueness, slot bounds, and its declared nonempty/completeness contract.
- P03: required publication roles and their subject bindings remain intact under the proposed orchestration change.
- P04: every advertised migration recipe is sound under explicit eligibility preconditions; pin-only releases may omit migration support but must say so.
- P05: any advertised behavioral equivalence, such as P2's planner optimization, holds for all well-formed inputs, not only fixtures.

Required migration families for the demo are (a) unchanged task semantics with ordering-only change and (b) equivalent planner implementation with unchanged workflow. Prove preservation of result bindings, the downward-closed set of completed prerequisites, and required-gate identities. It is legitimate for a migration to reject a state outside these conditions.

The verifier supplies the actual previous release's exports/source as read-only, digest-bound inputs for compatibility checking. A candidate cannot define a convenient fictitious predecessor and prove migration from that instead.

Do not require a fake handwritten theorem for every prompt edit. State which generic theorem applies, which finite object was checked, and which new general obligation was proved. Formal evidence should be useful and correctly scoped.

### 9.3 Proof audit and build binding

The fixed verifier must:

1. Start from a fresh candidate source snapshot and approved, digest-checked dependencies; discard candidate-supplied compiled objects and caches.
2. Compile with a fixed build command and pinned toolchain in a credential-free sandbox.
3. Construct a **trusted statement bridge** referencing fully qualified candidate declarations with the exact frozen expected types. Matching theorem names or printing “proved” is not enough.
4. Inspect the transitive axiom closure of required theorems. Allow only the documented approved Lean foundational axioms, initially `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, custom axioms, or `native_decide`-style oracle dependencies for general claims.
5. Reject `sorry`, admitted targets, forbidden compiler replacement mechanisms such as candidate `implemented_by`/`extern`, and unsafe/partial runtime logic on candidate execution paths. Enforce import/namespace/build allowlists. Source lint supplements checking; it does not replace it.
6. Replay required declarations with the pinned independent kernel-checking tool (`leanchecker` or a documented equivalent that genuinely rechecks the proof objects). A fresh compilation alone must not be mislabeled as independent replay.
7. Build the production package executable from the exact checked definitions using the fixed wrapper. Export its workflow and verify structural equality with the proof-bound value/manifest.
8. Run protected positive tests and negative controls. Distinguish a semantic rejection from a syntax error, missing dependency, resource exhaustion, or timeout.
9. Have the trusted verifier service produce the receipt from observed results. Never accept candidate stdout, a JSON `verified: true`, or an agent-authored manifest as a verification attestation.

The compiler, codec, and operational wrapper remain trusted even with this binding. Document them in `ASSURANCE.md`. Do not claim that proof checking verifies the C compiler, Node process launcher, or containers.

### 9.4 Nonvacuity and mutation requirements

Supply a complete positive execution reaching publication under all required reviews. A release that rejects all work is not acceptable.

Include semantic mutants that attempt to accept a stale result, start work after cancellation, publish without refutation, use an approval for a different digest, drop completed evidence during migration, and change the default while mutating pinned jobs. Include proof cheats: `sorry`, an extra axiom, weaker theorem statement, false “pass” output, source/binary mismatch, substituted protected module, and compiler replacement of a proved function.

A killed mutant must fail the intended proof/guard/test. A compile error can establish that a prohibited construct is rejected, but it is not a semantic mutation kill. Timeout or exhausted memory means **inconclusive**, never “proved safe” or “mutant killed.”

## 10. Codex CLI adapter

### 10.1 One inference path

Expose an internal interface resembling:

```ts
interface LlmRequest {
  invocationId: string;
  role: "author" | "proof_repair" | "reproduce" | "refute" | "summarize";
  contextManifestDigest: string;
  prompt: string;
  outputSchemaPath: string;
  timeoutMs: number;
  maxOutputBytes: number;
  model?: string;
}

interface LlmResult {
  invocationId: string;
  transport: "completed" | "failed" | "timed_out" | "cancelled" | "invalid_output";
  result: unknown | null;
  transcriptDigest: string;
  stderrDigest: string;
  exitCode: number | null;
  usage: { inputTokens?: number; outputTokens?: number; cachedInputTokens?: number } | null;
}
```

All actual model requests must pass through this adapter. A deterministic fake is allowed only for tests/demos explicitly labeled fake. There must be no fallback HTTP call, SDK, hidden nested agent, or separate provider.

### 10.2 Invocation

The official CLI supports noninteractive execution, JSONL events, structured final output, and stdin prompts [S1, S2]. The intended command shape is:

```sh
codex --ask-for-approval never exec \
  --sandbox read-only \
  --json \
  --output-schema /io/result.schema.json \
  --output-last-message /io/result.json \
  --ephemeral \
  -
```

This is a human-readable illustration. The implementation must spawn an executable with an argument array and write the prompt to stdin. Do not use `shell: true`, interpolate prompts into a command string, or execute commands contained in model output.

Run against a sanitized Git workspace in the isolated LLM runner. The runner-owned config must disable shell tools and unified execution, nested agents, apps/MCP/plugins/hooks, web search, and automatic installations. The current official configuration reference documents relevant toggles, including `features.shell_tool`, `features.unified_exec`, and agent controls [S3]. Exact support must be tested for the pinned CLI; config spellings alone are not proof that a tool is disabled. Prevent inherited/project configuration from re-enabling capabilities.

The intended v1 interaction is **context in → structured proposed file changes/review out**. File edits and compiler/test calls occur afterward through the workbench's own journaled, isolated stages. This keeps proof-repair loops observable and credential-free code execution enforceable. It deliberately does not delegate an unbounded tool loop to Codex.

### 10.3 Capability and authentication checks

`workbench doctor` must report executable resolution, CLI version, accepted noninteractive command, schema/JSONL support, security profile, auth readiness, container isolation, pinned Lean/compiler availability, and state-directory permissions.

Use `--help`/version probes without inference by default. A separately invoked `doctor --live` performs a tiny structured-response smoke test with explicit operator consent. Test both success and rejection of a requested forbidden shell/subagent action. If the installed version cannot enforce the required profile, block live mode with a concrete diagnostic. Do not degrade to an unrestricted mode.

The configured model is operator-selected. Do not hardcode a particular model name or invent pricing. Authentication is established outside job prompts; never log credentials or bake them into a release.

### 10.4 Output processing

Drain stdout and stderr concurrently to bounded files. Decode stdout as incremental JSONL; enforce per-line/total limits, preserve unknown well-formed event types as diagnostics, and never convert telemetry events into job authority.

Successful transport requires exit code zero, the expected terminal success event for the tested CLI version, no terminal failure/cancellation, and a complete final result validating against the role schema. Missing output, malformed/truncated JSON, incompatible schema, output overflow, a hung approval prompt, or a nonzero exit fails the attempt.

Parse a single final object with strict schemas and no extra fields. Treat every model field as untrusted data. Stamp actor, subject digest, source snapshot, attempt identity, timestamps, and role outside the model result.

Use fresh invocations in v1. Durable workflow recovery comes from the workbench journal, not `resume --last`. If session reuse is added later, it must use an explicit session ID tied to one job/attempt and cannot replace committed stage records.

Store invocation configuration and prompt/context digests. Unknown/missing usage remains unknown, not zero. UI/log export redacts secrets and does not require displaying model reasoning streams.

### 10.5 Structured author output

Use strict JSON Schemas with `additionalProperties: false`. An author response contains a summary, outcome (`proposed` or `blocked`), file edits, claimed obligations, and blockers. File edits use exact preimages rather than fuzzy patches:

```json
{
  "outcome": "proposed",
  "summary": "Parallelize independent review stages.",
  "edits": [
    {
      "path": "Planner.lean",
      "operation": "replace",
      "expected_sha256": "<digest of supplied source bytes>",
      "content": "<complete replacement source>"
    }
  ],
  "claimed_obligations": ["P01", "P02", "P03", "P04"],
  "blockers": []
}
```

This object is illustrative, not a valid fixture until placeholder values are replaced. Create/delete operations have explicit preimage rules. Allow only candidate package paths, regular UTF-8 text files, bounded size/count, and exact original hashes. Never accept an edit to `protected/`, build files, dependencies, runner configuration, or verifier inputs. A claim to satisfy P02 is not evidence until checked.

Review output contains `pass`, `fail`, or `inconclusive`, a summary, cited input artifacts, and concrete concerns. It cannot create files, mark a peer's result, authorize activation, or choose its own subject.

### 10.6 Context and repair loops

Build a deterministic context manifest from immutable source/evidence. Mark repository text, logs, and user-supplied content as data; instructions within them cannot change authority. Include only permitted files. Do not silently truncate a theorem, prerequisite, or source file: split the task or report insufficient context.

Each repair iteration is a new recorded Codex invocation and candidate revision. Feed back actual compiler/proof diagnostics and the unchanged frozen targets. Bound the loop and stop on exhausted budget. Preserve all rejected candidates and why they failed. A previous review does not carry across revised proof/code bytes without re-evaluation of the new payload.

## 11. Runner lifecycle, recovery, and budgets

The supervisor, not the model, sends heartbeats and observes child/container liveness. Track last output/progress separately from process health; a silent long proof is not necessarily dead, and an alive process is not necessarily progressing.

Initial configurable defaults (engineering limits, not performance promises): two concurrent Codex invocations, one proof/build container, five-second supervisor heartbeats, thirty-second renewable leases, twenty-minute LLM wall timeout, thirty-minute proof-check wall timeout, three-second graceful termination followed by forced container cleanup, five-minute idle warning, ten MiB captured output per invocation, and three candidate revisions per change request. Expose all effective limits before launch.

Budgets apply to the parent change request across its jobs and retries. Restarting, splitting a job, or producing another candidate must not reset consumed attempts/time. Reserve capacity before authorization and release it only through recorded settlement/expiry. Optional reported-token limits stop subsequent authorizations; do not represent them as a guaranteed monetary or provider-side per-call cap.

On startup:

1. Take the exclusive controller lock; refuse a second writer.
2. Verify state integrity, installed kernel/release digests, and the latest journal/snapshot consistency.
3. Commit a new controller epoch, fencing every previous live attempt.
4. Reconcile and terminate all identified previous attempt containers; leave cleanup-pending states explicit.
5. Preserve all committed results. Mark unresolved old attempts lost and retry only under their policy and remaining budget.
6. Resume queued/pinned work only after dependencies and installed release availability have been checked.

Do not restart finished stages because the order of concurrent launches changed. Do not kill unrelated processes by broad name matching. Do not garbage-collect a version still needed by an unfinished job or journal replay.

## 12. Self-improvement workflow and evidence provenance

### 12.1 Bootstrap exception

A human runs the initial build, verifies the kernel, and installs a known genesis package with a recorded genesis manifest. This is a trust root, not a self-certified release. Retain a stable CLI for inspection, pause, and restore if the UI or a planner fails.

After genesis, ordinary self-updates use the running workbench. Kernel/schema/host changes are outside that mechanism and require an explicit external maintenance upgrade with a new trust inventory. Do not add an automatic escape hatch for them.

### 12.2 A change request creates several linked jobs

A change request binds to the active base release at creation. It has an author job and, for each frozen candidate revision, an evaluation job. These are ordinary durable jobs executed through the same engine and pinned package rules as other work.

The author gets the base package source, desired change, frozen API/contracts, allowed paths, and a budget. The trusted materializer applies proposed edits to a new isolated snapshot. After freezing, no process may edit that revision.

The evaluation workflow is:

```text
author job → materialize/freeze candidate
                 ↓
             fixed build
                 ↓
          fixed proof verification
                 ↓
      reproduction review (fresh context)
                 ↓  [P0 ordering only]
        refutation review (fresh context)
                 ↓
          evidence summary/report
                 ↓
      protected publication gate
                 ↓
       operator approval + activation
```

Under P1, reproduction and refutation run in parallel after the shared build/proof inputs. Reproduction includes a fresh execution of protected regression/fault tests in its own evaluation container; the model may interpret their output but cannot supply the test exit status. Refutation gets the frozen candidate and required evidence/context but not the peer reviewer's judgment. Distinct invocations do not imply statistically independent reasoning; the enforced claim is process/context separation and recorded provenance.

A negative required review stops publication. Additional investigation or repairs create new journaled work. Do not implement a majority vote that outvotes a failed mandatory gate.

### 12.3 No self-certification recursion

The **installed** verifier checks the candidate, using installed contracts and protected tests. The candidate cannot select a weaker gate, set its verification status, supply the operator identity, or execute the new planner for production before activation.

When P0 produces P1, P0 governs the evaluation job. When P1 produces P2, P1 governs it. The candidate may be executed only in an isolated test sandbox until activated. This ends the “who verifies the verifier” recursion at an explicit human-installed protected root.

## 13. Content identities and activation

### 13.1 Avoid circular manifests

Use separate identifiers:

- `source_digest`: canonical manifest of all candidate source/prompt/migration files, excluding generated outputs.
- `payload_digest`: canonical manifest containing source digest, package binary, workflow exports, toolchain/core/contract identities, and semantic assets; excludes reviews and approvals.
- `release_digest`: canonical envelope of payload digest, accepted evidence references, compatibility declarations, and producer/base lineage; excludes human approvals.

Reviews and verifier receipts bind to the payload digest. Human approval binds to the release digest. An approval is not included in the digest it signs/approves. Document canonical encoding and use golden vectors; sorted keys, explicit array ordering, no duplicate keys/floats, and digest-of-exact-file-bytes rules must be consistent across TS and Lean.

A trusted verifier receipt records source and binary digests, toolchain/core/contract/test-harness identities, exact theorem targets, axiom inventory, checks and outcomes, and verified workflow exports. An authenticated local verifier channel suffices for v1; do not add decorative cryptographic signatures without a key custody design.

### 13.2 Publication and activation sequence

Build/store the complete immutable release bundle before the publication transaction. Publication registers verified availability. Activation performs a compare-and-swap on `(expected_active_release, new_release_digest)` after rechecking the exact approval and bundle integrity.

If another activation changed the default, return `BASE_RELEASE_CHANGED` and require a new preview/approval. Never silently rebase and reuse the old approval.

New job creation selects and records its release in one transaction. A racing creation therefore uses either the old or new complete release, never a mixture. Existing jobs remain unchanged.

Pin the package binary, prompts, result schemas, planner, and supported toolchain/profile identities together. Executing an old DAG with the new prompts is not version pinning.

### 13.3 Rollback and recovery

Rollback is a new audited activation of a retained known-good release with explicit approval and expected-base checking. It changes future job defaults only. It does not rewrite completed history, reverse arbitrary state, or silently move jobs created under the reverted version.

Keep a documented out-of-band **pause/inspect/export** recovery command. Restoring a database backup is a maintenance action with a new controller epoch and operator warning about lost post-backup journal entries; it is not equivalent to package rollback.

## 14. Existing jobs and checked migrations

### 14.1 Default policy

Leave every existing job pinned. Pinning is a supported outcome, not a failed update. The UI must never equate “new default active” with “all jobs upgraded.”

Migration is an explicit per-job action authorized by the operator. v1 supports only identity mapping of stable step IDs with unchanged semantic fingerprints for reused completed steps, unchanged subject/input identity, preserved required gates, and compatible ordering/planner changes. No arbitrary migration code, task renaming, partial output conversion, changed completed prompts, or fabricated review passes.

An added step may start only as pending and cannot replace a required completed gate. An unstarted optional step may be retired only when the fixed recipe validator permits it. Required roles cannot be removed. If the transformation falls outside these rules, leave the job pinned and explain why.

### 14.2 Protocol

1. Request pause, stopping new authorization while existing work settles.
2. Confirm no live attempt authority, pending launch effects, or unresolved job containers. Record trusted quiescence observation. Do not claim quiescence merely because no worker has recently printed output.
3. Build a migration preview from the exact job revision, old/new exports, evidence map, and recipe.
4. Check the package's general compatibility theorem/receipt and run the fixed concrete `canMigrate` check on this state.
5. Show kept results, new/reset pending work, retired optional steps, remaining gates, target release, and rejection reasons. Bind approval to this plan and expected job revision.
6. Apply in one transaction with revision comparison; increment job epoch, record version transition and compatibility witness, preserve original completion artifacts/provenance, and change only the permitted state.
7. Resume by a separate explicit command. No dispatch occurs as an unrecorded side effect of preview.

Any concurrent change invalidating the preview returns `STALE_MIGRATION_PLAN`. Recompute and obtain approval again. Failure leaves the paused job on its old version; the operator can resume it there.

Completed results retain their original **acceptance-time** epoch, lease, generation, and source provenance. They need not match a new current epoch to remain valid history. A prior completion was authorized at acceptance; it does not become invalid when its lease later expires. This distinction must be reflected in K03 and K09, not papered over by rewriting evidence fields.

Do not migrate the author/evaluation jobs that produced a target release onto that target. v1 keeps self-improvement jobs pinned throughout. Demonstrate migration using ordinary package-audit jobs.

## 15. Fixed job kinds and result publication

Support three initial kinds:

- `package_audit`: review a registered, immutable workbench-compatible package/fixture using build, proof, reproduction, refutation, and summary stages. Successful publication produces a local report artifact, not an installed release.
- `change_author`: generate/repair a successor orchestration package under the change request's fixed budget and allowed paths.
- `change_evaluate`: evaluate a frozen successor package and, if all gates pass, register a publishable local release.

These share the same kernel, runner, journal, versioned scheduling code, and evidence machinery. No kind accepts a model-provided shell command. A trusted `PublishReport` command applies the same relevant review/subject gates as report publication requires, without granting release/activation authority.

Separate “author call completed,” “candidate verified,” “report published,” “release published,” and “release activated” in data and UI. Never mark the whole change successful merely because code was generated.

## 16. API and CLI contract

All write requests require authentication, a unique `command_id`, and expected revisions where applicable. Enforce strict JSON schemas and bounded payloads. Use stable machine-readable rejection codes plus a human-readable explanation and current revision.

| Endpoint | Purpose |
|---|---|
| `GET /api/status` | Active release, controller epoch, assurance/isolation status, capacity, health. |
| `POST /api/jobs` | Create a package-audit job from immutable registered input. Optional explicit release must have been operator-activated previously. |
| `GET /api/jobs/:id` | State, pinned version, attempts, gates, result references. |
| `POST /api/jobs/:id/pause` | Stop new dispatch and drain. |
| `POST /api/jobs/:id/resume` | Resume an eligible paused job. |
| `POST /api/jobs/:id/cancel` | Commit cancellation and request cleanup. |
| `GET /api/jobs/:id/events` | Journal SSE stream with sequence-based reconnect; no inferred authority from UI state. |
| `GET /api/artifacts/:digest` | Authorized, typed/sanitized artifact retrieval; no arbitrary path reads. |
| `POST /api/changes` | Begin a bounded in-product improvement request. |
| `GET /api/changes/:id` | Candidate lineage, comparisons, budgets, proofs, tests, and reviews. |
| `POST /api/changes/:id/revise` | Explicitly request a new revision/investigation within budget. |
| `GET /api/releases/:digest` | Immutable bundle/evidence/assurance details. |
| `POST /api/releases/:digest/approve` | Exact-release operator approval against expected active base. |
| `POST /api/releases/:digest/activate` | Checked compare-and-swap activation. |
| `POST /api/approvals/:id/revoke` | Prevent future use of the approval; does not erase an earlier valid activation. |
| `POST /api/jobs/:id/migrations/preview` | Compute a non-mutating concrete compatibility preview. |
| `POST /api/jobs/:id/migrations/apply` | Apply the operator-approved plan to the expected paused revision. |

Internal runner/verifier callbacks use a separate authenticated channel not exposed in candidate containers. Callback credentials are attempt/role scoped and cannot activate releases. Where practical, keep those credentials in the supervisor rather than the model process.

Provide equivalent CLI commands for `doctor`, `serve`, `job submit/show/pause/resume/cancel`, `change propose/show`, `release show/approve/activate`, `migrate preview/apply`, `journal verify/export`, `demo`, and `recovery pause-all`. These are product CLI names, not Codex subcommands.

Bind to loopback by default; require an operator token/session even locally. Validate Host/Origin and protect state-changing requests against CSRF. Never place the operator token in candidate context or SSE URLs. Do not expose an unauthenticated privileged UI by switching the bind address. Remote hosting is outside v1.

## 17. UI requirements

Build a functional, restrained interface before adding decoration.

**Jobs:** readable table, state filters, pinned release, last actual progress, pending cleanup, budgets, and creation time. Drill into steps, multiple attempts, role-specific evidence, and immutable artifact links.

**Job detail:** separate authorization, OS observation, transport outcome, accepted result, and cleanup. Show cancellation as effective immediately for authority while cleanup remains visible. Preserve journal ordering across SSE reconnects; deduplicate by sequence.

**Improve:** request editor; selected base; current budget; source/graph changes; why a task can now run in parallel; which obligations are retained; rejected candidates and actual diagnostics.

**Release review:** exact release/payload/source digests; proof statement names and statuses; trusted assumptions; protected versus supplemental test results; reproduction/refutation outcomes; migration options; clear approve/reject/activate controls. Approval pages are served by the protected UI, not candidate HTML.

**Assurance:** display distinct labels such as `proof replay passed`, `runtime guard checked`, `integration test passed`, `model review: pass`, `inconclusive`, and `outside verified boundary`. Never show a single “formally verified system” badge.

Render candidate Markdown/JSON as untrusted content: escape HTML, sanitize links, disable executable embeds, and do not render logs as terminal control sequences. Full keyboard operation and visible focus are required; status must not rely on color alone.

## 18. Acceptance tests — release blocking

These are required executable tests, not an aspirational checklist. Use deterministic barriers/fault hooks rather than sleeps wherever possible. Preserve traces and artifacts for failures.

| ID | Scenario and expected result |
|---|---|
| A01 | **Happy path:** real protected build/proof checking and two distinct review attempts complete; report/release publication requires their matching evidence. |
| A02 | **Restart after committed completion:** restart before the next step; the committed step is not reinvoked and its artifact is unchanged. |
| A03 | **Stale result:** expire A, authorize B, then deliver A's success; reject A without overwriting B/current state. |
| A04 | **Duplicate callbacks:** deliver the same command/result repeatedly; one accepted commit and one semantic completion. |
| A05 | **Conflicting duplicate:** reuse a command ID or completed attempt with different bytes; conflict, not overwrite. |
| A06 | **Cancellation race:** barrier around authorization/launch/commit; after cancellation no new authority or accepted completion, and preauthorized processes are cleaned up. |
| A07 | **Lost supervisor/process:** kill it and recover; distinguish lost authority from finished work and terminate descendants/containers. |
| A08 | **Launch uncertainty:** crash between container launch and recording success; recover without blindly double-launching and fence any old result. |
| A09 | **Mixed source evidence:** review payload A, alter one source/prompt byte to B, and try publication; reject stale evidence. |
| A10 | **Missing/negative review:** remove refutation, forge its role in model JSON, or return inconclusive; no publication. |
| A11 | **Protected file edit:** propose changes to kernel, verifier, contracts, build files, or isolation profile; reject materialization. |
| A12 | **Proof cheats:** all §9.4 cheating fixtures fail for recorded reasons; raw stdout cannot create a verifier receipt. |
| A13 | **Activation race:** two approvals based on P0; activate one, then the other; the second gets `BASE_RELEASE_CHANGED`. |
| A14 | **Create/activate race:** every new job pins exactly one complete release; no new prompts with an old workflow. |
| A15 | **Safe migration:** pause/quiesce a P0 audit job with committed build/proof work; migrate to P1; reuse allowed results exactly and complete outstanding reviews. |
| A16 | **Unsafe migration:** changed completed fingerprint, unmet new prerequisite, missing result, active attempt, or stale preview; reject without moving versions. |
| A17 | **Pinning:** ineligible/unselected jobs finish on P0 after P1 activation. P0 artifacts stay retained. |
| A18 | **Rollback:** activate P0 again for new jobs; P1 jobs/history do not silently change. |
| A19 | **CLI failure modes:** test malformed/truncated output, nonzero exit, output overflow, unknown telemetry, timeout, auth failure, and unsupported `--exec`; no false success/provider fallback. |
| A20 | **Forbidden execution/credentials:** requested model shell/subagent/connector actions are unavailable; candidate build code cannot read a planted credential sentinel or controller data. |
| A21 | **Path attacks:** traversal, symlinks, wrong preimage hashes, and oversized edits cannot escape staging or replace protected artifacts. |
| A22 | **Replay:** rebuild authoritative state from genesis and the accepted journal; match canonical state/result/effect identities without another LLM call. |
| A23 | **Crash persistence:** inject failures around blob fsync/rename, journal commit, receipt return, and outbox dispatch; no committed dangling artifact or invented success. |
| A24 | **Invariant testing:** generate arbitrary valid/invalid command traces and compare the actual executable kernel with expected invariant checks; include paused/cancelled/expired/migrated states. |
| A25 | **Nonvacuity:** work is eventually dispatched under a fair healthy test harness; the tested positive case reaches publication. Empty-plan/reject-all variants fail. This is a test, not a general liveness proof. |
| A26 | **Real recursion:** P0 produces P1; P1 produces P2; executed planner hashes change; proofs/evidence are bound to those hashes and no external hand patch activates them. |
| A27 | **Equivalence improvement:** the P2 general planner-equivalence theorem passes; deterministic fixtures match and measured benchmarks are recorded. |
| A28 | **Budgets:** retries, crashes, child jobs, and revised candidates do not reset parent limits; exhausted budgets block new authorization. |
| A29 | **Approval integrity:** forged/changed-digest/revoked approvals fail; revocation does not retroactively falsify the history of an earlier authorized activation. |
| A30 | **No fake assurance:** with verifier/toolchain missing or unavailable, product can display diagnostics but cannot publish or activate a new self-update. |

For property tests, retain reproducible random seeds and minimized counterexamples. For fault tests, use a test-only controller harness; do not expose arbitrary fault injection in the production UI/API.

## 19. Required demonstration scripts

### 19.1 Deterministic integration demo

`workbench demo --fake-llm` uses a deterministic fake CLI boundary with prewritten responses but **real** kernel, SQLite, containers, Lean compilation, proof replay, and release gates. The UI/report must clearly say that inference was mocked. This is the normal offline CI path.

Run the six-stage founding demonstration in §0. Include a paused eligible audit job and a running/ineligible pinned job; show the distinction. Explicitly present the blocked review-bypass attempt and its rejection reason.

### 19.2 Live Codex demo

`workbench demo --live-codex` requires operator authentication and an explicit budget. It uses the real adapter for authoring, proof repair, reproduction/refutation interpretation, and summarization. The input must describe desired changes, not hand the model prewritten successor source as its output.

Store all invocation, candidate, proof, fault-test, approval, version, and migration evidence. Failure to author/prove within budget is a valid recorded failed experiment, not permission to substitute a canned success.

The acceptance bundle must state separately whether deterministic integration passed and whether the live demo was actually run and succeeded. Lack of available credentials in a build environment is reported honestly; live behavior is not claimed from mocks.

## 20. Implementation milestones and completion gates

Build in this order. Prefer a correct thin vertical slice to many placeholder screens.

**M0 — Reproducible foundation.** Repository layout, pinned toolchain, Codex/OCI `doctor`, strict codecs/digest vectors, genesis fixture, fixed build/check commands, and state-directory isolation. Gate: exact CLI invocation works in the supported environment, forbidden tools are blocked, and a trivial Lean program/proof replays. Record unsupported environmental requirements explicitly.

**M1 — Authoritative kernel.** Implement types, lifecycle, publication/activation/migration guards, and initial proofs K01–K12. Compile and invoke the actual core through a minimal CLI. Gate: initialization/preservation/target proofs, source-bound executable, positive scenario, and targeted semantic mutants. The first transition path must already use Lean; do not build a parallel TS authority “temporarily.”

**M2 — Durable execution.** SQLite command journal, idempotency, blob store, outbox, supervisor, fake Codex adapter, restart/fencing/cancel logic. Gate: A02–A08, A21–A24, A28. No polished UI needed yet.

**M3 — Real model boundary and review jobs.** Codex structured calls, trusted patch materializer, credential-free build/proof/test runners, independent contexts, exact subject binding, bounded repairs. Gate: A01, A09–A12, A19–A20, A30. Distinguish positive model review from authoritative verification.

**M4 — Protected releases and coexistence.** Bundle identities, verifier receipts, operator approval, atomic activation, pinning, supported migrations, rollback. Gate: A13–A18, A29, migration general proofs, and concrete previews.

**M5 — In-product self-improvement.** Functional UI and CLI plus P0→P1→P2 workflow. Gate: A25–A27 and deterministic end-to-end demo. This is the first complete realization of the concept.

**M6 — Hardening and handoff.** Full fault/mutation suite, operator docs, honest assurance matrix, resource/error handling, live demo where credentials permit. Gate: complete evidence bundle with each requirement passed/failed/not-run and no hidden skips.

Proofs must be completed before verified self-update is enabled. Intermediate development can show `not verified`, but there is no “accept anyway” button. If an obligation is difficult, keep it intact, save progress, reduce nonessential scope, and report the blocker. Never substitute a theorem about an unused simplified model.

## 21. Deliverables from the coding agent

Deliver runnable source, exact setup instructions, pinned dependencies/images, database initialization, `doctor`, a seeded genesis release, all Lean sources and proof checks, deterministic fake-Codex fixtures, real adapter integration, automated fault/mutation tests, both demo commands, and the web/CLI interfaces.

Include:

- `README.md`: installation, authentication boundary, run/check commands, and an end-to-end example.
- `ASSURANCE.md`: property IDs → exact definitions/theorems → runtime callsites → tests → assumptions/exclusions. Include toolchain/checker identities and unresolved items.
- `TOOLCHAIN.md`: versions, image digests, offline dependency provisioning, and independent proof-checker setup.
- `RECOVERY.md`: journal verification, stalled/lost worker cleanup, paused recovery, package rollback versus backup restoration.
- `DEMO-RESULTS.md`: actually executed commands, artifacts/digests, true outcomes, measured improvement, and whether inference was real or mocked.
- `OPEN-ITEMS.md`: incomplete work and its consequence for activation or assurance.

Provide one top-level `scripts/check-all` command that fails on any required failed/missing check. Fast developer tests can be separate. Skipping live inference without credentials is allowed only as an explicit not-run status; skipping protected proof replay cannot produce a release-ready status.

## 22. Design rules that must survive implementation

1. The current product builds/evaluates its successor; the candidate never judges its own admissibility.
2. Proof targets refer to executed definitions or explicitly bounded wrapper assumptions, not an unrelated model.
3. A result, proof, test, review, and approval are each bound to the exact relevant immutable subject.
4. Agents propose; authenticated fixed services commit observations; the protected kernel admits state transitions.
5. The journal is the recovery authority; a model session or in-memory concurrency order is not.
6. Pin first, migrate explicitly, preserve history, and never turn unknown/missing evidence into success.
7. Distinguish failures, rejected changes, unavailable tools, and inconclusive checks. They are not interchangeable.
8. Self-improvement can change executable orchestration, but cannot edit its own safety boundary in v1.

## 23. Definition of done

The product runs a real multistage package-audit job; recovers committed work after failures; safely rejects stale/duplicate/conflicting results; accepts a Codex-authored successor package only after source-bound proof checking and required reviews; activates it with exact human approval; keeps existing jobs correctly pinned or explicitly migrates eligible paused jobs; and uses that successor to build a second executable improvement.

The protected checks reject a candidate that bypasses refutation even when the model claims it is safe. The implementation and documentation accurately distinguish the proven internal guarantees from trusted wrappers and unverified behavior. The deterministic demonstration passes without external hand-editing of live orchestration. A live demonstration is reported only if actually executed.

## 24. Source and interpretation notes

These sources establish the limited factual basis below. They do not endorse this design. Source-derived details and the product's new normative requirements must remain distinguishable.

**[R1] Methods report (private, not included in this repository):** *CPython free-threading verification: methods report*, September 24, 2026, `cpython-proof.md`. Lines 148–174 describe the wake-behavior/model gap and proof exclusions. Lines 154–163 describe proof auditing. Lines 276–281 describe dead agents reported as running, orphaned solver processes, journal-based resumption, and timeout misclassification. These motivate the implementation-link, provenance, process, and recovery requirements; they do not demonstrate this proposed workbench is correct.

**[S1] OpenAI, Non-interactive mode**, checked September 26, 2026. Documents `codex exec`, stdin prompts, JSONL, structured outputs, and authentication cautions. Original official entry point: `https://developers.openai.com/codex/noninteractive` (redirected when checked to `https://learn.chatgpt.com/docs/non-interactive-mode`).

**[S2] OpenAI, Codex CLI / Developer commands**, checked September 26, 2026. Flag/command reference, including `exec`, JSON/output options, and approval/sandbox controls. `https://developers.openai.com/codex/cli/reference` (redirected when checked to `https://learn.chatgpt.com/docs/developer-commands?surface=cli`).

**[S3] OpenAI, Configuration Reference**, checked September 26, 2026. Configuration controls for shell execution, agents, applications, and approvals. `https://developers.openai.com/codex/config-reference` (redirected when checked to `https://learn.chatgpt.com/docs/config-file/config-reference`). Pin/test actual installed behavior; these references are not a promise of future CLI compatibility.

**[S4] The Lean Developers, The Lean Language Reference**, checked September 26, 2026. Lean is both an executable language and a proof environment; this spec's use of a common source for runtime functions and proofs is a design choice, not proof of compilation or deployment correctness. `https://lean-lang.org/doc/reference/latest/Introduction/`.

**[S5] SQLite, Transaction documentation**, checked September 26, 2026. Basis for treating transaction boundaries and explicit write serialization as part of the persistence design. `https://www.sqlite.org/lang_transaction.html`.

