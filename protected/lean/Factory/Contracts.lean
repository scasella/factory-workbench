import Factory.Check
import Factory.PackageContracts
/-
  Factory.Contracts — PROTECTED property definitions K01–K12 over the
  EXECUTED kernel definitions (`Factory.apply`, `Factory.Check.*`).
  These statements are advertised in ASSURANCE.md and must not be weakened.
  Proofs live in Factory/Proofs.lean.

  Conventions:
  * State invariants are stated over the same Boolean functions used by the
    runtime checker (`Factory.Check`), so the runtime oracle and the theorem
    agree by construction.
  * Transition properties quantify over EVERY authenticated envelope `e` and
    every accepted transition `apply s e = .ok t`.
-/
namespace Factory.Contracts
open Factory Factory.Check

/-- States reachable from the empty pre-bootstrap state by accepted
    transitions of the executed kernel. -/
inductive Reachable : State → Prop
  | init : Reachable emptyState
  | step {s : State} {e : Envelope} {t : Transition} :
      Reachable s → apply s e = .ok t → Reachable t.state

/-- Reflexive-transitive closure of accepted transitions. -/
inductive Steps : State → State → Prop
  | refl (s : State) : Steps s s
  | step {s u : State} {e : Envelope} {t : Transition} :
      apply s e = .ok t → Steps t.state u → Steps s u

/-! ### State invariants -/

/-- K01 well-formed state. -/
def K01 (s : State) : Prop :=
  idsUnique s = true ∧ releasesOk s = true ∧ changesOk s = true ∧
  ∀ j ∈ s.jobs, jobPinned s j = true ∧ attemptsConsistent j = true ∧ acceptedConsistent j = true

/-- K02 (state part): one logical step state per stable step ID in each job. -/
def K02 (s : State) : Prop := ∀ j ∈ s.jobs, (j.steps.map (·.id)).Nodup

/-- K03 (state part): each accepted completion records an acceptance tick
    strictly before its acceptance-time lease deadline. -/
def K03 (s : State) : Prop := ∀ j ∈ s.jobs, acceptedFenced j = true

/-- K05 (state part): terminal jobs hold no live authority. -/
def K05 (s : State) : Prop := ∀ j ∈ s.jobs, terminalQuiet j = true

/-- K06 (state part): every non-genesis release is backed by its evaluation
    job's passing, subject-bound, contract-bound required evidence. -/
def K06 (s : State) : Prop := releasesEvidenced s = true

/-- K07 (state part): every non-root activation used a matching approval
    recorded against the same release and base. -/
def K07 (s : State) : Prop := activationsApproved s = true

/-- K10: resource authority within configured bounds. -/
def K10 (s : State) : Prop := resourcesOk s = true

def Safe (s : State) : Prop := K01 s ∧ K02 s ∧ K03 s ∧ K05 s ∧ K06 s ∧ K07 s ∧ K10 s

/-! ### Transition properties -/

def acceptedAt (s : State) (jid : JobId) (sid : StepId) : Option Accepted :=
  (s.findJob? jid).bind (fun j => (j.findStep? sid).bind (·.accepted))

/-- K02 (transition part): accepted completions are never replaced or removed. -/
def AcceptedStable (s s' : State) : Prop :=
  ∀ jid sid a, acceptedAt s jid sid = some a → acceptedAt s' jid sid = some a

/-- K03 (transition part): any completion newly accepted by a transition was
    delivered for the attempt that, in the pre-state, was the step's current,
    live attempt of the current job epoch and controller epoch, strictly
    before its lease deadline; the record stores that fencing identity. -/
def FencedAcceptance (s : State) (e : Envelope) (s' : State) : Prop :=
  ∀ jid sid a, acceptedAt s jid sid = none → acceptedAt s' jid sid = some a →
    ∃ j ∈ s.jobs, j.id = jid ∧ ∃ st ∈ j.steps, st.id = sid ∧ st.current = some a.gen ∧
      ∃ att ∈ j.attempts, att.step = sid ∧ att.gen = a.gen ∧ att.status.live = true ∧
        att.jobEpoch = j.epoch ∧ att.ctrlEpoch = s.ctrlEpoch ∧ e.tick < att.deadline ∧
        a.jobEpoch = att.jobEpoch ∧ a.ctrlEpoch = att.ctrlEpoch ∧ a.leaseDeadline = att.deadline ∧
        a.fingerprint = att.fingerprint ∧ a.subject = att.subject ∧ e.epoch = s.ctrlEpoch

def attemptIn (s : State) (jid : JobId) (sid : StepId) (g : Nat) : Option Attempt :=
  (s.findJob? jid).bind (fun j => j.findAttempt? sid g)

/-- Explicit (implementation-independent) statement that step `p` of job `j`
    has succeeded with an accepted result. -/
def StepDone (j : Job) (p : StepId) : Prop :=
  ∃ q ∈ j.steps, q.id = p ∧ q.status = .succeeded ∧ q.accepted.isSome = true

/-- K04: a newly authorized attempt had all prerequisites — every ordering
    edge AND every semantic producer — succeeded with an accepted result, and it
    carries exactly the semantic inputs of its step spec: the job input for
    `jobInput` bindings and the producer's accepted result digest for
    `stepOutput` bindings (stated explicitly, not via the kernel's own
    `prereqsDone`/`bindInputs`, so weakening those functions breaks the proof). -/
def DependencySafe (s : State) (s' : State) : Prop :=
  ∀ jid sid g a, attemptIn s jid sid g = none → attemptIn s' jid sid g = some a →
    ∃ j ∈ s.jobs, j.id = jid ∧ ∃ w, s.workflowOf j = some w ∧ ∃ spec ∈ w.steps, spec.id = sid ∧
      a.status = .authorized ∧
      (∀ p ∈ spec.after, StepDone j p) ∧
      a.inputs.length = spec.inputs.length ∧
      (∀ i < spec.inputs.length, ∀ b, spec.inputs[i]? = some b →
        match b.source with
        | .jobInput => a.inputs[i]? = some (b.name, j.input)
        | .stepOutput p => StepDone j p ∧ ∃ q ∈ j.steps, q.id = p ∧ ∃ acc, q.accepted = some acc ∧
            a.inputs[i]? = some (b.name, acc.result))

/-- K05 (transition part): after cancellation no new authority and no new
    acceptance for that job; terminal job statuses never change. -/
def CancellationFinal (s s' : State) : Prop :=
  ∀ j ∈ s.jobs, j.status.terminal = true →
    ∃ j' ∈ s'.jobs, j'.id = j.id ∧ j'.status = j.status ∧ j'.attempts.length = j.attempts.length ∧
      (∀ sid, (j'.findStep? sid).bind (·.accepted) = (j.findStep? sid).bind (·.accepted))

/-- Publication-gate roles fixed by the CONTRACT (restated here so that the
    guarantee does not depend on the kernel's own gate function). -/
def gateRoles : List Role := [.build, .prove, .reproduce, .refute]

/-- Explicit passing evidence for role `r` in job `j` under workflow `w`: a step
    whose ROLE COMES FROM THE PINNED WORKFLOW (not from model output) has an
    accepted result with outcome `pass` and status `succeeded`. -/
def PassingEvidence (j : Job) (w : WorkflowDef) (r : Role) (a : Accepted) : Prop :=
  ∃ sp ∈ w.steps, sp.role = r ∧ ∃ st ∈ j.steps, st.id = sp.id ∧ st.accepted = some a ∧
    a.outcome = .pass ∧ st.status = .succeeded

/-- The required-evidence conditions for job `j`, stated explicitly: passing
    build/prove/reproduce/refute evidence; build bound to the job's subject
    (frozen candidate) and producing payload `payload`; prove/reproduce/refute
    bound to that payload; trusted evidence carrying the current contract. -/
def RequiredEvidence (s : State) (j : Job) (w : WorkflowDef) (payload : Digest) (exports : List WorkflowDef) : Prop :=
  ∃ b p rp rf, PassingEvidence j w .build b ∧ PassingEvidence j w .prove p ∧
    PassingEvidence j w .reproduce rp ∧ PassingEvidence j w .refute rf ∧
    b.subject = j.subject ∧ b.produced = some payload ∧ b.exports = exports ∧
    p.subject = payload ∧ rp.subject = payload ∧ rf.subject = payload ∧
    b.contract = s.contract ∧ p.contract = s.contract

/-- K06 (transition part): every release or report publication implies the
    explicit required evidence for its job, and the published record is bound
    to that payload, the job's subject and the current contract. -/
def PublicationGated (s : State) (e : Envelope) (t : Transition) : Prop :=
  (∀ jid d as, e.cmd = .publishRelease jid d as →
    ∃ j ∈ s.jobs, j.id = jid ∧ j.kind = .changeEvaluate ∧ j.status = .succeeded ∧
      ∃ w, s.workflowOf j = some w ∧ ∃ payload exports, RequiredEvidence s j w payload exports ∧
        ∃ r ∈ t.state.releases, r.digest = d ∧ r.payload = payload ∧ r.workflows = exports ∧
          r.contract = s.contract ∧ r.source = j.subject) ∧
  (∀ jid d, e.cmd = .publishReport jid d →
    ∃ j ∈ s.jobs, j.id = jid ∧ j.kind = .packageAudit ∧ j.status = .succeeded ∧
      ∃ w, s.workflowOf j = some w ∧ ∃ payload exports, RequiredEvidence s j w payload exports ∧
        ∃ r ∈ t.state.reports, r.job = jid ∧ r.digest = d ∧ r.subject = payload)

/-- K07 (transition part): activation requires a live, unrevoked approval
    for the exact release digest against the exact expected active base,
    and the compare-and-swap base matches. -/
def ActivationBound (s : State) (e : Envelope) (t : Transition) : Prop :=
  ∀ rel base aid, e.cmd = .activateRelease rel base aid →
    s.active = some base ∧ t.state.active = some rel ∧
    ∃ ap ∈ s.approvals, ap.id = aid ∧ ap.release = rel ∧ ap.expectedBase = base ∧
      ap.revoked = false ∧ ap.contract = s.contract ∧ e.actor.isOperator = true

/-- K08: no transition other than an explicit MigrateJob changes any existing
    job's pinned release; a MigrateJob changes only the named job's pin; and
    activation (changing the default) leaves every job untouched.
    (Corrected 2026-09-26: an earlier draft placed `∀ jid tgt r` outside the
    `≠ migrateJob` premise, which made the statement false for every accepted
    migration — see PROOF-NOTES.md. This version states the intended property
    and additionally covers the jobs NOT named by a migration.) -/
def PinningPreserved (s : State) (e : Envelope) (t : Transition) : Prop :=
  ((∀ jid tgt r, e.cmd ≠ .migrateJob jid tgt r) →
    ∀ j ∈ s.jobs, ∃ j' ∈ t.state.jobs, j'.id = j.id ∧ j'.release = j.release) ∧
  (∀ jid tgt r, e.cmd = .migrateJob jid tgt r →
    ∀ j ∈ s.jobs, j.id ≠ jid → ∃ j' ∈ t.state.jobs, j'.id = j.id ∧ j'.release = j.release) ∧
  (∀ rel base aid, e.cmd = .activateRelease rel base aid → t.state.jobs = s.jobs)

/-- K09: a successful migration preserves every completed result exactly
    (with its original acceptance-time provenance), invents none, keeps the
    subject/input identity, keeps all attempt history, advances the job epoch
    (fencing), and leaves the job paused. -/
def MigrationPreserving (s : State) (e : Envelope) (t : Transition) : Prop :=
  ∀ jid tgt r, e.cmd = .migrateJob jid tgt r →
    ∃ j ∈ s.jobs, j.id = jid ∧ j.status = .paused ∧ j.revision = r ∧
    ∃ j' ∈ t.state.jobs, j'.id = jid ∧ j'.release = tgt ∧ j'.subject = j.subject ∧
      j'.input = j.input ∧ j'.epoch = j.epoch + 1 ∧ j'.attempts = j.attempts ∧
      j'.status = .paused ∧
      (∀ sid a, (j.findStep? sid).bind (·.accepted) = some a → (j'.findStep? sid).bind (·.accepted) = some a) ∧
      (∀ sid a, (j'.findStep? sid).bind (·.accepted) = some a → (j.findStep? sid).bind (·.accepted) = some a)

/-- K12: every launch intent returned by an accepted transition names an
    attempt that this transition newly authorized in the post-state; every
    publication intent names a release/report present in the post-state. -/
def EffectCausality (s : State) (t : Transition) : Prop :=
  ∀ eff ∈ t.effects,
    (eff.kind = .launch → attemptIn s eff.job eff.step eff.gen = none ∧
      ∃ a, attemptIn t.state eff.job eff.step eff.gen = some a ∧ a.status = .authorized ∧
        a.inputs = eff.inputs ∧ a.subject = eff.subject) ∧
    (eff.kind = .releasePublished → ∃ r ∈ t.state.releases, r.digest = eff.subject) ∧
    (eff.kind = .reportPublished → ∃ r ∈ t.state.reports, r.job = eff.job ∧ r.digest = eff.subject)

end Factory.Contracts
