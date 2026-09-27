import Factory.Kernel
/-
  Factory.Check — executable invariant diagnostics over kernel state.
  Used at runtime (startup integrity check, `journal verify`) and by the
  property-test harness (A24) as the oracle compared against the executable
  kernel. The Prop-level contracts in `Contracts.lean` are stated over these
  same Boolean definitions where noted, so the oracle and the theorems agree.
-/
namespace Factory.Check
open Factory

def noDupBy {α} [BEq α] : List α → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && noDupBy xs

/-- K01: unique IDs. -/
def idsUnique (s : State) : Bool :=
  noDupBy (s.jobs.map (·.id)) && noDupBy (s.releases.map (·.digest)) &&
  noDupBy (s.budgets.map (·.id)) && noDupBy (s.approvals.map (·.id)) &&
  noDupBy (s.changes.map (·.id))

/-- K01: each job is pinned to an installed release whose workflow for the
    job kind is well-formed, and the job's step list mirrors that workflow. -/
def jobPinned (s : State) (j : Job) : Bool :=
  match s.workflowOf j with
  | some w => wellFormedWorkflow w && j.steps.map (·.id) == w.steps.map (·.id) &&
              (s.findBudget? j.budget).isSome
  | none => false

/-- K01: attempt/step authority relationships are consistent. -/
def attemptsConsistent (j : Job) : Bool :=
  noDupBy (j.attempts.map (·.gen)) &&
  j.attempts.all (fun a => decide (1 ≤ a.gen) && decide (a.gen ≤ j.attempts.length)) &&
  j.steps.all (fun st => match st.current with
    | some g => match j.findAttempt? st.id g with
      | some a => a.status.live && st.status == .active && st.accepted.isNone
      | none => false
    | none => st.status != .active) &&
  j.attempts.all (fun a => !a.status.live ||
    (match j.findStep? a.step with
     | some st => st.current == some a.gen
     | none => false))

/-- K01: accepted results exist exactly for settled steps. -/
def acceptedConsistent (j : Job) : Bool :=
  j.steps.all (fun st => match st.accepted with
    | some a => st.current.isNone && st.status == stepStatusOf a.outcome
    | none => st.status == .pending || st.status == .active || st.status == .failed)

/-- K01: change requests reference an existing budget and base release. -/
def changesOk (s : State) : Bool :=
  s.changes.all (fun c => (s.findBudget? c.budget).isSome && (s.findRelease? c.base).isSome)

/-- K03: every accepted completion was accepted strictly within its lease. -/
def acceptedFenced (j : Job) : Bool :=
  j.steps.all (fun st => match st.accepted with
    | some a => decide (a.acceptedAt < a.leaseDeadline) && a.gen ≤ j.attempts.length
    | none => true)

/-- K05: a terminal job holds no live authority. -/
def terminalQuiet (j : Job) : Bool := !j.status.terminal || j.liveAttempts.isEmpty

/-- K10: resource authority within configured bounds. -/
def resourcesOk (s : State) : Bool :=
  s.budgets.all (fun b => decide (b.used ≤ b.limit)) &&
  decide (s.liveOfClass .llm ≤ s.config.llmSlots) &&
  decide (s.liveOfClass .container ≤ s.config.containerSlots) &&
  s.jobs.all (fun j => match s.workflowOf j with
    | some w => decide (j.liveAttempts.length ≤ w.maxParallel)
    | none => j.liveAttempts.isEmpty)

/-- K01: releases well-formed, active release installed. -/
def releasesOk (s : State) : Bool :=
  s.releases.all (fun r => exportsOk r.workflows) &&
  (match s.active with
   | some d => (s.findRelease? d).isSome && s.wasActivated d
   | none => s.releases.isEmpty) &&
  (s.releases.filter (·.evidenceJob.isNone)).length ≤ 1

/-- K06: every non-genesis release is backed by passing, correctly bound
    required evidence in its (terminal, frozen) evaluation job. -/
def releasesEvidenced (s : State) : Bool :=
  s.releases.all (fun r => match r.evidenceJob with
    | none => true
    | some jid => match s.findJob? jid with
      | some j => j.kind == .changeEvaluate && j.status == .succeeded &&
        (match s.workflowOf j with
         | some w => match gatesPass s j w with
           | .ok (p, ws) => p == r.payload && ws == r.workflows && r.source == j.subject
           | .error _ => false
         | none => false)
      | none => false)

/-- K07: every non-root activation used a matching recorded approval. -/
def activationsApproved (s : State) : Bool :=
  s.activations.all (fun a => match a.approval with
    | none => a.base.isNone
    | some id => s.approvals.any (fun ap => ap.id == id && ap.release == a.release &&
                                              some ap.expectedBase == a.base)) &&
  (s.activations.filter (·.approval.isNone)).length ≤ 1

def violations (s : State) : List String :=
  (if idsUnique s then [] else ["K01: duplicate identifiers"]) ++
  (if releasesOk s then [] else ["K01: release/active-release inconsistency"]) ++
  (if changesOk s then [] else ["K01: change request references missing budget/release"]) ++
  (s.jobs.filter (fun j => !jobPinned s j)).map (fun j => s!"K01: job {j.id} not pinned to a well-formed installed workflow") ++
  (s.jobs.filter (fun j => !attemptsConsistent j)).map (fun j => s!"K01: job {j.id} attempt/authority inconsistency") ++
  (s.jobs.filter (fun j => !acceptedConsistent j)).map (fun j => s!"K02: job {j.id} accepted/status inconsistency") ++
  (s.jobs.filter (fun j => !acceptedFenced j)).map (fun j => s!"K03: job {j.id} accepted outside lease") ++
  (s.jobs.filter (fun j => !terminalQuiet j)).map (fun j => s!"K05: terminal job {j.id} holds authority") ++
  (if resourcesOk s then [] else ["K10: resource bound exceeded"]) ++
  (if releasesEvidenced s then [] else ["K06: release without matching required evidence"]) ++
  (if activationsApproved s then [] else ["K07: activation without matching approval"])

end Factory.Check
