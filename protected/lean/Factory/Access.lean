import Factory.Workflow
/-
  Factory.Access — pure lookup/update helpers over kernel state.
-/
namespace Factory

def need {α} (o : Option α) (r : RejectReason) : Except RejectReason α :=
  match o with
  | some a => .ok a
  | none => .error r

def check (b : Bool) (r : RejectReason) : Except RejectReason Unit :=
  if b then .ok () else .error r

def State.findJob? (s : State) (id : JobId) : Option Job := s.jobs.find? (·.id == id)

/-- Replace the job with the same ID, bumping its revision. -/
def State.putJob (s : State) (j : Job) : State :=
  { s with jobs := s.jobs.map (fun x => if x.id == j.id then { j with revision := x.revision + 1 } else x) }

def State.findRelease? (s : State) (d : Digest) : Option Release := s.releases.find? (·.digest == d)

def State.workflowOf (s : State) (j : Job) : Option WorkflowDef :=
  (s.findRelease? j.release).bind (fun r => workflowFor r.workflows j.kind)

def State.findBudget? (s : State) (id : BudgetId) : Option Budget := s.budgets.find? (·.id == id)

def State.putBudget (s : State) (b : Budget) : State :=
  { s with budgets := s.budgets.map (fun x => if x.id == b.id then b else x) }

def State.findChange? (s : State) (id : ChangeId) : Option Change := s.changes.find? (·.id == id)

def State.putChange (s : State) (c : Change) : State :=
  { s with changes := s.changes.map (fun x => if x.id == c.id then c else x) }

def State.findApproval? (s : State) (id : ApprovalId) : Option Approval := s.approvals.find? (·.id == id)

def State.wasActivated (s : State) (d : Digest) : Bool := s.activations.any (·.release == d)

def Job.findStep? (j : Job) (id : StepId) : Option StepState := j.steps.find? (·.id == id)

def Job.setStep (j : Job) (st : StepState) : Job :=
  { j with steps := j.steps.map (fun x => if x.id == st.id then st else x) }

def Job.findAttempt? (j : Job) (step : StepId) (gen : Nat) : Option Attempt :=
  j.attempts.find? (fun a => a.step == step && a.gen == gen)

def Job.setAttempt (j : Job) (a : Attempt) : Job :=
  { j with attempts := j.attempts.map (fun x => if x.step == a.step && x.gen == a.gen then a else x) }

def Job.liveAttempts (j : Job) : List Attempt := j.attempts.filter (·.status.live)

def Job.liveOfClass (j : Job) (c : ResourceClass) : Nat :=
  (j.attempts.filter (fun a => a.status.live && a.role.resource == c)).length

def State.liveOfClass (s : State) (c : ResourceClass) : Nat :=
  (s.jobs.map (fun j => j.liveOfClass c)).sum

def ResourceClass.limit (cfg : Config) : ResourceClass → Nat
  | .llm => cfg.llmSlots
  | .container => cfg.containerSlots

/-- A step's prerequisites have all succeeded (accepted with outcome pass). -/
def prereqsDone (j : Job) (spec : StepSpec) : Bool :=
  spec.prereqs.all (fun p => match j.findStep? p with
    | some st => st.status == .succeeded
    | none => false)

def StepState.idle (st : StepState) : Bool :=
  st.status == .pending && st.current.isNone && st.accepted.isNone

def dispatchable (st : JobStatus) : Bool := st == .queued || st == .running

/-- Kernel eligibility: the set the planner may choose from. -/
def readySteps (s : State) (j : Job) : List StepId :=
  match s.workflowOf j with
  | none => []
  | some w =>
    if dispatchable j.status then
      (w.steps.filter (fun spec => match j.findStep? spec.id with
        | some st => st.idle && prereqsDone j spec
        | none => false)).map (·.id)
    else []

def Budget.remaining (b : Budget) : Nat := b.limit - b.used

/-- Effective concurrency bound offered to the planner. -/
def plannerSlots (s : State) (j : Job) : Nat :=
  match s.workflowOf j, s.findBudget? j.budget with
  | some w, some b => min (w.maxParallel - j.liveAttempts.length) b.remaining
  | _, _ => 0

def payloadOf (j : Job) (w : WorkflowDef) : Option Digest :=
  match w.uniqueRole .build with
  | some b => match j.findStep? b.id with
    | some st => st.accepted.bind (fun a => if a.outcome == .pass then a.produced else none)
    | none => none
  | none => none

/-- Subject bound by the kernel (never by model output). -/
def subjectFor (j : Job) (w : WorkflowDef) (spec : StepSpec) : Option Digest :=
  match spec.role with
  | .build | .author | .materialize => some j.subject
  | _ => payloadOf j w

def bindInputs (j : Job) (spec : StepSpec) : Option (List (String × Digest)) :=
  spec.inputs.mapM (fun b => match b.source with
    | .jobInput => some (b.name, j.input)
    | .stepOutput p => (j.findStep? p).bind (fun st => st.accepted.map (fun a => (b.name, a.result))))

def combineOutcome : Outcome → Outcome → Outcome
  | .pass, .pass => .pass
  | .fail, _ => .fail
  | _, .fail => .fail
  | _, _ => .inconclusive

def stepStatusOf : Outcome → StepStatus
  | .pass => .succeeded
  | .fail => .failed
  | .inconclusive => .blocked

def jobStatusAfter (j : Job) : JobStatus :=
  if j.steps.any (·.status == .failed) then .failed
  else if j.steps.any (·.status == .blocked) then .blocked
  else if j.steps.all (·.status == .succeeded) then .succeeded
  else j.status

def launchId (j : JobId) (s : StepId) (g : Nat) : String := s!"launch:{j}:{s}:{g}"
def terminateId (j : JobId) (s : StepId) (g : Nat) : String := s!"terminate:{j}:{s}:{g}"

def terminateEffect (j : Job) (a : Attempt) : EffectIntent :=
  { id := terminateId j.id a.step a.gen, kind := .terminate, job := j.id, step := a.step,
    gen := a.gen, subject := a.subject, inputs := [] }

/-- Revoke every live attempt of a job: attempts get `newStatus`, steps lose
    authority, and terminate intents are emitted. -/
def StepState.dropAuthority (st : StepState) : StepState :=
  if st.current.isSome then
    { st with current := none, status := (if st.status == .active then .pending else st.status) }
  else st

def Attempt.revokeTo (newStatus : AttemptStatus) (a : Attempt) : Attempt :=
  if a.status.live then { a with status := newStatus } else a

def Job.revokeLive (j : Job) (newStatus : AttemptStatus) : Job × List EffectIntent :=
  ({ j with attempts := j.attempts.map (Attempt.revokeTo newStatus),
            steps := j.steps.map StepState.dropAuthority },
   j.liveAttempts.map (terminateEffect j))

/-- Recompute job status after a step changed; a job that becomes terminal
    revokes its remaining live attempts. -/
def finalizeJob (j : Job) : Job × List EffectIntent :=
  let st := jobStatusAfter j
  if st.terminal && !j.status.terminal then
    let r := j.revokeLive .cancelled
    ({ r.1 with status := st }, r.2)
  else ({ j with status := st }, [])

end Factory
