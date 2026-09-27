import Factory.Migration
/-
  Factory.Kernel — the authoritative pure transition function.
  No clock, database, LLM, filesystem or network: every observation arrives
  in the authenticated `Envelope`. The coordinator persists exactly what this
  function returns; it has no alternative success/authorization path.
-/
namespace Factory

def Actor.isOperator : Actor → Bool
  | .operator _ => true
  | _ => false

def Actor.name : Actor → String
  | .operator n => n
  | .coordinator => "coordinator"
  | .supervisor => "supervisor"
  | .verifier => "verifier"

def Role.verifierRole : Role → Bool
  | .build | .prove => true
  | _ => false

/-- Fixed actor-permission table. Human-only commands require an operator. -/
def permitted (a : Actor) : Command → Bool
  | .bootstrap .. | .createJob .. | .pauseJob .. | .resumeJob .. | .cancelJob ..
  | .createChange .. | .recordApproval .. | .revokeApproval .. | .activateRelease ..
  | .migrateJob .. => a.isOperator
  | .reviseChange .. => a.isOperator || a == .coordinator
  | .startAttempt .. | .observeLaunchDispatched .. | .expireAttempt ..
  | .acknowledgeQuiescence .. | .registerCandidate .. | .publishReport ..
  | .publishRelease .. | .recoverController => a == .coordinator
  | .observeProcessStarted .. | .heartbeat .. | .commitResult .. => a == .supervisor
  | .recordVerification .. => a == .verifier
  | .failAttempt .. => a == .supervisor || a == .verifier

def emptyState : State :=
  { ctrlEpoch := 0, clock := 0, contract := "", config := default, releases := [],
    active := none, activations := [], approvals := [], jobs := [], budgets := [],
    changes := [], migrations := [], reports := [] }

def ok (s : State) (evs : List DomainEvent) (effs : List EffectIntent := []) :
    Except RejectReason Transition :=
  .ok { state := s, events := evs, effects := effs }

/-! ### Bootstrap (human-authorized trust root, §12.1) -/

def doBootstrap (s : State) (e : Envelope) (g : Release) (contract : Digest) (cfg : Config) :
    Except RejectReason Transition := do
  check s.releases.isEmpty .alreadyBootstrapped
  check (g.digest.valid && g.payload.valid && g.source.valid && contract.valid) .invalidDigest
  check (exportsOk g.workflows) .invalidWorkflow
  check (cfg.llmSlots ≥ 1 && cfg.containerSlots ≥ 1 && cfg.leaseTicks ≥ 1) .limitExceeded
  let g' := { g with contract := contract, evidenceJob := none, producer := none, parent := none }
  ok { s with contract := contract, config := cfg, releases := [g'], active := some g.digest,
              activations := [{ release := g.digest, base := none, approval := none, atTick := e.tick }] }
    [.releasePublished g.digest, .releaseActivated g.digest]

/-! ### Jobs -/

def newJob (id : JobId) (kind : JobKind) (rel : Digest) (w : WorkflowDef) (input subject : Digest)
    (budget : BudgetId) (change : Option ChangeId) : Job :=
  { id := id, kind := kind, release := rel, input := input, subject := subject, epoch := 0,
    status := .queued, steps := w.steps.map (fun sp => freshStep sp.id), attempts := [],
    budget := budget, change := change, revision := 0 }

/-- Validates and constructs a job pinned to `rel`, atomically with creation. -/
def mkJob (s : State) (id : JobId) (kind : JobKind) (rel : Digest) (input subject : Digest)
    (budget : BudgetId) (change : Option ChangeId) : Except RejectReason Job := do
  check (s.findJob? id).isNone .duplicateJob
  check (s.jobs.length < s.config.maxJobs) .limitExceeded
  check (input.valid && subject.valid) .invalidDigest
  check (id != "") .unknownJob
  let r ← need (s.findRelease? rel) .unknownRelease
  check (s.wasActivated rel) .releaseNotActivated
  let w ← need (workflowFor r.workflows kind) .invalidWorkflow
  check (wellFormedWorkflow w) .invalidWorkflow
  check (w.steps.length ≤ s.config.maxSteps) .limitExceeded
  return newJob id kind rel w input subject budget change

def doCreateJob (s : State) (id : JobId) (kind : JobKind) (input subject : Digest)
    (rel? : Option Digest) (budget : BudgetId) (limit : Nat) : Except RejectReason Transition := do
  check (kind == .packageAudit) .wrongRole
  check (s.findBudget? budget).isNone .duplicateJob
  check (budget != "") .unknownJob
  let rel ← need (rel?.orElse (fun _ => s.active)) .unknownRelease
  let j ← mkJob s id kind rel input subject budget none
  ok { s with jobs := s.jobs ++ [j], budgets := s.budgets ++ [{ id := budget, limit := limit, used := 0 }] }
    [.jobCreated id rel]

def doStartAttempt (s : State) (e : Envelope) (jid : JobId) (sid : StepId) (fp : Digest) :
    Except RejectReason Transition := do
  let j ← need (s.findJob? jid) .unknownJob
  check (dispatchable j.status) .jobNotDispatchable
  let w ← need (s.workflowOf j) .unknownRelease
  let spec ← need (w.find? sid) .unknownStep
  let st ← need (j.findStep? sid) .unknownStep
  check st.idle .stepHasAuthority
  check (prereqsDone j spec) .stepNotEligible
  check fp.valid .invalidDigest
  let subj ← need (subjectFor j w spec) .stepNotEligible
  let ins ← need (bindInputs j spec) .stepNotEligible
  let b ← need (s.findBudget? j.budget) .budgetExhausted
  check (b.used < b.limit) .budgetExhausted
  check (j.liveAttempts.length < w.maxParallel) .concurrencyBound
  check (s.liveOfClass spec.role.resource < spec.role.resource.limit s.config) .noSlots
  let gen := j.attempts.length + 1
  let a : Attempt := { step := sid, role := spec.role, gen := gen, jobEpoch := j.epoch,
                       ctrlEpoch := s.ctrlEpoch, deadline := e.tick + s.config.leaseTicks, status := .authorized,
                       subject := subj, fingerprint := fp, inputs := ins, container := "" }
  let j' : Job := { j with attempts := j.attempts ++ [a], status := .running }
  let j'' := j'.setStep { st with status := .active, current := some gen }
  let s' := (s.putJob j'').putBudget { b with used := b.used + 1 }
  ok s' [.attemptAuthorized jid sid gen]
    [{ id := launchId jid sid gen, kind := .launch, job := jid, step := sid, gen := gen,
       subject := subj, inputs := ins }]

/-- Locate the current, live, correctly-fenced attempt. -/
def currentAttempt (s : State) (j : Job) (sid : StepId) (gen : Nat) :
    Except RejectReason (StepState × Attempt) := do
  let st ← need (j.findStep? sid) .unknownStep
  let a ← need (j.findAttempt? sid gen) .unknownAttempt
  check (st.current == some gen) .notCurrentAttempt
  check a.status.live .notCurrentAttempt
  check (a.jobEpoch == j.epoch && a.ctrlEpoch == s.ctrlEpoch) .notCurrentAttempt
  return (st, a)

def doObserveDispatched (s : State) (jid : JobId) (sid : StepId) (gen : Nat) :
    Except RejectReason Transition := do
  let j ← need (s.findJob? jid) .unknownJob
  check (!j.status.terminal) .jobTerminal
  let (_, a) ← currentAttempt s j sid gen
  check (a.status == .authorized) .notCurrentAttempt
  ok (s.putJob (j.setAttempt { a with status := .starting })) [.attemptObserved jid sid gen .starting]

def doObserveStarted (s : State) (e : Envelope) (jid : JobId) (sid : StepId) (gen : Nat) (c : String) :
    Except RejectReason Transition := do
  let j ← need (s.findJob? jid) .unknownJob
  check (!j.status.terminal) .jobTerminal
  let (_, a) ← currentAttempt s j sid gen
  check (e.tick < a.deadline) .leaseExpired
  check (c != "") .unknownAttempt
  ok (s.putJob (j.setAttempt { a with status := .running, container := c })) [.attemptObserved jid sid gen .running]

def doHeartbeat (s : State) (e : Envelope) (jid : JobId) (sid : StepId) (gen : Nat) :
    Except RejectReason Transition := do
  let j ← need (s.findJob? jid) .unknownJob
  check (!j.status.terminal) .jobTerminal
  let (_, a) ← currentAttempt s j sid gen
  check (e.tick < a.deadline) .leaseExpired
  ok (s.putJob (j.setAttempt { a with deadline := e.tick + s.config.leaseTicks })) []

/-- Settle a result (CommitResult / RecordVerification). The verifier path is
    NOT a back door: it passes exactly the same fencing/lease checks. -/
def doSettle (s : State) (e : Envelope) (jid : JobId) (sid : StepId) (gen : Nat)
    (r : ResultEnvelope) (viaVerifier : Bool) : Except RejectReason Transition := do
  let j ← need (s.findJob? jid) .unknownJob
  let w ← need (s.workflowOf j) .unknownRelease
  let spec ← need (w.find? sid) .unknownStep
  check (spec.role.verifierRole == viaVerifier) .wrongRole
  let st ← need (j.findStep? sid) .unknownStep
  let _ ← need (j.findAttempt? sid gen) .unknownAttempt
  match st.accepted with
  | some acc =>
    if acc.gen == gen && acc.result == r.result && acc.fingerprint == r.fingerprint then
      ok s [.idempotentReplay jid sid gen]
    else .error .conflictingCompletion
  | none => do
    check (!j.status.terminal) .jobTerminal
    let (_, a) ← currentAttempt s j sid gen
    check (e.tick < a.deadline) .leaseExpired
    check (r.fingerprint == a.fingerprint) .fingerprintMismatch
    check r.result.valid .invalidDigest
    check (!spec.role.trustedObservation || r.modelOutcome == .pass) .wrongRole
    let o := combineOutcome r.modelOutcome r.trustedOutcome
    check (o != .pass || spec.role != .build ||
      (match r.produced with | some p => p.valid | none => false) && exportsOk r.exports &&
       r.contract == s.contract) .notPublishable
    check (o != .pass || spec.role != .prove || r.contract == s.contract) .contractMismatch
    check (o != .pass || spec.role != .materialize ||
      (match r.produced with | some p => p.valid | none => false)) .notPublishable
    let acc : Accepted := { gen := gen, jobEpoch := a.jobEpoch, ctrlEpoch := a.ctrlEpoch,
                            leaseDeadline := a.deadline, acceptedAt := e.tick, release := j.release,
                            subject := a.subject, fingerprint := a.fingerprint, result := r.result, outcome := o,
                            produced := r.produced, exports := r.exports, contract := r.contract }
    let j1 := (j.setAttempt { a with status := .succeeded }).setStep
      { st with accepted := some acc, current := none, status := stepStatusOf o }
    let (j2, effs) := finalizeJob j1
    ok (s.putJob j2) ([.resultAccepted jid sid gen o] ++
      (if j2.status != j.status then [.jobStatus jid j2.status] else [])) effs

/-- Transport failure / expiry: attempt settles, retry only under policy. -/
def settleFailure (s : State) (j : Job) (spec : StepSpec) (st : StepState) (a : Attempt)
    (status : AttemptStatus) : Job × List EffectIntent :=
  let f := st.failures + 1
  let st' := { st with current := none, failures := f,
                       status := (if f > spec.retries then .failed else .pending) }
  finalizeJob ((j.setAttempt { a with status := status }).setStep st')

def doFailAttempt (s : State) (jid : JobId) (sid : StepId) (gen : Nat) :
    Except RejectReason Transition := do
  let j ← need (s.findJob? jid) .unknownJob
  check (!j.status.terminal) .jobTerminal
  let w ← need (s.workflowOf j) .unknownRelease
  let spec ← need (w.find? sid) .unknownStep
  let (st, a) ← currentAttempt s j sid gen
  let (j', effs) := settleFailure s j spec st a .failed
  ok (s.putJob j') [.attemptSettled jid sid gen .failed] (terminateEffect j a :: effs)

def doExpireAttempt (s : State) (e : Envelope) (jid : JobId) (sid : StepId) (gen : Nat) :
    Except RejectReason Transition := do
  let j ← need (s.findJob? jid) .unknownJob
  check (!j.status.terminal) .jobTerminal
  let w ← need (s.workflowOf j) .unknownRelease
  let spec ← need (w.find? sid) .unknownStep
  let (st, a) ← currentAttempt s j sid gen
  check (e.tick ≥ a.deadline) .leaseNotExpired
  let (j', effs) := settleFailure s j spec st a .expired
  ok (s.putJob j') [.attemptSettled jid sid gen .expired] (terminateEffect j a :: effs)

def doPause (s : State) (jid : JobId) : Except RejectReason Transition := do
  let j ← need (s.findJob? jid) .unknownJob
  check (dispatchable j.status) .notPausable
  ok (s.putJob { j with status := .pauseRequested }) [.jobStatus jid .pauseRequested]

def doAckQuiescence (s : State) (jid : JobId) (clear : Bool) : Except RejectReason Transition := do
  let j ← need (s.findJob? jid) .unknownJob
  check (j.status == .pauseRequested) .notPauseRequested
  check (j.liveAttempts.isEmpty && clear) .notQuiescent
  ok (s.putJob { j with status := .paused }) [.jobStatus jid .paused]

def doResume (s : State) (jid : JobId) : Except RejectReason Transition := do
  let j ← need (s.findJob? jid) .unknownJob
  check (j.status == .paused) .notPaused
  ok (s.putJob { j with status := .running }) [.jobStatus jid .running]

def doCancel (s : State) (jid : JobId) : Except RejectReason Transition := do
  let j ← need (s.findJob? jid) .unknownJob
  check (!j.status.terminal) .jobTerminal
  let (j1, effs) := j.revokeLive .cancelled
  ok (s.putJob { j1 with status := .cancelled, epoch := j.epoch + 1 }) [.jobStatus jid .cancelled] effs

/-! ### Change requests (§12.2) -/

def doCreateChange (s : State) (id : ChangeId) (req : Digest) (aj : JobId) (bid : BudgetId)
    (limit revLimit : Nat) : Except RejectReason Transition := do
  check (s.findChange? id).isNone .duplicateChange
  check (id != "" && bid != "") .unknownChange
  check (s.findBudget? bid).isNone .duplicateChange
  check (revLimit ≥ 1) .revisionBudgetExhausted
  let base ← need s.active .unknownRelease
  let j ← mkJob s aj .changeAuthor base req base bid (some id)
  let c : Change := { id := id, request := req, base := base, budget := bid, revisionLimit := revLimit,
                      revisions := 1, jobs := [aj], candidates := [], status := .open }
  ok { s with jobs := s.jobs ++ [j], budgets := s.budgets ++ [{ id := bid, limit := limit, used := 0 }],
              changes := s.changes ++ [c] } [.jobCreated aj base, .changeUpdated id]

def doReviseChange (s : State) (id : ChangeId) (aj : JobId) (diag : Digest) :
    Except RejectReason Transition := do
  let c ← need (s.findChange? id) .unknownChange
  check (c.status == .open) .changeClosed
  check (c.revisions < c.revisionLimit) .revisionBudgetExhausted
  let j ← mkJob s aj .changeAuthor c.base diag c.base c.budget (some id)
  ok ({ s with jobs := s.jobs ++ [j] }.putChange
        { c with revisions := c.revisions + 1, jobs := c.jobs ++ [aj] })
    [.jobCreated aj c.base, .changeUpdated id]

def doRegisterCandidate (s : State) (cid : ChangeId) (aj ej : JobId) (src : Digest) :
    Except RejectReason Transition := do
  let c ← need (s.findChange? cid) .unknownChange
  check (c.status == .open) .changeClosed
  check (c.jobs.contains aj) .unknownJob
  let a ← need (s.findJob? aj) .unknownJob
  check (a.kind == .changeAuthor && a.status == .succeeded) .authorNotComplete
  let w ← need (s.workflowOf a) .unknownRelease
  let m ← need (w.uniqueRole .materialize) .invalidWorkflow
  let mst ← need (a.findStep? m.id) .authorNotComplete
  let acc ← need mst.accepted .authorNotComplete
  check (acc.outcome == .pass && acc.produced == some src) .sourceMismatch
  check (!c.candidates.contains src) .duplicateRelease
  let j ← mkJob s ej .changeEvaluate c.base src src c.budget (some cid)
  ok ({ s with jobs := s.jobs ++ [j] }.putChange
        { c with jobs := c.jobs ++ [ej], candidates := c.candidates ++ [src] })
    [.jobCreated ej c.base, .changeUpdated cid]

/-! ### Publication gate (K06) -/

/-- The accepted, passing evidence for a required role, if any. -/
def gateEvidence (j : Job) (w : WorkflowDef) (r : Role) : Option Accepted :=
  match w.uniqueRole r with
  | some sp => match j.findStep? sp.id with
    | some st => match st.accepted with
      | some a => if a.outcome == .pass && st.status == .succeeded then some a else none
      | none => none
    | none => none
  | none => none

/-- Required-evidence check: roles come from the kernel's pinned workflow,
    subjects from kernel-stamped attempt records, and trusted evidence must
    carry the current contract identity. Returns the verified payload. -/
def gatesPass (s : State) (j : Job) (w : WorkflowDef) : Except RejectReason (Digest × List WorkflowDef) := do
  let b ← need (gateEvidence j w .build) .gateFailed
  let p ← need (gateEvidence j w .prove) .gateFailed
  let rp ← need (gateEvidence j w .reproduce) .gateFailed
  let rf ← need (gateEvidence j w .refute) .gateFailed
  let payload ← need b.produced .gateMissing
  check (b.subject == j.subject) .subjectMismatch
  check (p.subject == payload && rp.subject == payload && rf.subject == payload) .subjectMismatch
  check (b.contract == s.contract && p.contract == s.contract) .contractMismatch
  check (exportsOk b.exports) .invalidWorkflow
  return (payload, b.exports)

def doPublishReport (s : State) (jid : JobId) (rep : Digest) : Except RejectReason Transition := do
  let j ← need (s.findJob? jid) .unknownJob
  check (j.kind == .packageAudit) .wrongRole
  check (j.status == .succeeded) .notPublishable
  let w ← need (s.workflowOf j) .unknownRelease
  let (payload, _) ← gatesPass s j w
  check rep.valid .invalidDigest
  check (!s.reports.any (·.job == jid)) .duplicateRelease
  ok { s with reports := s.reports ++ [{ job := jid, digest := rep, subject := payload }] }
    [.reportPublished jid rep]
    [{ id := s!"report:{jid}", kind := .reportPublished, job := jid, step := "", gen := 0,
       subject := rep, inputs := [] }]

def doPublishRelease (s : State) (jid : JobId) (d : Digest) (assets : List Asset) :
    Except RejectReason Transition := do
  let j ← need (s.findJob? jid) .unknownJob
  check (j.kind == .changeEvaluate) .wrongRole
  check (j.status == .succeeded) .notPublishable
  let cid ← need j.change .unknownChange
  let c ← need (s.findChange? cid) .unknownChange
  check (c.status == .open) .changeClosed
  let w ← need (s.workflowOf j) .unknownRelease
  let (payload, exports) ← gatesPass s j w
  check d.valid .invalidDigest
  check (s.findRelease? d).isNone .duplicateRelease
  check (assets.all (fun a => a.digest.valid)) .invalidDigest
  let rel : Release := { digest := d, payload := payload, source := j.subject, parent := some c.base,
                         contract := s.contract, workflows := exports, assets := assets, evidenceJob := some jid,
                         producer := some j.release }
  ok ({ s with releases := s.releases ++ [rel] }.putChange { c with status := .published })
    [.releasePublished d, .changeUpdated cid]
    [{ id := s!"release:{d}", kind := .releasePublished, job := jid, step := "", gen := 0,
       subject := d, inputs := [] }]

/-! ### Approval and activation (K07, K08) -/

def doRecordApproval (s : State) (e : Envelope) (id : ApprovalId) (rel base : Digest) :
    Except RejectReason Transition := do
  check (s.findApproval? id).isNone .duplicateApproval
  check (id != "") .unknownApproval
  let _ ← need (s.findRelease? rel) .notPublished
  check (s.active == some base) .baseReleaseChanged
  ok { s with approvals := s.approvals ++ [{ id := id, release := rel, expectedBase := base,
                                             contract := s.contract, operator := e.actor.name, atTick := e.tick, revoked := false }] }
    [.approvalRecorded id]

def doRevokeApproval (s : State) (id : ApprovalId) : Except RejectReason Transition := do
  let a ← need (s.findApproval? id) .unknownApproval
  ok { s with approvals := s.approvals.map (fun x => if x.id == id then { a with revoked := true } else x) }
    [.approvalRevoked id]

def doActivate (s : State) (e : Envelope) (rel expected : Digest) (aid : ApprovalId) :
    Except RejectReason Transition := do
  check (s.active == some expected) .baseReleaseChanged
  let a ← need (s.findApproval? aid) .unknownApproval
  check (!a.revoked) .approvalRevoked
  check (a.release == rel && a.expectedBase == expected && a.contract == s.contract) .approvalMismatch
  let r ← need (s.findRelease? rel) .notPublished
  check (r.contract == s.contract) .contractMismatch
  check (exportsOk r.workflows) .invalidWorkflow
  check (rel != expected) .approvalMismatch
  -- jobs are untouched: activation changes only the default for NEW jobs (K08)
  let act : Activation := { release := rel, base := some expected, approval := some aid, atTick := e.tick }
  ok { s with active := some rel, activations := s.activations ++ [act] }
    [.releaseActivated rel]

/-! ### Migration (K09) -/

def doMigrate (s : State) (e : Envelope) (jid : JobId) (target : Digest) (rev : Nat) :
    Except RejectReason Transition := do
  let j ← need (s.findJob? jid) .unknownJob
  check (j.revision == rev) .staleMigrationPlan
  let t ← need (s.findRelease? target) .unknownRelease
  check (s.wasActivated target) .releaseNotActivated
  check (canMigrateB s j t) .migrationIneligible
  let newW ← need (workflowFor t.workflows j.kind) .migrationIneligible
  let steps := migratedSteps j newW
  let j' : Job := { j with release := target, epoch := j.epoch + 1, steps := steps }
  let kept := (j.steps.filter (fun st => st.accepted.isSome)).map (·.id)
  ok { (s.putJob j') with migrations := s.migrations ++ [{ job := jid, fromRel := j.release,
                                                           toRel := target, revision := rev, kept := kept,
                                                           reset := (steps.filter (fun st => st.accepted.isNone)).map (·.id),
                                                           retired := (j.steps.filter (fun st => (newW.find? st.id).isNone)).map (·.id),
                                                           atTick := e.tick }] }
    [.jobMigrated jid target]

/-! ### Controller recovery (§11) -/

def recoverJob (s : State) (j : Job) : Job × List EffectIntent :=
  match s.workflowOf j with
  | none => j.revokeLive .lost
  | some w =>
    if j.liveAttempts.isEmpty then (j, []) else
    let effs := j.liveAttempts.map (terminateEffect j)
    let j1 : Job := { j with
      attempts := j.attempts.map (fun a => if a.status.live then { a with status := .lost } else a),
      steps := j.steps.map (fun st =>
        if st.current.isSome then
          let f := st.failures + 1
          let lim := match w.find? st.id with | some sp => sp.retries | none => 0
          { st with current := none, failures := f, status := (if f > lim then .failed else .pending) }
        else st) }
    let (j2, effs2) := finalizeJob j1
    (j2, effs ++ effs2)

def doRecover (s : State) (e : Envelope) : Except RejectReason Transition :=
  let rs := s.jobs.map (fun j => if j.status.terminal then (j, []) else recoverJob s j)
  ok { s with ctrlEpoch := e.epoch, clock := e.tick, jobs := rs.map (·.1) }
    [.controllerRecovered e.epoch] (rs.map (·.2)).flatten

/-! ### Entry point -/

/-- Epoch/clock fencing applied to every envelope before dispatch. -/
def admit (s : State) (e : Envelope) : Except RejectReason State :=
  match e.cmd with
  | .bootstrap .. => do
    check (e.epoch == s.ctrlEpoch) .staleEpoch
    return { s with clock := max s.clock e.tick }
  | .recoverController => do
    check s.active.isSome .notBootstrapped
    check (e.epoch == s.ctrlEpoch + 1) .staleEpoch
    return s
  | _ => do
    check s.active.isSome .notBootstrapped
    check (e.epoch == s.ctrlEpoch) .staleEpoch
    check (e.tick ≥ s.clock) .clockRegression
    return { s with clock := e.tick }

def dispatch (s : State) (e : Envelope) : Except RejectReason Transition :=
  match e.cmd with
  | .bootstrap g c cfg => doBootstrap s e g c cfg
  | .createJob id k i sb r b l => doCreateJob s id k i sb r b l
  | .startAttempt j st fp => doStartAttempt s e j st fp
  | .observeLaunchDispatched j st g => doObserveDispatched s j st g
  | .observeProcessStarted j st g c => doObserveStarted s e j st g c
  | .heartbeat j st g => doHeartbeat s e j st g
  | .commitResult j st g r => doSettle s e j st g r false
  | .recordVerification j st g r => doSettle s e j st g r true
  | .failAttempt j st g => doFailAttempt s j st g
  | .expireAttempt j st g => doExpireAttempt s e j st g
  | .pauseJob j => doPause s j
  | .acknowledgeQuiescence j c => doAckQuiescence s j c
  | .resumeJob j => doResume s j
  | .cancelJob j => doCancel s j
  | .createChange id rq aj b l rl => doCreateChange s id rq aj b l rl
  | .reviseChange id aj d => doReviseChange s id aj d
  | .registerCandidate c aj ej src => doRegisterCandidate s c aj ej src
  | .publishReport j r => doPublishReport s j r
  | .publishRelease j d a => doPublishRelease s j d a
  | .recordApproval id r b => doRecordApproval s e id r b
  | .revokeApproval id => doRevokeApproval s id
  | .activateRelease r x a => doActivate s e r x a
  | .migrateJob j t r => doMigrate s e j t r
  | .recoverController => doRecover s e

/-- THE authoritative transition function (§6.1). -/
def apply (s : State) (e : Envelope) : Except RejectReason Transition := do
  check (permitted e.actor e.cmd) .unauthorizedActor
  let s1 ← admit s e
  dispatch s1 e

/-- Offline journal replay: fold accepted envelopes from a state. Rejected
    envelopes are skipped exactly as they were at runtime (no state change). -/
def replay (s : State) : List Envelope → State
  | [] => s
  | e :: es => match apply s e with
    | .ok t => replay t.state es
    | .error _ => replay s es

end Factory
