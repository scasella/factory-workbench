/-
  Factory.Types — protected domain types shared by the kernel and by
  orchestration packages. Candidate packages import this module read-only;
  they cannot edit it (enforced by the materializer allowlist and by the
  fixed verifier, which compiles against the image-installed copy).

  All identifiers are opaque strings. Digests are 64 lowercase hex chars;
  the kernel only checks shape (`Digest.valid`), never hashes. Hashing is a
  trusted host boundary (see ASSURANCE.md).
-/
namespace Factory

abbrev Digest := String
abbrev JobId := String
abbrev StepId := String
abbrev ChangeId := String
abbrev ApprovalId := String
abbrev BudgetId := String

/-- Shape check for a SHA-256 hex digest. -/
def Digest.valid (d : Digest) : Bool :=
  d.length == 64 && d.all (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f'))

inductive Role where
  | author | materialize | build | prove | reproduce | refute | summarize
  deriving DecidableEq, Repr, Inhabited

inductive JobKind where
  | packageAudit | changeAuthor | changeEvaluate
  deriving DecidableEq, Repr, Inhabited

/-- Resource class of the fixed runner implementing a role. -/
inductive ResourceClass where
  | llm | container
  deriving DecidableEq, Repr, Inhabited

/-- Fixed (protected) mapping from role to runner resource class.
    Packages choose roles; they cannot choose runner implementations. -/
def Role.resource : Role → ResourceClass
  | .author => .llm | .reproduce => .llm | .refute => .llm | .summarize => .llm
  | .materialize => .container | .build => .container | .prove => .container

/-- Roles whose evidence is observed by the fixed trusted harness
    (materializer / verifier), as opposed to model judgment. -/
def Role.trustedObservation : Role → Bool
  | .materialize | .build | .prove => true
  | _ => false

inductive InputSource where
  | jobInput
  | stepOutput (step : StepId)
  deriving DecidableEq, Repr, Inhabited

structure InputBinding where
  name   : String
  source : InputSource
  deriving DecidableEq, Repr, Inhabited

/-- A workflow step. `after` are pure ordering edges; `inputs` are semantic
    data dependencies. Both gate eligibility, but only `inputs` affect the
    semantic fingerprint. -/
structure StepSpec where
  id      : StepId
  role    : Role
  after   : List StepId
  inputs  : List InputBinding
  prompt  : String      -- package-relative prompt asset path, "" if none
  retries : Nat         -- transport-failure retries allowed
  deriving DecidableEq, Repr, Inhabited

structure WorkflowDef where
  kind        : JobKind
  steps       : List StepSpec
  maxParallel : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Input to an orchestration package's pure planner. -/
structure PlannerView where
  workflow : WorkflowDef
  ready    : List StepId
  slots    : Nat
  deriving DecidableEq, Repr, Inhabited

inductive Outcome where
  | pass | fail | inconclusive
  deriving DecidableEq, Repr, Inhabited

inductive JobStatus where
  | queued | running | pauseRequested | paused | blocked | succeeded | failed | cancelled
  deriving DecidableEq, Repr, Inhabited

def JobStatus.terminal : JobStatus → Bool
  | .blocked | .succeeded | .failed | .cancelled => true
  | _ => false

inductive StepStatus where
  | pending | active | succeeded | failed | blocked
  deriving DecidableEq, Repr, Inhabited

inductive AttemptStatus where
  | authorized | starting | running | succeeded | failed | expired | cancelled | lost
  deriving DecidableEq, Repr, Inhabited

/-- An attempt holds live authority while authorized/starting/running. -/
def AttemptStatus.live : AttemptStatus → Bool
  | .authorized | .starting | .running => true
  | _ => false

/-- Result accepted for a step. Records acceptance-time fencing identity
    (§14.2): these fields are never rewritten, including by migration. -/
structure Accepted where
  gen          : Nat
  jobEpoch     : Nat
  ctrlEpoch    : Nat
  leaseDeadline : Nat
  acceptedAt   : Nat
  release      : Digest         -- producer release (job's pinned release at acceptance)
  subject      : Digest
  fingerprint  : Digest
  result       : Digest         -- digest of stored result artifact
  outcome      : Outcome        -- effective outcome (model verdict ∧ trusted checks)
  produced     : Option Digest  -- materialize: source digest; build: payload digest
  exports      : List WorkflowDef -- build: verified workflow exports
  contract     : Digest         -- contract identity observed by harness ("" for model roles)
  deriving DecidableEq, Repr, Inhabited

structure Attempt where
  step       : StepId
  role       : Role
  gen        : Nat
  jobEpoch   : Nat
  ctrlEpoch  : Nat
  deadline   : Nat
  status     : AttemptStatus
  subject    : Digest
  fingerprint : Digest
  inputs     : List (String × Digest)
  container  : String          -- supervisor-observed container identity, "" until observed
  deriving DecidableEq, Repr, Inhabited

structure StepState where
  id        : StepId
  status    : StepStatus
  current   : Option Nat        -- generation of the attempt holding authority
  accepted  : Option Accepted
  failures  : Nat               -- transport failures consumed
  deriving DecidableEq, Repr, Inhabited

structure Job where
  id       : JobId
  kind     : JobKind
  release  : Digest             -- pinned release
  input    : Digest
  subject  : Digest
  epoch    : Nat
  status   : JobStatus
  steps    : List StepState
  attempts : List Attempt
  budget   : BudgetId
  change   : Option ChangeId
  revision : Nat
  deriving DecidableEq, Repr, Inhabited

structure Budget where
  id    : BudgetId
  limit : Nat
  used  : Nat
  deriving DecidableEq, Repr, Inhabited

inductive ReleaseStatus where
  | published
  deriving DecidableEq, Repr, Inhabited

structure Asset where
  path   : String
  digest : Digest
  deriving DecidableEq, Repr, Inhabited

structure Release where
  digest    : Digest
  payload   : Digest
  source    : Digest
  parent    : Option Digest
  contract  : Digest
  workflows : List WorkflowDef
  assets    : List Asset
  evidenceJob : Option JobId   -- evaluation job whose evidence admitted it; none = genesis
  producer  : Option Digest    -- release that governed the evaluation
  deriving DecidableEq, Repr, Inhabited

structure Approval where
  id           : ApprovalId
  release      : Digest
  expectedBase : Digest
  contract     : Digest
  operator     : String
  atTick : Nat
  revoked      : Bool
  deriving DecidableEq, Repr, Inhabited

structure Activation where
  release  : Digest
  base     : Option Digest
  approval : Option ApprovalId  -- none only for the bootstrap trust root
  atTick : Nat
  deriving DecidableEq, Repr, Inhabited

inductive ChangeStatus where
  | open | published | exhausted | closed
  deriving DecidableEq, Repr, Inhabited

structure Change where
  id            : ChangeId
  request       : Digest
  base          : Digest
  budget        : BudgetId
  revisionLimit : Nat
  revisions     : Nat
  jobs          : List JobId
  candidates    : List Digest
  status        : ChangeStatus
  deriving DecidableEq, Repr, Inhabited

structure Migration where
  job        : JobId
  fromRel    : Digest
  toRel      : Digest
  revision   : Nat
  kept       : List StepId
  reset      : List StepId
  retired    : List StepId
  atTick : Nat
  deriving DecidableEq, Repr, Inhabited

structure Report where
  job     : JobId
  digest  : Digest
  subject : Digest
  deriving DecidableEq, Repr, Inhabited

structure Config where
  llmSlots       : Nat
  containerSlots : Nat
  leaseTicks     : Nat
  maxJobs        : Nat
  maxSteps       : Nat
  deriving DecidableEq, Repr, Inhabited

structure State where
  ctrlEpoch   : Nat
  clock       : Nat
  contract    : Digest
  config      : Config
  releases    : List Release
  active      : Option Digest
  activations : List Activation
  approvals   : List Approval
  jobs        : List Job
  budgets     : List Budget
  changes     : List Change
  migrations  : List Migration
  reports     : List Report
  deriving DecidableEq, Repr, Inhabited

inductive Actor where
  | operator (name : String)
  | coordinator
  | supervisor
  | verifier
  deriving DecidableEq, Repr, Inhabited

/-- Result envelope stamped by the trusted supervisor/verifier. Model output
    contributes only `modelOutcome` (for review roles); everything else is
    observed or computed outside the model. -/
structure ResultEnvelope where
  result         : Digest
  modelOutcome   : Outcome       -- pass for non-model roles
  trustedOutcome : Outcome       -- harness/test observation; pass for pure model roles
  produced       : Option Digest
  exports        : List WorkflowDef
  contract       : Digest
  fingerprint    : Digest
  deriving DecidableEq, Repr, Inhabited

inductive Command where
  | bootstrap (genesis : Release) (contract : Digest) (config : Config)
  | createJob (id : JobId) (kind : JobKind) (input subject : Digest)
      (release : Option Digest) (budget : BudgetId) (limit : Nat)
  | startAttempt (job : JobId) (step : StepId) (fingerprint : Digest)
  | observeLaunchDispatched (job : JobId) (step : StepId) (gen : Nat)
  | observeProcessStarted (job : JobId) (step : StepId) (gen : Nat) (container : String)
  | heartbeat (job : JobId) (step : StepId) (gen : Nat)
  | commitResult (job : JobId) (step : StepId) (gen : Nat) (r : ResultEnvelope)
  | recordVerification (job : JobId) (step : StepId) (gen : Nat) (r : ResultEnvelope)
  | failAttempt (job : JobId) (step : StepId) (gen : Nat)
  | expireAttempt (job : JobId) (step : StepId) (gen : Nat)
  | pauseJob (job : JobId)
  | acknowledgeQuiescence (job : JobId) (containersClear : Bool)
  | resumeJob (job : JobId)
  | cancelJob (job : JobId)
  | createChange (id : ChangeId) (request : Digest) (authorJob : JobId)
      (budget : BudgetId) (attemptLimit revisionLimit : Nat)
  | reviseChange (id : ChangeId) (authorJob : JobId) (diagnostics : Digest)
  | registerCandidate (change : ChangeId) (authorJob : JobId) (evalJob : JobId) (source : Digest)
  | publishReport (job : JobId) (report : Digest)
  | publishRelease (job : JobId) (digest : Digest) (assets : List Asset)
  | recordApproval (id : ApprovalId) (release expectedBase : Digest)
  | revokeApproval (id : ApprovalId)
  | activateRelease (release expectedActive : Digest) (approval : ApprovalId)
  | migrateJob (job : JobId) (target : Digest) (expectedRevision : Nat)
  | recoverController
  deriving DecidableEq, Repr, Inhabited

/-- Authenticated envelope. The coordinator attaches actor, controller
    epoch and monotonic tick; none of these come from model output. -/
structure Envelope where
  actor : Actor
  epoch : Nat
  tick  : Nat
  cmd   : Command
  deriving DecidableEq, Repr, Inhabited

inductive EffectKind where
  | launch | terminate | releasePublished | reportPublished
  deriving DecidableEq, Repr, Inhabited

structure EffectIntent where
  id      : String
  kind    : EffectKind
  job     : JobId
  step    : StepId
  gen     : Nat
  subject : Digest
  inputs  : List (String × Digest)
  deriving DecidableEq, Repr, Inhabited

inductive DomainEvent where
  | jobCreated (job : JobId) (release : Digest)
  | attemptAuthorized (job : JobId) (step : StepId) (gen : Nat)
  | attemptObserved (job : JobId) (step : StepId) (gen : Nat) (status : AttemptStatus)
  | resultAccepted (job : JobId) (step : StepId) (gen : Nat) (outcome : Outcome)
  | idempotentReplay (job : JobId) (step : StepId) (gen : Nat)
  | attemptSettled (job : JobId) (step : StepId) (gen : Nat) (status : AttemptStatus)
  | jobStatus (job : JobId) (status : JobStatus)
  | releasePublished (release : Digest)
  | reportPublished (job : JobId) (report : Digest)
  | approvalRecorded (id : ApprovalId)
  | approvalRevoked (id : ApprovalId)
  | releaseActivated (release : Digest)
  | jobMigrated (job : JobId) (toRel : Digest)
  | controllerRecovered (epoch : Nat)
  | changeUpdated (id : ChangeId)
  deriving DecidableEq, Repr, Inhabited

structure Transition where
  state   : State
  events  : List DomainEvent
  effects : List EffectIntent
  deriving Repr, Inhabited

inductive RejectReason where
  | unauthorizedActor | staleEpoch | clockRegression | alreadyBootstrapped | notBootstrapped
  | unknownJob | duplicateJob | unknownStep | unknownRelease | releaseNotActivated
  | invalidWorkflow | invalidDigest | limitExceeded
  | jobNotDispatchable | stepNotEligible | stepHasAuthority | alreadyAccepted
  | budgetExhausted | noSlots | concurrencyBound
  | unknownAttempt | notCurrentAttempt | leaseExpired | leaseNotExpired
  | fingerprintMismatch | conflictingCompletion | wrongRole | jobTerminal
  | notPausable | notPauseRequested | notQuiescent | notPaused
  | unknownChange | duplicateChange | changeClosed | revisionBudgetExhausted
  | authorNotComplete | sourceMismatch
  | gateMissing | gateFailed | subjectMismatch | contractMismatch | notPublishable
  | duplicateRelease | notPublished
  | unknownApproval | duplicateApproval | approvalRevoked | approvalMismatch
  | baseReleaseChanged
  | migrationIneligible | staleMigrationPlan | migrationUnsupported
  deriving DecidableEq, Repr, Inhabited

def RejectReason.code : RejectReason → String
  | .unauthorizedActor => "UNAUTHORIZED_ACTOR" | .staleEpoch => "STALE_EPOCH"
  | .clockRegression => "CLOCK_REGRESSION" | .alreadyBootstrapped => "ALREADY_BOOTSTRAPPED"
  | .notBootstrapped => "NOT_BOOTSTRAPPED" | .unknownJob => "UNKNOWN_JOB"
  | .duplicateJob => "DUPLICATE_JOB" | .unknownStep => "UNKNOWN_STEP"
  | .unknownRelease => "UNKNOWN_RELEASE" | .releaseNotActivated => "RELEASE_NOT_ACTIVATED"
  | .invalidWorkflow => "INVALID_WORKFLOW" | .invalidDigest => "INVALID_DIGEST"
  | .limitExceeded => "LIMIT_EXCEEDED" | .jobNotDispatchable => "JOB_NOT_DISPATCHABLE"
  | .stepNotEligible => "STEP_NOT_ELIGIBLE" | .stepHasAuthority => "STEP_HAS_AUTHORITY"
  | .alreadyAccepted => "ALREADY_ACCEPTED" | .budgetExhausted => "BUDGET_EXHAUSTED"
  | .noSlots => "NO_SLOTS" | .concurrencyBound => "CONCURRENCY_BOUND"
  | .unknownAttempt => "UNKNOWN_ATTEMPT" | .notCurrentAttempt => "STALE_ATTEMPT"
  | .leaseExpired => "LEASE_EXPIRED" | .leaseNotExpired => "LEASE_NOT_EXPIRED"
  | .fingerprintMismatch => "FINGERPRINT_MISMATCH" | .conflictingCompletion => "CONFLICTING_COMPLETION"
  | .wrongRole => "WRONG_ROLE" | .jobTerminal => "JOB_TERMINAL"
  | .notPausable => "NOT_PAUSABLE" | .notPauseRequested => "NOT_PAUSE_REQUESTED"
  | .notQuiescent => "NOT_QUIESCENT" | .notPaused => "NOT_PAUSED"
  | .unknownChange => "UNKNOWN_CHANGE" | .duplicateChange => "DUPLICATE_CHANGE"
  | .changeClosed => "CHANGE_CLOSED" | .revisionBudgetExhausted => "REVISION_BUDGET_EXHAUSTED"
  | .authorNotComplete => "AUTHOR_NOT_COMPLETE" | .sourceMismatch => "SOURCE_MISMATCH"
  | .gateMissing => "GATE_MISSING" | .gateFailed => "GATE_FAILED"
  | .subjectMismatch => "SUBJECT_MISMATCH" | .contractMismatch => "CONTRACT_MISMATCH"
  | .notPublishable => "NOT_PUBLISHABLE" | .duplicateRelease => "DUPLICATE_RELEASE"
  | .notPublished => "NOT_PUBLISHED" | .unknownApproval => "UNKNOWN_APPROVAL"
  | .duplicateApproval => "DUPLICATE_APPROVAL" | .approvalRevoked => "APPROVAL_REVOKED"
  | .approvalMismatch => "APPROVAL_MISMATCH" | .baseReleaseChanged => "BASE_RELEASE_CHANGED"
  | .migrationIneligible => "MIGRATION_INELIGIBLE" | .staleMigrationPlan => "STALE_MIGRATION_PLAN"
  | .migrationUnsupported => "MIGRATION_UNSUPPORTED"

end Factory
