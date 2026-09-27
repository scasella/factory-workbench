import Factory.Types
import Factory.Json
/-
  Factory.Codec — strict typed codec for kernel and package boundary values.
  Audited boundary (trusted; not covered by kernel theorems).
-/
namespace Factory.Codec
open Factory Factory.Json

class Enc (α : Type) where enc : α → J
class Dec (α : Type) where dec : J → Except Err α
export Enc (enc)
export Dec (dec)

instance : Enc Nat := ⟨encNat⟩
instance : Dec Nat := ⟨decNat⟩
instance : Enc String := ⟨.str⟩
instance : Dec String := ⟨J.getStr⟩
instance : Enc Bool := ⟨.bool⟩
instance : Dec Bool := ⟨J.getBool⟩
instance {α} [Enc α] : Enc (List α) := ⟨fun xs => .arr (xs.map enc)⟩
instance {α} [Dec α] : Dec (List α) := ⟨decList dec⟩
instance {α} [Enc α] : Enc (Option α) := ⟨encOpt enc⟩
instance {α} [Dec α] : Dec (Option α) := ⟨decOpt dec⟩
instance {α β} [Enc α] [Enc β] : Enc (α × β) := ⟨fun (a, b) => .arr [enc a, enc b]⟩
instance {α β} [Dec α] [Dec β] : Dec (α × β) := ⟨fun j => do
  match ← j.getArr with
  | [a, b] => return (← dec a, ← dec b)
  | _ => throw "expected pair"⟩

/-- Enumerations as string tags; unknown tags rejected. -/
def enumCodec {α} [BEq α] (table : List (String × α)) : (α → J) × (J → Except Err α) :=
  (fun a => .str ((table.find? (·.2 == a)).map (·.1) |>.getD "?"),
   fun j => do
     let s ← j.getStr
     match table.find? (·.1 == s) with
     | some (_, a) => return a
     | none => throw s!"unknown tag '{s}'")

instance : BEq Role := ⟨fun a b => decide (a = b)⟩
instance : BEq JobKind := ⟨fun a b => decide (a = b)⟩
instance : BEq Outcome := ⟨fun a b => decide (a = b)⟩
instance : BEq JobStatus := ⟨fun a b => decide (a = b)⟩
instance : BEq StepStatus := ⟨fun a b => decide (a = b)⟩
instance : BEq AttemptStatus := ⟨fun a b => decide (a = b)⟩
instance : BEq ChangeStatus := ⟨fun a b => decide (a = b)⟩
instance : BEq EffectKind := ⟨fun a b => decide (a = b)⟩
instance : BEq ReleaseStatus := ⟨fun a b => decide (a = b)⟩

def roleT : List (String × Role) :=
  [("author", .author), ("materialize", .materialize), ("build", .build), ("prove", .prove),
   ("reproduce", .reproduce), ("refute", .refute), ("summarize", .summarize)]
def kindT : List (String × JobKind) :=
  [("package_audit", .packageAudit), ("change_author", .changeAuthor), ("change_evaluate", .changeEvaluate)]
def outcomeT : List (String × Outcome) := [("pass", .pass), ("fail", .fail), ("inconclusive", .inconclusive)]
def jobStatusT : List (String × JobStatus) :=
  [("queued", .queued), ("running", .running), ("pause_requested", .pauseRequested),
   ("paused", .paused), ("blocked", .blocked), ("succeeded", .succeeded), ("failed", .failed),
   ("cancelled", .cancelled)]
def stepStatusT : List (String × StepStatus) :=
  [("pending", .pending), ("active", .active), ("succeeded", .succeeded), ("failed", .failed),
   ("blocked", .blocked)]
def attemptStatusT : List (String × AttemptStatus) :=
  [("authorized", .authorized), ("starting", .starting), ("running", .running),
   ("succeeded", .succeeded), ("failed", .failed), ("expired", .expired),
   ("cancelled", .cancelled), ("lost", .lost)]
def changeStatusT : List (String × ChangeStatus) :=
  [("open", .open), ("published", .published), ("exhausted", .exhausted), ("closed", .closed)]
def effectKindT : List (String × EffectKind) :=
  [("launch", .launch), ("terminate", .terminate), ("release_published", .releasePublished),
   ("report_published", .reportPublished)]

instance : Enc Role := ⟨(enumCodec roleT).1⟩
instance : Dec Role := ⟨(enumCodec roleT).2⟩
instance : Enc JobKind := ⟨(enumCodec kindT).1⟩
instance : Dec JobKind := ⟨(enumCodec kindT).2⟩
instance : Enc Outcome := ⟨(enumCodec outcomeT).1⟩
instance : Dec Outcome := ⟨(enumCodec outcomeT).2⟩
instance : Enc JobStatus := ⟨(enumCodec jobStatusT).1⟩
instance : Dec JobStatus := ⟨(enumCodec jobStatusT).2⟩
instance : Enc StepStatus := ⟨(enumCodec stepStatusT).1⟩
instance : Dec StepStatus := ⟨(enumCodec stepStatusT).2⟩
instance : Enc AttemptStatus := ⟨(enumCodec attemptStatusT).1⟩
instance : Dec AttemptStatus := ⟨(enumCodec attemptStatusT).2⟩
instance : Enc ChangeStatus := ⟨(enumCodec changeStatusT).1⟩
instance : Dec ChangeStatus := ⟨(enumCodec changeStatusT).2⟩
instance : Enc EffectKind := ⟨(enumCodec effectKindT).1⟩
instance : Dec EffectKind := ⟨(enumCodec effectKindT).2⟩

def obj (kvs : List (String × J)) : J := .obj kvs

instance : Enc InputSource := ⟨fun
  | .jobInput => obj [("type", .str "job_input")]
  | .stepOutput p => obj [("type", .str "step_output"), ("step", .str p)]⟩
instance : Dec InputSource := ⟨fun j => do
  let kvs ← j.getObj
  match kvs.find? (·.1 == "type") with
  | some (_, .str "job_input") => let _ ← fields j ["type"]; return .jobInput
  | some (_, .str "step_output") => let f ← fields j ["type", "step"]; return .stepOutput (← dec (f "step"))
  | _ => throw "unknown input source"⟩

instance : Enc InputBinding := ⟨fun b => obj [("name", enc b.name), ("source", enc b.source)]⟩
instance : Dec InputBinding := ⟨fun j => do
  let f ← fields j ["name", "source"]
  return { name := ← dec (f "name"), source := ← dec (f "source") }⟩

instance : Enc StepSpec := ⟨fun s => obj [("id", enc s.id), ("role", enc s.role), ("after", enc s.after),
  ("inputs", enc s.inputs), ("prompt", enc s.prompt), ("retries", enc s.retries)]⟩
instance : Dec StepSpec := ⟨fun j => do
  let f ← fields j ["id", "role", "after", "inputs", "prompt", "retries"]
  return { id := ← dec (f "id"), role := ← dec (f "role"), after := ← dec (f "after"),
           inputs := ← dec (f "inputs"), prompt := ← dec (f "prompt"), retries := ← dec (f "retries") }⟩

instance : Enc WorkflowDef := ⟨fun w => obj [("kind", enc w.kind), ("steps", enc w.steps),
  ("max_parallel", enc w.maxParallel)]⟩
instance : Dec WorkflowDef := ⟨fun j => do
  let f ← fields j ["kind", "steps", "max_parallel"]
  return { kind := ← dec (f "kind"), steps := ← dec (f "steps"), maxParallel := ← dec (f "max_parallel") }⟩

instance : Enc PlannerView := ⟨fun v => obj [("workflow", enc v.workflow), ("ready", enc v.ready),
  ("slots", enc v.slots)]⟩
instance : Dec PlannerView := ⟨fun j => do
  let f ← fields j ["workflow", "ready", "slots"]
  return { workflow := ← dec (f "workflow"), ready := ← dec (f "ready"), slots := ← dec (f "slots") }⟩

instance : Enc Accepted := ⟨fun a => obj [("gen", enc a.gen), ("job_epoch", enc a.jobEpoch),
  ("ctrl_epoch", enc a.ctrlEpoch), ("lease_deadline", enc a.leaseDeadline),
  ("accepted_at", enc a.acceptedAt), ("release", enc a.release), ("subject", enc a.subject),
  ("fingerprint", enc a.fingerprint), ("result", enc a.result), ("outcome", enc a.outcome),
  ("produced", enc a.produced), ("exports", enc a.exports), ("contract", enc a.contract)]⟩
instance : Dec Accepted := ⟨fun j => do
  let f ← fields j ["gen", "job_epoch", "ctrl_epoch", "lease_deadline", "accepted_at", "release",
    "subject", "fingerprint", "result", "outcome", "produced", "exports", "contract"]
  return { gen := ← dec (f "gen"), jobEpoch := ← dec (f "job_epoch"), ctrlEpoch := ← dec (f "ctrl_epoch"),
           leaseDeadline := ← dec (f "lease_deadline"), acceptedAt := ← dec (f "accepted_at"),
           release := ← dec (f "release"), subject := ← dec (f "subject"),
           fingerprint := ← dec (f "fingerprint"), result := ← dec (f "result"),
           outcome := ← dec (f "outcome"), produced := ← dec (f "produced"),
           exports := ← dec (f "exports"), contract := ← dec (f "contract") }⟩

instance : Enc Attempt := ⟨fun a => obj [("step", enc a.step), ("role", enc a.role), ("gen", enc a.gen),
  ("job_epoch", enc a.jobEpoch), ("ctrl_epoch", enc a.ctrlEpoch), ("deadline", enc a.deadline),
  ("status", enc a.status), ("subject", enc a.subject), ("fingerprint", enc a.fingerprint),
  ("inputs", enc a.inputs), ("container", enc a.container)]⟩
instance : Dec Attempt := ⟨fun j => do
  let f ← fields j ["step", "role", "gen", "job_epoch", "ctrl_epoch", "deadline", "status", "subject",
    "fingerprint", "inputs", "container"]
  return { step := ← dec (f "step"), role := ← dec (f "role"), gen := ← dec (f "gen"),
           jobEpoch := ← dec (f "job_epoch"), ctrlEpoch := ← dec (f "ctrl_epoch"),
           deadline := ← dec (f "deadline"), status := ← dec (f "status"), subject := ← dec (f "subject"),
           fingerprint := ← dec (f "fingerprint"), inputs := ← dec (f "inputs"),
           container := ← dec (f "container") }⟩

instance : Enc StepState := ⟨fun s => obj [("id", enc s.id), ("status", enc s.status),
  ("current", enc s.current), ("accepted", enc s.accepted), ("failures", enc s.failures)]⟩
instance : Dec StepState := ⟨fun j => do
  let f ← fields j ["id", "status", "current", "accepted", "failures"]
  return { id := ← dec (f "id"), status := ← dec (f "status"), current := ← dec (f "current"),
           accepted := ← dec (f "accepted"), failures := ← dec (f "failures") }⟩

instance : Enc Job := ⟨fun j => obj [("id", enc j.id), ("kind", enc j.kind), ("release", enc j.release),
  ("input", enc j.input), ("subject", enc j.subject), ("epoch", enc j.epoch), ("status", enc j.status),
  ("steps", enc j.steps), ("attempts", enc j.attempts), ("budget", enc j.budget),
  ("change", enc j.change), ("revision", enc j.revision)]⟩
instance : Dec Job := ⟨fun j => do
  let f ← fields j ["id", "kind", "release", "input", "subject", "epoch", "status", "steps", "attempts",
    "budget", "change", "revision"]
  return { id := ← dec (f "id"), kind := ← dec (f "kind"), release := ← dec (f "release"),
           input := ← dec (f "input"), subject := ← dec (f "subject"), epoch := ← dec (f "epoch"),
           status := ← dec (f "status"), steps := ← dec (f "steps"), attempts := ← dec (f "attempts"),
           budget := ← dec (f "budget"), change := ← dec (f "change"), revision := ← dec (f "revision") }⟩

instance : Enc Budget := ⟨fun b => obj [("id", enc b.id), ("limit", enc b.limit), ("used", enc b.used)]⟩
instance : Dec Budget := ⟨fun j => do
  let f ← fields j ["id", "limit", "used"]
  return { id := ← dec (f "id"), limit := ← dec (f "limit"), used := ← dec (f "used") }⟩

instance : Enc Asset := ⟨fun a => obj [("path", enc a.path), ("digest", enc a.digest)]⟩
instance : Dec Asset := ⟨fun j => do
  let f ← fields j ["path", "digest"]
  return { path := ← dec (f "path"), digest := ← dec (f "digest") }⟩

instance : Enc Release := ⟨fun r => obj [("digest", enc r.digest), ("payload", enc r.payload),
  ("source", enc r.source), ("parent", enc r.parent), ("contract", enc r.contract),
  ("workflows", enc r.workflows), ("assets", enc r.assets), ("evidence_job", enc r.evidenceJob),
  ("producer", enc r.producer)]⟩
instance : Dec Release := ⟨fun j => do
  let f ← fields j ["digest", "payload", "source", "parent", "contract", "workflows", "assets",
    "evidence_job", "producer"]
  return { digest := ← dec (f "digest"), payload := ← dec (f "payload"), source := ← dec (f "source"),
           parent := ← dec (f "parent"), contract := ← dec (f "contract"),
           workflows := ← dec (f "workflows"), assets := ← dec (f "assets"),
           evidenceJob := ← dec (f "evidence_job"), producer := ← dec (f "producer") }⟩

instance : Enc Approval := ⟨fun a => obj [("id", enc a.id), ("release", enc a.release),
  ("expected_base", enc a.expectedBase), ("contract", enc a.contract), ("operator", enc a.operator),
  ("at", enc a.atTick), ("revoked", enc a.revoked)]⟩
instance : Dec Approval := ⟨fun j => do
  let f ← fields j ["id", "release", "expected_base", "contract", "operator", "at", "revoked"]
  return { id := ← dec (f "id"), release := ← dec (f "release"), expectedBase := ← dec (f "expected_base"),
           contract := ← dec (f "contract"), operator := ← dec (f "operator"), atTick := ← dec (f "at"),
           revoked := ← dec (f "revoked") }⟩

instance : Enc Activation := ⟨fun a => obj [("release", enc a.release), ("base", enc a.base),
  ("approval", enc a.approval), ("at", enc a.atTick)]⟩
instance : Dec Activation := ⟨fun j => do
  let f ← fields j ["release", "base", "approval", "at"]
  return { release := ← dec (f "release"), base := ← dec (f "base"), approval := ← dec (f "approval"),
           atTick := ← dec (f "at") }⟩

instance : Enc Change := ⟨fun c => obj [("id", enc c.id), ("request", enc c.request), ("base", enc c.base),
  ("budget", enc c.budget), ("revision_limit", enc c.revisionLimit), ("revisions", enc c.revisions),
  ("jobs", enc c.jobs), ("candidates", enc c.candidates), ("status", enc c.status)]⟩
instance : Dec Change := ⟨fun j => do
  let f ← fields j ["id", "request", "base", "budget", "revision_limit", "revisions", "jobs",
    "candidates", "status"]
  return { id := ← dec (f "id"), request := ← dec (f "request"), base := ← dec (f "base"),
           budget := ← dec (f "budget"), revisionLimit := ← dec (f "revision_limit"),
           revisions := ← dec (f "revisions"), jobs := ← dec (f "jobs"),
           candidates := ← dec (f "candidates"), status := ← dec (f "status") }⟩

instance : Enc Migration := ⟨fun m => obj [("job", enc m.job), ("from", enc m.fromRel), ("to", enc m.toRel),
  ("revision", enc m.revision), ("kept", enc m.kept), ("reset", enc m.reset), ("retired", enc m.retired),
  ("at", enc m.atTick)]⟩
instance : Dec Migration := ⟨fun j => do
  let f ← fields j ["job", "from", "to", "revision", "kept", "reset", "retired", "at"]
  return { job := ← dec (f "job"), fromRel := ← dec (f "from"), toRel := ← dec (f "to"),
           revision := ← dec (f "revision"), kept := ← dec (f "kept"), reset := ← dec (f "reset"),
           retired := ← dec (f "retired"), atTick := ← dec (f "at") }⟩

instance : Enc Report := ⟨fun r => obj [("job", enc r.job), ("digest", enc r.digest), ("subject", enc r.subject)]⟩
instance : Dec Report := ⟨fun j => do
  let f ← fields j ["job", "digest", "subject"]
  return { job := ← dec (f "job"), digest := ← dec (f "digest"), subject := ← dec (f "subject") }⟩

instance : Enc Config := ⟨fun c => obj [("llm_slots", enc c.llmSlots), ("container_slots", enc c.containerSlots),
  ("lease_ticks", enc c.leaseTicks), ("max_jobs", enc c.maxJobs), ("max_steps", enc c.maxSteps)]⟩
instance : Dec Config := ⟨fun j => do
  let f ← fields j ["llm_slots", "container_slots", "lease_ticks", "max_jobs", "max_steps"]
  return { llmSlots := ← dec (f "llm_slots"), containerSlots := ← dec (f "container_slots"),
           leaseTicks := ← dec (f "lease_ticks"), maxJobs := ← dec (f "max_jobs"),
           maxSteps := ← dec (f "max_steps") }⟩

instance : Enc State := ⟨fun s => obj [("ctrl_epoch", enc s.ctrlEpoch), ("clock", enc s.clock),
  ("contract", enc s.contract), ("config", enc s.config), ("releases", enc s.releases),
  ("active", enc s.active), ("activations", enc s.activations), ("approvals", enc s.approvals),
  ("jobs", enc s.jobs), ("budgets", enc s.budgets), ("changes", enc s.changes),
  ("migrations", enc s.migrations), ("reports", enc s.reports)]⟩
instance : Dec State := ⟨fun j => do
  let f ← fields j ["ctrl_epoch", "clock", "contract", "config", "releases", "active", "activations",
    "approvals", "jobs", "budgets", "changes", "migrations", "reports"]
  return { ctrlEpoch := ← dec (f "ctrl_epoch"), clock := ← dec (f "clock"), contract := ← dec (f "contract"),
           config := ← dec (f "config"), releases := ← dec (f "releases"), active := ← dec (f "active"),
           activations := ← dec (f "activations"), approvals := ← dec (f "approvals"),
           jobs := ← dec (f "jobs"), budgets := ← dec (f "budgets"), changes := ← dec (f "changes"),
           migrations := ← dec (f "migrations"), reports := ← dec (f "reports") }⟩

instance : Enc Actor := ⟨fun
  | .operator n => obj [("type", .str "operator"), ("name", .str n)]
  | .coordinator => obj [("type", .str "coordinator")]
  | .supervisor => obj [("type", .str "supervisor")]
  | .verifier => obj [("type", .str "verifier")]⟩
instance : Dec Actor := ⟨fun j => do
  let kvs ← j.getObj
  match kvs.find? (·.1 == "type") with
  | some (_, .str "operator") =>
    let f ← fields j ["type", "name"]
    let n : String ← dec (f "name")
    if n.isEmpty then throw "empty operator name"
    return .operator n
  | some (_, .str "coordinator") => let _ ← fields j ["type"]; return .coordinator
  | some (_, .str "supervisor") => let _ ← fields j ["type"]; return .supervisor
  | some (_, .str "verifier") => let _ ← fields j ["type"]; return .verifier
  | _ => throw "unknown actor"⟩

instance : Enc ResultEnvelope := ⟨fun r => obj [("result", enc r.result), ("model_outcome", enc r.modelOutcome),
  ("trusted_outcome", enc r.trustedOutcome), ("produced", enc r.produced), ("exports", enc r.exports),
  ("contract", enc r.contract), ("fingerprint", enc r.fingerprint)]⟩
instance : Dec ResultEnvelope := ⟨fun j => do
  let f ← fields j ["result", "model_outcome", "trusted_outcome", "produced", "exports", "contract",
    "fingerprint"]
  return { result := ← dec (f "result"), modelOutcome := ← dec (f "model_outcome"),
           trustedOutcome := ← dec (f "trusted_outcome"), produced := ← dec (f "produced"),
           exports := ← dec (f "exports"), contract := ← dec (f "contract"),
           fingerprint := ← dec (f "fingerprint") }⟩

def cmdObj (t : String) (kvs : List (String × J)) : J := obj (("type", .str t) :: kvs)

instance : Enc Command := ⟨fun
  | .bootstrap g c cfg => cmdObj "bootstrap" [("genesis", enc g), ("contract", enc c), ("config", enc cfg)]
  | .createJob id k i sb r b l => cmdObj "create_job" [("job", enc id), ("kind", enc k), ("input", enc i),
      ("subject", enc sb), ("release", enc r), ("budget", enc b), ("limit", enc l)]
  | .startAttempt j s fp => cmdObj "start_attempt" [("job", enc j), ("step", enc s), ("fingerprint", enc fp)]
  | .observeLaunchDispatched j s g => cmdObj "observe_launch_dispatched" [("job", enc j), ("step", enc s), ("gen", enc g)]
  | .observeProcessStarted j s g c => cmdObj "observe_process_started" [("job", enc j), ("step", enc s),
      ("gen", enc g), ("container", enc c)]
  | .heartbeat j s g => cmdObj "heartbeat" [("job", enc j), ("step", enc s), ("gen", enc g)]
  | .commitResult j s g r => cmdObj "commit_result" [("job", enc j), ("step", enc s), ("gen", enc g), ("result", enc r)]
  | .recordVerification j s g r => cmdObj "record_verification" [("job", enc j), ("step", enc s), ("gen", enc g),
      ("result", enc r)]
  | .failAttempt j s g => cmdObj "fail_attempt" [("job", enc j), ("step", enc s), ("gen", enc g)]
  | .expireAttempt j s g => cmdObj "expire_attempt" [("job", enc j), ("step", enc s), ("gen", enc g)]
  | .pauseJob j => cmdObj "pause_job" [("job", enc j)]
  | .acknowledgeQuiescence j c => cmdObj "acknowledge_quiescence" [("job", enc j), ("containers_clear", enc c)]
  | .resumeJob j => cmdObj "resume_job" [("job", enc j)]
  | .cancelJob j => cmdObj "cancel_job" [("job", enc j)]
  | .createChange id r aj b l rl => cmdObj "create_change" [("change", enc id), ("request", enc r),
      ("author_job", enc aj), ("budget", enc b), ("attempt_limit", enc l), ("revision_limit", enc rl)]
  | .reviseChange id aj d => cmdObj "revise_change" [("change", enc id), ("author_job", enc aj),
      ("diagnostics", enc d)]
  | .registerCandidate c aj ej s => cmdObj "register_candidate" [("change", enc c), ("author_job", enc aj),
      ("eval_job", enc ej), ("source", enc s)]
  | .publishReport j r => cmdObj "publish_report" [("job", enc j), ("report", enc r)]
  | .publishRelease j d a => cmdObj "publish_release" [("job", enc j), ("release", enc d), ("assets", enc a)]
  | .recordApproval id r b => cmdObj "record_approval" [("approval", enc id), ("release", enc r),
      ("expected_base", enc b)]
  | .revokeApproval id => cmdObj "revoke_approval" [("approval", enc id)]
  | .activateRelease r x a => cmdObj "activate_release" [("release", enc r), ("expected_active", enc x),
      ("approval", enc a)]
  | .migrateJob j t r => cmdObj "migrate_job" [("job", enc j), ("target", enc t), ("expected_revision", enc r)]
  | .recoverController => cmdObj "recover_controller" []⟩

instance : Dec Command := ⟨fun j => do
  let kvs ← j.getObj
  let t ← match kvs.find? (·.1 == "type") with
    | some (_, .str t) => pure t
    | _ => throw "command without type"
  let g (names : List String) := fields j ("type" :: names)
  match t with
  | "bootstrap" => do let f ← g ["genesis", "contract", "config"]
                      return .bootstrap (← dec (f "genesis")) (← dec (f "contract")) (← dec (f "config"))
  | "create_job" => do
      let f ← g ["job", "kind", "input", "subject", "release", "budget", "limit"]
      return .createJob (← dec (f "job")) (← dec (f "kind")) (← dec (f "input")) (← dec (f "subject"))
        (← dec (f "release")) (← dec (f "budget")) (← dec (f "limit"))
  | "start_attempt" => do let f ← g ["job", "step", "fingerprint"]
                          return .startAttempt (← dec (f "job")) (← dec (f "step")) (← dec (f "fingerprint"))
  | "observe_launch_dispatched" => do let f ← g ["job", "step", "gen"]
                                      return .observeLaunchDispatched (← dec (f "job")) (← dec (f "step")) (← dec (f "gen"))
  | "observe_process_started" => do
      let f ← g ["job", "step", "gen", "container"]
      return .observeProcessStarted (← dec (f "job")) (← dec (f "step")) (← dec (f "gen")) (← dec (f "container"))
  | "heartbeat" => do let f ← g ["job", "step", "gen"]
                      return .heartbeat (← dec (f "job")) (← dec (f "step")) (← dec (f "gen"))
  | "commit_result" => do let f ← g ["job", "step", "gen", "result"]
                          return .commitResult (← dec (f "job")) (← dec (f "step")) (← dec (f "gen")) (← dec (f "result"))
  | "record_verification" => do
      let f ← g ["job", "step", "gen", "result"]
      return .recordVerification (← dec (f "job")) (← dec (f "step")) (← dec (f "gen")) (← dec (f "result"))
  | "fail_attempt" => do let f ← g ["job", "step", "gen"]
                         return .failAttempt (← dec (f "job")) (← dec (f "step")) (← dec (f "gen"))
  | "expire_attempt" => do let f ← g ["job", "step", "gen"]
                           return .expireAttempt (← dec (f "job")) (← dec (f "step")) (← dec (f "gen"))
  | "pause_job" => do let f ← g ["job"]; return .pauseJob (← dec (f "job"))
  | "acknowledge_quiescence" => do let f ← g ["job", "containers_clear"]
                                   return .acknowledgeQuiescence (← dec (f "job")) (← dec (f "containers_clear"))
  | "resume_job" => do let f ← g ["job"]; return .resumeJob (← dec (f "job"))
  | "cancel_job" => do let f ← g ["job"]; return .cancelJob (← dec (f "job"))
  | "create_change" => do
      let f ← g ["change", "request", "author_job", "budget", "attempt_limit", "revision_limit"]
      return .createChange (← dec (f "change")) (← dec (f "request")) (← dec (f "author_job"))
        (← dec (f "budget")) (← dec (f "attempt_limit")) (← dec (f "revision_limit"))
  | "revise_change" => do let f ← g ["change", "author_job", "diagnostics"]
                          return .reviseChange (← dec (f "change")) (← dec (f "author_job")) (← dec (f "diagnostics"))
  | "register_candidate" => do
      let f ← g ["change", "author_job", "eval_job", "source"]
      return .registerCandidate (← dec (f "change")) (← dec (f "author_job")) (← dec (f "eval_job")) (← dec (f "source"))
  | "publish_report" => do let f ← g ["job", "report"]; return .publishReport (← dec (f "job")) (← dec (f "report"))
  | "publish_release" => do let f ← g ["job", "release", "assets"]
                            return .publishRelease (← dec (f "job")) (← dec (f "release")) (← dec (f "assets"))
  | "record_approval" => do let f ← g ["approval", "release", "expected_base"]
                            return .recordApproval (← dec (f "approval")) (← dec (f "release")) (← dec (f "expected_base"))
  | "revoke_approval" => do let f ← g ["approval"]; return .revokeApproval (← dec (f "approval"))
  | "activate_release" => do
      let f ← g ["release", "expected_active", "approval"]
      return .activateRelease (← dec (f "release")) (← dec (f "expected_active")) (← dec (f "approval"))
  | "migrate_job" => do let f ← g ["job", "target", "expected_revision"]
                        return .migrateJob (← dec (f "job")) (← dec (f "target")) (← dec (f "expected_revision"))
  | "recover_controller" => do let _ ← g []; return .recoverController
  | other => throw s!"unknown command '{other}'"⟩

instance : Enc Envelope := ⟨fun e => obj [("actor", enc e.actor), ("epoch", enc e.epoch), ("tick", enc e.tick),
  ("command", enc e.cmd)]⟩
instance : Dec Envelope := ⟨fun j => do
  let f ← fields j ["actor", "epoch", "tick", "command"]
  return { actor := ← dec (f "actor"), epoch := ← dec (f "epoch"), tick := ← dec (f "tick"), cmd := ← dec (f "command") }⟩

instance : Enc EffectIntent := ⟨fun e => obj [("id", enc e.id), ("kind", enc e.kind), ("job", enc e.job),
  ("step", enc e.step), ("gen", enc e.gen), ("subject", enc e.subject), ("inputs", enc e.inputs)]⟩

instance : Enc DomainEvent := ⟨fun
  | .jobCreated j r => cmdObj "job_created" [("job", enc j), ("release", enc r)]
  | .attemptAuthorized j s g => cmdObj "attempt_authorized" [("job", enc j), ("step", enc s), ("gen", enc g)]
  | .attemptObserved j s g st => cmdObj "attempt_observed" [("job", enc j), ("step", enc s), ("gen", enc g), ("status", enc st)]
  | .resultAccepted j s g o => cmdObj "result_accepted" [("job", enc j), ("step", enc s), ("gen", enc g), ("outcome", enc o)]
  | .idempotentReplay j s g => cmdObj "idempotent_replay" [("job", enc j), ("step", enc s), ("gen", enc g)]
  | .attemptSettled j s g st => cmdObj "attempt_settled" [("job", enc j), ("step", enc s), ("gen", enc g), ("status", enc st)]
  | .jobStatus j st => cmdObj "job_status" [("job", enc j), ("status", enc st)]
  | .releasePublished r => cmdObj "release_published" [("release", enc r)]
  | .reportPublished j r => cmdObj "report_published" [("job", enc j), ("report", enc r)]
  | .approvalRecorded id => cmdObj "approval_recorded" [("approval", enc id)]
  | .approvalRevoked id => cmdObj "approval_revoked" [("approval", enc id)]
  | .releaseActivated r => cmdObj "release_activated" [("release", enc r)]
  | .jobMigrated j r => cmdObj "job_migrated" [("job", enc j), ("to", enc r)]
  | .controllerRecovered e => cmdObj "controller_recovered" [("epoch", enc e)]
  | .changeUpdated id => cmdObj "change_updated" [("change", enc id)]⟩

instance : Enc Transition := ⟨fun t => obj [("state", enc t.state), ("events", enc t.events),
  ("effects", enc t.effects)]⟩

end Factory.Codec
