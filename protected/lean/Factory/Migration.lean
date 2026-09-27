import Factory.Access
/-
  Factory.Migration — the fixed v1 migration recipe: identity mapping of
  stable step IDs. Completed steps are reused only when their static identity
  (role, semantic inputs, prompt bytes digest) is unchanged and every
  prerequisite under the NEW workflow is itself completed (downward closed).
  Unstarted non-required steps absent from the new workflow are retired.
  Everything else is rejected; the job stays pinned.
-/
namespace Factory

/-- Per-step compatibility check for one existing step state. -/
def migStepOk (j : Job) (oldAssets newAssets : List Asset) (oldW newW : WorkflowDef)
    (st : StepState) : Bool :=
  match st.accepted with
  | some _ =>
    match oldW.find? st.id, newW.find? st.id with
    | some o, some n =>
        staticId oldAssets o == staticId newAssets n &&
        st.status == .succeeded &&
        n.prereqs.all (fun p => match j.findStep? p with
          | some q => q.accepted.isSome && q.status == .succeeded
          | none => false)
    | _, _ => false
  | none =>
    match newW.find? st.id with
    | some _ => true
    | none => match oldW.find? st.id with
      | some o => !(requiredRoles j.kind).contains o.role
      | none => false

def freshStep (id : StepId) : StepState :=
  { id := id, status := .pending, current := none, accepted := none, failures := 0 }

/-- New step list: reuse accepted steps exactly; everything else pending. -/
def migratedSteps (j : Job) (newW : WorkflowDef) : List StepState :=
  newW.steps.map (fun spec => match j.findStep? spec.id with
    | some st => if st.accepted.isSome then st else { st with status := .pending, current := none }
    | none => freshStep spec.id)

/-- Concrete `canMigrate` check on the current state (§14.2 step 4). -/
def canMigrateB (s : State) (j : Job) (target : Release) : Bool :=
  match s.findRelease? j.release, workflowFor target.workflows j.kind with
  | some oldRel, some newW =>
    match workflowFor oldRel.workflows j.kind with
    | some oldW =>
      j.kind == .packageAudit &&
      j.status == .paused &&
      j.liveAttempts.isEmpty &&
      target.digest != j.release &&
      wellFormedWorkflow newW &&
      newW.steps.length ≤ s.config.maxSteps &&
      j.steps.all (migStepOk j oldRel.assets target.assets oldW newW)
    | none => false
  | _, _ => false

structure MigrationPreview where
  kept    : List StepId
  reset   : List StepId
  retired : List StepId
  reasons : List String
  deriving Repr

/-- Non-mutating preview with human-readable reasons (diagnostic only; the
    authoritative decision is `canMigrateB` inside `apply`). -/
def migrationPreview (s : State) (j : Job) (target : Release) : MigrationPreview :=
  match s.findRelease? j.release, workflowFor target.workflows j.kind with
  | some oldRel, some newW =>
    match workflowFor oldRel.workflows j.kind with
    | some oldW =>
      let kept := (j.steps.filter (fun st => st.accepted.isSome)).map (·.id)
      let retired := (j.steps.filter (fun st => (newW.find? st.id).isNone)).map (·.id)
      let reset := (newW.steps.filter (fun sp => !(kept.contains sp.id))).map (·.id)
      let r1 := if j.kind == .packageAudit then [] else ["self-improvement jobs stay pinned (v1)"]
      let r2 := if j.status == .paused then [] else ["job is not paused/quiescent"]
      let r3 := if j.liveAttempts.isEmpty then [] else ["job has live attempt authority"]
      let r4 := if target.digest != j.release then [] else ["job already pinned to target"]
      let r5 := if wellFormedWorkflow newW then [] else ["target workflow ill-formed"]
      let r6 := (j.steps.filter (fun st => !migStepOk j oldRel.assets target.assets oldW newW st)).map
        (fun st => s!"step {st.id}: changed identity, unmet new prerequisite, or required step removed")
      { kept, reset, retired, reasons := r1 ++ r2 ++ r3 ++ r4 ++ r5 ++ r6 }
    | none => { kept := [], reset := [], retired := [], reasons := ["job release has no workflow"] }
  | none, _ => { kept := [], reset := [], retired := [], reasons := ["job release unknown"] }
  | _, none => { kept := [], reset := [], retired := [], reasons := ["target has no workflow for job kind"] }

end Factory
