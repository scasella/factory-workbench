import Factory.Workflow
/-
  Factory.PackageContracts — FROZEN statement types for orchestration
  package obligations (P01–P05). The verifier's trusted statement bridge
  instantiates exactly these types against fully qualified candidate
  declarations; a candidate cannot weaken them.
-/
namespace Factory.Contracts
open Factory

/-- P01: exported workflows satisfy the fixed well-formedness and
    mandatory-role/binding requirements (one workflow per job kind). -/
def P01 (ws : List WorkflowDef) : Prop := exportsOk ws = true

/-- Planner output contract for one view: order-preserving selection from the
    ready list (declared priority policy = kernel ready order), no duplicates,
    within the effective concurrency bound, and nonvacuous: if work is ready
    and a slot is free, something is proposed. -/
def PlanOk (v : PlannerView) (p : List StepId) : Prop :=
  p.Sublist v.ready ∧ p.Nodup ∧ p.length ≤ v.slots ∧ (v.ready ≠ [] → 0 < v.slots → p ≠ [])

/-- P02: the planner satisfies `PlanOk` on EVERY view (general, not fixtures). -/
def P02 (plan : PlannerView → List StepId) : Prop := ∀ v, PlanOk v (plan v)

/-- P03: required publication roles and their subject bindings are retained
    relative to the ACTUAL previous release (verifier-supplied). -/
def P03 (prev new : List WorkflowDef) : Prop := gatesRetained prev new = true

/-- P04 (family a): ordering-only change — same steps, roles, semantic inputs
    and prompt paths; only ordering edges / maxParallel may differ. -/
def P04OrderingOnly (prev new : List WorkflowDef) : Prop :=
  exportsOrderingOnlyCompatible prev new = true

/-- P04 (family b): unchanged workflow (planner-only change). -/
def P04Unchanged (prev new : List WorkflowDef) : Prop := new = prev

/-- P05: behavioral equivalence of planners for all views. -/
def P05 (prevPlan plan : PlannerView → List StepId) : Prop := ∀ v, plan v = prevPlan v

end Factory.Contracts
