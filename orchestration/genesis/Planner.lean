import Factory.Types
/-
  Genesis planner (P0): stable-ID order, at most ONE dispatch per decision.
-/
namespace FactoryPkg
open Factory

/-- Remove later duplicates, keeping first occurrences. -/
def dedup : List StepId → List StepId
  | [] => []
  | x :: xs => x :: (dedup xs).filter (fun y => y != x)

def plan (v : PlannerView) : List StepId :=
  (dedup v.ready).take (min 1 v.slots)

end FactoryPkg
