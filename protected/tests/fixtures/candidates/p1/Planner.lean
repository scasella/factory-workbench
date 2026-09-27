import Factory.Types
/-
  P1 planner: stable ready order, dispatch up to the effective concurrency
  bound offered by the kernel (so independent reviews run in parallel).
-/
namespace FactoryPkg
open Factory

/-- Remove later duplicates, keeping first occurrences. -/
def dedup : List StepId → List StepId
  | [] => []
  | x :: xs => x :: (dedup xs).filter (fun y => y != x)

def plan (v : PlannerView) : List StepId :=
  (dedup v.ready).take v.slots

end FactoryPkg
