import Factory.Types
/-
  P2 planner: single pass over the ready list that skips already-selected
  IDs and stops as soon as the concurrency bound is reached (no quadratic
  dedup of the whole list, no materialized intermediate list).
-/
namespace FactoryPkg
open Factory

def pick : Nat → List StepId → List StepId → List StepId
  | 0, _, _ => []
  | _, _, [] => []
  | k + 1, seen, x :: xs =>
    if seen.contains x then pick (k + 1) seen xs else x :: pick k (x :: seen) xs

def plan (v : PlannerView) : List StepId := pick v.slots [] v.ready

end FactoryPkg
