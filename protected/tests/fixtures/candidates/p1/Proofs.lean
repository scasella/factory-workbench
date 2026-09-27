import Factory.PackageContracts
import FactoryPkg.Package
import FactoryPkg.Planner
import FactoryPrev.Package
import FactoryPrev.Planner
/-
  P1 proofs. P01/P03/P04 are finite kernel-reduced checks of the fixed
  Boolean functions on this package's exports versus the verifier-supplied
  predecessor (P0). P02 is general over all planner views.
-/
namespace FactoryPkg
open Factory Factory.Contracts

theorem p01 : P01 workflows := by unfold P01; decide

theorem dedup_sublist : ∀ l : List StepId, (dedup l).Sublist l
  | [] => by simp [dedup]
  | x :: xs => by
    simp only [dedup]
    exact ((List.filter_sublist).trans (dedup_sublist xs)).cons_cons x

theorem dedup_nodup : ∀ l : List StepId, (dedup l).Nodup
  | [] => by simp [dedup]
  | x :: xs => by
    simp only [dedup, List.nodup_cons]
    refine ⟨?_, (dedup_nodup xs).filter _⟩
    simp [List.mem_filter]

theorem dedup_ne_nil : ∀ l : List StepId, l ≠ [] → dedup l ≠ []
  | [] => by simp
  | x :: xs => by simp [dedup]

theorem p02 : P02 plan := by
  intro v
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (List.take_sublist _ _).trans (dedup_sublist _)
  · exact (dedup_nodup _).sublist (List.take_sublist _ _)
  · simp [plan]; omega
  · intro hr hs
    simp [plan]
    exact ⟨by omega, dedup_ne_nil _ hr⟩

theorem p03 : P03 FactoryPrev.workflows workflows := by unfold P03; decide

theorem p04 : P04OrderingOnly FactoryPrev.workflows workflows := by unfold P04OrderingOnly; decide

end FactoryPkg
