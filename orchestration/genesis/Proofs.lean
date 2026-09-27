import Factory.PackageContracts
import FactoryPkg.Package
import FactoryPkg.Planner
import FactoryPrev.Package
import FactoryPrev.Planner
/-
  Genesis proofs. Obligations are stated with the FROZEN contract types; the
  verifier's statement bridge re-states them and checks these declarations
  have exactly those types.

  * P01 is a finite, kernel-reduced check (`decide`) of the fixed
    well-formedness function on this package's concrete exports.
  * P02 is a GENERAL theorem over all planner views.
  * P03 is a finite kernel-reduced check against the verifier-supplied
    predecessor (for genesis, the bootstrap verifier supplies genesis itself).
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
    refine ⟨?_, dedup_ne_nil _ hr⟩
    omega

theorem p03 : P03 FactoryPrev.workflows workflows := by unfold P03; decide

end FactoryPkg
