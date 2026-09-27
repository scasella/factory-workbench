import Factory.PackageContracts
import FactoryPkg.Package
import FactoryPkg.Planner
import FactoryPrev.Package
import FactoryPrev.Planner
/-
  P2 proofs. P05 is a GENERAL equivalence: for every planner view the
  optimized planner returns exactly what the verified predecessor (P1,
  supplied read-only by the verifier as FactoryPrev) returns. P02 follows
  from P05 plus general lemmas about the predecessor's definition.
-/
namespace FactoryPkg
open Factory Factory.Contracts

theorem p01 : P01 workflows := by unfold P01; decide

theorem filter_filter_ne (l : List StepId) (x : StepId) (seen : List StepId) (h : seen.contains x = true) :
    (l.filter (fun y => y != x)).filter (fun y => !seen.contains y) = l.filter (fun y => !seen.contains y) := by
  rw [List.filter_filter]
  congr 1
  funext a
  by_cases ha : a = x
  · subst ha
    have hm : a ∈ seen := by simpa using h
    simp [hm]
  · simp [ha]
theorem filter_filter_cons (l : List StepId) (x : StepId) (seen : List StepId) :
    (l.filter (fun y => y != x)).filter (fun y => !seen.contains y) =
      l.filter (fun y => !(x :: seen).contains y) := by
  rw [List.filter_filter]
  congr 1
  funext a
  by_cases ha : a = x
  · subst ha; simp
  · simp [ha, Bool.and_comm]
theorem pick_eq : ∀ (k : Nat) (seen l : List StepId),
    pick k seen l = ((FactoryPrev.dedup l).filter (fun y => !seen.contains y)).take k
  | 0, seen, l => by simp [pick]
  | k + 1, seen, [] => by simp [pick, FactoryPrev.dedup]
  | k + 1, seen, x :: xs => by
    by_cases h : seen.contains x = true
    · simp only [pick, h, ite_true, FactoryPrev.dedup, List.filter_cons, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [filter_filter_ne _ x seen h]
      exact pick_eq (k + 1) seen xs
    · have h' : seen.contains x = false := by simpa using h
      simp only [pick, h', FactoryPrev.dedup, List.filter_cons, Bool.not_false, ite_true,
        List.take_succ_cons, Bool.false_eq_true, ite_false]
      rw [filter_filter_cons, pick_eq k (x :: seen) xs]
theorem p05 : P05 FactoryPrev.plan plan := by
  intro v
  unfold plan FactoryPrev.plan
  rw [pick_eq]
  have : (fun y : StepId => !([] : List StepId).contains y) = (fun _ => true) := by funext y; simp
  rw [this, List.filter_eq_self.mpr (fun _ _ => rfl)]

theorem prev_dedup_sublist : ∀ l : List StepId, (FactoryPrev.dedup l).Sublist l
  | [] => by simp [FactoryPrev.dedup]
  | x :: xs => by
    simp only [FactoryPrev.dedup]
    exact ((List.filter_sublist).trans (prev_dedup_sublist xs)).cons_cons x

theorem prev_dedup_nodup : ∀ l : List StepId, (FactoryPrev.dedup l).Nodup
  | [] => by simp [FactoryPrev.dedup]
  | x :: xs => by
    simp only [FactoryPrev.dedup, List.nodup_cons]
    refine ⟨?_, (prev_dedup_nodup xs).filter _⟩
    simp [List.mem_filter]

theorem prev_dedup_ne_nil : ∀ l : List StepId, l ≠ [] → FactoryPrev.dedup l ≠ []
  | [] => by simp
  | x :: xs => by simp [FactoryPrev.dedup]

theorem p02 : P02 plan := by
  intro v
  rw [p05 v]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (List.take_sublist _ _).trans (prev_dedup_sublist _)
  · exact (prev_dedup_nodup _).sublist (List.take_sublist _ _)
  · simp [FactoryPrev.plan]; omega
  · intro hr hs
    simp [FactoryPrev.plan]
    exact ⟨by omega, prev_dedup_ne_nil _ hr⟩

theorem p03 : P03 FactoryPrev.workflows workflows := by unfold P03; decide

theorem p04 : P04Unchanged FactoryPrev.workflows workflows := by unfold P04Unchanged; decide

end FactoryPkg
