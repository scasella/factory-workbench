import Factory.ProofHandlers
/-
  Factory.ProofExplicit — bridges from the kernel's decision functions
  (`prereqsDone`, `bindInputs`, `gatesPass`) to the explicit,
  implementation-independent statements in Contracts.lean
  (`StepDone`, the per-index input binding of `DependencySafe`,
  `PassingEvidence`, `RequiredEvidence`).
-/
namespace Factory.Contracts
open Factory Factory.Check

/-! ### Option-`mapM` -/

theorem mapM_option_spec {α β} (f : α → Option β) :
    ∀ (l : List α) (r : List β), l.mapM f = some r →
      r.length = l.length ∧ ∀ (i : Nat) b, l[i]? = some b → ∃ y, f b = some y ∧ r[i]? = some y
  | [], r, h => by
    simp only [List.mapM_nil] at h
    cases h
    simp
  | a :: l, r, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨y, hy, r', hr', rfl⟩ := h
    obtain ⟨ih1, ih2⟩ := mapM_option_spec f l r' hr'
    refine ⟨by simp [ih1], ?_⟩
    intro i b hb
    cases i with
    | zero => simp at hb; subst hb; exact ⟨y, hy, rfl⟩
    | succ i => simpa using ih2 i b (by simpa using hb)

/-! ### Prerequisites -/

theorem stepDone_of_prereq {j : Job} (hj : JInv j) {spec : StepSpec}
    (hpre : prereqsDone j spec = true) {p : StepId} (hp : p ∈ spec.prereqs) : StepDone j p := by
  unfold prereqsDone at hpre
  rw [List.all_eq_true] at hpre
  have := hpre p hp
  split at this
  · rename_i q hq
    have hqm := List.mem_of_find?_eq_some hq
    have hqid : q.id = p := by simpa using List.find?_some hq
    have hst : q.status = .succeeded := by simpa using this
    refine ⟨q, hqm, hqid, hst, ?_⟩
    have hacc := hj.acc q hqm
    unfold stepAccOk at hacc
    cases hqa : q.accepted with
    | some _ => rfl
    | none => rw [hqa, hst] at hacc; simp at hacc
  · cases this

/-- The kernel's `prereqsDone`/`bindInputs` imply the explicit K04 conditions. -/
theorem dep_explicit {j : Job} (hj : JInv j) {w : WorkflowDef} {sid : StepId} {spec : StepSpec}
    {ins : List (String × Digest)}
    (hspec : w.find? sid = some spec) (hpre : prereqsDone j spec = true)
    (hins : bindInputs j spec = some ins) :
    spec ∈ w.steps ∧ spec.id = sid ∧ (∀ p ∈ spec.after, StepDone j p) ∧
      ins.length = spec.inputs.length ∧
      (∀ i < spec.inputs.length, ∀ b, spec.inputs[i]? = some b →
        match b.source with
        | .jobInput => ins[i]? = some (b.name, j.input)
        | .stepOutput p => StepDone j p ∧ ∃ q ∈ j.steps, q.id = p ∧ ∃ acc, q.accepted = some acc ∧
            ins[i]? = some (b.name, acc.result)) := by
  have hmem : spec ∈ w.steps := List.mem_of_find?_eq_some hspec
  have hid : spec.id = sid := by simpa using List.find?_some hspec
  obtain ⟨hlen, hidx⟩ := mapM_option_spec _ spec.inputs ins hins
  refine ⟨hmem, hid, fun p hp => stepDone_of_prereq hj hpre (by simp [StepSpec.prereqs, hp]), hlen, ?_⟩
  intro i _ b hb
  obtain ⟨y, hy, hiy⟩ := hidx i b hb
  have hbm : b ∈ spec.inputs := List.mem_of_getElem? hb
  split
  · rename_i hsrc
    simp only [hsrc, Option.some.injEq] at hy
    rw [hiy, hy]
  · rename_i p hsrc
    simp only [hsrc] at hy
    refine ⟨stepDone_of_prereq hj hpre ?_, ?_⟩
    · simp only [StepSpec.prereqs, List.mem_append, StepSpec.inputSteps, List.mem_filterMap]
      exact Or.inr ⟨b, hbm, by simp [hsrc]⟩
    · cases hq : j.findStep? p with
      | none => rw [hq] at hy; cases hy
      | some q =>
        rw [hq] at hy
        simp only [Option.bind_some, Option.map_eq_some_iff] at hy
        obtain ⟨acc, hacc, rfl⟩ := hy
        exact ⟨q, List.mem_of_find?_eq_some hq, by simpa using List.find?_some hq, acc, hacc, hiy⟩

/-! ### Publication gates -/

theorem gateEvidence_explicit {j : Job} {w : WorkflowDef} {r : Role} {a : Accepted}
    (h : gateEvidence j w r = some a) : PassingEvidence j w r a := by
  unfold gateEvidence at h
  split at h
  · rename_i sp hsp
    split at h
    · rename_i st hst
      split at h
      · rename_i a0 ha0
        split at h
        · rename_i hc
          simp only [Option.some.injEq] at h
          subst h
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          unfold WorkflowDef.uniqueRole at hsp
          split at hsp
          · rename_i sp' hl
            simp only [Option.some.injEq] at hsp
            subst hsp
            have hm : sp' ∈ w.stepsWithRole r := by rw [hl]; simp
            unfold WorkflowDef.stepsWithRole at hm
            rw [List.mem_filter] at hm
            exact ⟨sp', hm.1, by simpa using hm.2, st, List.mem_of_find?_eq_some hst,
              by simpa using List.find?_some hst, ha0, hc.1, hc.2⟩
          · cases hsp
        · cases h
      · cases h
    · cases h
  · cases h

theorem gatesPass_explicit {s : State} {j : Job} {w : WorkflowDef} {p : Digest} {ws : List WorkflowDef}
    (h : gatesPass s j w = .ok (p, ws)) : RequiredEvidence s j w p ws := by
  unfold gatesPass at h
  unfold_ok h
  obtain ⟨b, hb, pr, hp, rp, hrp, rf, hrf, pay, hpay, _, h1, _, h2, _, h3, _, _, hx⟩ := h
  simp only [Prod.mk.injEq] at hx
  obtain ⟨rfl, rfl⟩ := hx
  simp only [beq_iff_eq, Bool.and_eq_true] at h1 h2 h3
  exact ⟨b, pr, rp, rf, gateEvidence_explicit hb, gateEvidence_explicit hp, gateEvidence_explicit hrp,
    gateEvidence_explicit hrf, h1, hpay, rfl, h2.1.1, h2.1.2, h2.2, h3.1, h3.2⟩

theorem doPublishReport_gate {s : State} {jid : JobId} {rep : Digest} {t : Transition}
    (h : doPublishReport s jid rep = .ok t) :
    ∃ j w pw, s.findJob? jid = some j ∧ j.kind = .packageAudit ∧ j.status = .succeeded ∧
      s.workflowOf j = some w ∧ gatesPass s j w = .ok pw ∧
      t.state = { s with reports := s.reports ++ [{ job := jid, digest := rep, subject := pw.1 }] } := by
  unfold doPublishReport at h
  unfold_ok h
  obtain ⟨j, hj, _, hk, _, hst, w, hw, pw, hpw, _, _, _, _, hts⟩ := h
  simp only [beq_iff_eq] at hk hst
  exact ⟨j, w, pw, hj, hk, hst, hw, hpw, by rw [hts]⟩

end Factory.Contracts
