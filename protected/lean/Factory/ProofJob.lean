import Factory.ProofLemmas
/-
  Factory.ProofJob — job-level invariant preservation lemmas.
-/
namespace Factory.Contracts
open Factory Factory.Check

structure AC (j : Job) : Prop where
  gnodup : (j.attempts.map (·.gen)).Nodup
  grange : ∀ a ∈ j.attempts, 1 ≤ a.gen ∧ a.gen ≤ j.attempts.length
  cur : ∀ st ∈ j.steps, ∀ g, st.current = some g → st.status = .active ∧ st.accepted = none ∧
    ∃ a ∈ j.attempts, a.step = st.id ∧ a.gen = g ∧ a.status.live = true
  idle : ∀ st ∈ j.steps, st.current = none → st.status ≠ .active
  live : ∀ a ∈ j.attempts, a.status.live = true → ∃ st ∈ j.steps, st.id = a.step ∧ st.current = some a.gen

theorem findAttempt?_eq_some {j : Job} {sid g a} (hg : (j.attempts.map (·.gen)).Nodup) :
    j.findAttempt? sid g = some a ↔ a ∈ j.attempts ∧ a.step = sid ∧ a.gen = g := by
  constructor
  · intro h
    have := List.find?_some h
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨List.mem_of_find?_eq_some h, this⟩
  · rintro ⟨ha, rfl, rfl⟩
    exact find?_eq_some_of_key hg ha (by simp) (by
      intro y _ hy; simp only [Bool.and_eq_true, beq_iff_eq] at hy; exact hy.2)

theorem findStep?_eq_some {j : Job} {sid st} (hn : (j.steps.map (·.id)).Nodup) :
    j.findStep? sid = some st ↔ st ∈ j.steps ∧ st.id = sid :=
  find?_id_eq_some_iff hn

theorem ac_iff {j : Job} (hn : (j.steps.map (·.id)).Nodup) : attemptsConsistent j = true ↔ AC j := by
  unfold attemptsConsistent
  simp only [Bool.and_eq_true, List.all_eq_true, noDupBy_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨hg, hr⟩, hc⟩, hl⟩
    refine ⟨hg, hr, ?_, ?_, ?_⟩
    · intro st hst g hcur
      have := hc st hst
      rw [hcur] at this
      simp only at this
      split at this
      · rename_i a ha
        rw [findAttempt?_eq_some hg] at ha
        simp only [Bool.and_eq_true, beq_iff_eq] at this
        exact ⟨this.1.2, by simpa using this.2, a, ha.1, ha.2.1, ha.2.2, this.1.1⟩
      · exact absurd this (by simp)
    · intro st hst hcur
      have := hc st hst
      rw [hcur] at this
      simpa using this
    · intro a ha hlive
      have := hl a ha
      simp only [hlive, Bool.not_true, Bool.false_or] at this
      split at this
      · rename_i st hst
        rw [findStep?_eq_some hn] at hst
        exact ⟨st, hst.1, hst.2, by simpa using this⟩
      · exact absurd this (by simp)
  · rintro ⟨hg, hr, hc, hi, hl⟩
    refine ⟨⟨⟨hg, hr⟩, ?_⟩, ?_⟩
    · intro st hst
      cases hcur : st.current with
      | none => simpa using hi st hst hcur
      | some g =>
        obtain ⟨h1, h2, a, ha, h3, h4, h5⟩ := hc st hst g hcur
        simp only
        rw [(findAttempt?_eq_some hg).2 ⟨ha, h3, h4⟩]
        simp [h1, h2, h5]
    · intro a ha
      cases hlive : a.status.live with
      | false => simp
      | true =>
        obtain ⟨st, hst, h1, h2⟩ := hl a ha hlive
        simp only [Bool.not_true, Bool.false_or]
        rw [(findStep?_eq_some hn).2 ⟨hst, h1⟩]
        simp [h2]

/-! ### Step-level Boolean pieces of the job invariants -/

def stepAccOk (st : StepState) : Bool :=
  match st.accepted with
  | some a => st.current.isNone && st.status == stepStatusOf a.outcome
  | none => st.status == .pending || st.status == .active || st.status == .failed

def stepFenced (n : Nat) (st : StepState) : Bool :=
  match st.accepted with
  | some a => decide (a.acceptedAt < a.leaseDeadline) && decide (a.gen ≤ n)
  | none => true

theorem acceptedConsistent_eq (j : Job) : acceptedConsistent j = j.steps.all stepAccOk := rfl

theorem acceptedFenced_eq (j : Job) : acceptedFenced j = j.steps.all (stepFenced j.attempts.length) := rfl

theorem terminalQuiet_iff (j : Job) :
    terminalQuiet j = true ↔ (j.status.terminal = true → ∀ a ∈ j.attempts, a.status.live = false) := by
  unfold terminalQuiet Job.liveAttempts
  cases j.status.terminal <;> simp [List.filter_eq_nil_iff]

/-! ### Replacement in a list with a unique match -/

theorem mem_replace {α} {l : List α} {p : α → Bool} {a' x : α} :
    x ∈ l.map (fun y => if p y then a' else y) → x = a' ∨ (x ∈ l ∧ p x = false) := by
  intro h
  rw [List.mem_map] at h
  obtain ⟨y, hy, rfl⟩ := h
  by_cases hp : p y = true
  · simp [hp]
  · simp only [hp]; simp at hp; exact Or.inr ⟨hy, hp⟩

theorem mem_replace_of {α} {l : List α} {p : α → Bool} {a' y : α} (hy : y ∈ l) (hp : p y = false) :
    y ∈ l.map (fun y => if p y then a' else y) := by
  rw [List.mem_map]; exact ⟨y, hy, by simp [hp]⟩

theorem mem_replace_new {α} {l : List α} {p : α → Bool} {a a' : α} (ha : a ∈ l) (hp : p a = true) :
    a' ∈ l.map (fun y => if p y then a' else y) := by
  rw [List.mem_map]; exact ⟨a, ha, by simp [hp]⟩

theorem map_replace_key {α β} {l : List α} {p : α → Bool} {a' : α} {key : α → β}
    (h : ∀ y ∈ l, p y = true → key a' = key y) :
    (l.map (fun y => if p y then a' else y)).map key = l.map key := by
  rw [List.map_map]
  apply List.map_congr_left
  intro y hy
  simp only [Function.comp]
  split
  · exact h y hy (by assumption)
  · rfl

theorem setAttempt_gens (j : Job) (a : Attempt) :
    (j.setAttempt a).attempts.map (·.gen) = j.attempts.map (·.gen) := by
  unfold Job.setAttempt
  apply map_replace_key
  intro y _ hy
  simp only [Bool.and_eq_true, beq_iff_eq] at hy
  exact hy.2.symm

theorem setAttempt_length (j : Job) (a : Attempt) :
    (j.setAttempt a).attempts.length = j.attempts.length := by
  simp [Job.setAttempt]

theorem setStep_ids (j : Job) (st : StepState) :
    (j.setStep st).steps.map (·.id) = j.steps.map (·.id) := by
  unfold Job.setStep
  apply map_replace_key
  intro y _ hy
  simp only [beq_iff_eq] at hy
  exact hy.symm

/-! ### Revoking live authority -/

theorem revokeLive_attempts (j : Job) (ns : AttemptStatus) :
    (j.revokeLive ns).1.attempts = j.attempts.map (Attempt.revokeTo ns) := rfl

theorem revokeLive_steps (j : Job) (ns : AttemptStatus) :
    (j.revokeLive ns).1.steps = j.steps.map StepState.dropAuthority := rfl

theorem revokeTo_live {ns : AttemptStatus} (hns : ns.live = false) (a : Attempt) :
    (a.revokeTo ns).status.live = false := by
  unfold Attempt.revokeTo; split <;> simp_all

theorem dropAuthority_id (st : StepState) : st.dropAuthority.id = st.id := by
  unfold StepState.dropAuthority; split <;> rfl

theorem dropAuthority_accepted (st : StepState) : st.dropAuthority.accepted = st.accepted := by
  unfold StepState.dropAuthority; split <;> rfl

theorem dropAuthority_current (st : StepState) : st.dropAuthority.current = none := by
  unfold StepState.dropAuthority; split
  · rfl
  · rename_i h; simpa using h

theorem revokeTo_gen (ns : AttemptStatus) (a : Attempt) : (a.revokeTo ns).gen = a.gen := by
  unfold Attempt.revokeTo; split <;> rfl

theorem revokeTo_step (ns : AttemptStatus) (a : Attempt) : (a.revokeTo ns).step = a.step := by
  unfold Attempt.revokeTo; split <;> rfl

theorem revokeTo_role (ns : AttemptStatus) (a : Attempt) : (a.revokeTo ns).role = a.role := by
  unfold Attempt.revokeTo; split <;> rfl

theorem revokeTo_live_imp (ns : AttemptStatus) (hns : ns.live = false) (a : Attempt) :
    (a.revokeTo ns).status.live = true → a.status.live = true := by
  rw [revokeTo_live hns]; simp

/-- Any job whose attempts/steps are the revoked versions of an AC job is AC. -/
theorem ac_revoked {j j' : Job} {ns : AttemptStatus} (hns : ns.live = false) (hac : AC j)
    (ha : j'.attempts = j.attempts.map (Attempt.revokeTo ns))
    (hs : j'.steps = j.steps.map StepState.dropAuthority) : AC j' := by
  have hgens : j'.attempts.map (·.gen) = j.attempts.map (·.gen) := by
    rw [ha, List.map_map]; apply List.map_congr_left; intro y _; exact revokeTo_gen ns y
  have hlen : j'.attempts.length = j.attempts.length := by rw [ha, List.length_map]
  refine ⟨hgens ▸ hac.gnodup, ?_, ?_, ?_, ?_⟩
  · intro a h
    rw [ha, List.mem_map] at h
    obtain ⟨y, hy, rfl⟩ := h
    rw [revokeTo_gen, hlen]; exact hac.grange y hy
  · intro st h g hg
    rw [hs, List.mem_map] at h
    obtain ⟨y, _, rfl⟩ := h
    rw [dropAuthority_current] at hg; cases hg
  · intro st h _
    rw [hs, List.mem_map] at h
    obtain ⟨y, hy, rfl⟩ := h
    unfold StepState.dropAuthority
    split
    · simp only; split <;> simp_all
    · rename_i hc; exact hac.idle y hy (by simpa using hc)
  · intro a h hl
    rw [ha, List.mem_map] at h
    obtain ⟨y, _, rfl⟩ := h
    rw [revokeTo_live hns] at hl; cases hl

theorem stepAccOk_dropAuthority {j : Job} (hac : AC j) {st : StepState} (hst : st ∈ j.steps)
    (hok : stepAccOk st = true) : stepAccOk st.dropAuthority = true := by
  unfold StepState.dropAuthority
  split
  · rename_i hc
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hc
    obtain ⟨h1, h2, _⟩ := hac.cur st hst g hg
    simp [stepAccOk, h1, h2]
  · exact hok

theorem stepFenced_dropAuthority (n : Nat) (st : StepState) :
    stepFenced n st.dropAuthority = stepFenced n st := by
  unfold stepFenced; rw [dropAuthority_accepted]

/-! ### The job-intrinsic invariant -/

structure JInv (j : Job) : Prop where
  nodup : (j.steps.map (·.id)).Nodup
  ac : AC j
  acc : ∀ st ∈ j.steps, stepAccOk st = true
  fenced : ∀ st ∈ j.steps, stepFenced j.attempts.length st = true
  quiet : j.status.terminal = true → ∀ a ∈ j.attempts, a.status.live = false

theorem jinv_iff (j : Job) :
    ((j.steps.map (·.id)).Nodup ∧ attemptsConsistent j = true ∧ acceptedConsistent j = true ∧
      acceptedFenced j = true ∧ terminalQuiet j = true) ↔ JInv j := by
  constructor
  · rintro ⟨hn, hac, hacc, hf, hq⟩
    rw [acceptedConsistent_eq, List.all_eq_true] at hacc
    rw [acceptedFenced_eq, List.all_eq_true] at hf
    exact ⟨hn, (ac_iff hn).1 hac, hacc, hf, (terminalQuiet_iff j).1 hq⟩
  · rintro ⟨hn, hac, hacc, hf, hq⟩
    refine ⟨hn, (ac_iff hn).2 hac, ?_, ?_, (terminalQuiet_iff j).2 hq⟩
    · rw [acceptedConsistent_eq, List.all_eq_true]; exact hacc
    · rw [acceptedFenced_eq, List.all_eq_true]; exact hf

/-- Relations between a job and its successor used by transition properties. -/
def AccSame (j j' : Job) : Prop :=
  ∀ sid, (j'.findStep? sid).bind (·.accepted) = (j.findStep? sid).bind (·.accepted)

def AttKeys (j j' : Job) : Prop :=
  ∀ sid g, (j'.findAttempt? sid g).isSome = (j.findAttempt? sid g).isSome

def LiveLe (j j' : Job) : Prop :=
  (∀ c, j'.liveOfClass c ≤ j.liveOfClass c) ∧ j'.liveAttempts.length ≤ j.liveAttempts.length

theorem AccSame.refl (j : Job) : AccSame j j := fun _ => rfl
theorem AttKeys.refl (j : Job) : AttKeys j j := fun _ _ => rfl
theorem LiveLe.refl (j : Job) : LiveLe j j := ⟨fun _ => Nat.le_refl _, Nat.le_refl _⟩

theorem AccSame.trans {a b c : Job} (h1 : AccSame a b) (h2 : AccSame b c) : AccSame a c :=
  fun sid => (h2 sid).trans (h1 sid)
theorem AttKeys.trans {a b c : Job} (h1 : AttKeys a b) (h2 : AttKeys b c) : AttKeys a c :=
  fun sid g => (h2 sid g).trans (h1 sid g)
theorem LiveLe.trans {a b c : Job} (h1 : LiveLe a b) (h2 : LiveLe b c) : LiveLe a c :=
  ⟨fun cl => Nat.le_trans (h2.1 cl) (h1.1 cl), Nat.le_trans h2.2 h1.2⟩

theorem findStep?_map_dropAuthority (steps : List StepState) (k : StepId) :
    (steps.map StepState.dropAuthority).find? (·.id == k) =
      (steps.find? (·.id == k)).map StepState.dropAuthority := by
  rw [List.find?_map]; congr 1; apply congrArg (fun p => List.find? p steps); funext x
  simp [Function.comp, dropAuthority_id]

theorem findAttempt?_map_revokeTo (ns : AttemptStatus) (atts : List Attempt) (sid : StepId) (g : Nat) :
    (atts.map (Attempt.revokeTo ns)).find? (fun a => a.step == sid && a.gen == g) =
      (atts.find? (fun a => a.step == sid && a.gen == g)).map (Attempt.revokeTo ns) := by
  rw [List.find?_map]; congr 1; apply congrArg (fun p => List.find? p atts); funext x
  simp [Function.comp, revokeTo_gen, revokeTo_step]

theorem revokeLive_accSame (j : Job) (j' : Job)
    (hs : j'.steps = j.steps.map StepState.dropAuthority) : AccSame j j' := by
  intro sid
  unfold Job.findStep?
  rw [hs, findStep?_map_dropAuthority]
  cases j.steps.find? (·.id == sid) <;> simp [dropAuthority_accepted]

theorem revokeLive_attKeys (j : Job) (ns : AttemptStatus) (j' : Job)
    (ha : j'.attempts = j.attempts.map (Attempt.revokeTo ns)) : AttKeys j j' := by
  intro sid g
  unfold Job.findAttempt?
  rw [ha, findAttempt?_map_revokeTo]
  cases j.attempts.find? _ <;> simp

theorem revokeLive_liveLe (j : Job) (ns : AttemptStatus) (hns : ns.live = false) (j' : Job)
    (ha : j'.attempts = j.attempts.map (Attempt.revokeTo ns)) : LiveLe j j' := by
  constructor
  · intro c
    unfold Job.liveOfClass
    rw [ha]
    apply length_filter_le_of_imp
    intro x _ h
    rw [revokeTo_live hns] at h; simp at h
  · unfold Job.liveAttempts
    rw [ha]
    apply length_filter_le_of_imp
    intro x _ h
    rw [revokeTo_live hns] at h; simp at h

theorem revokeLive_noLive (j : Job) (ns : AttemptStatus) (hns : ns.live = false) :
    ∀ a ∈ (j.revokeLive ns).1.attempts, a.status.live = false := by
  intro a h
  rw [revokeLive_attempts, List.mem_map] at h
  obtain ⟨y, _, rfl⟩ := h
  exact revokeTo_live hns y

/-- Revoking live authority (with a non-live status) preserves the intrinsic
    invariant, whatever job status is set afterwards. -/
theorem jinv_revoked {j j' : Job} {ns : AttemptStatus} (hns : ns.live = false) (hj : JInv j)
    (ha : j'.attempts = j.attempts.map (Attempt.revokeTo ns))
    (hs : j'.steps = j.steps.map StepState.dropAuthority) : JInv j' := by
  refine ⟨?_, ac_revoked hns hj.ac ha hs, ?_, ?_, ?_⟩
  · rw [hs, List.map_map]
    have : ((·.id) ∘ StepState.dropAuthority) = (·.id : StepState → StepId) := by
      funext x; simp [Function.comp, dropAuthority_id]
    rw [this]; exact hj.nodup
  · intro st h
    rw [hs, List.mem_map] at h
    obtain ⟨y, hy, rfl⟩ := h
    exact stepAccOk_dropAuthority hj.ac hy (hj.acc y hy)
  · intro st h
    rw [hs, List.mem_map] at h
    obtain ⟨y, hy, rfl⟩ := h
    rw [stepFenced_dropAuthority, ha, List.length_map]; exact hj.fenced y hy
  · intro _ a h
    rw [ha, List.mem_map] at h
    obtain ⟨y, _, rfl⟩ := h
    exact revokeTo_live hns y

/-! ### finalizeJob -/

theorem finalizeJob_fst (j : Job) :
    (finalizeJob j).1 =
      if ((jobStatusAfter j).terminal && !j.status.terminal) = true then
        { (j.revokeLive .cancelled).1 with status := jobStatusAfter j }
      else { j with status := jobStatusAfter j } := by
  unfold finalizeJob; dsimp only
  by_cases hc : ((jobStatusAfter j).terminal && !j.status.terminal) = true
  · rw [ite_eq_left hc, ite_eq_left hc]
  · rw [ite_eq_right hc, ite_eq_right hc]

theorem finalizeJob_snd_terminate (j : Job) :
    ∀ eff ∈ (finalizeJob j).2, eff.kind = .terminate := by
  unfold finalizeJob; dsimp only
  by_cases hc : ((jobStatusAfter j).terminal && !j.status.terminal) = true
  · rw [ite_eq_left hc]
    intro eff h
    simp only [Job.revokeLive, List.mem_map] at h
    obtain ⟨a, _, rfl⟩ := h
    rfl
  · rw [ite_eq_right hc]; simp

/-- Everything `finalizeJob` guarantees about its result. -/
theorem finalizeJob_spec (j : Job) (hj : JInv j) (hnt : j.status.terminal = false) :
    let j' := (finalizeJob j).1
    JInv j' ∧ AccSame j j' ∧ AttKeys j j' ∧ LiveLe j j' ∧
    j'.id = j.id ∧ j'.kind = j.kind ∧ j'.release = j.release ∧ j'.input = j.input ∧
    j'.subject = j.subject ∧ j'.epoch = j.epoch ∧ j'.budget = j.budget ∧ j'.change = j.change ∧
    j'.revision = j.revision ∧ j'.attempts.length = j.attempts.length ∧
    j'.steps.map (·.id) = j.steps.map (·.id) := by
  intro j'
  have hj' : j' = _ := finalizeJob_fst j
  split at hj'
  · rename_i hc
    have hns : AttemptStatus.cancelled.live = false := rfl
    have ha : j'.attempts = j.attempts.map (Attempt.revokeTo .cancelled) := by rw [hj']; rfl
    have hs : j'.steps = j.steps.map StepState.dropAuthority := by rw [hj']; rfl
    have hinv := jinv_revoked hns hj ha hs
    refine ⟨⟨hinv.nodup, hinv.ac, hinv.acc, hinv.fenced, ?_⟩, revokeLive_accSame j j' hs,
      revokeLive_attKeys j _ j' ha, revokeLive_liveLe j _ hns j' ha, ?_⟩
    · intro _ a h; rw [ha, List.mem_map] at h; obtain ⟨y, _, rfl⟩ := h; exact revokeTo_live hns y
    · rw [hj']
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [Job.revokeLive], ?_⟩
      simp [Job.revokeLive, List.map_map, Function.comp, dropAuthority_id]
  · rename_i hc
    have hq : j'.status.terminal = false := by
      rw [hj']; simp only
      simp only [hnt, Bool.not_false, Bool.and_true] at hc
      simpa using hc
    rw [hj'] at hq ⊢
    refine ⟨⟨hj.nodup, ?_, hj.acc, hj.fenced, ?_⟩, AccSame.refl _, AttKeys.refl _, LiveLe.refl _,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨hj.ac.gnodup, hj.ac.grange, hj.ac.cur, hj.ac.idle, hj.ac.live⟩
    · intro h; rw [hq] at h; cases h

/-! ### Uniqueness consequences -/

theorem attempt_eq_of_gen {j : Job} (hac : AC j) {x y : Attempt} (hx : x ∈ j.attempts)
    (hy : y ∈ j.attempts) (h : x.gen = y.gen) : x = y :=
  nodup_map_inj hac.gnodup hx hy h

theorem step_eq_of_id {j : Job} (hn : (j.steps.map (·.id)).Nodup) {x y : StepState}
    (hx : x ∈ j.steps) (hy : y ∈ j.steps) (h : x.id = y.id) : x = y :=
  nodup_map_inj hn hx hy h

theorem stepFenced_mono {n m : Nat} (h : n ≤ m) (st : StepState) (hf : stepFenced n st = true) :
    stepFenced m st = true := by
  unfold stepFenced at *
  split at hf
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hf ⊢; exact ⟨hf.1, Nat.le_trans hf.2 h⟩
  · rfl

/-! ### Retiring the current attempt of a step (settle / transport failure) -/

theorem retire_spec {j : Job} {st st' : StepState} {a a' : Attempt} (hj : JInv j)
    (hnt : j.status.terminal = false)
    (hst : st ∈ j.steps) (ha : a ∈ j.attempts) (hcur : st.current = some a.gen) (hstep : a.step = st.id)
    (ha1 : a'.step = a.step) (ha2 : a'.gen = a.gen) (ha3 : a'.status.live = false)
    (hs1 : st'.id = st.id) (hs2 : st'.current = none) (hs3 : st'.status ≠ .active)
    (hs4 : stepAccOk st' = true) (hs5 : stepFenced j.attempts.length st' = true) :
    let j1 := (j.setAttempt a').setStep st'
    JInv j1 ∧ AttKeys j j1 ∧ LiveLe j j1 ∧
    (∀ k, j1.findStep? k = (j.findStep? k).map (fun x => if x.id == st'.id then st' else x)) ∧
    j1.id = j.id ∧ j1.kind = j.kind ∧ j1.release = j.release ∧ j1.input = j.input ∧
    j1.subject = j.subject ∧ j1.epoch = j.epoch ∧ j1.budget = j.budget ∧ j1.change = j.change ∧
    j1.revision = j.revision ∧ j1.status = j.status ∧ j1.attempts.length = j.attempts.length ∧
    j1.steps.map (·.id) = j.steps.map (·.id) := by
  intro j1
  have hA : j1.attempts = j.attempts.map
      (fun y => if (y.step == a'.step && y.gen == a'.gen) then a' else y) := rfl
  have hS : j1.steps = j.steps.map (fun y => if y.id == st'.id then st' else y) := rfl
  have hlen : j1.attempts.length = j.attempts.length := by rw [hA, List.length_map]
  have hids : j1.steps.map (·.id) = j.steps.map (·.id) := setStep_ids _ _
  -- uniqueness facts
  have hAu : ∀ y ∈ j.attempts, (y.step == a'.step && y.gen == a'.gen) = true → y = a := by
    intro y hy hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact attempt_eq_of_gen hj.ac hy ha (by rw [hp.2, ha2])
  have hSu : ∀ y ∈ j.steps, (y.id == st'.id) = true → y = st := by
    intro y hy hp
    simp only [beq_iff_eq] at hp
    exact step_eq_of_id hj.nodup hy hst (by rw [hp, hs1])
  have hac : AC j1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show ((j.setAttempt a').attempts.map (·.gen)).Nodup
      rw [setAttempt_gens]; exact hj.ac.gnodup
    · intro x hx
      rw [hA] at hx
      rcases mem_replace hx with rfl | ⟨hx, _⟩
      · rw [ha2, hlen]; exact hj.ac.grange a ha
      · rw [hlen]; exact hj.ac.grange x hx
    · intro x hx g hg
      rw [hS] at hx
      rcases mem_replace hx with rfl | ⟨hx, hp⟩
      · rw [hs2] at hg; cases hg
      · obtain ⟨h1, h2, b, hb, hb1, hb2, hb3⟩ := hj.ac.cur x hx g hg
        refine ⟨h1, h2, b, ?_, hb1, hb2, hb3⟩
        rw [hA]
        apply mem_replace_of hb
        cases hq : (b.step == a'.step && b.gen == a'.gen)
        · rfl
        · have := hAu b hb hq
          subst this
          have hp' : x.id ≠ st'.id := by simpa using hp
          exact absurd (by rw [hs1, ← hstep, hb1]) hp'
    · intro x hx hc
      rw [hS] at hx
      rcases mem_replace hx with rfl | ⟨hx, _⟩
      · exact hs3
      · exact hj.ac.idle x hx hc
    · intro y hy hl
      rw [hA] at hy
      rcases mem_replace hy with rfl | ⟨hy, hp⟩
      · rw [ha3] at hl; cases hl
      · obtain ⟨x, hx, hx1, hx2⟩ := hj.ac.live y hy hl
        refine ⟨x, ?_, hx1, hx2⟩
        rw [hS]
        apply mem_replace_of hx
        cases hq : (x.id == st'.id)
        · rfl
        · have := hSu x hx hq
          subst this
          rw [hcur] at hx2
          have hg : y.gen = a.gen := (Option.some.inj hx2).symm
          have hp' : ¬((y.step == a'.step && y.gen == a'.gen) = true) := by rw [hp]; simp
          simp only [Bool.and_eq_true, beq_iff_eq] at hp'
          exact absurd ⟨by rw [ha1, hstep, hx1], by rw [ha2, hg]⟩ hp'
  refine ⟨⟨by rw [hids]; exact hj.nodup, hac, ?_, ?_, ?_⟩, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, hlen, hids⟩
  · intro x hx
    rw [hS] at hx
    rcases mem_replace hx with rfl | ⟨hx, _⟩
    · exact hs4
    · exact hj.acc x hx
  · intro x hx
    rw [hlen]
    rw [hS] at hx
    rcases mem_replace hx with rfl | ⟨hx, _⟩
    · exact hs5
    · exact hj.fenced x hx
  · intro ht; rw [show j1.status = j.status from rfl, hnt] at ht; cases ht
  · intro k g
    show ((j.setAttempt a').findAttempt? k g).isSome = _
    rw [findAttempt?_setAttempt]; cases j.findAttempt? k g <;> simp
  · constructor
    · intro c
      unfold Job.liveOfClass
      rw [hA]
      apply length_filter_le_of_imp
      intro y hy hp
      split at hp
      · simp [ha3] at hp
      · exact hp
    · unfold Job.liveAttempts
      rw [hA]
      apply length_filter_le_of_imp
      intro y hy hp
      split at hp
      · simp [ha3] at hp
      · exact hp
  · intro k
    exact findStep?_setStep _ _ _

/-! ### Modifying a live attempt in place (observe / heartbeat) -/

theorem modify_spec {j : Job} {a a' : Attempt} (hj : JInv j) (ha : a ∈ j.attempts)
    (ha1 : a'.step = a.step) (ha2 : a'.gen = a.gen) (ha3 : a'.status.live = a.status.live)
    (ha4 : a'.role = a.role) :
    let j1 := j.setAttempt a'
    JInv j1 ∧ AttKeys j j1 ∧ LiveLe j j1 ∧ j1.steps = j.steps ∧
    j1.id = j.id ∧ j1.kind = j.kind ∧ j1.release = j.release ∧ j1.input = j.input ∧
    j1.subject = j.subject ∧ j1.epoch = j.epoch ∧ j1.budget = j.budget ∧ j1.change = j.change ∧
    j1.revision = j.revision ∧ j1.status = j.status ∧ j1.attempts.length = j.attempts.length := by
  intro j1
  have hA : j1.attempts = j.attempts.map
      (fun y => if (y.step == a'.step && y.gen == a'.gen) then a' else y) := rfl
  have hlen : j1.attempts.length = j.attempts.length := by rw [hA, List.length_map]
  have hAu : ∀ y ∈ j.attempts, (y.step == a'.step && y.gen == a'.gen) = true → y = a := by
    intro y hy hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact attempt_eq_of_gen hj.ac hy ha (by rw [hp.2, ha2])
  have hac : AC j1 := by
    refine ⟨?_, ?_, ?_, hj.ac.idle, ?_⟩
    · show ((j.setAttempt a').attempts.map (·.gen)).Nodup
      rw [setAttempt_gens]; exact hj.ac.gnodup
    · intro x hx
      rw [hA] at hx
      rcases mem_replace hx with rfl | ⟨hx, _⟩
      · rw [ha2, hlen]; exact hj.ac.grange a ha
      · rw [hlen]; exact hj.ac.grange x hx
    · intro x hx g hg
      obtain ⟨h1, h2, b, hb, hb1, hb2, hb3⟩ := hj.ac.cur x hx g hg
      refine ⟨h1, h2, ?_⟩
      cases hq : (b.step == a'.step && b.gen == a'.gen)
      · exact ⟨b, by rw [hA]; exact mem_replace_of hb hq, hb1, hb2, hb3⟩
      · have := hAu b hb hq
        subst this
        exact ⟨a', by rw [hA]; exact mem_replace_new hb hq, by rw [ha1, hb1], by rw [ha2, hb2],
          by rw [ha3, hb3]⟩
    · intro y hy hl
      rw [hA] at hy
      rcases mem_replace hy with rfl | ⟨hy, _⟩
      · obtain ⟨x, hx, hx1, hx2⟩ := hj.ac.live a ha (by rw [← ha3]; exact hl)
        exact ⟨x, hx, by rw [hx1, ha1], by rw [hx2, ha2]⟩
      · exact hj.ac.live y hy hl
  refine ⟨⟨hj.nodup, hac, hj.acc, by rw [hlen]; exact hj.fenced, ?_⟩, ?_, ?_, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, hlen⟩
  · intro ht x hx
    rw [hA] at hx
    rcases mem_replace hx with rfl | ⟨hx, _⟩
    · rw [ha3]; exact hj.quiet ht a ha
    · exact hj.quiet ht x hx
  · intro k g
    show ((j.setAttempt a').findAttempt? k g).isSome = _
    rw [findAttempt?_setAttempt]; cases j.findAttempt? k g <;> simp
  · constructor
    · intro c
      unfold Job.liveOfClass
      rw [hA]
      apply length_filter_le_of_imp
      intro y hy hp
      split at hp
      · rename_i hq
        rw [hAu y hy hq]
        rw [← ha3, ← ha4]; exact hp
      · exact hp
    · unfold Job.liveAttempts
      rw [hA]
      apply length_filter_le_of_imp
      intro y hy hp
      split at hp
      · rename_i hq
        rw [hAu y hy hq, ← ha3]; exact hp
      · exact hp

/-! ### Authorizing a new attempt (startAttempt) -/

theorem liveOfClass_append (j : Job) (a : Attempt) (atts : List Attempt) (c : ResourceClass)
    (h : j.attempts = atts ++ [a]) (j0 : Job) (h0 : j0.attempts = atts) :
    j.liveOfClass c = j0.liveOfClass c + (if (a.status.live && a.role.resource == c) then 1 else 0) := by
  unfold Job.liveOfClass
  rw [h, h0, List.filter_append, List.length_append]
  simp only [List.filter_cons, List.filter_nil]
  split <;> simp

theorem start_spec {j : Job} {st : StepState} {a : Attempt} (hj : JInv j) (hst : st ∈ j.steps)
    (hi2 : st.current = none) (hi3 : st.accepted = none)
    (ha1 : a.step = st.id) (ha2 : a.gen = j.attempts.length + 1) (ha3 : a.status = .authorized) :
    let j1 := ({ j with attempts := j.attempts ++ [a], status := .running } : Job).setStep
      { st with status := .active, current := some (j.attempts.length + 1) }
    JInv j1 ∧
    (∀ c, j1.liveOfClass c = j.liveOfClass c + (if a.role.resource == c then 1 else 0)) ∧
    j1.liveAttempts.length = j.liveAttempts.length + 1 ∧
    j1.attempts = j.attempts ++ [a] ∧
    (∀ k, j1.findStep? k = (j.findStep? k).map (fun x => if x.id == st.id then
        { st with status := .active, current := some (j.attempts.length + 1) } else x)) ∧
    j1.id = j.id ∧ j1.kind = j.kind ∧ j1.release = j.release ∧ j1.input = j.input ∧
    j1.subject = j.subject ∧ j1.epoch = j.epoch ∧ j1.budget = j.budget ∧ j1.change = j.change ∧
    j1.revision = j.revision ∧ j1.status = .running ∧
    j1.steps.map (·.id) = j.steps.map (·.id) := by
  intro j1
  have hA : j1.attempts = j.attempts ++ [a] := rfl
  have hS : j1.steps = j.steps.map (fun y => if y.id == st.id then
      { st with status := .active, current := some (j.attempts.length + 1) } else y) := rfl
  have hlen : j1.attempts.length = j.attempts.length + 1 := by rw [hA]; simp
  have hlive : a.status.live = true := by rw [ha3]; rfl
  have hSu : ∀ y ∈ j.steps, (y.id == st.id) = true → y = st := by
    intro y hy hp
    simp only [beq_iff_eq] at hp
    exact step_eq_of_id hj.nodup hy hst hp
  have hac : AC j1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hA, List.map_append, List.nodup_append]
      refine ⟨hj.ac.gnodup, by simp, ?_⟩
      intro x hx y hy
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
      rw [List.mem_map] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      have := (hj.ac.grange b hb).2
      omega
    · intro x hx
      rw [hlen]
      rw [hA, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · have := hj.ac.grange x hx; omega
      · omega
    · intro x hx g hg
      rw [hS] at hx
      rcases mem_replace hx with rfl | ⟨hx, hp⟩
      · simp only [Option.some.injEq] at hg
        refine ⟨rfl, hi3, a, by rw [hA]; simp, ha1, by omega, hlive⟩
      · obtain ⟨h1, h2, b, hb, hb1, hb2, hb3⟩ := hj.ac.cur x hx g hg
        exact ⟨h1, h2, b, by rw [hA]; simp [hb], hb1, hb2, hb3⟩
    · intro x hx hc
      rw [hS] at hx
      rcases mem_replace hx with rfl | ⟨hx, _⟩
      · cases hc
      · exact hj.ac.idle x hx hc
    · intro y hy hl
      rw [hA, List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · obtain ⟨x, hx, hx1, hx2⟩ := hj.ac.live y hy hl
        refine ⟨x, ?_, hx1, hx2⟩
        rw [hS]
        apply mem_replace_of hx
        cases hq : (x.id == st.id)
        · rfl
        · have := hSu x hx hq; subst this; rw [hi2] at hx2; cases hx2
      · exact ⟨_, by rw [hS]; exact mem_replace_new hst (by simp), by simp [ha1], by simp [ha2]⟩
  refine ⟨⟨by rw [show j1.steps.map (·.id) = j.steps.map (·.id) from setStep_ids _ _]; exact hj.nodup,
      hac, ?_, ?_, ?_⟩, ?_, ?_, hA, fun k => findStep?_setStep _ _ _, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, setStep_ids _ _⟩
  · intro x hx
    rw [hS] at hx
    rcases mem_replace hx with rfl | ⟨hx, _⟩
    · simp [stepAccOk, hi3]
    · exact hj.acc x hx
  · intro x hx
    rw [hS] at hx
    rcases mem_replace hx with rfl | ⟨hx, _⟩
    · simp [stepFenced, hi3]
    · exact stepFenced_mono (by rw [hlen]; omega) x (hj.fenced x hx)
  · intro ht; cases ht
  · intro c
    rw [liveOfClass_append j1 a j.attempts c hA j rfl]
    simp [hlive]
  · unfold Job.liveAttempts
    rw [hA, List.filter_append]
    simp [hlive]

/-! ### Status-only changes (pause / acknowledge / resume) -/

theorem status_spec {j : Job} (hj : JInv j) (x : JobStatus)
    (hq : x.terminal = true → ∀ a ∈ j.attempts, a.status.live = false) :
    JInv { j with status := x } :=
  ⟨hj.nodup, ⟨hj.ac.gnodup, hj.ac.grange, hj.ac.cur, hj.ac.idle, hj.ac.live⟩, hj.acc, hj.fenced, hq⟩

theorem find?_congr_mem {α} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.find?_cons, h a (by simp)]
    split
    · rfl
    · exact find?_congr_mem (fun x hx => h x (by simp [hx]))

/-! ### Generic revocation with a custom step update (controller recovery) -/

theorem jinv_revokedGen {j j' : Job} {ns : AttemptStatus} {h : StepState → StepState}
    (hns : ns.live = false) (hj : JInv j)
    (ha : j'.attempts = j.attempts.map (Attempt.revokeTo ns))
    (hs : j'.steps = j.steps.map h)
    (h1 : ∀ st ∈ j.steps, (h st).id = st.id) (h2 : ∀ st ∈ j.steps, (h st).accepted = st.accepted)
    (h3 : ∀ st ∈ j.steps, (h st).current = none) (h4 : ∀ st ∈ j.steps, st.current = none → h st = st)
    (h5 : ∀ st ∈ j.steps, st.current.isSome → (h st).status = .pending ∨ (h st).status = .failed) :
    JInv j' ∧ AccSame j j' ∧ AttKeys j j' ∧ LiveLe j j' ∧ j'.attempts.length = j.attempts.length ∧
    j'.steps.map (·.id) = j.steps.map (·.id) := by
  have hids : j'.steps.map (·.id) = j.steps.map (·.id) := by
    rw [hs, List.map_map]; apply List.map_congr_left; intro y hy; exact h1 y hy
  have hlen : j'.attempts.length = j.attempts.length := by rw [ha, List.length_map]
  have hgens : j'.attempts.map (·.gen) = j.attempts.map (·.gen) := by
    rw [ha, List.map_map]; apply List.map_congr_left; intro y _; exact revokeTo_gen ns y
  refine ⟨⟨by rw [hids]; exact hj.nodup, ⟨hgens ▸ hj.ac.gnodup, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_,
    ?_, hlen, hids⟩
  · intro a hm
    rw [ha, List.mem_map] at hm
    obtain ⟨y, hy, rfl⟩ := hm
    rw [revokeTo_gen, hlen]; exact hj.ac.grange y hy
  · intro st hm g hg
    rw [hs, List.mem_map] at hm
    obtain ⟨y, hy, rfl⟩ := hm
    rw [h3 y hy] at hg; cases hg
  · intro st hm _
    rw [hs, List.mem_map] at hm
    obtain ⟨y, hy, rfl⟩ := hm
    cases hc : y.current with
    | none => rw [h4 y hy hc]; exact hj.ac.idle y hy hc
    | some g =>
      rcases h5 y hy (by simp [hc]) with hh | hh <;> rw [hh] <;> simp
  · intro a hm hl
    rw [ha, List.mem_map] at hm
    obtain ⟨y, _, rfl⟩ := hm
    rw [revokeTo_live hns] at hl; cases hl
  · intro st hm
    rw [hs, List.mem_map] at hm
    obtain ⟨y, hy, rfl⟩ := hm
    cases hc : y.current with
    | none => rw [h4 y hy hc]; exact hj.acc y hy
    | some g =>
      obtain ⟨_, hacc, _⟩ := hj.ac.cur y hy g hc
      unfold stepAccOk
      rw [h2 y hy, hacc]
      rcases h5 y hy (by simp [hc]) with hh | hh <;> rw [hh] <;> rfl
  · intro st hm
    rw [hs, List.mem_map] at hm
    obtain ⟨y, hy, rfl⟩ := hm
    have := hj.fenced y hy
    unfold stepFenced at this ⊢
    rw [h2 y hy, hlen]; exact this
  · intro _ a hm
    rw [ha, List.mem_map] at hm
    obtain ⟨y, _, rfl⟩ := hm
    exact revokeTo_live hns y
  · intro sid
    unfold Job.findStep?
    rw [hs, List.find?_map, find?_congr_mem (q := fun x : StepState => x.id == sid)
      (fun x hx => by simp [Function.comp, h1 x hx])]
    cases hf : j.steps.find? (·.id == sid) with
    | none => rfl
    | some y => simp [h2 y (List.mem_of_find?_eq_some hf)]
  · exact revokeLive_attKeys j ns j' ha
  · exact revokeLive_liveLe j ns hns j' ha

/-! ### Migration -/

def migStep (j : Job) (spec : StepSpec) : StepState :=
  match j.findStep? spec.id with
  | some st => if st.accepted.isSome then st else { st with status := .pending, current := none }
  | none => freshStep spec.id

theorem migratedSteps_eq (j : Job) (w : WorkflowDef) : migratedSteps j w = w.steps.map (migStep j) := rfl

theorem migStep_id (j : Job) (spec : StepSpec) : (migStep j spec).id = spec.id := by
  unfold migStep
  split
  · rename_i st hst
    have := List.find?_some hst
    simp only [beq_iff_eq] at this
    split <;> exact this
  · rfl

theorem migStep_cases (j : Job) (spec : StepSpec) :
    (∃ st, j.findStep? spec.id = some st ∧ st.accepted.isSome = true ∧ migStep j spec = st) ∨
    ((migStep j spec).accepted = none ∧ (migStep j spec).current = none ∧
      (migStep j spec).status = .pending) := by
  unfold migStep
  split
  · rename_i st hst
    by_cases hc : st.accepted.isSome = true
    · exact Or.inl ⟨st, hst, hc, by simp [hc]⟩
    · right; simp only [hc]; simp at hc; simp [hc]
  · right; simp [freshStep]

theorem migrate_spec {j : Job} {w : WorkflowDef} (target : Digest) (hj : JInv j)
    (hnl : ∀ a ∈ j.attempts, a.status.live = false) (hwf : (w.steps.map (·.id)).Nodup) :
    let j' : Job := { j with release := target, epoch := j.epoch + 1, steps := migratedSteps j w }
    JInv j' ∧ j'.steps.map (·.id) = w.steps.map (·.id) ∧
    (∀ k, j'.findStep? k = (w.steps.find? (·.id == k)).map (migStep j)) := by
  intro j'
  have hS : j'.steps = w.steps.map (migStep j) := rfl
  have hids : j'.steps.map (·.id) = w.steps.map (·.id) := by
    rw [hS, List.map_map]; apply List.map_congr_left; intro y _; exact migStep_id j y
  -- every new step is either an old accepted step or an idle pending step
  have hcases : ∀ x ∈ j'.steps, (x ∈ j.steps ∧ x.accepted.isSome = true) ∨
      (x.accepted = none ∧ x.current = none ∧ x.status = .pending) := by
    intro x hx
    rw [hS, List.mem_map] at hx
    obtain ⟨spec, _, rfl⟩ := hx
    rcases migStep_cases j spec with ⟨st, hst, hacc, heq⟩ | h
    · rw [heq]; exact Or.inl ⟨List.mem_of_find?_eq_some hst, hacc⟩
    · exact Or.inr h
  have hcur : ∀ x ∈ j'.steps, x.current = none := by
    intro x hx
    rcases hcases x hx with ⟨hm, hacc⟩ | ⟨_, h, _⟩
    · have := hj.acc x hm
      unfold stepAccOk at this
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hacc
      rw [ha] at this
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at this
      exact this.1
    · exact h
  refine ⟨⟨by rw [hids]; exact hwf, ⟨hj.ac.gnodup, hj.ac.grange, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, hids, ?_⟩
  · intro x hx g hg; rw [hcur x hx] at hg; cases hg
  · intro x hx _
    rcases hcases x hx with ⟨hm, hacc⟩ | ⟨_, _, h⟩
    · have := hj.acc x hm
      unfold stepAccOk at this
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hacc
      rw [ha] at this
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      rw [this.2]; cases a.outcome <;> simp [stepStatusOf]
    · rw [h]; simp
  · intro a ha hl; rw [hnl a ha] at hl; cases hl
  · intro x hx
    rcases hcases x hx with ⟨hm, _⟩ | ⟨h1, _, h2⟩
    · exact hj.acc x hm
    · simp [stepAccOk, h1, h2]
  · intro x hx
    rcases hcases x hx with ⟨hm, _⟩ | ⟨h1, _, _⟩
    · exact hj.fenced x hm
    · simp [stepFenced, h1]
  · intro _ a ha; exact hnl a ha
  · intro k
    show (w.steps.map (migStep j)).find? (·.id == k) = _
    rw [List.find?_map]
    congr 1
    apply congrArg (fun p => List.find? p w.steps)
    funext x; simp [Function.comp, migStep_id]

end Factory.Contracts
