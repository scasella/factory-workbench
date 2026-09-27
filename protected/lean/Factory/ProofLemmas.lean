import Factory.Contracts
/-
  Factory.ProofLemmas — reusable lemmas for the kernel safety proofs
  (Factory/Proofs.lean). Nothing here changes any kernel definition.
-/
namespace Factory.Contracts
open Factory Factory.Check

/-! ### Except-monad plumbing -/

theorem bind_eq_ok {ε α β} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem check_eq_ok {b : Bool} {r : RejectReason} {u : Unit} : check b r = .ok u ↔ b = true := by
  unfold check; split <;> simp_all

theorem need_eq_ok {α} {o : Option α} {r : RejectReason} {a : α} : need o r = .ok a ↔ o = some a := by
  unfold need; split <;> simp_all

theorem ok_eq_ok {s evs effs t} :
    ok s evs effs = .ok t ↔ t = { state := s, events := evs, effects := effs } := by
  unfold ok; constructor <;> intro h <;> cases h <;> rfl

theorem pure_eq_ok {ε α} {a b : α} : (pure a : Except ε α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

/-! ### Generic list facts -/

theorem noDupBy_iff {α} [BEq α] [LawfulBEq α] (l : List α) : noDupBy l = true ↔ l.Nodup := by
  induction l with
  | nil => simp [noDupBy]
  | cons x xs ih => simp [noDupBy, ih, List.nodup_cons]

theorem noDupB_iff (l : List StepId) : noDupB l = true ↔ l.Nodup := by
  induction l with
  | nil => simp [noDupB]
  | cons x xs ih => simp [noDupB, ih, List.nodup_cons]

theorem nodup_map_inj {α β} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => by simp at hx
  | a :: l, h, x, y, hx, hy, hxy => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · exact absurd hxy.symm (h.1 y hy)
    · exact absurd hxy (h.1 x hx)
    · exact nodup_map_inj h.2 hx hy hxy

/-- `find?` under a predicate that identifies elements by a unique key. -/
theorem find?_eq_some_of_key {α β} {p : α → Bool} {key : α → β} {l : List α} {x : α}
    (hn : (l.map key).Nodup) (hx : x ∈ l) (hp : p x = true)
    (hk : ∀ y ∈ l, p y = true → key y = key x) : l.find? p = some x := by
  cases hf : l.find? p with
  | none => rw [List.find?_eq_none] at hf; exact absurd hp (hf x hx)
  | some y =>
    have hy := List.mem_of_find?_eq_some hf
    have hpy := List.find?_some hf
    rw [nodup_map_inj hn hy hx (hk y hy hpy)]

theorem find?_id_eq_some_iff {α} {key : α → String} {l : List α} {k : String} {x : α}
    (hn : (l.map key).Nodup) : l.find? (fun y => key y == k) = some x ↔ x ∈ l ∧ key x = k := by
  constructor
  · intro h
    exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩
  · rintro ⟨hx, rfl⟩
    exact find?_eq_some_of_key hn hx (by simp) (by intro y _ hy; simpa using hy)

theorem sum_le_sum_of_le {α} {f g : α → Nat} :
    ∀ {l : List α}, (∀ x ∈ l, f x ≤ g x) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    have := h a (by simp)
    have := sum_le_sum_of_le (l := l) (fun x hx => h x (by simp [hx]))
    omega

theorem length_filter_le_of_imp {α} {p q : α → Bool} {f : α → α} :
    ∀ {l : List α}, (∀ x ∈ l, p (f x) = true → q x = true) →
      ((l.map f).filter p).length ≤ (l.filter q).length
  | [], _ => by simp
  | a :: l, h => by
    have ih := length_filter_le_of_imp (l := l) (p := p) (q := q) (f := f)
      (fun x hx => h x (by simp [hx]))
    have ha := h a (by simp)
    simp only [List.map_cons, List.filter_cons]
    by_cases hp : p (f a) = true
    · simp [hp, ha hp]; omega
    · by_cases hq : q a = true
      · simp [hp, hq]; omega
      · simp [hp, hq]; omega

/-! ### Key-preserving replacement lemmas (no uniqueness needed) -/

theorem findJob?_putJob (s : State) (j' : Job) (k : JobId) :
    (s.putJob j').findJob? k =
      (s.findJob? k).map (fun x => if x.id == j'.id then { j' with revision := x.revision + 1 } else x) := by
  unfold State.findJob? State.putJob
  rw [List.find?_map]
  congr 1
  apply congrArg (fun p => List.find? p s.jobs)
  funext x
  simp only [Function.comp]
  split <;> simp_all

theorem findStep?_setStep (j : Job) (st : StepState) (k : StepId) :
    (j.setStep st).findStep? k = (j.findStep? k).map (fun x => if x.id == st.id then st else x) := by
  unfold Job.findStep? Job.setStep
  rw [List.find?_map]
  congr 1
  apply congrArg (fun p => List.find? p j.steps)
  funext x
  simp only [Function.comp]
  split <;> simp_all

theorem findAttempt?_setAttempt (j : Job) (a : Attempt) (sid : StepId) (g : Nat) :
    (j.setAttempt a).findAttempt? sid g =
      (j.findAttempt? sid g).map (fun x => if x.step == a.step && x.gen == a.gen then a else x) := by
  unfold Job.findAttempt? Job.setAttempt
  rw [List.find?_map]
  congr 1
  apply congrArg (fun p => List.find? p j.attempts)
  funext x
  simp only [Function.comp]
  split
  · rename_i h; simp only [Bool.and_eq_true, beq_iff_eq] at h; rw [h.1, h.2]
  · rfl

end Factory.Contracts
