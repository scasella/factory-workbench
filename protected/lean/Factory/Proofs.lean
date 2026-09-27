import Factory.ProofTransitions
/-
  Factory.Proofs — machine-checked proofs of the protected contracts in
  Factory/Contracts.lean about the EXECUTED kernel (`Factory.apply`).
  No `sorry`, no new axioms; see PROOF-NOTES.md.
-/
namespace Factory.Contracts
open Factory Factory.Check

/-! ### Decomposing `apply` -/

theorem apply_ok {s : State} {e : Envelope} {t : Transition} (h : apply s e = .ok t) :
    permitted e.actor e.cmd = true ∧ ∃ s1, admit s e = .ok s1 ∧ dispatch s1 e = .ok t := by
  unfold apply at h
  unfold_ok h
  obtain ⟨_, hp, s1, ha, hd⟩ := h
  exact ⟨hp, s1, ha, hd⟩

theorem admit_ok {s s1 : State} {e : Envelope} (h : admit s e = .ok s1) :
    (∃ c, s1 = { s with clock := c }) ∧
    (e.cmd ≠ .recoverController → e.epoch = s.ctrlEpoch) := by
  unfold admit at h
  split at h
  · rename_i hc
    unfold_ok h
    obtain ⟨_, h1, h2⟩ := h
    exact ⟨⟨_, h2.symm⟩, fun _ => by simpa using h1⟩
  · rename_i hc
    unfold_ok h
    obtain ⟨_, _, _, _, h2⟩ := h
    subst h2
    exact ⟨⟨s.clock, rfl⟩, fun h => absurd hc h⟩
  · unfold_ok h
    obtain ⟨_, _, _, h1, _, _, h2⟩ := h
    exact ⟨⟨_, h2.symm⟩, fun _ => by simpa using h1⟩

theorem safeP_clock {s : State} (c : Nat) (h : SafeP s) : SafeP { s with clock := c } :=
  (safe_iff _).1 ((safe_iff s).2 h)

theorem dispatch_safe {s : State} {e : Envelope} {t : Transition} (hS : SafeP s)
    (h : dispatch s e = .ok t) : SafeP t.state := by
  rcases e with ⟨actor, epoch, tick, cmd⟩
  cases cmd <;> simp only [dispatch] at h
  · exact safe_doBootstrap hS h
  · exact safe_doCreateJob hS h
  · exact safe_startAcc hS (doStartAttempt_ok h)
  · exact safe_obsLike hS (doObserveDispatched_ok h)
  · exact safe_obsLike hS (doObserveStarted_ok h)
  · exact safe_obsLike hS (doHeartbeat_ok h)
  · rcases doSettle_ok h with ⟨hts, _⟩ | hacc
    · rw [hts]; exact hS
    · exact safe_settleAcc hS hacc
  · rcases doSettle_ok h with ⟨hts, _⟩ | hacc
    · rw [hts]; exact hS
    · exact safe_settleAcc hS hacc
  · exact safe_failLike hS (doFailAttempt_ok h)
  · exact safe_failLike hS (doExpireAttempt_ok h)
  · exact safe_statusLike hS (doPause_ok h).1
  · exact safe_statusLike hS (doAckQuiescence_ok h).1
  · exact safe_statusLike hS (doResume_ok h).1
  · exact safe_doCancel hS h
  · exact safe_doCreateChange hS h
  · exact safe_doReviseChange hS h
  · exact safe_doRegisterCandidate hS h
  · exact safe_doPublishReport hS h
  · exact safe_pubRel hS (doPublishRelease_ok h)
  · exact safe_doRecordApproval hS h
  · exact safe_doRevokeApproval hS h
  · exact safe_doActivate hS h
  · exact safe_migAcc hS (doMigrate_ok h)
  · exact safe_doRecover hS h

/-! ### Main safety theorems -/

theorem initial_safe : Safe emptyState := by
  rw [safe_iff]
  refine ⟨by simp [emptyState], by simp [emptyState], by simp [emptyState], by simp [emptyState],
    by simp [emptyState], by simp [emptyState, releasesOk], by simp [emptyState, changesOk],
    by simp [emptyState], by simp [emptyState, releasesEvidenced], by simp [emptyState, activationsApproved],
    by simp [emptyState], by simp [emptyState, State.liveOfClass], by simp [emptyState, State.liveOfClass]⟩

theorem apply_preserves {s : State} {e : Envelope} {t : Transition} (h : Safe s)
    (hs : apply s e = .ok t) : Safe t.state := by
  rw [safe_iff] at h ⊢
  obtain ⟨_, s1, ha, hd⟩ := apply_ok hs
  obtain ⟨⟨c, rfl⟩, _⟩ := admit_ok ha
  exact dispatch_safe (safeP_clock c h) hd

theorem reachable_safe {s : State} (h : Reachable s) : Safe s := by
  induction h with
  | init => exact initial_safe
  | step _ hs ih => exact apply_preserves ih hs

/-! ### Lifting `dispatch`-level facts through `admit` -/

/-- Every accepted transition factors through a clock-only update of the
    pre-state followed by `dispatch`. -/
theorem apply_dispatch {s : State} {e : Envelope} {t : Transition} (hs : apply s e = .ok t) :
    permitted e.actor e.cmd = true ∧ (e.cmd ≠ .recoverController → e.epoch = s.ctrlEpoch) ∧
    ∃ c, dispatch { s with clock := c } e = .ok t := by
  obtain ⟨hp, s1, ha, hd⟩ := apply_ok hs
  obtain ⟨⟨c, rfl⟩, hep⟩ := admit_ok ha
  exact ⟨hp, hep, c, hd⟩

/-! ### K02: accepted results are stable -/

theorem k02_stable {s : State} {e : Envelope} {t : Transition} (h : Safe s)
    (hs : apply s e = .ok t) : AcceptedStable s t.state := by
  rw [safe_iff] at h
  obtain ⟨_, _, c, hd⟩ := apply_dispatch hs
  have hS1 := safeP_clock c h
  have := shape_accepted_stable hS1 (dispatch_shape hS1 hd)
  exact this

theorem AcceptedStable.trans {a b c : State} (h1 : AcceptedStable a b) (h2 : AcceptedStable b c) :
    AcceptedStable a c := fun jid sid x hx => h2 jid sid x (h1 jid sid x hx)

theorem k02_trace {s u : State} (h : Safe s) (hst : Steps s u) : AcceptedStable s u := by
  induction hst with
  | refl => exact fun _ _ _ hx => hx
  | step hs _ ih => exact (k02_stable h hs).trans (ih (apply_preserves h hs))

/-! ### K03: fenced acceptance -/

theorem k03_fenced {s : State} {e : Envelope} {t : Transition} (h : Safe s)
    (hs : apply s e = .ok t) : FencedAcceptance s e t.state := by
  rw [safe_iff] at h
  obtain ⟨_, hep, c, hd⟩ := apply_dispatch hs
  have hS1 := safeP_clock c h
  have := shape_fenced hS1 hep (dispatch_shape hS1 hd)
  exact this

/-! ### K04: dependency safety -/

theorem k04_dependency {s : State} {e : Envelope} {t : Transition} (h : Safe s)
    (hs : apply s e = .ok t) : DependencySafe s t.state := by
  rw [safe_iff] at h
  obtain ⟨_, _, c, hd⟩ := apply_dispatch hs
  have hS1 := safeP_clock c h
  have := shape_dependency hS1 (dispatch_shape hS1 hd)
  exact this

/-! ### K05: cancellation / terminal finality -/

theorem k05_final {s : State} {e : Envelope} {t : Transition} (h : Safe s)
    (hs : apply s e = .ok t) : CancellationFinal s t.state := by
  rw [safe_iff] at h
  obtain ⟨_, _, c, hd⟩ := apply_dispatch hs
  have hS1 := safeP_clock c h
  have := shape_cancellation hS1 (dispatch_shape hS1 hd)
  exact this

/-! ### K06: publication is gated -/

theorem k06_gated {s : State} {e : Envelope} {t : Transition} (_h : Safe s)
    (hs : apply s e = .ok t) : PublicationGated s e t := by
  obtain ⟨_, _, c, hd⟩ := apply_dispatch hs
  rcases e with ⟨actor, epoch, tick, cmd⟩
  refine ⟨?_, ?_⟩
  · intro jid d as hcmd
    simp only at hcmd
    subst hcmd
    simp only [dispatch] at hd
    obtain ⟨j, cid, ch, w, pw, rel, hj, hk, hst, _, _, hw, hpw, _, h1, h2, h3, h4, h5, _, hts, _⟩ :=
      doPublishRelease_ok hd
    have hre := gatesPass_explicit (p := pw.1) (ws := pw.2) hpw
    refine ⟨j, List.mem_of_find?_eq_some hj, by simpa using List.find?_some hj, hk, hst, w, hw, pw.1, pw.2,
      hre, rel, ?_, h1, h2, h3, h5, h4⟩
    rw [hts]; exact List.mem_append_right _ (List.mem_singleton_self _)
  · intro jid d hcmd
    simp only at hcmd
    subst hcmd
    simp only [dispatch] at hd
    obtain ⟨j, w, pw, hj, hk, hst, hw, hpw, hts⟩ := doPublishReport_gate hd
    have hre := gatesPass_explicit (p := pw.1) (ws := pw.2) hpw
    refine ⟨j, List.mem_of_find?_eq_some hj, by simpa using List.find?_some hj, hk, hst, w, hw, pw.1, pw.2,
      hre, { job := jid, digest := d, subject := pw.1 }, ?_, rfl, rfl, rfl⟩
    rw [hts]; exact List.mem_append_right _ (List.mem_singleton_self _)

/-! ### K07: activation is bound to an approval (no invariant needed) -/

theorem k07_bound {s : State} {e : Envelope} {t : Transition} (hs : apply s e = .ok t) :
    ActivationBound s e t := by
  intro rel base aid hcmd
  obtain ⟨hp, _, c, hd⟩ := apply_dispatch hs
  rcases e with ⟨actor, epoch, tick, cmd⟩
  simp only at hcmd
  subst hcmd
  simp only [dispatch] at hd
  obtain ⟨a, r, hact, ha, h1, h2, h3, h4, _, hts, _⟩ := doActivate_ok hd
  refine ⟨hact, by rw [hts], a, List.mem_of_find?_eq_some ha, by simpa using List.find?_some ha, h2, h3, h1,
    h4, ?_⟩
  simpa [permitted] using hp

/-! ### K08: pinning -/

/-- Second conjunct of K08: activation leaves every job untouched. -/
theorem k08_activation {s : State} {e : Envelope} {t : Transition} (hs : apply s e = .ok t) :
    ∀ rel base aid, e.cmd = .activateRelease rel base aid → t.state.jobs = s.jobs := by
  intro rel base aid hcmd
  obtain ⟨_, _, c, hd⟩ := apply_dispatch hs
  rcases e with ⟨actor, epoch, tick, cmd⟩
  simp only at hcmd
  subst hcmd
  simp only [dispatch] at hd
  obtain ⟨_, _, _, _, _, _, _, _, _, hts, _⟩ := doActivate_ok hd
  rw [hts]

/-- K08, first conjunct: for every command that is not a `migrateJob`, no
    job's pinned release changes. -/
theorem k08_nonmigrate_jobs {s : State} {e : Envelope} {t : Transition} (h : Safe s)
    (hs : apply s e = .ok t) (hm : ∀ jid tgt r, e.cmd ≠ .migrateJob jid tgt r) :
    ∀ j ∈ s.jobs, ∃ j' ∈ t.state.jobs, j'.id = j.id ∧ j'.release = j.release := by
  rw [safe_iff] at h
  obtain ⟨_, _, c, hd⟩ := apply_dispatch hs
  have hS1 := safeP_clock c h
  have := shape_pinning hS1 (dispatch_shape hS1 hd) hm
  exact this

/-- For an accepted `migrateJob jid ..`, every OTHER job keeps its pinned
    release. -/
theorem k08_migrate_others {s : State} {e : Envelope} {t : Transition} (_h : Safe s)
    (hs : apply s e = .ok t) {jid : JobId} {tgt : Digest} {r : Nat}
    (hcmd : e.cmd = .migrateJob jid tgt r) :
    ∀ j ∈ s.jobs, j.id ≠ jid → ∃ j' ∈ t.state.jobs, j'.id = j.id ∧ j'.release = j.release := by
  intro x hx hne
  obtain ⟨_, _, c, hd⟩ := apply_dispatch hs
  rcases e with ⟨actor, epoch, tick, cmd⟩
  simp only at hcmd
  subst hcmd
  simp only [dispatch] at hd
  obtain ⟨j, _, newW, _, _, hj, _, _, _, _, _, _, _, _, _, _, hjobs, _⟩ := doMigrate_ok hd
  have hjid : j.id = jid := by simpa using List.find?_some hj
  refine ⟨x, ?_, rfl, rfl⟩
  rw [hjobs]
  exact List.mem_map.2 ⟨x, hx, by simp [hjid, hne]⟩

/-- K08 (as stated in Contracts.lean): pinning is preserved by every accepted
    transition — non-migration commands keep every pin, a migration changes
    only the named job's pin, and activation leaves all jobs untouched. -/
theorem k08_pinning {s : State} {e : Envelope} {t : Transition} (h : Safe s)
    (hs : apply s e = .ok t) : PinningPreserved s e t :=
  ⟨fun hm => k08_nonmigrate_jobs h hs hm, fun _ _ _ hcmd => k08_migrate_others h hs hcmd, k08_activation hs⟩

/-! ### K09: migration preserves results -/

theorem k09_migration {s : State} {e : Envelope} {t : Transition} (_h : Safe s)
    (hs : apply s e = .ok t) : MigrationPreserving s e t := by
  intro jid tgt r hcmd
  obtain ⟨_, _, c, hd⟩ := apply_dispatch hs
  rcases e with ⟨actor, epoch, tick, cmd⟩
  simp only at hcmd
  subst hcmd
  simp only [dispatch] at hd
  obtain ⟨j, tr, newW, oldRel, oldW, hj, hrev, _, _, _, _, _, hst, _, _, hall, hjobs, _⟩ := doMigrate_ok hd
  refine ⟨j, List.mem_of_find?_eq_some hj, by simpa using List.find?_some hj, hst, hrev,
    { ({ j with release := tgt, epoch := j.epoch + 1, steps := migratedSteps j newW } : Job) with revision := j.revision + 1 },
    ?_, by simpa using List.find?_some hj, rfl, rfl, rfl, rfl, rfl, hst, ?_, ?_⟩
  · rw [hjobs]; exact List.mem_map.2 ⟨j, List.mem_of_find?_eq_some hj, by simp⟩
  · intro sid a ha
    rw [findStep?_revision]
    exact mig_accMono hall sid a ha
  · intro sid a ha
    rw [findStep?_revision] at ha
    exact mig_accRev sid a ha

/-! ### K11: journal replay semantics -/

theorem k11_replay_nil {s : State} : replay s [] = s := rfl

theorem k11_replay_cons_ok {s : State} {e : Envelope} {es : List Envelope} {t : Transition}
    (h : apply s e = .ok t) : replay s (e :: es) = replay t.state es := by
  simp only [replay, h]

theorem k11_replay_cons_err {s : State} {e : Envelope} {es : List Envelope} {r : RejectReason}
    (h : apply s e = .error r) : replay s (e :: es) = replay s es := by
  simp only [replay, h]

theorem k11_replay_append {s : State} {es fs : List Envelope} :
    replay s (es ++ fs) = replay (replay s es) fs := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    cases h : apply s e with
    | ok t => rw [List.cons_append, k11_replay_cons_ok h, k11_replay_cons_ok h, ih]
    | error r => rw [List.cons_append, k11_replay_cons_err h, k11_replay_cons_err h, ih]

theorem k11_replay_reachable {s : State} {es : List Envelope} (h : Reachable s) :
    Reachable (replay s es) := by
  induction es generalizing s with
  | nil => exact h
  | cons e es ih =>
    cases hr : apply s e with
    | ok t => rw [k11_replay_cons_ok hr]; exact ih (Reachable.step h hr)
    | error r => rw [k11_replay_cons_err hr]; exact ih h

/-- Replay is the unique function consistent with the journal semantics: it is
    determined by `apply` alone (determinism is definitional). -/
theorem k11_replay_deterministic {s : State} {es : List Envelope} :
    ∀ f : State → List Envelope → State,
      (∀ s, f s [] = s) →
      (∀ s e es t, apply s e = .ok t → f s (e :: es) = f t.state es) →
      (∀ s e es r, apply s e = .error r → f s (e :: es) = f s es) →
      f s es = replay s es := by
  intro f h0 h1 h2
  induction es generalizing s with
  | nil => rw [h0]; rfl
  | cons e es ih =>
    cases hr : apply s e with
    | ok t => rw [h1 s e es t hr, k11_replay_cons_ok hr, ih]
    | error r => rw [h2 s e es r hr, k11_replay_cons_err hr, ih]

/-! ### K12: effect causality -/

theorem k12_causality {s : State} {e : Envelope} {t : Transition} (h : Safe s)
    (hs : apply s e = .ok t) : EffectCausality s t := by
  rw [safe_iff] at h
  obtain ⟨_, _, c, hd⟩ := apply_dispatch hs
  have hS1 := safeP_clock c h
  have := dispatch_causality hS1 hd
  exact this

/-! ### Reachable-state corollaries -/

theorem k02_reachable {s : State} {e : Envelope} {t : Transition} (h : Reachable s)
    (hs : apply s e = .ok t) : AcceptedStable s t.state := k02_stable (reachable_safe h) hs

theorem k02_trace_reachable {s u : State} (h : Reachable s) (hst : Steps s u) : AcceptedStable s u :=
  k02_trace (reachable_safe h) hst

theorem k03_reachable {s : State} {e : Envelope} {t : Transition} (h : Reachable s)
    (hs : apply s e = .ok t) : FencedAcceptance s e t.state := k03_fenced (reachable_safe h) hs

theorem k04_reachable {s : State} {e : Envelope} {t : Transition} (h : Reachable s)
    (hs : apply s e = .ok t) : DependencySafe s t.state := k04_dependency (reachable_safe h) hs

theorem k05_reachable {s : State} {e : Envelope} {t : Transition} (h : Reachable s)
    (hs : apply s e = .ok t) : CancellationFinal s t.state := k05_final (reachable_safe h) hs

theorem k06_reachable {s : State} {e : Envelope} {t : Transition} (h : Reachable s)
    (hs : apply s e = .ok t) : PublicationGated s e t := k06_gated (reachable_safe h) hs

theorem k07_reachable {s : State} {e : Envelope} {t : Transition} (_h : Reachable s)
    (hs : apply s e = .ok t) : ActivationBound s e t := k07_bound hs

theorem k08_reachable {s : State} {e : Envelope} {t : Transition} (h : Reachable s)
    (hs : apply s e = .ok t) : PinningPreserved s e t := k08_pinning (reachable_safe h) hs

theorem k08_activation_reachable {s : State} {e : Envelope} {t : Transition} (_h : Reachable s)
    (hs : apply s e = .ok t) :
    ∀ rel base aid, e.cmd = .activateRelease rel base aid → t.state.jobs = s.jobs := k08_activation hs

theorem k09_reachable {s : State} {e : Envelope} {t : Transition} (h : Reachable s)
    (hs : apply s e = .ok t) : MigrationPreserving s e t := k09_migration (reachable_safe h) hs

theorem k12_reachable {s : State} {e : Envelope} {t : Transition} (h : Reachable s)
    (hs : apply s e = .ok t) : EffectCausality s t := k12_causality (reachable_safe h) hs

/-- Every state of every accepted trace from a reachable state is safe. -/
theorem steps_safe {s u : State} (h : Safe s) (hst : Steps s u) : Safe u := by
  induction hst with
  | refl => exact h
  | step hs _ ih => exact ih (apply_preserves h hs)

end Factory.Contracts
