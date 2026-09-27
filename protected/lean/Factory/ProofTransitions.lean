import Factory.ProofExplicit
/-
  Factory.ProofTransitions — classification of how an accepted command
  changes the job list, with the per-job relations needed by the
  transition contracts (K02, K03, K04, K05, K08).
-/
namespace Factory.Contracts
open Factory Factory.Check

def AccMono (j j' : Job) : Prop :=
  ∀ sid a, (j.findStep? sid).bind (·.accepted) = some a → (j'.findStep? sid).bind (·.accepted) = some a

def FenceNew (s : State) (e : Envelope) (j j' : Job) : Prop :=
  ∀ sid a, (j.findStep? sid).bind (·.accepted) = none → (j'.findStep? sid).bind (·.accepted) = some a →
    ∃ st ∈ j.steps, st.id = sid ∧ st.current = some a.gen ∧
      ∃ att ∈ j.attempts, att.step = sid ∧ att.gen = a.gen ∧ att.status.live = true ∧
        att.jobEpoch = j.epoch ∧ att.ctrlEpoch = s.ctrlEpoch ∧ e.tick < att.deadline ∧
        a.jobEpoch = att.jobEpoch ∧ a.ctrlEpoch = att.ctrlEpoch ∧ a.leaseDeadline = att.deadline ∧
        a.fingerprint = att.fingerprint ∧ a.subject = att.subject

def DepNew (s : State) (j j' : Job) : Prop :=
  ∀ sid g a, j.findAttempt? sid g = none → j'.findAttempt? sid g = some a →
    ∃ w, s.workflowOf j = some w ∧ ∃ spec, w.find? sid = some spec ∧
      prereqsDone j spec = true ∧ bindInputs j spec = some a.inputs ∧ a.status = .authorized

theorem AccSame.mono {j j' : Job} (h : AccSame j j') : AccMono j j' := by
  intro sid a ha; rw [h sid]; exact ha

theorem AccSame.fence {s : State} {e : Envelope} {j j' : Job} (h : AccSame j j') : FenceNew s e j j' := by
  intro sid a h1 h2; rw [h sid, h1] at h2; cases h2

theorem AttKeys.dep {s : State} {j j' : Job} (h : AttKeys j j') : DepNew s j j' := by
  intro sid g a h1 h2
  have := h sid g
  rw [h1, h2] at this
  cases this

/-- The four ways an accepted command can change the job list. -/
def JobsShape (s : State) (e : Envelope) (t : Transition) : Prop :=
  t.state.jobs = s.jobs ∨
  (∃ j, t.state.jobs = s.jobs ++ [j] ∧ s.findJob? j.id = none ∧ j.attempts = [] ∧
    ∀ k, (j.findStep? k).bind (·.accepted) = none) ∨
  (∃ jid j j', s.findJob? jid = some j ∧ j.status.terminal = false ∧ j'.id = j.id ∧
    t.state.jobs = (s.putJob j').jobs ∧ e.cmd ≠ .recoverController ∧
    AccMono j j' ∧ FenceNew s e j j' ∧ DepNew s j j' ∧
    (j'.release = j.release ∨ ∃ tgt r, e.cmd = .migrateJob jid tgt r)) ∨
  (e.cmd = .recoverController ∧ t.state.jobs = s.jobs.map (fun j => (recoverAll s j).1))

/-! ### Per-command job relations -/

theorem shape_putJob {s : State} {e : Envelope} {t : Transition} {jid : JobId} {j j' : Job}
    (hjobs : t.state.jobs = (s.putJob j').jobs)
    (hf : s.findJob? jid = some j) (hnt : j.status.terminal = false) (hid : j'.id = j.id)
    (hc : e.cmd ≠ .recoverController)
    (h1 : AccMono j j') (h2 : FenceNew s e j j') (h3 : DepNew s j j') (h4 : j'.release = j.release) :
    JobsShape s e t :=
  Or.inr (Or.inr (Or.inl ⟨jid, j, j', hf, hnt, hid, hjobs, hc, h1, h2, h3, Or.inl h4⟩))

theorem newJob_basic (id : JobId) (kind : JobKind) (rel : Digest) (w : WorkflowDef) (input subject : Digest)
    (budget : BudgetId) (change : Option ChangeId) :
    let j := newJob id kind rel w input subject budget change
    j.id = id ∧ j.attempts = [] ∧ ∀ k, (j.findStep? k).bind (·.accepted) = none := by
  intro j
  refine ⟨rfl, rfl, ?_⟩
  intro k
  cases hf : j.findStep? k with
  | none => rfl
  | some st =>
    have := List.mem_of_find?_eq_some hf
    simp only [j, newJob, List.mem_map] at this
    obtain ⟨_, _, rfl⟩ := this
    rfl

theorem shape_addJob {s : State} {e : Envelope} {t : Transition} {id : JobId}
    {kind : JobKind} {rel input subject : Digest} {budget : BudgetId} {change : Option ChangeId} {j : Job}
    (hj : mkJob s id kind rel input subject budget change = .ok j) (hjobs : t.state.jobs = s.jobs ++ [j]) :
    JobsShape s e t := by
  obtain ⟨hfresh, r0, w, _, _, _, _, rfl⟩ := mkJob_ok hj
  obtain ⟨hid, hatt, hacc⟩ := newJob_basic id kind rel w input subject budget change
  exact Or.inr (Or.inl ⟨_, hjobs, by rw [hid]; exact hfresh, hatt, hacc⟩)

theorem accMono_replace {j j1 : Job} {st st' : StepState} {sid : StepId}
    (hrel : ∀ k, j1.findStep? k = (j.findStep? k).map (fun x => if x.id == st'.id then st' else x))
    (hst : j.findStep? sid = some st) (hsid : st'.id = st.id) (hn : (j.steps.map (·.id)).Nodup)
    (hacc : st.accepted = none) : AccMono j j1 := by
  intro k a h
  rw [hrel]
  cases hx : j.findStep? k with
  | none => rw [hx] at h; cases h
  | some x =>
    rw [hx] at h
    simp only [Option.bind_some] at h
    simp only [Option.map_some, Option.bind_some]
    split
    · rename_i hq
      have : x = st := step_eq_of_id hn (List.mem_of_find?_eq_some hx) (List.mem_of_find?_eq_some hst)
        (by simp only [beq_iff_eq] at hq; rw [hq, hsid])
      subst this; rw [hacc] at h; cases h
    · exact h

theorem accSame_replace {j j1 : Job} {st st' : StepState} {sid : StepId}
    (hrel : ∀ k, j1.findStep? k = (j.findStep? k).map (fun x => if x.id == st'.id then st' else x))
    (hst : j.findStep? sid = some st) (hsid : st'.id = st.id) (hn : (j.steps.map (·.id)).Nodup)
    (hacc : st'.accepted = st.accepted) : AccSame j j1 := by
  intro k
  rw [hrel]
  cases hx : j.findStep? k with
  | none => rfl
  | some x =>
    simp only [Option.map_some, Option.bind_some]
    split
    · rename_i hq
      have : x = st := step_eq_of_id hn (List.mem_of_find?_eq_some hx) (List.mem_of_find?_eq_some hst)
        (by simp only [beq_iff_eq] at hq; rw [hq, hsid])
      subst this; exact hacc
    · rfl

theorem attKeys_setAttempt (j : Job) (a : Attempt) : AttKeys j (j.setAttempt a) := by
  intro k g
  rw [findAttempt?_setAttempt]; cases j.findAttempt? k g <;> simp

/-! ### Classification of every command -/

theorem shape_obsLike {s : State} {e : Envelope} {jid : JobId} {sid : StepId} {g : Nat} {t : Transition}
    (hc : e.cmd ≠ .recoverController) (h : ObsLike s jid sid g t) : JobsShape s e t := by
  obtain ⟨j, p, a', hj, hnt, _, _, _, _, _, hts, _⟩ := h
  exact shape_putJob (j' := j.setAttempt a') (by rw [hts]) hj hnt rfl hc (AccSame.refl j).mono
    (AccSame.refl j).fence (attKeys_setAttempt j a').dep rfl

theorem shape_statusLike {s : State} {e : Envelope} {jid : JobId} {t : Transition}
    (hc : e.cmd ≠ .recoverController) (h : StatusLike s jid t) : JobsShape s e t := by
  obtain ⟨j, x, hj, hnt, _, hts⟩ := h
  exact shape_putJob (j' := { j with status := x }) (by rw [hts]) hj hnt rfl hc (AccSame.refl j).mono
    (AccSame.refl j).fence (AttKeys.refl j).dep rfl

theorem shape_cancel {s : State} {e : Envelope} {jid : JobId} {t : Transition}
    (hc : e.cmd ≠ .recoverController) (h : doCancel s jid = .ok t) : JobsShape s e t := by
  obtain ⟨j, hj, hnt, hts, _⟩ := doCancel_ok h
  have has : AccSame j { (j.revokeLive .cancelled).1 with status := .cancelled, epoch := j.epoch + 1 } :=
    revokeLive_accSame j _ rfl
  have hak : AttKeys j { (j.revokeLive .cancelled).1 with status := .cancelled, epoch := j.epoch + 1 } :=
    revokeLive_attKeys j .cancelled _ rfl
  exact shape_putJob (j' := { (j.revokeLive .cancelled).1 with status := .cancelled, epoch := j.epoch + 1 })
    (by rw [hts]) hj hnt rfl hc has.mono has.fence hak.dep rfl

theorem shape_settleAcc {s : State} {e : Envelope} {jid : JobId} {sid : StepId} {g : Nat} {t : Transition}
    (hS : SafeP s) (hc : e.cmd ≠ .recoverController) (h : SettleAcc s e jid sid g t) : JobsShape s e t := by
  obtain ⟨j, st, a, acc, hj, hst, hacc, hnt, ha, hcur, hlive, he1, he2, hdl, hg, h1, h2, hld, _, h3, h4, hts, _⟩ := h
  obtain ⟨_, _, hinv, _, _⟩ := job_of_find hS hj
  have ham := List.mem_of_find?_eq_some ha
  have hap : a.step = sid ∧ a.gen = g := by simpa using List.find?_some ha
  have hsid : st.id = sid := by simpa using List.find?_some hst
  have hstm := List.mem_of_find?_eq_some hst
  obtain ⟨hinv1, hak1, _, hrel1, e0, _, e2, _, _, _, _, _, _, est, _, _⟩ :=
    retire_spec (st' := { st with accepted := some acc, current := none, status := stepStatusOf acc.outcome })
      (a' := { a with status := .succeeded }) hinv hnt hstm ham
      (by rw [hcur, hap.2]) (by rw [hap.1, hsid]) rfl rfl rfl rfl rfl
      (by cases acc.outcome <;> simp [stepStatusOf])
      (by simp [stepAccOk])
      (by
        have := (hinv.ac.grange a ham).2
        simp only [stepFenced, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by omega, by omega⟩)
  have hnt1 : (settledJob j st a acc).status.terminal = false := by rw [← hnt]; exact congrArg _ est
  obtain ⟨_, has2, hak2, _, f0, _, f2, _⟩ := finalizeJob_spec (settledJob j st a acc) hinv1 hnt1
  have hrel1' : ∀ k, (settledJob j st a acc).findStep? k = (j.findStep? k).map
      (fun x => if x.id == st.id then { st with accepted := some acc, current := none, status := stepStatusOf acc.outcome } else x) := hrel1
  refine shape_putJob (by rw [hts]) hj hnt (f0.trans e0) hc ?_ ?_ (hak1.trans hak2).dep (f2.trans e2)
  · intro k a0 h0
    rw [has2 k]
    exact accMono_replace (st' := { st with accepted := some acc, current := none, status := stepStatusOf acc.outcome })
      hrel1' hst rfl hinv.nodup hacc k a0 h0
  · intro k a0 hn h0
    rw [has2 k, hrel1' k] at h0
    cases hx : j.findStep? k with
    | none => rw [hx] at h0; cases h0
    | some x =>
      rw [hx] at h0 hn
      simp only [Option.map_some, Option.bind_some] at h0 hn
      split at h0
      · rename_i hq
        have hxst : x = st := step_eq_of_id hinv.nodup (List.mem_of_find?_eq_some hx) hstm
          (by simpa using hq)
        subst hxst
        have hk : x.id = k := by simpa using List.find?_some hx
        simp only [Option.some.injEq] at h0
        subst h0
        refine ⟨x, hstm, hk, by rw [hcur, hg], a, ham, by rw [hap.1, ← hsid, hk], by rw [hap.2, hg],
          hlive, he1, he2, hdl, h1, h2, hld, h3, h4⟩
      · rw [hn] at h0; cases h0

theorem shape_failLike {s : State} {e : Envelope} {jid : JobId} {sid : StepId} {g : Nat} {t : Transition}
    (hS : SafeP s) (hc : e.cmd ≠ .recoverController) (h : FailLike s jid sid g t) : JobsShape s e t := by
  obtain ⟨j, spec, p, ns, hj, hnt, hp, hns, hts, _⟩ := h
  obtain ⟨_, _, hinv, _, _⟩ := job_of_find hS hj
  obtain ⟨hst, ha, hcur, _, _, _⟩ := currentAttempt_ok hp
  have hstm := List.mem_of_find?_eq_some hst
  have ham := List.mem_of_find?_eq_some ha
  have hap : p.2.step = sid ∧ p.2.gen = g := by simpa using List.find?_some ha
  have hsid : p.1.id = sid := by simpa using List.find?_some hst
  have hacc : p.1.accepted = none := (hinv.ac.cur p.1 hstm g hcur).2.1
  obtain ⟨hinv1, hak1, _, hrel1, e0, _, e2, _, _, _, _, _, _, est, _, _⟩ :=
    retire_spec (st' := { p.1 with current := none, failures := p.1.failures + 1, status := (if p.1.failures + 1 > spec.retries then .failed else .pending) })
      (a' := { p.2 with status := ns }) hinv hnt hstm ham
      (by rw [hcur, hap.2]) (by rw [hap.1, hsid]) rfl rfl hns rfl rfl
      (by split <;> simp)
      (by simp only [stepAccOk, hacc]; split <;> simp)
      (by simp [stepFenced, hacc])
  have hnt1 : (failedJob j spec p.1 p.2 ns).status.terminal = false := by
    rw [← hnt]; exact congrArg _ est
  obtain ⟨_, has2, hak2, _, f0, _, f2, _⟩ := finalizeJob_spec (failedJob j spec p.1 p.2 ns) hinv1 hnt1
  have has : AccSame j (finalizeJob (failedJob j spec p.1 p.2 ns)).1 :=
    (accSame_replace hrel1 hst rfl hinv.nodup rfl).trans has2
  exact shape_putJob (by rw [hts]) hj hnt (f0.trans e0) hc has.mono has.fence (hak1.trans hak2).dep
    (f2.trans e2)

theorem shape_startAcc {s : State} {e : Envelope} {jid : JobId} {sid : StepId} {fp : Digest}
    {t : Transition} (hS : SafeP s) (hc : e.cmd ≠ .recoverController) (h : StartAcc s e jid sid fp t) :
    JobsShape s e t := by
  obtain ⟨j, w, spec, st, b, a, _, _, hj, hd, hw, hspec, hst, hidle, hpre, _, hins, _, _, _, _, ha1, _, ha3,
    ha4, hts, _⟩ := h
  obtain ⟨_, _, hinv, _, _⟩ := job_of_find hS hj
  have hnt : j.status.terminal = false := by
    unfold dispatchable at hd
    simp only [Bool.or_eq_true, beq_iff_eq] at hd
    rcases hd with hd | hd <;> rw [hd] <;> rfl
  have hsid : st.id = sid := by simpa using List.find?_some hst
  simp only [StepState.idle, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hidle
  obtain ⟨_, _, _, hatt, hrel, e0, _, e2, _⟩ :=
    start_spec (a := a) hinv (List.mem_of_find?_eq_some hst) hidle.1.2 hidle.2 (by rw [ha1, hsid]) ha3 ha4
  have has : AccSame j (startedJob j st a) :=
    accSame_replace (j1 := startedJob j st a) (st' := { st with status := .active, current := some (j.attempts.length + 1) })
      hrel hst rfl hinv.nodup rfl
  refine shape_putJob (by rw [hts]; rfl) hj hnt e0 hc has.mono has.fence ?_ e2
  intro k g a0 hn h0
  unfold Job.findAttempt? at hn h0
  rw [hatt, List.find?_append, hn] at h0
  simp only [Option.none_or, List.find?_cons, List.find?_nil] at h0
  split at h0
  · rename_i hq
    simp only [Option.some.injEq] at h0
    subst h0
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    refine ⟨w, hw, spec, by rw [← hq.1, ha1]; exact hspec, hpre, hins, ha4⟩
  · cases h0

theorem mig_accMono {j : Job} {newW : WorkflowDef} {target : Digest} {oldA newA : List Asset} {oldW : WorkflowDef}
    (hall : ∀ st ∈ j.steps, migStepOk j oldA newA oldW newW st = true) :
    AccMono j { j with release := target, epoch := j.epoch + 1, steps := migratedSteps j newW } := by
  intro k a h0
  show ((newW.steps.map (migStep j)).find? (·.id == k)).bind (·.accepted) = some a
  rw [List.find?_map, find?_congr_mem (q := fun x : StepSpec => x.id == k)
    (fun x _ => by simp [Function.comp, migStep_id])]
  cases hx : j.findStep? k with
  | none => rw [hx] at h0; cases h0
  | some x =>
    rw [hx] at h0
    simp only [Option.bind_some] at h0
    have hxm := List.mem_of_find?_eq_some hx
    have hk : x.id = k := by simpa using List.find?_some hx
    have hok := hall x hxm
    unfold migStepOk at hok
    rw [h0] at hok
    simp only at hok
    split at hok
    · rename_i o n _ hn
      unfold WorkflowDef.find? at hn
      rw [hk] at hn
      rw [hn]
      simp only [Option.map_some, Option.bind_some]
      unfold migStep
      have hnk : n.id = k := by simpa using List.find?_some hn
      rw [hnk, hx]
      simp [h0]
    · cases hok

theorem mig_accRev {j : Job} {newW : WorkflowDef} {target : Digest} :
    AccMono { j with release := target, epoch := j.epoch + 1, steps := migratedSteps j newW } j := by
  intro k a h0
  change ((newW.steps.map (migStep j)).find? (·.id == k)).bind (·.accepted) = some a at h0
  rw [List.find?_map, find?_congr_mem (q := fun x : StepSpec => x.id == k)
    (fun x _ => by simp [Function.comp, migStep_id])] at h0
  cases hf : newW.steps.find? (·.id == k) with
  | none => rw [hf] at h0; cases h0
  | some n =>
    rw [hf] at h0
    simp only [Option.map_some, Option.bind_some] at h0
    have hnk : n.id = k := by simpa using List.find?_some hf
    rcases migStep_cases j n with ⟨st, hst', _, heq⟩ | ⟨hnone, _, _⟩
    · rw [heq] at h0
      rw [hnk] at hst'
      rw [hst']
      exact h0
    · rw [hnone] at h0; cases h0

theorem shape_migAcc {s : State} {e : Envelope} {jid : JobId} {target : Digest} {rev : Nat} {t : Transition}
    (hc : e.cmd = .migrateJob jid target rev) (h : MigAcc s jid target rev t) :
    JobsShape s e t := by
  obtain ⟨j, tr, newW, oldRel, oldW, hj, _, _, _, _, hnw, _, hst, hl, hwf, hall, hjobs, _⟩ := h
  have hnt : j.status.terminal = false := by rw [hst]; rfl
  refine Or.inr (Or.inr (Or.inl ⟨jid, j, { j with release := target, epoch := j.epoch + 1, steps := migratedSteps j newW }, hj, hnt, rfl, hjobs, by rw [hc]; simp,
    mig_accMono hall, ?_, ?_, Or.inr ⟨target, rev, hc⟩⟩))
  · intro k a hn h0
    rw [mig_accRev k a h0] at hn; cases hn
  · intro k g a hn h0
    have : ({ j with release := target, epoch := j.epoch + 1, steps := migratedSteps j newW } : Job).findAttempt? k g
        = j.findAttempt? k g := rfl
    rw [this, hn] at h0; cases h0

theorem dispatch_shape {s : State} {e : Envelope} {t : Transition} (hS : SafeP s)
    (h : dispatch s e = .ok t) : JobsShape s e t := by
  rcases e with ⟨actor, epoch, tick, cmd⟩
  cases cmd <;> simp only [dispatch] at h
  · exact Or.inl (by rw [(doBootstrap_ok h).2.2.2.2.2])
  · obtain ⟨_, rel, j, hj, _, hts⟩ := doCreateJob_ok h
    exact shape_addJob hj (by rw [hts])
  · exact shape_startAcc hS (by simp) (doStartAttempt_ok h)
  · exact shape_obsLike (by simp) (doObserveDispatched_ok h)
  · exact shape_obsLike (by simp) (doObserveStarted_ok h)
  · exact shape_obsLike (by simp) (doHeartbeat_ok h)
  · rcases doSettle_ok h with ⟨hts, _⟩ | hacc
    · exact Or.inl (by rw [hts])
    · exact shape_settleAcc hS (by simp) hacc
  · rcases doSettle_ok h with ⟨hts, _⟩ | hacc
    · exact Or.inl (by rw [hts])
    · exact shape_settleAcc hS (by simp) hacc
  · exact shape_failLike hS (by simp) (doFailAttempt_ok h)
  · exact shape_failLike hS (by simp) (doExpireAttempt_ok h)
  · exact shape_statusLike (by simp) (doPause_ok h).1
  · exact shape_statusLike (by simp) (doAckQuiescence_ok h).1
  · exact shape_statusLike (by simp) (doResume_ok h).1
  · exact shape_cancel (by simp) h
  · obtain ⟨_, _, base, j, c, _, hj, _, _, _, _, hts⟩ := doCreateChange_ok h
    exact shape_addJob hj (by rw [hts])
  · obtain ⟨c, j, c', _, hj, _, _, _, _, hts⟩ := doReviseChange_ok h
    exact shape_addJob hj (by rw [hts]; rfl)
  · obtain ⟨c, j, c', _, hj, _, _, _, _, hts⟩ := doRegisterCandidate_ok h
    exact shape_addJob hj (by rw [hts]; rfl)
  · exact Or.inl (by rw [(doPublishReport_ok h).choose_spec.1])
  · obtain ⟨_, _, c, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hts, _⟩ := doPublishRelease_ok h
    exact Or.inl (by rw [hts]; rfl)
  · exact Or.inl (by rw [(doRecordApproval_ok h).choose_spec.2.2.1])
  · exact Or.inl (by rw [(doRevokeApproval_ok h).choose_spec.2.1])
  · obtain ⟨_, _, _, _, _, _, _, _, _, hts, _⟩ := doActivate_ok h
    exact Or.inl (by rw [hts])
  · exact shape_migAcc rfl (doMigrate_ok h)
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, by rw [(doRecover_ok h).1]⟩))

/-! ### Job lookup after each shape -/

theorem findJob?_of_jobs {s' : State} {l : List Job} (h : s'.jobs = l) (k : JobId) :
    s'.findJob? k = l.find? (·.id == k) := by
  unfold State.findJob?; rw [h]

theorem findJob?_shapeB {s s' : State} {j : Job} (h : s'.jobs = s.jobs ++ [j]) (k : JobId) :
    s'.findJob? k = (s.findJob? k).or (if j.id = k then some j else none) := by
  rw [findJob?_of_jobs h, List.find?_append]
  unfold State.findJob?
  congr 1
  simp only [List.find?_cons, List.find?_nil]
  split <;> simp_all

theorem findJob?_shapeC {s s' : State} {jid : JobId} {j j' : Job} (hf : s.findJob? jid = some j)
    (hid : j'.id = j.id) (h : s'.jobs = (s.putJob j').jobs) (k : JobId) :
    s'.findJob? k = if k = jid then some { j' with revision := j.revision + 1 } else s.findJob? k := by
  have hj : j.id = jid := by simpa using List.find?_some hf
  rw [findJob?_of_jobs h]
  show (s.putJob j').findJob? k = _
  split
  · subst k; exact findJob?_putJob_self hf hid
  · rename_i hk; exact findJob?_putJob_other (by rw [hid, hj]; exact hk)

theorem findJob?_shapeD {s s' : State} (hS : SafeP s) (h : s'.jobs = s.jobs.map (fun j => (recoverAll s j).1))
    (k : JobId) : s'.findJob? k = (s.findJob? k).map (fun j => (recoverAll s j).1) := by
  rw [findJob?_of_jobs h, List.find?_map, find?_congr_mem (q := fun x : Job => x.id == k)
    (fun y hy => by simp [Function.comp, (recoverAll_spec hS hy).2.2.2.2.1])]
  rfl

theorem findStep?_revision (j : Job) (n : Nat) (k : StepId) :
    ({ j with revision := n } : Job).findStep? k = j.findStep? k := rfl

theorem findAttempt?_revision (j : Job) (n : Nat) (k : StepId) (g : Nat) :
    ({ j with revision := n } : Job).findAttempt? k g = j.findAttempt? k g := rfl

/-! ### Transition contracts at the `dispatch` level -/

theorem shape_accepted_stable {s : State} {e : Envelope} {t : Transition} (hS : SafeP s)
    (hsh : JobsShape s e t) : AcceptedStable s t.state := by
  intro k sid a h
  unfold acceptedAt at h ⊢
  cases hx : s.findJob? k with
  | none => rw [hx] at h; cases h
  | some x =>
    rw [hx] at h
    simp only [Option.bind_some] at h
    rcases hsh with hA | ⟨j, hB, _⟩ | ⟨jid, j, j', hf, _, hid, hC, _, hmono, _⟩ | ⟨_, hD⟩
    · rw [findJob?_of_jobs hA, show s.jobs.find? (·.id == k) = s.findJob? k from rfl, hx]; exact h
    · rw [findJob?_shapeB hB, hx]; exact h
    · rw [findJob?_shapeC hf hid hC]
      split
      · rename_i hk; subst hk; rw [hf] at hx; cases hx
        simp only [Option.bind_some, findStep?_revision]
        exact hmono sid a h
      · rw [hx]; exact h
    · rw [findJob?_shapeD hS hD, hx]
      simp only [Option.map_some, Option.bind_some]
      rw [(recoverAll_spec hS (List.mem_of_find?_eq_some hx)).2.1 sid]
      exact h

theorem shape_fenced {s : State} {e : Envelope} {t : Transition} (hS : SafeP s)
    (hep : e.cmd ≠ .recoverController → e.epoch = s.ctrlEpoch)
    (hsh : JobsShape s e t) : FencedAcceptance s e t.state := by
  intro k sid a h0 h1
  unfold acceptedAt at h0 h1
  rcases hsh with hA | ⟨j, hB, hfresh, _, hacc⟩ | ⟨jid, j, j', hf, _, hid, hC, hc, _, hfence, _⟩ | ⟨_, hD⟩
  · rw [findJob?_of_jobs hA] at h1
    change ((s.findJob? k).bind _) = _ at h1
    rw [h0] at h1; cases h1
  · rw [findJob?_shapeB hB] at h1
    cases hx : s.findJob? k with
    | some x => rw [hx] at h0 h1; simp only [Option.some_or] at h1; rw [h0] at h1; cases h1
    | none =>
      rw [hx] at h1
      simp only [Option.none_or] at h1
      split at h1
      · simp only [Option.bind_some] at h1; rw [hacc] at h1; cases h1
      · cases h1
  · rw [findJob?_shapeC hf hid hC] at h1
    split at h1
    · rename_i hk; subst hk
      rw [hf] at h0
      simp only [Option.bind_some, findStep?_revision] at h0 h1
      obtain ⟨st, hst, h2, h3, att, hatt, h4⟩ := hfence sid a h0 h1
      exact ⟨j, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, st, hst, h2, h3,
        att, hatt, h4.1, h4.2.1, h4.2.2.1, h4.2.2.2.1, h4.2.2.2.2.1, h4.2.2.2.2.2.1, h4.2.2.2.2.2.2.1,
        h4.2.2.2.2.2.2.2.1, h4.2.2.2.2.2.2.2.2.1, h4.2.2.2.2.2.2.2.2.2.1, h4.2.2.2.2.2.2.2.2.2.2, hep hc⟩
    · rw [h0] at h1; cases h1
  · rw [findJob?_shapeD hS hD] at h1
    cases hx : s.findJob? k with
    | none => rw [hx] at h1; cases h1
    | some x =>
      rw [hx] at h0 h1
      simp only [Option.map_some, Option.bind_some] at h0 h1
      rw [(recoverAll_spec hS (List.mem_of_find?_eq_some hx)).2.1 sid, h0] at h1
      cases h1

theorem shape_dependency {s : State} {e : Envelope} {t : Transition} (hS : SafeP s)
    (hsh : JobsShape s e t) : DependencySafe s t.state := by
  intro k sid g a h0 h1
  unfold attemptIn at h0 h1
  rcases hsh with hA | ⟨j, hB, hfresh, hatt, _⟩ | ⟨jid, j, j', hf, _, hid, hC, _, _, _, hdep, _⟩ | ⟨_, hD⟩
  · rw [findJob?_of_jobs hA] at h1
    change ((s.findJob? k).bind _) = _ at h1
    rw [h0] at h1; cases h1
  · rw [findJob?_shapeB hB] at h1
    cases hx : s.findJob? k with
    | some x => rw [hx] at h0 h1; simp only [Option.some_or] at h1; rw [h0] at h1; cases h1
    | none =>
      rw [hx] at h1
      simp only [Option.none_or] at h1
      split at h1
      · simp only [Option.bind_some, Job.findAttempt?, hatt, List.find?_nil] at h1; cases h1
      · cases h1
  · rw [findJob?_shapeC hf hid hC] at h1
    split at h1
    · rename_i hk; subst hk
      rw [hf] at h0
      simp only [Option.bind_some, findAttempt?_revision] at h0 h1
      obtain ⟨w, hw, spec, hspec, h2, h3, h4⟩ := hdep sid g a h0 h1
      have hjm := List.mem_of_find?_eq_some hf
      obtain ⟨m1, m2, m3, m4, m5⟩ := dep_explicit (hS.jobs j hjm).1 hspec h2 h3
      exact ⟨j, hjm, by simpa using List.find?_some hf, w, hw, spec, m1, m2, h4, m3, m4, m5⟩
    · rw [h0] at h1; cases h1
  · rw [findJob?_shapeD hS hD] at h1
    cases hx : s.findJob? k with
    | none => rw [hx] at h1; cases h1
    | some x =>
      rw [hx] at h0 h1
      simp only [Option.map_some, Option.bind_some] at h0 h1
      have := (recoverAll_spec hS (List.mem_of_find?_eq_some hx)).2.2.1 sid g
      rw [h0, h1] at this; cases this

theorem shape_cancellation {s : State} {e : Envelope} {t : Transition} (hS : SafeP s)
    (hsh : JobsShape s e t) : CancellationFinal s t.state := by
  intro x hx ht
  rcases hsh with hA | ⟨j, hB, _⟩ | ⟨jid, j, j', hf, hnt, hid, hC, _⟩ | ⟨_, hD⟩
  · exact ⟨x, by rw [hA]; exact hx, rfl, rfl, rfl, fun _ => rfl⟩
  · exact ⟨x, by rw [hB]; exact List.mem_append_left _ hx, rfl, rfl, rfl, fun _ => rfl⟩
  · refine ⟨x, ?_, rfl, rfl, rfl, fun _ => rfl⟩
    rw [hC]
    cases hq : (x.id == j'.id)
    · exact List.mem_map.2 ⟨x, hx, by simp [hq]⟩
    · have hjm := List.mem_of_find?_eq_some hf
      have : x = j := nodup_map_inj hS.jobIds hx hjm (by simp only [beq_iff_eq] at hq; rw [hq, hid])
      subst this
      rw [hnt] at ht; cases ht
  · refine ⟨x, ?_, rfl, rfl, rfl, fun _ => rfl⟩
    rw [hD, List.mem_map]
    exact ⟨x, hx, by rw [(recoverAll_spec hS hx).2.2.2.2.2.2.2.2.2.1 ht]⟩

/-- K08 with the intended quantifier scope (see PROOF-NOTES.md). -/
theorem shape_pinning {s : State} {e : Envelope} {t : Transition} (hS : SafeP s)
    (hsh : JobsShape s e t) (hm : ∀ jid tgt r, e.cmd ≠ .migrateJob jid tgt r) :
    ∀ j ∈ s.jobs, ∃ j' ∈ t.state.jobs, j'.id = j.id ∧ j'.release = j.release := by
  intro x hx
  rcases hsh with hA | ⟨j, hB, _⟩ | ⟨jid, j, j', hf, hnt, hid, hC, _, _, _, _, hrel⟩ | ⟨_, hD⟩
  · exact ⟨x, by rw [hA]; exact hx, rfl, rfl⟩
  · exact ⟨x, by rw [hB]; exact List.mem_append_left _ hx, rfl, rfl⟩
  · have hrel' : j'.release = j.release := by
      rcases hrel with h | ⟨tgt, r, h⟩
      · exact h
      · exact absurd h (hm jid tgt r)
    rw [hC]
    cases hq : (x.id == j'.id)
    · exact ⟨x, List.mem_map.2 ⟨x, hx, by simp [hq]⟩, rfl, rfl⟩
    · have hjm := List.mem_of_find?_eq_some hf
      have : x = j := nodup_map_inj hS.jobIds hx hjm (by simp only [beq_iff_eq] at hq; rw [hq, hid])
      subst this
      exact ⟨{ j' with revision := x.revision + 1 }, List.mem_map.2 ⟨x, hx, by simp [hq]⟩, hid, hrel'⟩
  · refine ⟨(recoverAll s x).1, ?_, (recoverAll_spec hS hx).2.2.2.2.1, (recoverAll_spec hS hx).2.2.2.2.2.2.1⟩
    rw [hD, List.mem_map]
    exact ⟨x, hx, rfl⟩

/-! ### Effect causality (K12) at the `dispatch` level -/

theorem causality_of_terminate {s : State} {t : Transition}
    (h : ∀ eff ∈ t.effects, eff.kind = .terminate) : EffectCausality s t := by
  intro eff heff
  have := h eff heff
  refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_⟩ <;> rw [this] at h' <;> cases h'

theorem causality_nil {s : State} {t : Transition} (h : t.effects = []) : EffectCausality s t :=
  causality_of_terminate (by rw [h]; simp)

theorem dispatch_causality {s : State} {e : Envelope} {t : Transition} (hS : SafeP s)
    (h : dispatch s e = .ok t) : EffectCausality s t := by
  rcases e with ⟨actor, epoch, tick, cmd⟩
  cases cmd <;> simp only [dispatch] at h
  · exact causality_nil (doBootstrap_ok h).2.2.2.2.1
  · exact causality_nil (doCreateJob_ok h).2.choose_spec.choose_spec.2.1
  · rename_i jid sid fp
    obtain ⟨j, w, spec, st, b, a, _, _, hj, _, hw, hspec, hst, hidle, _, hsubj, hins, _, _, _, _, ha1, _, ha3,
      ha4, hts, heff⟩ := doStartAttempt_ok h
    obtain ⟨_, _, hinv, _, _⟩ := job_of_find hS hj
    intro eff hm
    rw [heff, List.mem_singleton] at hm
    subst hm
    refine ⟨fun _ => ⟨?_, a, ?_, ha4, rfl, rfl⟩, (fun h' => by cases h'), (fun h' => by cases h')⟩
    · show (s.findJob? _).bind _ = none
      rw [hj]
      simp only [Option.bind_some, Job.findAttempt?, List.find?_eq_none, Bool.and_eq_true, beq_iff_eq,
        not_and]
      intro x hx _ hg
      have := (hinv.ac.grange x hx).2
      omega
    · unfold attemptIn
      rw [hts]
      have : ((s.putJob (startedJob j st a)).putBudget { b with used := b.used + 1 }).findJob? jid =
          (s.putJob (startedJob j st a)).findJob? jid := rfl
      rw [this, findJob?_putJob_self (j' := startedJob j st a) hj rfl]
      simp only [Option.bind_some, findAttempt?_revision]
      show ((j.attempts ++ [a]).find? _) = some a
      rw [List.find?_append]
      have hnone : j.attempts.find? (fun x => x.step == sid && x.gen == j.attempts.length + 1) = none := by
        rw [List.find?_eq_none]
        intro x hx hp
        simp only [Bool.and_eq_true, beq_iff_eq] at hp
        have := (hinv.ac.grange x hx).2
        omega
      rw [hnone]
      simp [ha1, ha3]
  · exact causality_nil (doObserveDispatched_ok h).choose_spec.choose_spec.choose_spec.2.2.2.2.2.2.2.2
  · exact causality_nil (doObserveStarted_ok h).choose_spec.choose_spec.choose_spec.2.2.2.2.2.2.2.2
  · exact causality_nil (doHeartbeat_ok h).choose_spec.choose_spec.choose_spec.2.2.2.2.2.2.2.2
  · rcases doSettle_ok h with ⟨_, he, _⟩ | ⟨j, st, a, acc, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he⟩
    · exact causality_nil he
    · exact causality_of_terminate (by rw [he]; exact finalizeJob_snd_terminate _)
  · rcases doSettle_ok h with ⟨_, he, _⟩ | ⟨j, st, a, acc, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he⟩
    · exact causality_nil he
    · exact causality_of_terminate (by rw [he]; exact finalizeJob_snd_terminate _)
  · obtain ⟨j, spec, p, ns, _, _, _, _, _, he⟩ := doFailAttempt_ok h
    refine causality_of_terminate ?_
    rw [he]; intro eff hm
    rw [List.mem_cons] at hm
    rcases hm with rfl | hm
    · rfl
    · exact finalizeJob_snd_terminate _ eff hm
  · obtain ⟨j, spec, p, ns, _, _, _, _, _, he⟩ := doExpireAttempt_ok h
    refine causality_of_terminate ?_
    rw [he]; intro eff hm
    rw [List.mem_cons] at hm
    rcases hm with rfl | hm
    · rfl
    · exact finalizeJob_snd_terminate _ eff hm
  · exact causality_nil (doPause_ok h).2
  · exact causality_nil (doAckQuiescence_ok h).2
  · exact causality_nil (doResume_ok h).2
  · obtain ⟨j, _, _, _, he⟩ := doCancel_ok h
    refine causality_of_terminate ?_
    rw [he]; intro eff hm
    simp only [Job.revokeLive, List.mem_map] at hm
    obtain ⟨a, _, rfl⟩ := hm
    rfl
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, he, _⟩ := doCreateChange_ok h
    exact causality_nil he
  · obtain ⟨_, _, _, _, _, _, _, _, he, _⟩ := doReviseChange_ok h
    exact causality_nil he
  · obtain ⟨_, _, _, _, _, _, _, _, he, _⟩ := doRegisterCandidate_ok h
    exact causality_nil he
  · obtain ⟨x, hts, hx1, hx2, he⟩ := doPublishReport_ok h
    intro eff hm
    rw [he, List.mem_singleton] at hm
    subst hm
    refine ⟨(fun h' => by cases h'), (fun h' => by cases h'), fun _ => ⟨x, ?_, hx1, hx2⟩⟩
    rw [hts]; exact List.mem_append_right _ (List.mem_singleton_self _)
  · obtain ⟨_, _, _, _, _, rel, _, _, _, _, _, _, _, _, h1, _, _, _, _, _, hts, he⟩ := doPublishRelease_ok h
    intro eff hm
    rw [he, List.mem_singleton] at hm
    subst hm
    refine ⟨(fun h' => by cases h'), (fun _ => ⟨rel, ?_, h1⟩), (fun h' => by cases h')⟩
    rw [hts]; exact List.mem_append_right _ (List.mem_singleton_self _)
  · exact causality_nil (doRecordApproval_ok h).choose_spec.2.2.2
  · exact causality_nil (doRevokeApproval_ok h).choose_spec.2.2
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, he⟩ := doActivate_ok h
    exact causality_nil he
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he⟩ := doMigrate_ok h
    exact causality_nil he
  · refine causality_of_terminate ?_
    rw [(doRecover_ok h).2]
    intro eff hm
    rw [List.mem_flatten] at hm
    obtain ⟨l, hl, hm⟩ := hm
    rw [List.mem_map] at hl
    obtain ⟨j, hj, rfl⟩ := hl
    exact (recoverAll_spec hS hj).2.2.2.2.2.2.2.2.2.2 eff hm

end Factory.Contracts
