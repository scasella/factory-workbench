import Factory.ProofState
/-
  Factory.ProofHandlers — per-command characterization of `dispatch` and
  `Safe` preservation for every command handler.
-/
namespace Factory.Contracts
open Factory Factory.Check

macro "unfold_ok" h:ident : tactic =>
  `(tactic| simp only [bind_eq_ok, check_eq_ok, need_eq_ok, ok_eq_ok, pure_eq_ok] at $h:ident)

theorem limit_bound {s : State} (hS : SafeP s) (c : ResourceClass) : s.liveOfClass c ≤ c.limit s.config := by
  cases c
  · exact hS.llm
  · exact hS.cont

theorem workflowOf_same {s : State} {j j' : Job} (h1 : j'.release = j.release) (h2 : j'.kind = j.kind) :
    s.workflowOf j' = s.workflowOf j := by
  unfold State.workflowOf; rw [h1, h2]

theorem pinned_same {s : State} {j j' : Job} (h1 : j'.release = j.release) (h2 : j'.kind = j.kind)
    (h3 : j'.budget = j.budget) (h4 : j'.steps.map (·.id) = j.steps.map (·.id)) :
    jobPinned s j' = jobPinned s j := by
  unfold jobPinned; rw [workflowOf_same h1 h2, h3, h4]

theorem par_le {s : State} {j j' : Job} (hp : Par s j) (h1 : j'.release = j.release) (h2 : j'.kind = j.kind)
    (h3 : j'.liveAttempts.length ≤ j.liveAttempts.length) : Par s j' := by
  intro w hw
  rw [workflowOf_same h1 h2] at hw
  exact Nat.le_trans h3 (hp w hw)

theorem job_of_find {s : State} (hS : SafeP s) {jid : JobId} {j : Job} (hf : s.findJob? jid = some j) :
    j ∈ s.jobs ∧ j.id = jid ∧ JInv j ∧ jobPinned s j = true ∧ Par s j := by
  have hm := List.mem_of_find?_eq_some hf
  have hid : j.id = jid := by simpa using List.find?_some hf
  exact ⟨hm, hid, hS.jobs j hm⟩

/-- `putJob` of a job whose pinning-relevant fields are unchanged and whose
    live authority did not grow. -/
theorem safe_putJob_le {s : State} {jid : JobId} {j j' : Job}
    (hS : SafeP s) (hf : s.findJob? jid = some j) (hnt : j.status.terminal = false)
    (hinv : JInv j') (hle : LiveLe j j')
    (h0 : j'.id = j.id) (h1 : j'.release = j.release) (h2 : j'.kind = j.kind)
    (h3 : j'.budget = j.budget) (h4 : j'.steps.map (·.id) = j.steps.map (·.id)) :
    SafeP (s.putJob j') := by
  obtain ⟨_, _, _, hpin, hpar⟩ := job_of_find hS hf
  refine safe_putJob hS hf hnt h0 rfl rfl rfl rfl rfl rfl rfl rfl rfl hS.bud hinv
    (by rw [pinned_same h1 h2 h3 h4]; exact hpin) (par_le hpar h1 h2 hle.2) ?_
  intro c
  have := limit_bound hS c
  have := hle.1 c
  omega

theorem currentAttempt_ok {s : State} {j : Job} {sid : StepId} {gen : Nat} {p : StepState × Attempt}
    (h : currentAttempt s j sid gen = .ok p) :
    j.findStep? sid = some p.1 ∧ j.findAttempt? sid gen = some p.2 ∧ p.1.current = some gen ∧
    p.2.status.live = true ∧ p.2.jobEpoch = j.epoch ∧ p.2.ctrlEpoch = s.ctrlEpoch := by
  unfold currentAttempt at h
  unfold_ok h
  obtain ⟨st, hst, a, ha, _, h1, _, h2, _, h3, rfl⟩ := h
  simp only [beq_iff_eq, Bool.and_eq_true] at h1 h3
  exact ⟨hst, ha, h1, h2, h3.1, h3.2⟩

/-! ### Bootstrap -/

theorem doBootstrap_ok {s : State} {e : Envelope} {g : Release} {c : Digest} {cfg : Config}
    {t : Transition} (h : doBootstrap s e g c cfg = .ok t) :
    s.releases = [] ∧ exportsOk g.workflows = true ∧ 1 ≤ cfg.llmSlots ∧ 1 ≤ cfg.containerSlots ∧
    t.effects = [] ∧
    t.state =
      { s with contract := c, config := cfg,
               releases := [{ g with contract := c, evidenceJob := none, producer := none, parent := none }],
               active := some g.digest,
               activations := [{ release := g.digest, base := none, approval := none, atTick := e.tick }] } := by
  unfold doBootstrap at h
  unfold_ok h
  obtain ⟨_, h1, _, _, _, h3, _, h4, rfl⟩ := h
  simp only [List.isEmpty_iff, Bool.and_eq_true, decide_eq_true_eq] at h1 h4
  exact ⟨h1, h3, h4.1.1, h4.1.2, rfl, rfl⟩

theorem jobs_nil_of_releases_nil {s : State} (hS : SafeP s) (h : s.releases = []) : s.jobs = [] := by
  cases hj : s.jobs with
  | nil => rfl
  | cons x xs =>
    have := (hS.jobs x (by rw [hj]; simp)).2.1
    unfold jobPinned State.workflowOf State.findRelease? at this
    rw [h] at this
    simp at this

theorem safe_doBootstrap {s : State} {e : Envelope} {g : Release} {c : Digest} {cfg : Config}
    {t : Transition} (hS : SafeP s) (h : doBootstrap s e g c cfg = .ok t) : SafeP t.state := by
  obtain ⟨hr, hex, hl, hc, _, hts⟩ := doBootstrap_ok h
  rw [hts]
  have hj := jobs_nil_of_releases_nil hS hr
  refine ⟨by simp [hj], by simp, hS.budIds, hS.appIds, hS.chIds, ?_, ?_, by simp [hj], ?_, ?_, hS.bud,
    ?_, ?_⟩
  · simp [releasesOk, hex, State.findRelease?, State.wasActivated]
  · have := hS.chOk
    unfold changesOk at this ⊢
    rw [List.all_eq_true] at this ⊢
    intro x hx
    have := this x hx
    simp only [Bool.and_eq_true] at this
    unfold State.findRelease? at this
    rw [hr] at this
    simp at this
  · simp [releasesEvidenced]
  · simp [activationsApproved]
  · simp [State.liveOfClass, hj]
  · simp [State.liveOfClass, hj]

/-! ### Job creation -/

theorem topoOk_nodup : ∀ (seen : List StepId) (steps : List StepSpec), topoOk seen steps = true →
    (steps.map (·.id)).Nodup ∧ ∀ x ∈ steps, x.id ∉ seen
  | _, [], _ => by simp
  | seen, x :: rest, h => by
    unfold topoOk at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
    obtain ⟨⟨_, hx⟩, hr⟩ := h
    obtain ⟨ih1, ih2⟩ := topoOk_nodup (x.id :: seen) rest hr
    refine ⟨?_, ?_⟩
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih1⟩
      intro hm
      rw [List.mem_map] at hm
      obtain ⟨y, hy, hyx⟩ := hm
      exact ih2 y hy (by rw [hyx]; simp)
    · intro y hy
      rw [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hx
      · intro hm; exact ih2 y hy (List.mem_cons_of_mem _ hm)

theorem wellFormed_nodup {w : WorkflowDef} (h : wellFormedWorkflow w = true) :
    (w.steps.map (·.id)).Nodup := by
  unfold wellFormedWorkflow at h
  simp only [Bool.and_eq_true] at h
  exact (topoOk_nodup [] w.steps h.1.1.1.2).1

theorem mkJob_ok {s : State} {id : JobId} {kind : JobKind} {rel input subject : Digest} {budget : BudgetId}
    {change : Option ChangeId} {j : Job} (h : mkJob s id kind rel input subject budget change = .ok j) :
    s.findJob? id = none ∧ ∃ r w, s.findRelease? rel = some r ∧ s.wasActivated rel = true ∧
      workflowFor r.workflows kind = some w ∧ wellFormedWorkflow w = true ∧
      j = newJob id kind rel w input subject budget change := by
  unfold mkJob at h
  unfold_ok h
  obtain ⟨_, h1, _, _, _, _, _, _, r, hr, _, ha, w, hw, _, hwf, _, _, hj⟩ := h
  simp only [Option.isNone_iff_eq_none] at h1
  exact ⟨h1, r, w, hr, ha, hw, hwf, hj.symm⟩

theorem newJob_spec {s : State} {id : JobId} {kind : JobKind} {rel input subject : Digest}
    {budget : BudgetId} {change : Option ChangeId} {r : Release} {w : WorkflowDef}
    (hr : s.findRelease? rel = some r) (hw : workflowFor r.workflows kind = some w)
    (hwf : wellFormedWorkflow w = true) (hb : (s.findBudget? budget).isSome = true) :
    let j := newJob id kind rel w input subject budget change
    JInv j ∧ jobPinned s j = true ∧ Par s j ∧ (∀ c, j.liveOfClass c = 0) ∧ j.id = id ∧
    j.attempts = [] ∧ (∀ k, (j.findStep? k).bind (·.accepted) = none) := by
  intro j
  have hids : j.steps.map (·.id) = w.steps.map (·.id) := by
    simp [j, newJob, List.map_map, Function.comp, freshStep]
  refine ⟨⟨by rw [hids]; exact wellFormed_nodup hwf, ⟨by simp [j, newJob], by simp [j, newJob], ?_, ?_,
    by simp [j, newJob]⟩, ?_, ?_, by simp [j, newJob]⟩, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · intro st hst g hg
    simp only [j, newJob, List.mem_map] at hst
    obtain ⟨_, _, rfl⟩ := hst
    cases hg
  · intro st hst _
    simp only [j, newJob, List.mem_map] at hst
    obtain ⟨_, _, rfl⟩ := hst
    simp [freshStep]
  · intro st hst
    simp only [j, newJob, List.mem_map] at hst
    obtain ⟨_, _, rfl⟩ := hst
    simp [freshStep, stepAccOk]
  · intro st hst
    simp only [j, newJob, List.mem_map] at hst
    obtain ⟨_, _, rfl⟩ := hst
    simp [freshStep, stepFenced]
  · have hwo : s.workflowOf j = some w := by
      simp only [State.workflowOf, j, newJob, hr, Option.bind_some, hw]
    simp only [jobPinned, hwo, hwf, hids, beq_self_eq_true, Bool.true_and]
    exact hb
  · intro w' _; simp [j, newJob, Job.liveAttempts]
  · intro c; simp [j, newJob, Job.liveOfClass]
  · intro k
    cases hf : j.findStep? k with
    | none => rfl
    | some st =>
      have := List.mem_of_find?_eq_some hf
      simp only [j, newJob, List.mem_map] at this
      obtain ⟨_, _, rfl⟩ := this
      rfl

theorem doCreateJob_ok {s : State} {id : JobId} {k : JobKind} {i sb : Digest} {r : Option Digest}
    {b : BudgetId} {l : Nat} {t : Transition} (h : doCreateJob s id k i sb r b l = .ok t) :
    s.findBudget? b = none ∧ ∃ rel j, mkJob s id k rel i sb b none = .ok j ∧ t.effects = [] ∧
      t.state = { s with jobs := s.jobs ++ [j], budgets := s.budgets ++ [{ id := b, limit := l, used := 0 }] } := by
  unfold doCreateJob at h
  unfold_ok h
  obtain ⟨_, _, _, hb, _, _, rel, _, j, hj, hts⟩ := h
  simp only [Option.isNone_iff_eq_none] at hb
  exact ⟨hb, rel, j, hj, by rw [hts], by rw [hts]⟩

theorem budIds_append {s : State} {b : Budget} (hS : SafeP s) (hb : s.findBudget? b.id = none) :
    ((s.budgets ++ [b]).map (·.id)).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨hS.budIds, by simp, ?_⟩
  intro x hx y hy heq
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
  rw [List.mem_map] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  rw [State.findBudget?, List.find?_eq_none] at hb
  exact hb z hz (by simp [heq, hy])

theorem findBudget?_append_new {bs : List Budget} {b : Budget} (hb : bs.find? (·.id == b.id) = none) :
    ((bs ++ [b]).find? (·.id == b.id)).isSome = true := by
  rw [List.find?_append, hb]; simp

theorem safe_doCreateJob {s : State} {id : JobId} {k : JobKind} {i sb : Digest} {r : Option Digest}
    {b : BudgetId} {l : Nat} {t : Transition} (hS : SafeP s) (h : doCreateJob s id k i sb r b l = .ok t) :
    SafeP t.state := by
  obtain ⟨hb, rel, j, hj, _, hts⟩ := doCreateJob_ok h
  obtain ⟨hfresh, r0, w, hr, _, hw, hwf, rfl⟩ := mkJob_ok hj
  rw [hts]
  generalize hs' : ({ s with jobs := s.jobs ++ [newJob id k rel w i sb b none], budgets := s.budgets ++ [{ id := b, limit := l, used := 0 }] } : State) = s'
  have hbe : BudExt s s' := BudExt.append [{ id := b, limit := l, used := 0 }] (by rw [← hs'])
  have hb' : (s'.findBudget? b).isSome = true := by
    rw [← hs']; exact findBudget?_append_new (b := { id := b, limit := l, used := 0 }) hb
  obtain ⟨hinv, hpin, hpar, hlive, hid, _⟩ := newJob_spec (s := s') (id := id) (input := i) (subject := sb)
      (change := none) (by rw [← hs']; exact hr) hw hwf hb'
  subst hs'
  refine safe_addJob hS rfl (by rw [hid]; exact hfresh) rfl rfl rfl rfl rfl rfl hS.chIds
    (changesOk_of hS.chOk rfl (RelExt.of_eq rfl) hbe) hbe (budIds_append (b := { id := b, limit := l, used := 0 }) hS hb) ?_ hinv hpin hpar hlive
  intro x hx
  rw [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact hS.bud x hx
  · exact Nat.zero_le _

/-! ### Change requests -/

theorem changes_putChange {s : State} (hS : SafeP s) {cid : ChangeId} {c c' : Change}
    (hc : s.findChange? cid = some c) (hid : c'.id = c.id) (hb : c'.budget = c.budget)
    (hbase : c'.base = c.base) {s' : State} (hch : s'.changes = (s.putChange c').changes)
    (hre : RelExt s s') (hbe : BudExt s s') :
    (s'.changes.map (·.id)).Nodup ∧ changesOk s' = true := by
  have hcm : c ∈ s.changes := List.mem_of_find?_eq_some hc
  have hok := hS.chOk
  unfold changesOk at hok
  rw [List.all_eq_true] at hok
  constructor
  · rw [hch]
    show ((s.changes.map (fun x => if x.id == c'.id then c' else x)).map (·.id)).Nodup
    rw [map_replace_key (fun y _ hy => (by simpa using hy : y.id = c'.id).symm)]
    exact hS.chIds
  · unfold changesOk
    rw [hch, List.all_eq_true]
    intro x hx
    rcases mem_replace hx with rfl | ⟨hx, _⟩
    · have := hok c hcm
      simp only [Bool.and_eq_true] at this ⊢
      rw [hb, hbase]
      refine ⟨hbe _ this.1, ?_⟩
      obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.mp this.2
      rw [hre _ _ hr']; rfl
    · have := hok x hx
      simp only [Bool.and_eq_true] at this ⊢
      refine ⟨hbe _ this.1, ?_⟩
      obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.mp this.2
      rw [hre _ _ hr']; rfl

theorem doCreateChange_ok {s : State} {id : ChangeId} {rq : Digest} {aj : JobId} {b : BudgetId}
    {l rl : Nat} {t : Transition} (h : doCreateChange s id rq aj b l rl = .ok t) :
    s.findChange? id = none ∧ s.findBudget? b = none ∧ ∃ base j c, s.active = some base ∧
      mkJob s aj .changeAuthor base rq base b (some id) = .ok j ∧ c.id = id ∧ c.budget = b ∧
      c.base = base ∧ t.effects = [] ∧
      t.state = { s with jobs := s.jobs ++ [j], budgets := s.budgets ++ [{ id := b, limit := l, used := 0 }], changes := s.changes ++ [c] } := by
  unfold doCreateChange at h
  unfold_ok h
  obtain ⟨_, h1, _, _, _, h2, _, _, base, hbase, j, hj, hts⟩ := h
  simp only [Option.isNone_iff_eq_none] at h1 h2
  exact ⟨h1, h2, base, j, _, hbase, hj, rfl, rfl, rfl, by rw [hts], by rw [hts]⟩

theorem safe_doCreateChange {s : State} {id : ChangeId} {rq : Digest} {aj : JobId} {b : BudgetId}
    {l rl : Nat} {t : Transition} (hS : SafeP s) (h : doCreateChange s id rq aj b l rl = .ok t) :
    SafeP t.state := by
  obtain ⟨hc, hb, base, j, c, _, hj, hcid, hcb, hcbase, _, hts⟩ := doCreateChange_ok h
  obtain ⟨hfresh, r0, w, hr, _, hw, hwf, rfl⟩ := mkJob_ok hj
  rw [hts]
  generalize hs' : ({ s with jobs := s.jobs ++ [newJob aj .changeAuthor base w rq base b (some id)], budgets := s.budgets ++ [{ id := b, limit := l, used := 0 }], changes := s.changes ++ [c] } : State) = s'
  have hbe : BudExt s s' := BudExt.append [{ id := b, limit := l, used := 0 }] (by rw [← hs'])
  have hb' : (s'.findBudget? b).isSome = true := by
    rw [← hs']; exact findBudget?_append_new (b := { id := b, limit := l, used := 0 }) hb
  have hre : RelExt s s' := RelExt.of_eq (by rw [← hs'])
  obtain ⟨hinv, hpin, hpar, hlive, hid, _⟩ := newJob_spec (s := s') (id := aj) (input := rq)
      (subject := base) (change := some id) (hre _ _ hr) hw hwf hb'
  have hchIds : (s'.changes.map (·.id)).Nodup := by
    rw [← hs']
    show ((s.changes ++ [c]).map (·.id)).Nodup
    rw [List.map_append, List.nodup_append]
    refine ⟨hS.chIds, by simp, ?_⟩
    intro x hx y hy heq
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
    rw [List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [State.findChange?, List.find?_eq_none] at hc
    exact hc z hz (by simp [heq, hy, hcid])
  have hchOk : changesOk s' = true := by
    have hsc : s'.changes = s.changes ++ [c] := by rw [← hs']
    have h0 := hS.chOk
    unfold changesOk at h0 ⊢
    rw [hsc]
    simp only [List.all_append, Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true]
    refine ⟨?_, ?_⟩
    · rw [List.all_eq_true] at h0 ⊢
      intro x hx
      have := h0 x hx
      simp only [Bool.and_eq_true] at this ⊢
      refine ⟨hbe _ this.1, ?_⟩
      obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.mp this.2
      rw [hre _ _ hr']; rfl
    · refine ⟨?_, ?_⟩
      · rw [hcb]; exact hb'
      · rw [hcbase, hre _ _ hr]; rfl
  subst hs'
  refine safe_addJob hS rfl (by rw [hid]; exact hfresh) rfl rfl rfl rfl rfl rfl hchIds hchOk hbe
    (budIds_append (b := { id := b, limit := l, used := 0 }) hS hb) ?_ hinv hpin hpar hlive
  intro x hx
  rw [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact hS.bud x hx
  · exact Nat.zero_le _

theorem doReviseChange_ok {s : State} {id : ChangeId} {aj : JobId} {d : Digest} {t : Transition}
    (h : doReviseChange s id aj d = .ok t) :
    ∃ c j c', s.findChange? id = some c ∧ mkJob s aj .changeAuthor c.base d c.base c.budget (some id) = .ok j ∧
      c'.id = c.id ∧ c'.budget = c.budget ∧ c'.base = c.base ∧ t.effects = [] ∧
      t.state = ({ s with jobs := s.jobs ++ [j] } : State).putChange c' := by
  unfold doReviseChange at h
  unfold_ok h
  obtain ⟨c, hc, _, _, _, _, j, hj, hts⟩ := h
  exact ⟨c, j, { c with revisions := c.revisions + 1, jobs := c.jobs ++ [aj] }, hc, hj, rfl, rfl, rfl,
    by rw [hts], by rw [hts]⟩

theorem doRegisterCandidate_ok {s : State} {cid : ChangeId} {aj ej : JobId} {src : Digest} {t : Transition}
    (h : doRegisterCandidate s cid aj ej src = .ok t) :
    ∃ c j c', s.findChange? cid = some c ∧
      mkJob s ej .changeEvaluate c.base src src c.budget (some cid) = .ok j ∧
      c'.id = c.id ∧ c'.budget = c.budget ∧ c'.base = c.base ∧ t.effects = [] ∧
      t.state = ({ s with jobs := s.jobs ++ [j] } : State).putChange c' := by
  unfold doRegisterCandidate at h
  unfold_ok h
  obtain ⟨c, hc, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, j, hj, hts⟩ := h
  exact ⟨c, j, { c with jobs := c.jobs ++ [ej], candidates := c.candidates ++ [src] }, hc, hj, rfl, rfl,
    rfl, by rw [hts], by rw [hts]⟩

/-- Common tail of revise/register: append a job built by `mkJob` against an
    existing change's budget, then update that change in place. -/
theorem safe_addJob_putChange {s : State} {cid : ChangeId} {c c' : Change} {aj : JobId} {kind : JobKind}
    {input subject : Digest} {j : Job} (hS : SafeP s) (hc : s.findChange? cid = some c)
    (hj : mkJob s aj kind c.base input subject c.budget (some cid) = .ok j)
    (hid : c'.id = c.id) (hb : c'.budget = c.budget) (hbase : c'.base = c.base) :
    SafeP (({ s with jobs := s.jobs ++ [j] } : State).putChange c') := by
  obtain ⟨hfresh, r0, w, hr, _, hw, hwf, rfl⟩ := mkJob_ok hj
  generalize hs' : (({ s with jobs := s.jobs ++ [newJob aj kind c.base w input subject c.budget (some cid)] } : State).putChange c') = s'
  have hre : RelExt s s' := RelExt.of_eq (by rw [← hs']; rfl)
  have hbe : BudExt s s' := BudExt.of_ids (by rw [← hs']; rfl)
  have hcm : c ∈ s.changes := List.mem_of_find?_eq_some hc
  have hbc : (s.findBudget? c.budget).isSome = true := by
    have := hS.chOk
    unfold changesOk at this
    rw [List.all_eq_true] at this
    have := this c hcm
    simp only [Bool.and_eq_true] at this
    exact this.1
  obtain ⟨hinv, hpin, hpar, hlive, hid', _⟩ := newJob_spec (s := s') (id := aj) (input := input)
      (subject := subject) (change := some cid) (hre _ _ hr) hw hwf (hbe _ hbc)
  obtain ⟨hchIds, hchOk⟩ := changes_putChange hS hc hid hb hbase (s' := s')
    (by rw [← hs']; rfl) hre hbe
  subst hs'
  exact safe_addJob hS rfl (by rw [hid']; exact hfresh) rfl rfl rfl rfl rfl rfl hchIds hchOk hbe
    hS.budIds hS.bud hinv hpin hpar hlive

theorem safe_doReviseChange {s : State} {id : ChangeId} {aj : JobId} {d : Digest} {t : Transition}
    (hS : SafeP s) (h : doReviseChange s id aj d = .ok t) : SafeP t.state := by
  obtain ⟨c, j, c', hc, hj, h1, h2, h3, _, hts⟩ := doReviseChange_ok h
  rw [hts]; exact safe_addJob_putChange hS hc hj h1 h2 h3

theorem safe_doRegisterCandidate {s : State} {cid : ChangeId} {aj ej : JobId} {src : Digest}
    {t : Transition} (hS : SafeP s) (h : doRegisterCandidate s cid aj ej src = .ok t) : SafeP t.state := by
  obtain ⟨c, j, c', hc, hj, h1, h2, h3, _, hts⟩ := doRegisterCandidate_ok h
  rw [hts]; exact safe_addJob_putChange hS hc hj h1 h2 h3

/-! ### Observations and heartbeats (modify the current attempt in place) -/

/-- Shared shape of observeLaunchDispatched / observeProcessStarted / heartbeat. -/
def ObsLike (s : State) (jid : JobId) (sid : StepId) (g : Nat) (t : Transition) : Prop :=
  ∃ j p a', s.findJob? jid = some j ∧ j.status.terminal = false ∧ currentAttempt s j sid g = .ok p ∧
    a'.step = p.2.step ∧ a'.gen = p.2.gen ∧ a'.role = p.2.role ∧ a'.status.live = true ∧
    t.state = s.putJob (j.setAttempt a') ∧ t.effects = []

theorem doObserveDispatched_ok {s : State} {jid : JobId} {sid : StepId} {g : Nat} {t : Transition}
    (h : doObserveDispatched s jid sid g = .ok t) : ObsLike s jid sid g t := by
  unfold doObserveDispatched at h
  unfold_ok h
  obtain ⟨j, hj, _, hnt, p, hp, _, _, hts⟩ := h
  exact ⟨j, p, { p.2 with status := .starting }, hj, by simpa using hnt, hp, rfl, rfl, rfl, rfl,
    by rw [hts], by rw [hts]⟩

theorem doObserveStarted_ok {s : State} {e : Envelope} {jid : JobId} {sid : StepId} {g : Nat} {c : String}
    {t : Transition} (h : doObserveStarted s e jid sid g c = .ok t) : ObsLike s jid sid g t := by
  unfold doObserveStarted at h
  unfold_ok h
  obtain ⟨j, hj, _, hnt, p, hp, _, _, _, _, hts⟩ := h
  exact ⟨j, p, { p.2 with status := .running, container := c }, hj, by simpa using hnt, hp, rfl, rfl,
    rfl, rfl, by rw [hts], by rw [hts]⟩

theorem doHeartbeat_ok {s : State} {e : Envelope} {jid : JobId} {sid : StepId} {g : Nat}
    {t : Transition} (h : doHeartbeat s e jid sid g = .ok t) : ObsLike s jid sid g t := by
  unfold doHeartbeat at h
  unfold_ok h
  obtain ⟨j, hj, _, hnt, p, hp, _, _, hts⟩ := h
  exact ⟨j, p, { p.2 with deadline := e.tick + s.config.leaseTicks }, hj, by simpa using hnt, hp, rfl, rfl,
    rfl, (currentAttempt_ok hp).2.2.2.1, by rw [hts], by rw [hts]⟩

theorem safe_obsLike {s : State} {jid : JobId} {sid : StepId} {g : Nat} {t : Transition}
    (hS : SafeP s) (h : ObsLike s jid sid g t) : SafeP t.state := by
  obtain ⟨j, p, a', hj, hnt, hp, h1, h2, h3, h4, hts, _⟩ := h
  rw [hts]
  obtain ⟨_, _, hinv, _, _⟩ := job_of_find hS hj
  obtain ⟨_, ha, _, hlive, _, _⟩ := currentAttempt_ok hp
  obtain ⟨hinv', _, hle, hsteps, e0, e1, e2, _, _, _, e3, _⟩ :=
    modify_spec hinv (List.mem_of_find?_eq_some ha) h1 h2 (by rw [h4, hlive]) h3
  exact safe_putJob_le hS hj hnt hinv' hle e0 e2 e1 e3 (by rw [hsteps])

/-! ### Pause / acknowledge / resume -/

def StatusLike (s : State) (jid : JobId) (t : Transition) : Prop :=
  ∃ j x, s.findJob? jid = some j ∧ j.status.terminal = false ∧ x.terminal = false ∧
    t.state = s.putJob { j with status := x }

theorem doPause_ok {s : State} {jid : JobId} {t : Transition} (h : doPause s jid = .ok t) :
    StatusLike s jid t ∧ t.effects = [] := by
  unfold doPause at h
  unfold_ok h
  obtain ⟨j, hj, _, hd, hts⟩ := h
  refine ⟨⟨j, .pauseRequested, hj, ?_, rfl, by rw [hts]⟩, by rw [hts]⟩
  unfold dispatchable at hd
  simp only [Bool.or_eq_true, beq_iff_eq] at hd
  rcases hd with hd | hd <;> rw [hd] <;> rfl

theorem doAckQuiescence_ok {s : State} {jid : JobId} {c : Bool} {t : Transition}
    (h : doAckQuiescence s jid c = .ok t) : StatusLike s jid t ∧ t.effects = [] := by
  unfold doAckQuiescence at h
  unfold_ok h
  obtain ⟨j, hj, _, hd, _, _, hts⟩ := h
  simp only [beq_iff_eq] at hd
  exact ⟨⟨j, .paused, hj, by rw [hd]; rfl, rfl, by rw [hts]⟩, by rw [hts]⟩

theorem doResume_ok {s : State} {jid : JobId} {t : Transition} (h : doResume s jid = .ok t) :
    StatusLike s jid t ∧ t.effects = [] := by
  unfold doResume at h
  unfold_ok h
  obtain ⟨j, hj, _, hd, hts⟩ := h
  simp only [beq_iff_eq] at hd
  exact ⟨⟨j, .running, hj, by rw [hd]; rfl, rfl, by rw [hts]⟩, by rw [hts]⟩

theorem safe_statusLike {s : State} {jid : JobId} {t : Transition} (hS : SafeP s)
    (h : StatusLike s jid t) : SafeP t.state := by
  obtain ⟨j, x, hj, hnt, hx, hts⟩ := h
  rw [hts]
  obtain ⟨_, _, hinv, _, _⟩ := job_of_find hS hj
  exact safe_putJob_le hS hj hnt (status_spec hinv x (by rw [hx]; simp)) (LiveLe.refl j) rfl rfl rfl rfl rfl

/-! ### Cancel -/

theorem doCancel_ok {s : State} {jid : JobId} {t : Transition} (h : doCancel s jid = .ok t) :
    ∃ j, s.findJob? jid = some j ∧ j.status.terminal = false ∧
      t.state = s.putJob { (j.revokeLive .cancelled).1 with status := .cancelled, epoch := j.epoch + 1 } ∧
      t.effects = (j.revokeLive .cancelled).2 := by
  unfold doCancel at h
  unfold_ok h
  obtain ⟨j, hj, _, hnt, hts⟩ := h
  exact ⟨j, hj, by simpa using hnt, by rw [hts], by rw [hts]⟩

theorem safe_doCancel {s : State} {jid : JobId} {t : Transition} (hS : SafeP s)
    (h : doCancel s jid = .ok t) : SafeP t.state := by
  obtain ⟨j, hj, hnt, hts, _⟩ := doCancel_ok h
  rw [hts]
  obtain ⟨_, _, hinv, _, _⟩ := job_of_find hS hj
  have hns : AttemptStatus.cancelled.live = false := rfl
  refine safe_putJob_le hS hj hnt (jinv_revoked hns hinv rfl rfl) (revokeLive_liveLe j _ hns _ rfl)
    rfl rfl rfl rfl ?_
  simp [Job.revokeLive, List.map_map, Function.comp, dropAuthority_id]

/-! ### Settling results (commitResult / recordVerification) -/

def settledJob (j : Job) (st : StepState) (a : Attempt) (acc : Accepted) : Job :=
  (j.setAttempt { a with status := .succeeded }).setStep
    { st with accepted := some acc, current := none, status := stepStatusOf acc.outcome }

/-- The accepting branch of `doSettle`. -/
def SettleAcc (s : State) (e : Envelope) (jid : JobId) (sid : StepId) (g : Nat) (t : Transition) : Prop :=
  ∃ j st a acc, s.findJob? jid = some j ∧ j.findStep? sid = some st ∧ st.accepted = none ∧
    j.status.terminal = false ∧ j.findAttempt? sid g = some a ∧ st.current = some g ∧
    a.status.live = true ∧ a.jobEpoch = j.epoch ∧ a.ctrlEpoch = s.ctrlEpoch ∧ e.tick < a.deadline ∧
    acc.gen = g ∧ acc.jobEpoch = a.jobEpoch ∧ acc.ctrlEpoch = a.ctrlEpoch ∧
    acc.leaseDeadline = a.deadline ∧ acc.acceptedAt = e.tick ∧ acc.fingerprint = a.fingerprint ∧
    acc.subject = a.subject ∧
    t.state = s.putJob (finalizeJob (settledJob j st a acc)).1 ∧
    t.effects = (finalizeJob (settledJob j st a acc)).2

theorem doSettle_ok {s : State} {e : Envelope} {jid : JobId} {sid : StepId} {g : Nat}
    {r : ResultEnvelope} {v : Bool} {t : Transition} (h : doSettle s e jid sid g r v = .ok t) :
    (t.state = s ∧ t.effects = [] ∧ ∃ j st acc, s.findJob? jid = some j ∧ j.findStep? sid = some st ∧
      st.accepted = some acc) ∨ SettleAcc s e jid sid g t := by
  unfold doSettle at h
  unfold_ok h
  obtain ⟨j, hj, w, hw, spec, hspec, _, hv, st, hst, a0, ha0, h⟩ := h
  split at h
  · rename_i acc hacc
    split at h
    · unfold_ok h
      left
      exact ⟨by rw [h], by rw [h], j, st, acc, hj, hst, hacc⟩
    · cases h
  · rename_i hacc
    unfold_ok h
    obtain ⟨_, hnt, p, hp, _, hdl, _, _, _, _, _, _, _, _, _, _, _, _, hts⟩ := h
    obtain ⟨hst', ha, hcur, hlive, he1, he2⟩ := currentAttempt_ok hp
    have hpst : p.1 = st := by rw [hst] at hst'; exact (Option.some.inj hst').symm
    right
    refine ⟨j, st, p.2, Accepted.mk g p.2.jobEpoch p.2.ctrlEpoch p.2.deadline e.tick j.release
      p.2.subject p.2.fingerprint r.result (combineOutcome r.modelOutcome r.trustedOutcome) r.produced
      r.exports r.contract, hj, hst, hacc,
      by simpa using hnt, ha, by rw [← hpst]; exact hcur, hlive, he1, he2,
      by simpa using hdl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by rw [hts]; rfl, by rw [hts]; rfl⟩

theorem safe_settleAcc {s : State} {e : Envelope} {jid : JobId} {sid : StepId} {g : Nat} {t : Transition}
    (hS : SafeP s) (h : SettleAcc s e jid sid g t) : SafeP t.state := by
  obtain ⟨j, st, a, acc, hj, hst, hacc, hnt, ha, hcur, hlive, _, _, hdl, hg, _, _, hld, hat, _, _, hts, _⟩ := h
  rw [hts]
  obtain ⟨_, _, hinv, _, _⟩ := job_of_find hS hj
  have ham := List.mem_of_find?_eq_some ha
  have hap : a.step = sid ∧ a.gen = g := by simpa using List.find?_some ha
  have hsid : st.id = sid := by simpa using List.find?_some hst
  obtain ⟨hinv1, _, hle1, _, e0, e1, e2, _, _, _, e3, _, _, est, _, eids⟩ :=
    retire_spec (st' := { st with accepted := some acc, current := none, status := stepStatusOf acc.outcome })
      (a' := { a with status := .succeeded }) hinv hnt (List.mem_of_find?_eq_some hst) ham
      (by rw [hcur, hap.2]) (by rw [hap.1, hsid]) rfl rfl rfl rfl rfl
      (by cases acc.outcome <;> simp [stepStatusOf])
      (by simp [stepAccOk])
      (by
        have := (hinv.ac.grange a ham).2
        simp only [stepFenced, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by omega, by omega⟩)
  have hnt1 : (settledJob j st a acc).status.terminal = false := by rw [← hnt]; exact congrArg _ est
  obtain ⟨hinv2, _, _, hle2, f0, f1, f2, _, _, _, f3, _, _, _, fids⟩ :=
    finalizeJob_spec (settledJob j st a acc) hinv1 hnt1
  exact safe_putJob_le hS hj hnt hinv2 (hle1.trans hle2) (f0.trans e0) (f2.trans e2) (f1.trans e1)
    (f3.trans e3) (fids.trans eids)

/-! ### Transport failure / lease expiry -/

def failedJob (j : Job) (spec : StepSpec) (st : StepState) (a : Attempt) (ns : AttemptStatus) : Job :=
  (j.setAttempt { a with status := ns }).setStep
    { st with current := none, failures := st.failures + 1,
              status := (if st.failures + 1 > spec.retries then .failed else .pending) }

def FailLike (s : State) (jid : JobId) (sid : StepId) (g : Nat) (t : Transition) : Prop :=
  ∃ j spec p ns, s.findJob? jid = some j ∧ j.status.terminal = false ∧
    currentAttempt s j sid g = .ok p ∧ ns.live = false ∧
    t.state = s.putJob (finalizeJob (failedJob j spec p.1 p.2 ns)).1 ∧
    t.effects = terminateEffect j p.2 :: (finalizeJob (failedJob j spec p.1 p.2 ns)).2

theorem doFailAttempt_ok {s : State} {jid : JobId} {sid : StepId} {g : Nat} {t : Transition}
    (h : doFailAttempt s jid sid g = .ok t) : FailLike s jid sid g t := by
  unfold doFailAttempt settleFailure at h
  unfold_ok h
  obtain ⟨j, hj, _, hnt, w, _, spec, _, p, hp, hts⟩ := h
  exact ⟨j, spec, p, .failed, hj, by simpa using hnt, hp, rfl, by rw [hts]; rfl, by rw [hts]; rfl⟩

theorem doExpireAttempt_ok {s : State} {e : Envelope} {jid : JobId} {sid : StepId} {g : Nat}
    {t : Transition} (h : doExpireAttempt s e jid sid g = .ok t) : FailLike s jid sid g t := by
  unfold doExpireAttempt settleFailure at h
  unfold_ok h
  obtain ⟨j, hj, _, hnt, w, _, spec, _, p, hp, _, _, hts⟩ := h
  exact ⟨j, spec, p, .expired, hj, by simpa using hnt, hp, rfl, by rw [hts]; rfl, by rw [hts]; rfl⟩

theorem safe_failLike {s : State} {jid : JobId} {sid : StepId} {g : Nat} {t : Transition}
    (hS : SafeP s) (h : FailLike s jid sid g t) : SafeP t.state := by
  obtain ⟨j, spec, p, ns, hj, hnt, hp, hns, hts, _⟩ := h
  rw [hts]
  obtain ⟨_, _, hinv, _, _⟩ := job_of_find hS hj
  obtain ⟨hst, ha, hcur, _, _, _⟩ := currentAttempt_ok hp
  have hstm := List.mem_of_find?_eq_some hst
  have ham := List.mem_of_find?_eq_some ha
  have hap : p.2.step = sid ∧ p.2.gen = g := by simpa using List.find?_some ha
  have hsid : p.1.id = sid := by simpa using List.find?_some hst
  have hacc : p.1.accepted = none := (hinv.ac.cur p.1 hstm g hcur).2.1
  obtain ⟨hinv1, _, hle1, _, e0, e1, e2, _, _, _, e3, _, _, est, _, eids⟩ :=
    retire_spec (st' := { p.1 with current := none, failures := p.1.failures + 1, status := (if p.1.failures + 1 > spec.retries then .failed else .pending) })
      (a' := { p.2 with status := ns }) hinv hnt hstm ham
      (by rw [hcur, hap.2]) (by rw [hap.1, hsid]) rfl rfl hns rfl rfl
      (by split <;> simp)
      (by simp only [stepAccOk, hacc]; split <;> simp)
      (by simp [stepFenced, hacc])
  have hnt1 : (failedJob j spec p.1 p.2 ns).status.terminal = false := by
    rw [← hnt]; exact congrArg _ est
  obtain ⟨hinv2, _, _, hle2, f0, f1, f2, _, _, _, f3, _, _, _, fids⟩ :=
    finalizeJob_spec (failedJob j spec p.1 p.2 ns) hinv1 hnt1
  exact safe_putJob_le hS hj hnt hinv2 (hle1.trans hle2) (f0.trans e0) (f2.trans e2) (f1.trans e1)
    (f3.trans e3) (fids.trans eids)

/-! ### Authorizing an attempt -/

def startedJob (j : Job) (st : StepState) (a : Attempt) : Job :=
  ({ j with attempts := j.attempts ++ [a], status := .running } : Job).setStep
    { st with status := .active, current := some (j.attempts.length + 1) }

def StartAcc (s : State) (e : Envelope) (jid : JobId) (sid : StepId) (fp : Digest) (t : Transition) : Prop :=
  ∃ j w spec st b a, a.fingerprint = fp ∧ a.deadline = e.tick + s.config.leaseTicks ∧ s.findJob? jid = some j ∧ dispatchable j.status = true ∧ s.workflowOf j = some w ∧
    w.find? sid = some spec ∧ j.findStep? sid = some st ∧ st.idle = true ∧ prereqsDone j spec = true ∧
    subjectFor j w spec = some a.subject ∧ bindInputs j spec = some a.inputs ∧
    s.findBudget? j.budget = some b ∧ b.used < b.limit ∧ j.liveAttempts.length < w.maxParallel ∧
    s.liveOfClass spec.role.resource < spec.role.resource.limit s.config ∧
    a.step = sid ∧ a.role = spec.role ∧ a.gen = j.attempts.length + 1 ∧ a.status = .authorized ∧
    t.state = (s.putJob (startedJob j st a)).putBudget { b with used := b.used + 1 } ∧
    t.effects = [{ id := launchId jid sid (j.attempts.length + 1), kind := .launch, job := jid, step := sid,
                   gen := j.attempts.length + 1, subject := a.subject, inputs := a.inputs }]

theorem doStartAttempt_ok {s : State} {e : Envelope} {jid : JobId} {sid : StepId} {fp : Digest}
    {t : Transition} (h : doStartAttempt s e jid sid fp = .ok t) : StartAcc s e jid sid fp t := by
  unfold doStartAttempt at h
  unfold_ok h
  obtain ⟨j, hj, _, hd, w, hw, spec, hspec, st, hst, _, hidle, _, hpre, _, _, subj, hsubj, ins, hins,
    b, hb, _, hbl, _, hpar, _, hcls, hts⟩ := h
  refine ⟨j, w, spec, st, b, Attempt.mk sid spec.role (j.attempts.length + 1) j.epoch s.ctrlEpoch
    (e.tick + s.config.leaseTicks) .authorized subj fp ins "", rfl, rfl, hj, hd, hw, hspec, hst, hidle, hpre, hsubj,
    hins, hb, by simpa using hbl, by simpa using hpar, by simpa using hcls, rfl, rfl, rfl, rfl,
    by rw [hts]; rfl, by rw [hts]⟩

theorem safe_startAcc {s : State} {e : Envelope} {jid : JobId} {sid : StepId} {fp : Digest}
    {t : Transition} (hS : SafeP s) (h : StartAcc s e jid sid fp t) : SafeP t.state := by
  obtain ⟨j, w, spec, st, b, a, _, _, hj, hd, hw, _, hst, hidle, _, _, _, hb, hbl, hpar, hcls, ha1, ha2, ha3,
    ha4, hts, _⟩ := h
  rw [hts]
  obtain ⟨_, _, hinv, hpin, _⟩ := job_of_find hS hj
  have hnt : j.status.terminal = false := by
    unfold dispatchable at hd
    simp only [Bool.or_eq_true, beq_iff_eq] at hd
    rcases hd with hd | hd <;> rw [hd] <;> rfl
  have hsid : st.id = sid := by simpa using List.find?_some hst
  simp only [StepState.idle, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hidle
  obtain ⟨hinv', hlc, hla, _, _, e0, e1, e2, _, _, _, e3, _, _, _, eids⟩ :=
    start_spec (a := a) hinv (List.mem_of_find?_eq_some hst) hidle.1.2 hidle.2 (by rw [ha1, hsid]) ha3 ha4
  have hbm : b ∈ s.budgets := List.mem_of_find?_eq_some hb
  have hbid : b.id = j.budget := by simpa using List.find?_some hb
  refine safe_putJob (s' := (s.putJob (startedJob j st a)).putBudget { b with used := b.used + 1 })
    hS hj hnt e0 rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ hinv' ?_ ?_ ?_
  · show (s.budgets.map (fun x => if x.id == b.id then { b with used := b.used + 1 } else x)).map (·.id) = _
    exact map_replace_key (fun y _ hy => (by simpa using hy : y.id = b.id).symm)
  · intro x hx
    rcases mem_replace hx with rfl | ⟨hx, _⟩
    · show b.used + 1 ≤ b.limit; omega
    · exact hS.bud x hx
  · rw [pinned_same e2 e1 e3 eids]; exact hpin
  · intro w' hw'
    rw [workflowOf_same e2 e1, hw] at hw'
    cases hw'
    rw [hla]; omega
  · intro c
    rw [hlc c, ha2]
    have := limit_bound hS c
    by_cases hc : spec.role.resource = c
    · subst hc; simp; omega
    · simp [hc]; omega

/-! ### Publication -/

theorem gatesPass_exports {s : State} {j : Job} {w : WorkflowDef} {x : Digest × List WorkflowDef}
    (h : gatesPass s j w = .ok x) : exportsOk x.2 = true := by
  unfold gatesPass at h
  unfold_ok h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hex, hx⟩ := h
  rw [← hx]; exact hex

theorem doPublishReport_ok {s : State} {jid : JobId} {rep : Digest} {t : Transition}
    (h : doPublishReport s jid rep = .ok t) :
    ∃ x, t.state = { s with reports := s.reports ++ [x] } ∧ x.job = jid ∧ x.digest = rep ∧
      t.effects = [{ id := s!"report:{jid}", kind := .reportPublished, job := jid, step := "", gen := 0,
                     subject := rep, inputs := [] }] := by
  unfold doPublishReport at h
  unfold_ok h
  obtain ⟨_, _, _, _, _, _, _, _, p, _, _, _, _, _, hts⟩ := h
  exact ⟨_, by rw [hts], rfl, rfl, by rw [hts]⟩

theorem safe_doPublishReport {s : State} {jid : JobId} {rep : Digest} {t : Transition} (hS : SafeP s)
    (h : doPublishReport s jid rep = .ok t) : SafeP t.state := by
  obtain ⟨x, hts, _⟩ := doPublishReport_ok h
  rw [hts]
  exact safe_sameJobs hS rfl (RelExt.of_eq rfl) rfl rfl rfl hS.relIds hS.relOk hS.appIds hS.chIds hS.chOk
    (fun r hr => Or.inl hr) hS.act

def PubRel (s : State) (jid : JobId) (d : Digest) (t : Transition) : Prop :=
  ∃ j cid c w pw rel, s.findJob? jid = some j ∧ j.kind = .changeEvaluate ∧ j.status = .succeeded ∧
    j.change = some cid ∧ s.findChange? cid = some c ∧ s.workflowOf j = some w ∧
    gatesPass s j w = .ok pw ∧ s.findRelease? d = none ∧
    rel.digest = d ∧ rel.payload = pw.1 ∧ rel.workflows = pw.2 ∧ rel.source = j.subject ∧
    rel.contract = s.contract ∧ rel.evidenceJob = some jid ∧
    t.state = ({ s with releases := s.releases ++ [rel] } : State).putChange { c with status := .published } ∧
    t.effects = [{ id := s!"release:{d}", kind := .releasePublished, job := jid, step := "", gen := 0,
                   subject := d, inputs := [] }]

theorem doPublishRelease_ok {s : State} {jid : JobId} {d : Digest} {as : List Asset} {t : Transition}
    (h : doPublishRelease s jid d as = .ok t) : PubRel s jid d t := by
  unfold doPublishRelease at h
  unfold_ok h
  obtain ⟨j, hj, _, hk, _, hst, cid, hcid, c, hc, _, _, w, hw, pw, hpw, _, _, _, hd, _, _, hts⟩ := h
  simp only [beq_iff_eq, Option.isNone_iff_eq_none] at hk hst hd
  exact ⟨j, cid, c, w, pw, _, hj, hk, hst, hcid, hc, hw, hpw, hd, rfl, rfl, rfl, rfl, rfl, rfl,
    by rw [hts], by rw [hts]⟩

theorem safe_pubRel {s : State} {jid : JobId} {d : Digest} {t : Transition} (hS : SafeP s)
    (h : PubRel s jid d t) : SafeP t.state := by
  obtain ⟨j, cid, c, w, pw, rel, hj, hk, hst, _, hc, hw, hpw, hd, h1, h2, h3, h4, h5, h6, hts, _⟩ := h
  rw [hts]
  generalize hs' : (({ s with releases := s.releases ++ [rel] } : State).putChange { c with status := .published }) = s'
  have hrel : s'.releases = s.releases ++ [rel] := by rw [← hs']; rfl
  have hre : RelExt s s' := RelExt.append [rel] hrel
  have hbe : BudExt s s' := BudExt.of_ids (by rw [← hs']; rfl)
  obtain ⟨hchIds, hchOk⟩ := changes_putChange hS hc (c' := { c with status := .published }) rfl rfl rfl
    (s' := s') (by rw [← hs']; rfl) hre hbe
  have hjobs : s'.jobs = s.jobs := by rw [← hs']; rfl
  have hcon : s'.contract = s.contract := by rw [← hs']; rfl
  refine safe_sameJobs hS hjobs hre (by rw [← hs']; rfl) hcon (by rw [← hs']; rfl) ?_ ?_
    (by rw [← hs']; exact hS.appIds) hchIds hchOk ?_ ?_
  · rw [hrel, List.map_append, List.nodup_append]
    refine ⟨hS.relIds, by simp, ?_⟩
    intro x hx y hy heq
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
    rw [List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [State.findRelease?, List.find?_eq_none] at hd
    exact hd z hz (by simp [heq, hy, h1])
  · have := hS.relOk
    unfold releasesOk at this ⊢
    simp only [Bool.and_eq_true] at this ⊢
    obtain ⟨⟨ha, hb⟩, hc'⟩ := this
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hrel, List.all_append, ha]
      simp [h3, gatesPass_exports hpw]
    · have hact : s'.active = s.active := by rw [← hs']; rfl
      have hacts : s'.activations = s.activations := by rw [← hs']; rfl
      rw [hact]
      cases hsa : s.active with
      | none =>
        exfalso
        rw [hsa] at hb
        unfold State.workflowOf State.findRelease? at hw
        rw [List.isEmpty_iff.mp hb] at hw
        simp at hw
      | some x =>
        rw [hsa] at hb
        simp only [Bool.and_eq_true] at hb ⊢
        obtain ⟨hb1, hb2⟩ := hb
        obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.mp hb1
        rw [hre _ _ hr0]
        refine ⟨rfl, ?_⟩
        unfold State.wasActivated at hb2 ⊢
        rw [hacts]; exact hb2
    · rw [hrel, List.filter_append]
      simpa [h6] using hc'
  · intro r hr
    rw [hrel, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact Or.inl hr
    · right
      have hfj : s'.findJob? jid = some j := by unfold State.findJob?; rw [hjobs]; exact hj
      simp only [relEvid, h6, hfj, workflowOf_ext hre hw, gatesPass_congr hcon, hpw]
      simp [hk, hst, h2, h3, h4]
  · rw [activationsApproved_congr (by rw [← hs']) (by rw [← hs'])]; exact hS.act

/-! ### Approvals and activation -/

theorem doRecordApproval_ok {s : State} {e : Envelope} {id : ApprovalId} {rel base : Digest}
    {t : Transition} (h : doRecordApproval s e id rel base = .ok t) :
    ∃ ap, s.findApproval? id = none ∧ ap.id = id ∧ t.state = { s with approvals := s.approvals ++ [ap] } ∧
      t.effects = [] := by
  unfold doRecordApproval at h
  unfold_ok h
  obtain ⟨_, h1, _, _, _, _, _, _, hts⟩ := h
  simp only [Option.isNone_iff_eq_none] at h1
  exact ⟨_, h1, rfl, by rw [hts], by rw [hts]⟩

theorem safe_doRecordApproval {s : State} {e : Envelope} {id : ApprovalId} {rel base : Digest}
    {t : Transition} (hS : SafeP s) (h : doRecordApproval s e id rel base = .ok t) : SafeP t.state := by
  obtain ⟨ap, hfresh, hid, hts, _⟩ := doRecordApproval_ok h
  rw [hts]
  refine safe_sameJobs hS rfl (RelExt.of_eq rfl) rfl rfl rfl hS.relIds hS.relOk ?_ hS.chIds hS.chOk
    (fun r hr => Or.inl hr) ?_
  · show ((s.approvals ++ [ap]).map (·.id)).Nodup
    rw [List.map_append, List.nodup_append]
    refine ⟨hS.appIds, by simp, ?_⟩
    intro x hx y hy heq
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
    rw [List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [State.findApproval?, List.find?_eq_none] at hfresh
    exact hfresh z hz (by simp [heq, hy, hid])
  · have := hS.act
    unfold activationsApproved at this ⊢
    simp only [Bool.and_eq_true, List.all_eq_true] at this ⊢
    refine ⟨?_, this.2⟩
    intro a ha
    have := this.1 a ha
    split at this
    · exact this
    · simp only [List.any_append, Bool.or_eq_true]; exact Or.inl this

theorem doRevokeApproval_ok {s : State} {id : ApprovalId} {t : Transition}
    (h : doRevokeApproval s id = .ok t) :
    ∃ a, s.findApproval? id = some a ∧
      t.state = { s with approvals := s.approvals.map (fun x => if x.id == id then { a with revoked := true } else x) } ∧
      t.effects = [] := by
  unfold doRevokeApproval at h
  unfold_ok h
  obtain ⟨a, ha, hts⟩ := h
  exact ⟨a, ha, by rw [hts], by rw [hts]⟩

theorem safe_doRevokeApproval {s : State} {id : ApprovalId} {t : Transition} (hS : SafeP s)
    (h : doRevokeApproval s id = .ok t) : SafeP t.state := by
  obtain ⟨a, ha, hts, _⟩ := doRevokeApproval_ok h
  rw [hts]
  have ham : a ∈ s.approvals := List.mem_of_find?_eq_some ha
  have haid : a.id = id := by simpa using List.find?_some ha
  refine safe_sameJobs hS rfl (RelExt.of_eq rfl) rfl rfl rfl hS.relIds hS.relOk ?_ hS.chIds hS.chOk
    (fun r hr => Or.inl hr) ?_
  · show ((s.approvals.map (fun x => if x.id == id then { a with revoked := true } else x)).map (·.id)).Nodup
    rw [map_replace_key (fun y _ hy => by simp only [beq_iff_eq] at hy; exact haid.trans hy.symm)]
    exact hS.appIds
  · have := hS.act
    unfold activationsApproved at this ⊢
    simp only [Bool.and_eq_true, List.all_eq_true] at this ⊢
    refine ⟨?_, this.2⟩
    intro x hx
    have := this.1 x hx
    split at this
    · exact this
    · rename_i aid _
      rw [List.any_eq_true] at this ⊢
      obtain ⟨ap, hap, hp⟩ := this
      by_cases hq : (ap.id == id) = true
      · have : ap = a := nodup_map_inj hS.appIds hap ham (by simp only [beq_iff_eq] at hq; rw [hq, haid])
        subst this
        exact ⟨{ ap with revoked := true }, mem_replace_new hap hq, hp⟩
      · exact ⟨ap, mem_replace_of hap (by simpa using hq), hp⟩

theorem doActivate_ok {s : State} {e : Envelope} {rel base : Digest} {aid : ApprovalId} {t : Transition}
    (h : doActivate s e rel base aid = .ok t) :
    ∃ a r, s.active = some base ∧ s.findApproval? aid = some a ∧ a.revoked = false ∧ a.release = rel ∧
      a.expectedBase = base ∧ a.contract = s.contract ∧ s.findRelease? rel = some r ∧
      t.state = { s with active := some rel,
                         activations := s.activations ++ [{ release := rel, base := some base, approval := some aid, atTick := e.tick }] } ∧
      t.effects = [] := by
  unfold doActivate at h
  unfold_ok h
  obtain ⟨_, h1, a, ha, _, h2, _, h3, r, hr, _, _, _, _, _, _, hts⟩ := h
  simp only [beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true'] at h1 h2 h3
  exact ⟨a, r, h1, ha, h2, h3.1.1, h3.1.2, h3.2, hr, by rw [hts], by rw [hts]⟩

theorem safe_doActivate {s : State} {e : Envelope} {rel base : Digest} {aid : ApprovalId} {t : Transition}
    (hS : SafeP s) (h : doActivate s e rel base aid = .ok t) : SafeP t.state := by
  obtain ⟨a, r, _, ha, _, h2, h3, _, hr, hts, _⟩ := doActivate_ok h
  rw [hts]
  refine safe_sameJobs hS rfl (RelExt.of_eq rfl) rfl rfl rfl hS.relIds ?_ hS.appIds hS.chIds hS.chOk
    (fun r hr => Or.inl hr) ?_
  · have := hS.relOk
    unfold releasesOk at this ⊢
    simp only [Bool.and_eq_true] at this ⊢
    refine ⟨⟨this.1.1, ?_⟩, this.2⟩
    refine ⟨?_, by simp [State.wasActivated]⟩
    show (s.findRelease? rel).isSome = true
    rw [hr]; rfl
  · have := hS.act
    unfold activationsApproved at this ⊢
    simp only [Bool.and_eq_true, List.all_eq_true, List.filter_append, List.length_append] at this ⊢
    refine ⟨?_, by simpa using this.2⟩
    intro x hx
    rw [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact this.1 x hx
    · simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Option.some.injEq]
      exact ⟨a, List.mem_of_find?_eq_some ha, ⟨by simpa using List.find?_some ha, h2⟩, h3⟩

/-! ### Migration -/

theorem canMigrateB_ok {s : State} {j : Job} {tr : Release} (h : canMigrateB s j tr = true) :
    ∃ oldRel newW oldW, s.findRelease? j.release = some oldRel ∧ workflowFor tr.workflows j.kind = some newW ∧
      workflowFor oldRel.workflows j.kind = some oldW ∧ j.kind = .packageAudit ∧ j.status = .paused ∧
      (∀ a ∈ j.attempts, a.status.live = false) ∧ wellFormedWorkflow newW = true ∧
      (∀ st ∈ j.steps, migStepOk j oldRel.assets tr.assets oldW newW st = true) := by
  unfold canMigrateB at h
  split at h
  · rename_i oldRel newW h1 h2
    split at h
    · rename_i oldW h3
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.isEmpty_iff, Job.liveAttempts,
        List.filter_eq_nil_iff] at h
      obtain ⟨⟨⟨⟨⟨⟨hk, hs⟩, hl⟩, _⟩, hwf⟩, _⟩, hall⟩ := h
      exact ⟨oldRel, newW, oldW, h1, h2, h3, hk, hs, fun a ha => by simpa using hl a ha, hwf, hall⟩
    · cases h
  · cases h

def MigAcc (s : State) (jid : JobId) (target : Digest) (rev : Nat) (t : Transition) : Prop :=
  ∃ j tr newW oldRel oldW, s.findJob? jid = some j ∧ j.revision = rev ∧ s.findRelease? target = some tr ∧
    s.findRelease? j.release = some oldRel ∧ workflowFor oldRel.workflows j.kind = some oldW ∧
    workflowFor tr.workflows j.kind = some newW ∧ j.kind = .packageAudit ∧ j.status = .paused ∧
    (∀ a ∈ j.attempts, a.status.live = false) ∧ wellFormedWorkflow newW = true ∧
    (∀ st ∈ j.steps, migStepOk j oldRel.assets tr.assets oldW newW st = true) ∧
    t.state.jobs = (s.putJob { j with release := target, epoch := j.epoch + 1,
                                      steps := migratedSteps j newW }).jobs ∧
    t.state.releases = s.releases ∧ t.state.active = s.active ∧ t.state.activations = s.activations ∧
    t.state.approvals = s.approvals ∧ t.state.changes = s.changes ∧ t.state.contract = s.contract ∧
    t.state.config = s.config ∧ t.state.budgets = s.budgets ∧ t.state.reports = s.reports ∧
    t.state.ctrlEpoch = s.ctrlEpoch ∧ t.effects = []

theorem doMigrate_ok {s : State} {e : Envelope} {jid : JobId} {target : Digest} {rev : Nat} {t : Transition}
    (h : doMigrate s e jid target rev = .ok t) : MigAcc s jid target rev t := by
  unfold doMigrate at h
  unfold_ok h
  obtain ⟨j, hj, _, hrev, tr, htr, _, _, _, hcan, newW, hnw, hts⟩ := h
  obtain ⟨oldRel, newW', oldW, h1, h2, h3, hk, hs, hl, hwf, hall⟩ := canMigrateB_ok hcan
  rw [hnw] at h2; cases h2
  simp only [beq_iff_eq] at hrev
  subst hts
  exact ⟨j, tr, newW, oldRel, oldW, hj, hrev, htr, h1, h3, hnw, hk, hs, hl, hwf, hall, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem safe_migAcc {s : State} {jid : JobId} {target : Digest} {rev : Nat} {t : Transition}
    (hS : SafeP s) (h : MigAcc s jid target rev t) : SafeP t.state := by
  obtain ⟨j, tr, newW, oldRel, oldW, hj, _, htr, _, _, hnw, _, hst, hl, hwf, _, hjobs, hrel, hact, hacts,
    happ, hch, hcon, hcfg, hbud, _, _, _⟩ := h
  obtain ⟨_, _, hinv, hpin, _⟩ := job_of_find hS hj
  obtain ⟨hinv', hids, _⟩ := migrate_spec (w := newW) target hinv hl (wellFormed_nodup hwf)
  have hnt : j.status.terminal = false := by rw [hst]; rfl
  have hwo : s.workflowOf { j with release := target, epoch := j.epoch + 1, steps := migratedSteps j newW } =
      some newW := by
    simp only [State.workflowOf, htr, Option.bind_some, hnw]
  refine safe_putJob (j' := { j with release := target, epoch := j.epoch + 1, steps := migratedSteps j newW }) hS hj hnt rfl hjobs hrel hact hacts happ hch hcon hcfg (by rw [hbud])
    (by rw [hbud]; exact hS.bud) hinv' ?_ ?_ ?_
  · unfold jobPinned at hpin ⊢
    rw [hwo]
    cases hw0 : s.workflowOf j with
    | none => rw [hw0] at hpin; cases hpin
    | some w0 =>
      rw [hw0] at hpin
      simp only [Bool.and_eq_true] at hpin ⊢
      refine ⟨⟨hwf, ?_⟩, hpin.2⟩
      rw [hids]; simp
  · intro w' _
    have : Job.liveAttempts { j with release := target, epoch := j.epoch + 1, steps := migratedSteps j newW } = [] := by
      simp only [Job.liveAttempts, List.filter_eq_nil_iff]
      intro a ha; simp [hl a ha]
    rw [this]; simp
  · intro c
    have : Job.liveOfClass { j with release := target, epoch := j.epoch + 1, steps := migratedSteps j newW } c = 0 := by
      simp only [Job.liveOfClass, List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro a ha; simp [hl a ha]
    rw [this]
    have := limit_bound hS c
    omega

/-! ### Controller recovery -/

theorem ite_pf (c : Prop) [Decidable c] :
    (if c then StepStatus.failed else StepStatus.pending) = .pending ∨
    (if c then StepStatus.failed else StepStatus.pending) = .failed := by
  split <;> simp

def recStep (w : WorkflowDef) (st : StepState) : StepState :=
  if st.current.isSome = true then
    { st with current := none, failures := st.failures + 1,
              status := (if st.failures + 1 > (match w.find? st.id with | some sp => sp.retries | none => 0)
                         then .failed else .pending) }
  else st

def recJob (w : WorkflowDef) (j : Job) : Job :=
  { j with attempts := j.attempts.map (Attempt.revokeTo .lost), steps := j.steps.map (recStep w) }

theorem recoverJob_eq {s : State} {j : Job} {w : WorkflowDef} (hw : s.workflowOf j = some w) :
    recoverJob s j = if j.liveAttempts.isEmpty = true then (j, []) else
      ((finalizeJob (recJob w j)).1, j.liveAttempts.map (terminateEffect j) ++ (finalizeJob (recJob w j)).2) := by
  unfold recoverJob
  rw [hw]
  rfl

theorem recoverJob_spec {s : State} {j : Job} {w : WorkflowDef} (hj : JInv j) (hw : s.workflowOf j = some w)
    (hnt : j.status.terminal = false) :
    let j' := (recoverJob s j).1
    JInv j' ∧ AccSame j j' ∧ AttKeys j j' ∧ LiveLe j j' ∧ j'.id = j.id ∧ j'.kind = j.kind ∧
    j'.release = j.release ∧ j'.budget = j.budget ∧ j'.steps.map (·.id) = j.steps.map (·.id) ∧
    (∀ eff ∈ (recoverJob s j).2, eff.kind = .terminate) := by
  rw [recoverJob_eq hw]
  by_cases hc : j.liveAttempts.isEmpty = true
  · rw [ite_eq_left hc]
    exact ⟨hj, AccSame.refl _, AttKeys.refl _, LiveLe.refl _, rfl, rfl, rfl, rfl, rfl, by simp⟩
  · rw [ite_eq_right hc]
    have hns : AttemptStatus.lost.live = false := rfl
    obtain ⟨hinv1, has1, hak1, hle1, _, hids1⟩ := jinv_revokedGen (j' := recJob w j) (h := recStep w)
      hns hj rfl rfl
      (fun st _ => by unfold recStep; split <;> rfl)
      (fun st _ => by unfold recStep; split <;> rfl)
      (fun st _ => by unfold recStep; split <;> simp_all)
      (fun st _ hc => by unfold recStep; simp [hc])
      (fun st _ hc => by unfold recStep; simp only [hc, ite_true]; exact ite_pf _)
    obtain ⟨hinv2, has2, hak2, hle2, f0, f1, f2, _, _, _, f3, _, _, _, fids⟩ :=
      finalizeJob_spec (recJob w j) hinv1 hnt
    refine ⟨hinv2, has1.trans has2, hak1.trans hak2, hle1.trans hle2,
      f0, f1, f2, f3, fids.trans hids1, ?_⟩
    intro eff heff
    rw [List.mem_append] at heff
    rcases heff with heff | heff
    · rw [List.mem_map] at heff
      obtain ⟨a, _, rfl⟩ := heff
      rfl
    · exact finalizeJob_snd_terminate _ eff heff

def recoverAll (s : State) (j : Job) : Job × List EffectIntent :=
  if j.status.terminal = true then (j, []) else recoverJob s j

theorem doRecover_ok {s : State} {e : Envelope} {t : Transition} (h : doRecover s e = .ok t) :
    t.state = { s with ctrlEpoch := e.epoch, clock := e.tick, jobs := s.jobs.map (fun j => (recoverAll s j).1) } ∧
    t.effects = (s.jobs.map (fun j => (recoverAll s j).2)).flatten := by
  unfold doRecover at h
  unfold_ok h
  subst h
  simp only [List.map_map]
  exact ⟨rfl, rfl⟩

theorem recoverAll_spec {s : State} (hS : SafeP s) {j : Job} (hj : j ∈ s.jobs) :
    let j' := (recoverAll s j).1
    JInv j' ∧ AccSame j j' ∧ AttKeys j j' ∧ LiveLe j j' ∧ j'.id = j.id ∧ j'.kind = j.kind ∧
    j'.release = j.release ∧ j'.budget = j.budget ∧ j'.steps.map (·.id) = j.steps.map (·.id) ∧
    (j.status.terminal = true → (recoverAll s j) = (j, [])) ∧
    (∀ eff ∈ (recoverAll s j).2, eff.kind = .terminate) := by
  obtain ⟨hinv, hpin, _⟩ := hS.jobs j hj
  unfold recoverAll
  by_cases ht : j.status.terminal = true
  · rw [ite_eq_left ht]
    exact ⟨hinv, AccSame.refl _, AttKeys.refl _, LiveLe.refl _, rfl, rfl, rfl, rfl, rfl, fun _ => rfl,
      by simp⟩
  · have ht' : j.status.terminal = false := by simpa using ht
    rw [ite_eq_right ht]
    unfold jobPinned at hpin
    cases hw : s.workflowOf j with
    | none => rw [hw] at hpin; cases hpin
    | some w =>
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := recoverJob_spec hinv hw ht'
      exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, fun h => absurd h ht, a10⟩

theorem safe_doRecover {s : State} {e : Envelope} {t : Transition} (hS : SafeP s)
    (h : doRecover s e = .ok t) : SafeP t.state := by
  obtain ⟨hts, _⟩ := doRecover_ok h
  rw [hts]
  generalize hs' : ({ s with ctrlEpoch := e.epoch, clock := e.tick, jobs := s.jobs.map (fun j => (recoverAll s j).1) } : State) = s'
  have hjobs : s'.jobs = s.jobs.map (fun j => (recoverAll s j).1) := by rw [← hs']
  have hre : RelExt s s' := RelExt.of_eq (by rw [← hs'])
  have hbe : BudExt s s' := BudExt.of_ids (by rw [← hs'])
  have hcfg : s'.config = s.config := by rw [← hs']
  refine ⟨?_, by rw [← hs']; exact hS.relIds, by rw [← hs']; exact hS.budIds, by rw [← hs']; exact hS.appIds,
    by rw [← hs']; exact hS.chIds, by rw [← hs']; exact hS.relOk, changesOk_of hS.chOk (by rw [← hs']) hre hbe,
    ?_, ?_, by rw [← hs']; exact hS.act, by rw [← hs']; exact hS.bud, ?_, ?_⟩
  · have : (s.jobs.map (fun j => (recoverAll s j).1)).map (·.id) = s.jobs.map (·.id) := by
      rw [List.map_map]
      exact List.map_congr_left (fun j hj => (recoverAll_spec hS hj).2.2.2.2.1)
    rw [hjobs, this]
    exact hS.jobIds
  · intro x hx
    rw [hjobs, List.mem_map] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    obtain ⟨a1, _, _, a4, _, a6, a7, a8, a9, _⟩ := recoverAll_spec hS hj
    obtain ⟨_, hpin, hpar⟩ := hS.jobs j hj
    exact ⟨a1, jobPinned_ext' hre hbe (by rw [pinned_same a7 a6 a8 a9]; exact hpin),
      par_ext hre (by rw [pinned_same a7 a6 a8 a9]; exact hpin) (par_le hpar a7 a6 a4.2)⟩
  · refine evid_of hS.evid ?_ hre (by rw [← hs']) (fun r hr => Or.inl (by rw [← hs'] at hr; exact hr))
    intro k x hx ht
    unfold State.findJob? at hx ⊢
    rw [hjobs, List.find?_map, find?_congr_mem (q := fun x : Job => x.id == k)
      (fun y hy => by simp [Function.comp, (recoverAll_spec hS hy).2.2.2.2.1]), hx]
    simp only [Option.map_some, Option.some.injEq]
    rw [(recoverAll_spec hS (List.mem_of_find?_eq_some hx)).2.2.2.2.2.2.2.2.2.1 ht]
  · have := hS.llm
    have h2 : s'.liveOfClass .llm ≤ s.liveOfClass .llm := by
      unfold State.liveOfClass; rw [hjobs, List.map_map]
      exact sum_le_sum_of_le (fun j hj => (recoverAll_spec hS hj).2.2.2.1.1 _)
    rw [hcfg]; omega
  · have := hS.cont
    have h2 : s'.liveOfClass .container ≤ s.liveOfClass .container := by
      unfold State.liveOfClass; rw [hjobs, List.map_map]
      exact sum_le_sum_of_le (fun j hj => (recoverAll_spec hS hj).2.2.2.1.1 _)
    rw [hcfg]; omega

end Factory.Contracts
