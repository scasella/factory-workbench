import Factory.ProofJob
/-
  Factory.ProofState — state-level decomposition of `Safe` and generic
  preservation lemmas for the three shapes of job-list update.
-/
namespace Factory.Contracts
open Factory Factory.Check

def Par (s : State) (j : Job) : Prop :=
  ∀ w, s.workflowOf j = some w → j.liveAttempts.length ≤ w.maxParallel

structure SafeP (s : State) : Prop where
  jobIds : (s.jobs.map (·.id)).Nodup
  relIds : (s.releases.map (·.digest)).Nodup
  budIds : (s.budgets.map (·.id)).Nodup
  appIds : (s.approvals.map (·.id)).Nodup
  chIds : (s.changes.map (·.id)).Nodup
  relOk : releasesOk s = true
  chOk : changesOk s = true
  jobs : ∀ j ∈ s.jobs, JInv j ∧ jobPinned s j = true ∧ Par s j
  evid : releasesEvidenced s = true
  act : activationsApproved s = true
  bud : ∀ b ∈ s.budgets, b.used ≤ b.limit
  llm : s.liveOfClass .llm ≤ s.config.llmSlots
  cont : s.liveOfClass .container ≤ s.config.containerSlots

theorem safe_iff (s : State) : Safe s ↔ SafeP s := by
  unfold Safe K01 K02 K03 K05 K06 K07 K10 idsUnique resourcesOk
  simp only [Bool.and_eq_true, noDupBy_iff, List.all_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, hrel, hch, hj⟩, hn, hf, hq, hev, hact, ⟨⟨hb, hl⟩, hc⟩, hp⟩
    refine ⟨h1, h2, h3, h4, h5, hrel, hch, ?_, hev, hact, hb, hl, hc⟩
    intro j hm
    obtain ⟨hpin, hac, hacc⟩ := hj j hm
    refine ⟨(jinv_iff j).1 ⟨hn j hm, hac, hacc, hf j hm, hq j hm⟩, hpin, ?_⟩
    intro w hw
    have := hp j hm
    rw [hw] at this
    simpa using this
  · rintro ⟨h1, h2, h3, h4, h5, hrel, hch, hj, hev, hact, hb, hl, hc⟩
    have hj' := fun j hm => (jinv_iff j).2 (hj j hm).1
    refine ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, hrel, hch, fun j hm => ⟨(hj j hm).2.1, (hj' j hm).2.1,
      (hj' j hm).2.2.1⟩⟩, fun j hm => (hj' j hm).1, fun j hm => (hj' j hm).2.2.2.1,
      fun j hm => (hj' j hm).2.2.2.2, hev, hact, ⟨⟨hb, hl⟩, hc⟩, ?_⟩
    intro j hm
    obtain ⟨_, hpin, hpar⟩ := hj j hm
    unfold jobPinned at hpin
    split at hpin
    · rename_i w hw
      simpa using hpar w hw
    · cases hpin

/-! ### Congruences -/

theorem jinv_revision {j : Job} (h : JInv j) (n : Nat) : JInv { j with revision := n } :=
  ⟨h.nodup, ⟨h.ac.gnodup, h.ac.grange, h.ac.cur, h.ac.idle, h.ac.live⟩, h.acc, h.fenced, h.quiet⟩

theorem find?_isSome_iff_mem_map {α} {key : α → String} {l : List α} {k : String} :
    (l.find? (fun x => key x == k)).isSome = true ↔ k ∈ l.map key := by
  rw [List.find?_isSome, List.mem_map]
  constructor
  · rintro ⟨x, hx, hp⟩; exact ⟨x, hx, by simpa using hp⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by simp⟩

theorem findBudget?_isSome_congr {s s' : State} (h : s'.budgets.map (·.id) = s.budgets.map (·.id))
    (k : BudgetId) : (s'.findBudget? k).isSome = (s.findBudget? k).isSome := by
  unfold State.findBudget?
  apply Bool.eq_iff_iff.mpr
  rw [find?_isSome_iff_mem_map, find?_isSome_iff_mem_map, h]

/-- `s'` extends the release table of `s` (lookup-wise). -/
def RelExt (s s' : State) : Prop := ∀ d r, s.findRelease? d = some r → s'.findRelease? d = some r

theorem RelExt.of_eq {s s' : State} (h : s'.releases = s.releases) : RelExt s s' := by
  intro d r hr; unfold State.findRelease? at *; rw [h]; exact hr

theorem RelExt.append {s s' : State} (rs : List Release) (h : s'.releases = s.releases ++ rs) :
    RelExt s s' := by
  intro d r hr; unfold State.findRelease? at *; rw [h, List.find?_append, hr]; rfl

theorem workflowOf_ext {s s' : State} (h : RelExt s s') {j : Job} {w : WorkflowDef}
    (hw : s.workflowOf j = some w) : s'.workflowOf j = some w := by
  unfold State.workflowOf at *
  cases hr : s.findRelease? j.release with
  | none => rw [hr] at hw; cases hw
  | some r => rw [hr] at hw; rw [h _ _ hr]; exact hw

theorem jobPinned_ext {s s' : State} (h : RelExt s s')
    (hb : s'.budgets.map (·.id) = s.budgets.map (·.id)) {j : Job} (hp : jobPinned s j = true) :
    jobPinned s' j = true := by
  unfold jobPinned at *
  cases hw : s.workflowOf j with
  | none => rw [hw] at hp; cases hp
  | some w =>
    rw [hw] at hp; rw [workflowOf_ext h hw, findBudget?_isSome_congr hb]; exact hp

theorem par_ext {s s' : State} (h : RelExt s s') {j : Job} (hpin : jobPinned s j = true)
    (hp : Par s j) : Par s' j := by
  intro w hw
  unfold jobPinned at hpin
  cases hw0 : s.workflowOf j with
  | none => rw [hw0] at hpin; cases hpin
  | some w0 =>
    rw [workflowOf_ext h hw0] at hw
    cases hw
    exact hp _ hw0

theorem gatesPass_congr {s s' : State} (h : s'.contract = s.contract) (j : Job) (w : WorkflowDef) :
    gatesPass s' j w = gatesPass s j w := by
  unfold gatesPass; rw [h]

/-- Per-release evidence predicate (the body of `releasesEvidenced`). -/
def relEvid (s : State) (r : Release) : Bool :=
  match r.evidenceJob with
  | none => true
  | some jid => match s.findJob? jid with
    | some j => j.kind == .changeEvaluate && j.status == .succeeded &&
      (match s.workflowOf j with
       | some w => match gatesPass s j w with
         | .ok (p, ws) => p == r.payload && ws == r.workflows && r.source == j.subject
         | .error _ => false
       | none => false)
    | none => false

theorem releasesEvidenced_eq (s : State) : releasesEvidenced s = s.releases.all (relEvid s) := rfl

/-- Terminal jobs are carried over unchanged (lookup-wise). -/
def TermKept (s s' : State) : Prop :=
  ∀ jid x, s.findJob? jid = some x → x.status.terminal = true → s'.findJob? jid = some x

theorem relEvid_mono {s s' : State} (hk : TermKept s s') (hr : RelExt s s')
    (hc : s'.contract = s.contract) {r : Release} (h : relEvid s r = true) : relEvid s' r = true := by
  unfold relEvid at *
  split at h
  · rfl
  · rename_i jid hjid
    split at h
    · rename_i x hx
      have hsucc : x.status = .succeeded := by
        simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.1.2
      rw [hk jid x hx (by rw [hsucc]; rfl)]
      simp only
      cases hw : s.workflowOf x with
      | none => rw [hw] at h; simp at h
      | some w =>
        rw [hw] at h
        rw [workflowOf_ext hr hw]
        simp only at h ⊢
        rw [gatesPass_congr hc]
        exact h
    · cases h

theorem liveOfClass_eq_of_jobs {s s' : State} (h : s'.jobs = s.jobs) (c : ResourceClass) :
    s'.liveOfClass c = s.liveOfClass c := by
  unfold State.liveOfClass; rw [h]

theorem liveOfClass_revision (j : Job) (n : Nat) (c : ResourceClass) :
    Job.liveOfClass { j with revision := n } c = j.liveOfClass c := rfl

/-! ### Replacing one job (unique ids) -/

theorem putJob_split {s : State} {j j' : Job} (hu : (s.jobs.map (·.id)).Nodup) (hj : j ∈ s.jobs)
    (hid : j'.id = j.id) :
    ∃ l1 l2, s.jobs = l1 ++ j :: l2 ∧
      (s.putJob j').jobs = l1 ++ { j' with revision := j.revision + 1 } :: l2 ∧
      ∀ x ∈ l1 ++ l2, x.id ≠ j.id := by
  obtain ⟨l1, l2, hs⟩ := List.append_of_mem hj
  have hne : ∀ x ∈ l1 ++ l2, x.id ≠ j.id := by
    intro x hx heq
    rw [hs] at hu
    simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons, List.mem_map] at hu
    rcases List.mem_append.mp hx with hx | hx
    · exact hu.2.2 _ ⟨x, hx, rfl⟩ _ (by simp) heq
    · exact hu.2.1.1 ⟨x, hx, heq⟩
  refine ⟨l1, l2, hs, ?_, hne⟩
  unfold State.putJob
  simp only [hs, List.map_append, List.map_cons, hid, beq_self_eq_true, ite_true]
  congr 1
  · refine (List.map_congr_left (g := id) ?_).trans (List.map_id _)
    intro x hx
    have := hne x (List.mem_append_left _ hx)
    simp [this]
  · congr 1
    refine (List.map_congr_left (g := id) ?_).trans (List.map_id _)
    intro x hx
    have := hne x (List.mem_append_right _ hx)
    simp [this]

theorem liveOfClass_putJob {s : State} {j j' : Job} (hu : (s.jobs.map (·.id)).Nodup)
    (hj : j ∈ s.jobs) (hid : j'.id = j.id) (c : ResourceClass) :
    (s.putJob j').liveOfClass c + j.liveOfClass c = s.liveOfClass c + j'.liveOfClass c := by
  obtain ⟨l1, l2, hs, hs', _⟩ := putJob_split hu hj hid
  unfold State.liveOfClass
  rw [hs', hs]
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, liveOfClass_revision]
  omega

theorem mem_putJob {s : State} {j j' : Job} (hu : (s.jobs.map (·.id)).Nodup) (hj : j ∈ s.jobs)
    (hid : j'.id = j.id) {x : Job} (hx : x ∈ (s.putJob j').jobs) :
    x = { j' with revision := j.revision + 1 } ∨ (x ∈ s.jobs ∧ x.id ≠ j.id) := by
  obtain ⟨l1, l2, hs, hs', hne⟩ := putJob_split hu hj hid
  rw [hs'] at hx
  simp only [List.mem_append, List.mem_cons] at hx
  rcases hx with hx | rfl | hx
  · exact Or.inr ⟨by rw [hs]; simp [hx], hne x (by simp [hx])⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨by rw [hs]; simp [hx], hne x (by simp [hx])⟩

theorem putJob_ids (s : State) (j' : Job) :
    (s.putJob j').jobs.map (·.id) = s.jobs.map (·.id) := by
  unfold State.putJob
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp]
  split
  · rename_i h; exact (by simpa using h : x.id = j'.id).symm
  · rfl

theorem findJob?_eq_some {s : State} {jid : JobId} {j : Job} (hu : (s.jobs.map (·.id)).Nodup) :
    s.findJob? jid = some j ↔ j ∈ s.jobs ∧ j.id = jid :=
  find?_id_eq_some_iff hu

theorem findJob?_putJob_other {s : State} {j' : Job} {k : JobId} (hk : k ≠ j'.id) :
    (s.putJob j').findJob? k = s.findJob? k := by
  rw [findJob?_putJob]
  cases hf : s.findJob? k with
  | none => rfl
  | some x =>
    have := List.find?_some hf
    simp only [beq_iff_eq] at this
    simp [this, hk]

theorem findJob?_putJob_self {s : State} {j j' : Job} {jid : JobId} (hf : s.findJob? jid = some j)
    (hid : j'.id = j.id) : (s.putJob j').findJob? jid = some { j' with revision := j.revision + 1 } := by
  rw [findJob?_putJob, hf]
  have := List.find?_some hf
  simp [hid]

theorem termKept_putJob {s : State} {jid : JobId} {j j' : Job} (hf : s.findJob? jid = some j)
    (hid : j'.id = j.id) (hnt : j.status.terminal = false) (s' : State)
    (hjobs : s'.jobs = (s.putJob j').jobs) : TermKept s s' := by
  intro k x hx ht
  have hs' : s'.findJob? k = (s.putJob j').findJob? k := by
    unfold State.findJob?; rw [hjobs]
  rw [hs']
  by_cases hk : k = jid
  · subst hk; rw [hf] at hx; cases hx; rw [hnt] at ht; cases ht
  · have hj : j.id = jid := by simpa using List.find?_some hf
    rw [findJob?_putJob_other (by rw [hid, hj]; exact hk)]; exact hx

/-! ### Generic `SafeP` transfer lemmas -/

def BudExt (s s' : State) : Prop :=
  ∀ k, (s.findBudget? k).isSome = true → (s'.findBudget? k).isSome = true

theorem BudExt.of_ids {s s' : State} (h : s'.budgets.map (·.id) = s.budgets.map (·.id)) : BudExt s s' := by
  intro k hk; rw [findBudget?_isSome_congr h]; exact hk

theorem BudExt.append {s s' : State} (bs : List Budget) (h : s'.budgets = s.budgets ++ bs) :
    BudExt s s' := by
  intro k hk
  unfold State.findBudget? at *
  rw [h, List.find?_append]
  cases hf : s.budgets.find? (·.id == k) with
  | none => rw [hf] at hk; cases hk
  | some b => rfl

theorem jobPinned_ext' {s s' : State} (h : RelExt s s') (hb : BudExt s s') {j : Job}
    (hp : jobPinned s j = true) : jobPinned s' j = true := by
  unfold jobPinned at *
  cases hw : s.workflowOf j with
  | none => rw [hw] at hp; cases hp
  | some w =>
    rw [hw] at hp; rw [workflowOf_ext h hw]
    simp only [Bool.and_eq_true] at hp ⊢
    exact ⟨hp.1, hb _ hp.2⟩

theorem releasesOk_congr {s s' : State} (h1 : s'.releases = s.releases) (h2 : s'.active = s.active)
    (h3 : s'.activations = s.activations) : releasesOk s' = releasesOk s := by
  unfold releasesOk State.findRelease? State.wasActivated; rw [h1, h2, h3]

theorem changesOk_of {s s' : State} (hS : changesOk s = true) (hch : s'.changes = s.changes)
    (hr : RelExt s s') (hb : BudExt s s') : changesOk s' = true := by
  unfold changesOk at *
  rw [hch]
  rw [List.all_eq_true] at hS ⊢
  intro c hc
  have := hS c hc
  simp only [Bool.and_eq_true] at this ⊢
  refine ⟨hb _ this.1, ?_⟩
  obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.mp this.2
  rw [hr _ _ hr']; rfl

theorem activationsApproved_congr {s s' : State} (h1 : s'.activations = s.activations)
    (h2 : s'.approvals = s.approvals) : activationsApproved s' = activationsApproved s := by
  unfold activationsApproved; rw [h1, h2]

theorem evid_of {s s' : State} (hS : releasesEvidenced s = true) (hk : TermKept s s') (hr : RelExt s s')
    (hc : s'.contract = s.contract) (hnew : ∀ r ∈ s'.releases, r ∈ s.releases ∨ relEvid s' r = true) :
    releasesEvidenced s' = true := by
  rw [releasesEvidenced_eq, List.all_eq_true]
  rw [releasesEvidenced_eq, List.all_eq_true] at hS
  intro r hm
  rcases hnew r hm with h | h
  · exact relEvid_mono hk hr hc (hS r h)
  · exact h

theorem safe_putJob {s s' : State} {jid : JobId} {j j' : Job}
    (hS : SafeP s) (hf : s.findJob? jid = some j) (hnt : j.status.terminal = false) (hid : j'.id = j.id)
    (hjobs : s'.jobs = (s.putJob j').jobs)
    (hrel : s'.releases = s.releases) (hact : s'.active = s.active)
    (hacts : s'.activations = s.activations) (happ : s'.approvals = s.approvals)
    (hch : s'.changes = s.changes) (hcon : s'.contract = s.contract) (hcfg : s'.config = s.config)
    (hbid : s'.budgets.map (·.id) = s.budgets.map (·.id)) (hbud : ∀ b ∈ s'.budgets, b.used ≤ b.limit)
    (hinv : JInv j') (hpin : jobPinned s j' = true) (hpar : Par s j')
    (hlive : ∀ c, s.liveOfClass c + j'.liveOfClass c ≤ c.limit s.config + j.liveOfClass c) :
    SafeP s' := by
  have hj : j ∈ s.jobs := List.mem_of_find?_eq_some hf
  have hre : RelExt s s' := RelExt.of_eq hrel
  have hbe : BudExt s s' := BudExt.of_ids hbid
  have hliv : ∀ c, s'.liveOfClass c ≤ c.limit s.config := by
    intro c
    have h1 := liveOfClass_putJob hS.jobIds hj hid c
    have h2 := hlive c
    have h3 : s'.liveOfClass c = (s.putJob j').liveOfClass c := by
      unfold State.liveOfClass; rw [hjobs]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbud, ?_, ?_⟩
  · rw [hjobs, putJob_ids]; exact hS.jobIds
  · rw [hrel]; exact hS.relIds
  · rw [hbid]; exact hS.budIds
  · rw [happ]; exact hS.appIds
  · rw [hch]; exact hS.chIds
  · rw [releasesOk_congr hrel hact hacts]; exact hS.relOk
  · exact changesOk_of hS.chOk hch hre hbe
  · intro x hx
    rw [hjobs] at hx
    rcases mem_putJob hS.jobIds hj hid hx with rfl | ⟨hx, _⟩
    · exact ⟨jinv_revision hinv _, jobPinned_ext' hre hbe hpin, par_ext hre hpin hpar⟩
    · obtain ⟨h1, h2, h3⟩ := hS.jobs x hx
      exact ⟨h1, jobPinned_ext' hre hbe h2, par_ext hre h2 h3⟩
  · exact evid_of hS.evid (termKept_putJob hf hid hnt s' hjobs) hre hcon
      (fun r hr => Or.inl (by rw [← hrel]; exact hr))
  · rw [activationsApproved_congr hacts happ]; exact hS.act
  · rw [hcfg]; exact hliv .llm
  · rw [hcfg]; exact hliv .container

theorem termKept_append {s s' : State} (js : List Job) (h : s'.jobs = s.jobs ++ js) : TermKept s s' := by
  intro k x hx _
  unfold State.findJob? at *
  rw [h, List.find?_append, hx]; rfl

theorem safe_addJob {s s' : State} {j' : Job}
    (hS : SafeP s) (hjobs : s'.jobs = s.jobs ++ [j']) (hfresh : s.findJob? j'.id = none)
    (hrel : s'.releases = s.releases) (hact : s'.active = s.active)
    (hacts : s'.activations = s.activations) (happ : s'.approvals = s.approvals)
    (hcon : s'.contract = s.contract) (hcfg : s'.config = s.config)
    (hchIds : (s'.changes.map (·.id)).Nodup) (hchOk : changesOk s' = true)
    (hbe : BudExt s s') (hbIds : (s'.budgets.map (·.id)).Nodup) (hbud : ∀ b ∈ s'.budgets, b.used ≤ b.limit)
    (hinv : JInv j') (hpin : jobPinned s' j' = true) (hpar : Par s' j')
    (hlive : ∀ c, j'.liveOfClass c = 0) : SafeP s' := by
  have hre : RelExt s s' := RelExt.of_eq hrel
  refine ⟨?_, ?_, hbIds, ?_, hchIds, ?_, hchOk, ?_, ?_, ?_, hbud, ?_, ?_⟩
  · rw [hjobs, List.map_append, List.nodup_append]
    refine ⟨hS.jobIds, by simp, ?_⟩
    intro a ha b hb heq
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    rw [List.mem_map] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    rw [State.findJob?, List.find?_eq_none] at hfresh
    exact hfresh x hx (by simp [heq, hb])
  · rw [hrel]; exact hS.relIds
  · rw [happ]; exact hS.appIds
  · rw [releasesOk_congr hrel hact hacts]; exact hS.relOk
  · intro x hx
    rw [hjobs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · obtain ⟨h1, h2, h3⟩ := hS.jobs x hx
      exact ⟨h1, jobPinned_ext' hre hbe h2, par_ext hre h2 h3⟩
    · exact ⟨hinv, hpin, hpar⟩
  · exact evid_of hS.evid (termKept_append [j'] hjobs) hre hcon
      (fun r hr => Or.inl (by rw [← hrel]; exact hr))
  · rw [activationsApproved_congr hacts happ]; exact hS.act
  · have : s'.liveOfClass .llm = s.liveOfClass .llm := by
      unfold State.liveOfClass; rw [hjobs]; simp [hlive]
    rw [this, hcfg]; exact hS.llm
  · have : s'.liveOfClass .container = s.liveOfClass .container := by
      unfold State.liveOfClass; rw [hjobs]; simp [hlive]
    rw [this, hcfg]; exact hS.cont

theorem safe_sameJobs {s s' : State}
    (hS : SafeP s) (hjobs : s'.jobs = s.jobs) (hre : RelExt s s') (hbud : s'.budgets = s.budgets)
    (hcon : s'.contract = s.contract) (hcfg : s'.config = s.config)
    (hrelIds : (s'.releases.map (·.digest)).Nodup) (hrelOk : releasesOk s' = true)
    (happIds : (s'.approvals.map (·.id)).Nodup)
    (hchIds : (s'.changes.map (·.id)).Nodup) (hchOk : changesOk s' = true)
    (hnew : ∀ r ∈ s'.releases, r ∈ s.releases ∨ relEvid s' r = true)
    (hact : activationsApproved s' = true) : SafeP s' := by
  have hbe : BudExt s s' := BudExt.of_ids (by rw [hbud])
  refine ⟨by rw [hjobs]; exact hS.jobIds, hrelIds, by rw [hbud]; exact hS.budIds, happIds, hchIds,
    hrelOk, hchOk, ?_, ?_, hact, by rw [hbud]; exact hS.bud, ?_, ?_⟩
  · intro x hx
    rw [hjobs] at hx
    obtain ⟨h1, h2, h3⟩ := hS.jobs x hx
    exact ⟨h1, jobPinned_ext' hre hbe h2, par_ext hre h2 h3⟩
  · exact evid_of hS.evid (termKept_append [] (by rw [hjobs]; simp)) hre hcon hnew
  · rw [liveOfClass_eq_of_jobs hjobs, hcfg]; exact hS.llm
  · rw [liveOfClass_eq_of_jobs hjobs, hcfg]; exact hS.cont

end Factory.Contracts
