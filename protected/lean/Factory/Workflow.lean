import Factory.Types
/-
  Factory.Workflow — fixed workflow well-formedness, mandatory-role policy
  and planner contract checks. Executable definitions used at runtime by the
  kernel AND referenced by the proof contracts (Contracts.lean).
-/
namespace Factory

/-- Step IDs a step semantically consumes. -/
def StepSpec.inputSteps (s : StepSpec) : List StepId :=
  s.inputs.filterMap (fun b => match b.source with
    | .stepOutput p => some p
    | .jobInput => none)

/-- All prerequisites: ordering edges plus semantic input producers. -/
def StepSpec.prereqs (s : StepSpec) : List StepId := s.after ++ s.inputSteps

def WorkflowDef.ids (w : WorkflowDef) : List StepId := w.steps.map (·.id)

def WorkflowDef.find? (w : WorkflowDef) (id : StepId) : Option StepSpec :=
  w.steps.find? (·.id == id)

def WorkflowDef.stepsWithRole (w : WorkflowDef) (r : Role) : List StepSpec :=
  w.steps.filter (·.role == r)

/-- Listed order must be a topological order: every prerequisite of a step
    appears strictly earlier, and IDs are unique. This implies acyclicity. -/
def topoOk : List StepId → List StepSpec → Bool
  | _, [] => true
  | seen, s :: rest =>
      s.prereqs.all (fun p => seen.contains p) && !(seen.contains s.id) &&
      topoOk (s.id :: seen) rest

/-- Publication-gate roles fixed by the protected kernel. -/
def requiredRoles : JobKind → List Role
  | .packageAudit => [.build, .prove, .reproduce, .refute]
  | .changeEvaluate => [.build, .prove, .reproduce, .refute]
  | .changeAuthor => [.author, .materialize]

/-- Roles permitted in a workflow of each kind. -/
def allowedRoles : JobKind → List Role
  | .packageAudit => [.build, .prove, .reproduce, .refute, .summarize]
  | .changeEvaluate => [.build, .prove, .reproduce, .refute, .summarize]
  | .changeAuthor => [.author, .materialize]

def WorkflowDef.uniqueRole (w : WorkflowDef) (r : Role) : Option StepSpec :=
  match w.stepsWithRole r with
  | [s] => some s
  | _ => none

def StepSpec.consumes (s : StepSpec) (p : StepId) : Bool := s.inputSteps.contains p

/-- Subject/independence bindings for evaluation-style workflows:
    * build consumes the job input (the frozen candidate / fixture);
    * prove, reproduce and refute each consume build's output (the payload);
    * reproduce and refute never consume each other's output;
    * summarize consumes nothing but review outputs is allowed. -/
def evalBindingsOk (w : WorkflowDef) : Bool :=
  match w.uniqueRole .build, w.uniqueRole .prove, w.uniqueRole .reproduce, w.uniqueRole .refute with
  | some b, some p, some rp, some rf =>
      b.inputs.any (fun i => i.source == .jobInput) &&
      p.consumes b.id && rp.consumes b.id && rf.consumes b.id &&
      !(rp.consumes rf.id) && !(rf.consumes rp.id) &&
      -- reviewers must not consume the summary either
      (w.stepsWithRole .summarize).all (fun sm => !(rp.consumes sm.id) && !(rf.consumes sm.id))
  | _, _, _, _ => false

def authorBindingsOk (w : WorkflowDef) : Bool :=
  match w.uniqueRole .author, w.uniqueRole .materialize with
  | some a, some m => a.inputs.any (fun i => i.source == .jobInput) && m.consumes a.id
  | _, _ => false

def WorkflowDef.bindingsOk (w : WorkflowDef) : Bool :=
  match w.kind with
  | .changeAuthor => authorBindingsOk w
  | _ => evalBindingsOk w

/-- Fixed well-formedness check (runtime AND proof contract P01). -/
def wellFormedWorkflow (w : WorkflowDef) : Bool :=
  !w.steps.isEmpty &&
  w.maxParallel ≥ 1 &&
  topoOk [] w.steps &&
  w.steps.all (fun s => (allowedRoles w.kind).contains s.role) &&
  (requiredRoles w.kind).all (fun r => (w.stepsWithRole r).length == 1) &&
  w.bindingsOk

/-- A release's export list: exactly one well-formed workflow per kind. -/
def exportsOk (ws : List WorkflowDef) : Bool :=
  [JobKind.packageAudit, .changeAuthor, .changeEvaluate].all
    (fun k => (ws.filter (·.kind == k)).length == 1) &&
  ws.all wellFormedWorkflow

def workflowFor (ws : List WorkflowDef) (k : JobKind) : Option WorkflowDef :=
  ws.find? (·.kind == k)

/-! ### Planner contract (runtime check; the Prop form lives in Contracts) -/

/-- `p` is a sublist of `l` (order-preserving subsequence). -/
def isSublist : List StepId → List StepId → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x == y then isSublist xs ys else isSublist (x :: xs) ys

def noDupB : List StepId → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && noDupB xs

/-- Runtime planner-output check applied by the kernel before any dispatch. -/
def planOkB (v : PlannerView) (p : List StepId) : Bool :=
  isSublist p v.ready && noDupB p && p.length ≤ v.slots &&
  (v.ready.isEmpty || v.slots == 0 || !p.isEmpty)

/-! ### Static step identity (for migration compatibility) -/

def assetDigest (assets : List Asset) (path : String) : Option Digest :=
  if path == "" then some "" else (assets.find? (·.path == path)).map (·.digest)

structure StaticId where
  role   : Role
  inputs : List InputBinding
  prompt : Option Digest
  deriving DecidableEq, Repr

def staticId (assets : List Asset) (s : StepSpec) : StaticId :=
  { role := s.role, inputs := s.inputs, prompt := assetDigest assets s.prompt }

/-- Ordering-only compatibility between two workflows (migration family (a)):
    same step IDs in the same order, same roles/inputs/prompts, only ordering
    edges and maxParallel may differ. -/
def orderingOnlyCompatible (old new : WorkflowDef) : Bool :=
  old.kind == new.kind &&
  old.steps.length == new.steps.length &&
  (old.steps.zip new.steps).all (fun (a, b) =>
    a.id == b.id && a.role == b.role && a.inputs == b.inputs && a.prompt == b.prompt)

def exportsOrderingOnlyCompatible (old new : List WorkflowDef) : Bool :=
  [JobKind.packageAudit, .changeAuthor, .changeEvaluate].all (fun k =>
    match workflowFor old k, workflowFor new k with
    | some a, some b => orderingOnlyCompatible a b
    | _, _ => false)

/-- Required publication roles of `old` are all still required and bound in `new`. -/
def gatesRetained (old new : List WorkflowDef) : Bool :=
  [JobKind.packageAudit, .changeAuthor, .changeEvaluate].all (fun k =>
    match workflowFor old k, workflowFor new k with
    | some a, some b =>
        (requiredRoles k).all (fun r =>
          (a.stepsWithRole r).length == 1 && (b.stepsWithRole r).length == 1) &&
        b.bindingsOk
    | _, _ => false)

end Factory
