import Factory
/-
  Concrete counterexample for the literal statement of K08 (PinningPreserved).
  Runs the EXECUTED kernel (`Factory.apply`) from `emptyState` through an
  accepted trace that ends with an accepted `migrateJob`.
  Run: lake env lean Scratch/k08_counterexample.lean
-/
open Factory Factory.Check

def dg (c : Char) : String := String.ofList (List.replicate 64 c)

def bi (n : String) (src : InputSource) : InputBinding := { name := n, source := src }

def evalSteps : List StepSpec :=
  [ { id := "build", role := .build, after := [], inputs := [bi "in" .jobInput], prompt := "", retries := 0 },
    { id := "prove", role := .prove, after := [], inputs := [bi "p" (.stepOutput "build")], prompt := "", retries := 0 },
    { id := "reproduce", role := .reproduce, after := [], inputs := [bi "p" (.stepOutput "build")], prompt := "", retries := 0 },
    { id := "refute", role := .refute, after := [], inputs := [bi "p" (.stepOutput "build")], prompt := "", retries := 0 } ]

def wPA : WorkflowDef := { kind := .packageAudit, steps := evalSteps, maxParallel := 4 }
def wCE : WorkflowDef := { kind := .changeEvaluate, steps := evalSteps, maxParallel := 4 }
def wCA : WorkflowDef :=
  { kind := .changeAuthor, maxParallel := 2,
    steps := [ { id := "author", role := .author, after := [], inputs := [bi "req" .jobInput], prompt := "", retries := 0 },
               { id := "materialize", role := .materialize, after := [], inputs := [bi "a" (.stepOutput "author")], prompt := "", retries := 0 } ] }

def ws : List WorkflowDef := [wPA, wCA, wCE]

def genesis : Release :=
  { digest := dg 'a', payload := dg 'b', source := dg 'c', parent := none, contract := "", workflows := ws,
    assets := [], evidenceJob := none, producer := none }

def cfg : Config := { llmSlots := 4, containerSlots := 4, leaseTicks := 100, maxJobs := 10, maxSteps := 10 }

def res (fp : Digest) (produced : Option Digest) (exports : List WorkflowDef) (contract : Digest) : ResultEnvelope :=
  { result := dg '9', modelOutcome := .pass, trustedOutcome := .pass, produced := produced, exports := exports,
    contract := contract, fingerprint := fp }

def op : Actor := .operator "alice"
def env (a : Actor) (tick : Nat) (c : Command) : Envelope := { actor := a, epoch := 0, tick := tick, cmd := c }

def fp : Digest := dg '1'
def contractD : Digest := dg 'd'

/-- Everything up to (not including) the migration. -/
def trace : List Envelope :=
  [ env op 1 (.bootstrap genesis contractD cfg),
    env op 2 (.createJob "J" .packageAudit (dg 'e') (dg 'e') none "BJ" 10),
    env op 3 (.pauseJob "J"),
    env .coordinator 4 (.acknowledgeQuiescence "J" true),
    env op 5 (.createChange "C" (dg 'f') "A" "BC" 20 1),
    env .coordinator 6 (.startAttempt "A" "author" fp),
    env .supervisor 7 (.commitResult "A" "author" 1 (res fp none [] "")),
    env .coordinator 8 (.startAttempt "A" "materialize" fp),
    env .supervisor 9 (.commitResult "A" "materialize" 2 (res fp (some (dg '3')) [] "")),
    env .coordinator 10 (.registerCandidate "C" "A" "E" (dg '3')),
    env .coordinator 11 (.startAttempt "E" "build" fp),
    env .verifier 12 (.recordVerification "E" "build" 1 (res fp (some (dg '4')) ws contractD)),
    env .coordinator 13 (.startAttempt "E" "prove" fp),
    env .verifier 14 (.recordVerification "E" "prove" 2 (res fp none [] contractD)),
    env .coordinator 15 (.startAttempt "E" "reproduce" fp),
    env .supervisor 16 (.commitResult "E" "reproduce" 3 (res fp none [] "")),
    env .coordinator 17 (.startAttempt "E" "refute" fp),
    env .supervisor 18 (.commitResult "E" "refute" 4 (res fp none [] "")),
    env .coordinator 19 (.publishRelease "E" (dg '5') []),
    env op 20 (.recordApproval "AP" (dg '5') (dg 'a')),
    env op 21 (.activateRelease (dg '5') (dg 'a') "AP") ]

/-- Fold that reports every rejection (a counterexample trace must have none). -/
def run (s : State) : List Envelope → State × List String
  | [] => (s, [])
  | e :: es => match apply s e with
    | .ok t => run t.state es
    | .error r => let (s', errs) := run s es; (s', s!"{reprStr e.cmd |>.take 40}: {r.code}" :: errs)

def s0 : State := (run emptyState trace).1

def jobJ (s : State) : Option (JobId × Digest × Nat × String) :=
  (s.findJob? "J").map (fun j => (j.id, j.release, j.revision, reprStr j.status))

#eval (run emptyState trace).2                   -- expected: [] (every envelope accepted)
#eval violations s0                              -- expected: [] (runtime Safe oracle)
#eval s0.jobs.all (fun j => (j.steps.map (·.id)).Nodup)   -- K02 state part: true
#eval jobJ s0                                    -- J pinned to genesis dg 'a', paused, revision 2

def eMig : Envelope := env op 22 (.migrateJob "J" (dg '5') 2)

#eval match apply s0 eMig with
  | .ok t => s!"ACCEPTED; J after = {reprStr (jobJ t.state)}; violations after = {reprStr (violations t.state)}"
  | .error r => s!"rejected {r.code}"

-- Decidable rendering of the first conjunct of `PinningPreserved`,
-- instantiated at `jid := "J'"` (so `e.cmd ≠ .migrateJob "J'" _ _` holds).
#eval match apply s0 eMig with
  | .ok t => (eMig.cmd != Command.migrateJob "J'" (dg '5') 2,
              s0.jobs.all (fun j => t.state.jobs.any (fun j' => j'.id == j.id && j'.release == j.release)))
  | .error _ => (false, true)
-- expected: (true, false): premise holds, conclusion fails  ⇒  ¬ PinningPreserved s0 eMig t
