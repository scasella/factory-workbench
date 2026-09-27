import Factory.Types
/-
  Orchestration package P1: reproduction and refutation are independent.
  The incidental ordering edge refute-after-reproduce is removed; neither
  review consumes the other's output. Both gates remain mandatory.
-/
namespace FactoryPkg
open Factory

def evalSteps : List StepSpec := [
  { id := "build", role := .build, after := [],
    inputs := [{ name := "candidate", source := .jobInput }], prompt := "", retries := 1 },
  { id := "prove", role := .prove, after := [],
    inputs := [{ name := "payload", source := .stepOutput "build" }], prompt := "", retries := 1 },
  { id := "reproduce", role := .reproduce, after := [],
    inputs := [{ name := "payload", source := .stepOutput "build" },
               { name := "proof", source := .stepOutput "prove" }],
    prompt := "prompts/reproduce.md", retries := 2 },
  { id := "refute", role := .refute, after := [],
    inputs := [{ name := "payload", source := .stepOutput "build" },
               { name := "proof", source := .stepOutput "prove" }],
    prompt := "prompts/refute.md", retries := 2 },
  { id := "summarize", role := .summarize, after := [],
    inputs := [{ name := "reproduction", source := .stepOutput "reproduce" },
               { name := "refutation", source := .stepOutput "refute" }],
    prompt := "prompts/summarize.md", retries := 2 }
]

def auditWorkflow : WorkflowDef := { kind := .packageAudit, steps := evalSteps, maxParallel := 2 }
def evaluateWorkflow : WorkflowDef := { kind := .changeEvaluate, steps := evalSteps, maxParallel := 2 }

def authorWorkflow : WorkflowDef := {
  kind := .changeAuthor, maxParallel := 1,
  steps := [
    { id := "author", role := .author, after := [],
      inputs := [{ name := "request", source := .jobInput }], prompt := "prompts/author.md", retries := 1 },
    { id := "materialize", role := .materialize, after := [],
      inputs := [{ name := "proposal", source := .stepOutput "author" }], prompt := "", retries := 0 }
  ] }

def workflows : List WorkflowDef := [auditWorkflow, authorWorkflow, evaluateWorkflow]

end FactoryPkg
