import Factory.Kernel
import Factory.Codec
import Factory.Check
/-
  Factory.Main — fixed executable wrapper around the proved kernel.
  Request/response are single strict-JSON documents (versioned "v":"1").
  `--serve` processes one request per line until EOF (used by the coordinator
  to avoid process start-up per command; each request is independent and
  carries the full state — the wrapper keeps no state between requests).
-/
open Factory Factory.Json Factory.Codec

namespace Factory.Main

def protocolVersion : String := "1"

def okResp (kvs : List (String × J)) : J := .obj (("v", .str protocolVersion) :: ("ok", .bool true) :: kvs)
def errResp (kind code msg : String) : J :=
  .obj [("v", .str protocolVersion), ("ok", .bool false), ("error", .str kind), ("code", .str code),
        ("message", .str msg)]

def decField {α} [Dec α] (f : String → J) (n : String) : Except Err α := dec (f n)

def previewJ (s : State) (j : Job) (t : Release) : J :=
  let p := migrationPreview s j t
  .obj [("can_migrate", .bool (canMigrateB s j t && s.wasActivated t.digest)),
        ("activated", .bool (s.wasActivated t.digest)),
        ("revision", enc j.revision), ("from", enc j.release), ("to", enc t.digest),
        ("kept", enc p.kept), ("reset", enc p.reset), ("retired", enc p.retired),
        ("reasons", enc p.reasons)]

def handle (req : J) : J :=
  let r : Except Err J := do
    let kvs ← req.getObj
    let op ← match kvs.find? (·.1 == "op") with
      | some (_, .str o) => pure o
      | _ => throw "missing op"
    match kvs.find? (·.1 == "v") with
    | some (_, .str v) => if v != protocolVersion then throw s!"unsupported protocol version {v}"
    | _ => throw "missing v"
    match op with
    | "version" =>
      let _ ← fields req ["v", "op"]
      return okResp [("kernel", .str "factory-kernel"), ("protocol", .str protocolVersion)]
    | "initial" =>
      let _ ← fields req ["v", "op"]
      return okResp [("state", enc emptyState)]
    | "apply" =>
      let f ← fields req ["v", "op", "state", "envelope"]
      let s : State ← decField f "state"
      let e : Envelope ← decField f "envelope"
      match Factory.apply s e with
      | .ok t => return okResp [("accepted", .bool true), ("transition", enc t)]
      | .error rj => return okResp [("accepted", .bool false), ("reject", .str rj.code)]
    | "ready" =>
      let f ← fields req ["v", "op", "state", "job"]
      let s : State ← decField f "state"
      let jid : String ← decField f "job"
      match s.findJob? jid with
      | none => throw "unknown job"
      | some j =>
        return okResp [("ready", enc (readySteps s j)), ("slots", enc (plannerSlots s j)),
                       ("workflow", enc (s.workflowOf j))]
    | "check_plan" =>
      let f ← fields req ["v", "op", "view", "plan"]
      let v : PlannerView ← decField f "view"
      let p : List StepId ← decField f "plan"
      return okResp [("plan_ok", .bool (planOkB v p))]
    | "validate_workflows" =>
      let f ← fields req ["v", "op", "workflows"]
      let ws : List WorkflowDef ← decField f "workflows"
      return okResp [("exports_ok", .bool (exportsOk ws)),
                     ("each", enc (ws.map wellFormedWorkflow))]
    | "canonical" =>
      -- decode + re-encode: used for golden-vector and codec round-trip checks
      let f ← fields req ["v", "op", "kind", "value"]
      let k : String ← decField f "kind"
      match k with
      | "state" => let s : State ← decField f "value"; return okResp [("value", enc s)]
      | "envelope" => let e : Envelope ← decField f "value"; return okResp [("value", enc e)]
      | "workflows" => let w : List WorkflowDef ← decField f "value"; return okResp [("value", enc w)]
      | _ => throw "unknown canonical kind"
    | "migration_preview" =>
      let f ← fields req ["v", "op", "state", "job", "target"]
      let s : State ← decField f "state"
      let jid : String ← decField f "job"
      let tgt : String ← decField f "target"
      match s.findJob? jid, s.findRelease? tgt with
      | some j, some t => return okResp [("preview", previewJ s j t)]
      | _, _ => throw "unknown job or target"
    | "invariants" =>
      let f ← fields req ["v", "op", "state"]
      let s : State ← decField f "state"
      let vs := Factory.Check.violations s
      return okResp [("safe", .bool vs.isEmpty), ("violations", enc vs)]
    | "replay" =>
      let f ← fields req ["v", "op", "state", "envelopes"]
      let s : State ← decField f "state"
      let es : List Envelope ← decField f "envelopes"
      return okResp [("state", enc (Factory.replay s es))]
    | other => throw s!"unknown op '{other}'"
  match r with
  | .ok j => j
  | .error m => errResp "bad_request" "BAD_REQUEST" m

def processLine (line : String) : String :=
  match parse line with
  | .ok j => (handle j).compress
  | .error m => (errResp "bad_request" "BAD_JSON" m).compress

end Factory.Main

open Factory.Main in
def main (args : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  if args == ["--serve"] then
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      stdout.putStrLn (processLine (line.trimRight))
      stdout.flush
    return 0
  else if args.isEmpty then
    let input ← stdin.readToEnd
    stdout.putStrLn (processLine input.trimRight)
    return 0
  else
    IO.eprintln "usage: factory-kernel [--serve]  (JSON request on stdin)"
    return 2
