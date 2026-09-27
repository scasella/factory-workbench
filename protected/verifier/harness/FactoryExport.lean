import Factory.Codec
import FactoryPkg.Package
import FactoryPkg.Planner
/-
  FIXED package-runtime wrapper (protected). Exports the package's workflow
  definitions through the shared codec and serves the pure planner over
  JSONL. It cannot spawn work or touch state: it only maps views to lists.
-/
open Factory Factory.Json Factory.Codec

def serve : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let r : Except Err PlannerView := parse line.trimRight >>= dec
    match r with
    | .ok v => stdout.putStrLn (enc (FactoryPkg.plan v)).compress
    | .error m => stdout.putStrLn (J.obj [("error", .str m)]).compress
    stdout.flush

def main (args : List String) : IO UInt32 := do
  match args with
  | ["export"] => IO.println (enc FactoryPkg.workflows).compress; return 0
  | ["plan"] => serve; return 0
  | _ => IO.eprintln "usage: factory-package export|plan"; return 2
