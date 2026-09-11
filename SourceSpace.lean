import Compilatrix.CallReuse.SpaceObservations

open Lean Compilatrix.CallReuse.SpaceExamples

def main (args : List String) : IO UInt32 := do
  let output : Option System.FilePath ← match args with
    | [] => pure none
    | [path] => pure (some path)
    | _ => IO.eprintln "usage: source-space [new-output-directory]"; return 2
  try
    if let some path := output then
      if ← path.pathExists then throw (IO.userError "source-space requires a new output directory")
    let (results, checks) ← match runAll with
      | .error message => throw (IO.userError message)
      | .ok value => pure value
    if let some path := output then
      IO.FS.createDirAll path
      for result in results do
        IO.FS.writeFile (path / s!"{result.name}.json") (result.snapshot.pretty 100 ++ "\n")
      IO.FS.writeFile (path / "report.json") ((report results checks).pretty 100 ++ "\n")
    IO.println s!"source-space ok: {results.length} Ixon maps, {checks.length} boundaries; finite capacities, suspended reservations, and complete reclamation"
    return 0
  catch error =>
    IO.eprintln s!"source-space: {error}"
    return 1
