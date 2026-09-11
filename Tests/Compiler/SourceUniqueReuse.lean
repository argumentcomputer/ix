import Ix.Compiler.UniqueReuse.Rejections

/-! Fresh-process source unique reversal artifacts and static unique reuse observations. -/

open Lean Ix.Compiler.UniqueReuse.Examples

def main (args : List String) : IO UInt32 := do
  let output : Option System.FilePath ← match args with
    | [] => pure none
    | [path] => pure (some path)
    | _ =>
        IO.eprintln "usage: lake exe compiler-source-unique-reuse [new-output-directory]"
        return 2
  try
    if let some path := output then
      if ← path.pathExists then throw (IO.userError "source-unique-reuse requires a new output directory")
    let (results, checks) ← match runAll with
      | .error message => throw (IO.userError message)
      | .ok value => pure value
    if let some path := output then
      IO.FS.createDirAll path
      for result in results do
        IO.FS.writeFile (path / s!"{result.name}.json") (result.snapshot.pretty 100 ++ "\n")
      IO.FS.writeFile (path / "report.json") ((report results checks).pretty 100 ++ "\n")
    IO.println s!"source-unique-reuse ok: {results.length} Ixon reversals, {checks.length} policy/rejection checks; values, reservation prefixes, costs, and reclamation agree"
    return 0
  catch error =>
    IO.eprintln s!"source-unique-reuse: {error}"
    return 1
