import Ix.Compiler.Recursion.Rejections

/-! Source-driven recursion, loop, and reuse checks. An optional new output
directory receives complete program snapshots for the fresh-process gate. -/

open Ix.Compiler.Recursion.Examples

def main (args : List String) : IO UInt32 := do
  let output : Option System.FilePath ← match args with
    | [] => pure none
    | [path] => pure (some path)
    | _ =>
        IO.eprintln "usage: lake exe compiler-source-recursion [new-output-directory]"
        return 2
  try
    if let some path := output then
      if ← path.pathExists then throw (IO.userError "source-recursion requires a new output directory")
    let (results, rejections) ← match runAll with
      | .ok value => pure value
      | .error message => throw (IO.userError message)
    if let some path := output then
      IO.FS.createDirAll path
      for result in results do
        IO.FS.writeFile (path / s!"{result.name}.json") (result.snapshot.pretty 100 ++ "\n")
      IO.FS.writeFile (path / "report.json") ((report results rejections).pretty 100 ++ "\n")
    IO.println s!"source-recursion ok: {results.length} Ixon cases, {rejections.length} rejection/fallback checks; values agree and every heap reclaims"
    return 0
  catch error =>
    IO.eprintln s!"source-recursion: {error}"
    return 1
