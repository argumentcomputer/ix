import Ix.Compiler.UniqueReuse.NativeObservations

/-! Emit complete Ixon-to-native artifacts into a fresh output directory. -/

open Lean Ix.Compiler.UniqueReuse.Native.Examples

def main (args : List String) : IO UInt32 := do
  let output : Option System.FilePath ← match args with
    | [] => pure none
    | [path] => pure (some path)
    | _ => IO.eprintln "usage: lake exe compiler-source-native-unique [new-output-directory]"; return 2
  try
    if let some path := output then
      if ← path.pathExists then throw (IO.userError "source-native-unique requires a new output directory")
    let results ← match cases.mapM fun (name, values) => runCase name values with
      | .ok results => pure results
      | .error reason => throw (IO.userError reason)
    let rejected ← match rejections with
      | .ok results => pure results
      | .error reason => throw (IO.userError reason)
    if let some path := output then
      IO.FS.createDirAll path
      for result in results do
        IO.FS.writeFile (path / s!"{result.name}.json") (result.snapshot.pretty 100 ++ "\n")
        IO.FS.writeBinFile (path / s!"{result.name}-main.o") result.mainObject
        IO.FS.writeBinFile (path / s!"{result.name}-release.o") result.releaseObject
      IO.FS.writeFile (path / "report.json") ((report results rejected).pretty 100 ++ "\n")
    IO.println s!"source-native-unique ok: {results.length} Ixon reversals, main/release ELF pairs, byte-memory observations, {rejected.size} checked native fallbacks"
    return 0
  catch error =>
    IO.eprintln s!"source-native-unique: {error}"
    return 1
