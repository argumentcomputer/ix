import Ix.Compiler.UniqueReuse.RuntimeObservations

open Ix.Compiler.UniqueReuse.Runtime.Native.Examples

def main (args : List String) : IO UInt32 := do
  let (foldCounters, output) : Bool × Option System.FilePath ← match args with
    | [] => pure (false, none)
    | ["--counter-fold"] => pure (true, none)
    | [path] => pure (false, some path)
    | ["--counter-fold", path] => pure (true, some path)
    | _ => IO.eprintln "usage: lake exe compiler-source-native-runtime [--counter-fold] [new-output-directory]"; return 2
  try
    if let some path := output then
      if ← path.pathExists then throw (IO.userError "source-native-runtime requires a new output directory")
    let result ← match run foldCounters with
      | .ok result => pure result
      | .error reason => throw (IO.userError reason)
    if let some path := output then
      IO.FS.createDirAll path
      IO.FS.writeFile (path / "pipeline.json") (result.pipeline.pretty 100 ++ "\n")
      IO.FS.writeBinFile (path / "main.o") result.mainObject
      IO.FS.writeBinFile (path / "release.o") result.releaseObject
      for (name, snapshot) in result.cases do
        IO.FS.writeFile (path / s!"{name}.json") (snapshot.pretty 100 ++ "\n")
      IO.FS.writeFile (path / "report.json") (result.report.pretty 100 ++ "\n")
    IO.println s!"source-native-runtime ok: one compiled function, one ELF pair, {result.cases.length} runtime inputs and complete reclamation"
    return 0
  catch error =>
    IO.eprintln s!"source-native-runtime: {error}"
    return 1
