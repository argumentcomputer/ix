import Ix.Compiler.Coverage.UpstreamNative

open Lean Ix.Compiler Ix.Compiler.Coverage

def main (args : List String) : IO UInt32 := do
  try
    let (directory, name) ← match args with
      | [directory] => pure (directory, none)
      | [directory, name] => pure (directory, some name)
      | _ => throw (IO.userError "usage: lake exe compiler-source-native-upstream <new-output-directory> [upstream-name]")
    let directory : System.FilePath := directory
    if ← directory.pathExists then throw (IO.userError "source-native-upstream requires a fresh output directory")
    let cases ← if let some name := name then do
        let some fixture := Upstream.fixtures.find? (fun fixture => fixture.name == name) |
          throw (IO.userError "unknown upstream entry")
        let .ok result := (← Upstream.load Upstream.directory fixture).bind UpstreamNative.run |
          throw (IO.userError "upstream source/native compilation failed")
        pure [result]
      else do
        let .ok cases ← UpstreamNative.cases | throw (IO.userError "upstream source/native compilation failed")
        pure cases
    IO.FS.createDirAll directory
    for result in cases do
      IO.FS.writeFile (directory / s!"{result.name}.json") (result.snapshot.pretty 100 ++ "\n")
      if let some bytes := result.object then IO.FS.writeBinFile (directory / s!"{result.name}.o") bytes
    let report := Json.mkObj [("format", toJson "compilatrix/source-native-upstream-report/1"),
      ("policy", toJson UpstreamNative.policy), ("cases", toJson (cases.map CaseResult.row))]
    IO.FS.writeFile (directory / "report.json") (report.pretty 100 ++ "\n")
    IO.println s!"source-native-upstream ok: {cases.length} unchanged upstream entries, {cases.countP (·.object.isSome)} checked computational objects"
    return 0
  catch error =>
    IO.eprintln s!"source-native-upstream: {error}"
    return 1
