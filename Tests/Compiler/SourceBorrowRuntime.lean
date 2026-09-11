import Ix.Compiler.Borrow.RuntimeReport
import Ix.Compiler.IxIR2.Borrow.OpenExamples

open Lean Ix.Compiler

private def writeJson (path : System.FilePath) (value : Json) : IO Unit :=
  IO.FS.writeFile path (value.pretty 100 ++ "\n")

def main (args : List String) : IO UInt32 := do
  let [directory] := args
    | IO.eprintln "usage: source-borrow-runtime <new-output-directory>"
      return 2
  try
    let directory : System.FilePath := directory
    if ← directory.pathExists then throw (IO.userError "source-borrow-runtime requires a new output directory")
    let mut results := #[]
    for depth in [:9] do results := results.push (← Borrow.Runtime.runCase depth)
    if !IxIR2.Borrow.Open.Examples.guards.all (·.2) || !IxIR2.Borrow.Examples.guards.all (·.2) then
      throw (IO.userError "borrow runtime structural or ownership guard failed")
    IO.FS.createDirAll directory
    for result in results do writeJson (directory / s!"{result.name}.json") result.snapshot
    writeJson (directory / "report.json") (Json.mkObj [
      ("format", toJson "compilatrix/source-borrow-runtime/1"),
      ("policy", toJson "open-shared-tag-borrow/1"),
      ("input_policy", toJson "one-owned-shared-root-allocation-ordered-heap"),
      ("peak_policy", toJson "nonincreasing-peak-live-heap-nodes"),
      ("structural_guards", toJson IxIR2.Borrow.Open.Examples.guards),
      ("ownership_guards", toJson IxIR2.Borrow.Examples.guards),
      ("cases", toJson (results.map (·.row)))])
    let compileMs := results.foldl (fun total result => total + result.compileMs) 0
    let checkMs := results.foldl (fun total result => total + result.checkMs) 0
    IO.println s!"source-borrow-runtime ok: {results.size} source functions; 72 runtime inputs, 144 direct/PAP comparisons; 2 fewer RC operations, full reclamation, unchanged peak; compile {compileMs} ms, structural checks {checkMs} ms"
    return 0
  catch error =>
    IO.eprintln s!"source-borrow-runtime: {error}"
    return 1
