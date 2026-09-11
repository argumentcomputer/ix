import Ix.Compiler.Borrow.Report

open Lean Ix.Compiler

private def writeJson (path : System.FilePath) (json : Json) : IO Unit :=
  IO.FS.writeFile path (json.pretty 100 ++ "\n")

def main (args : List String) : IO UInt32 := do
  let [directory] := args
    | IO.eprintln "usage: lake exe compiler-source-borrow <new-output-directory>"
      return 2
  try
    let directory : System.FilePath := directory
    if ← directory.pathExists then throw (IO.userError "source-borrow requires a new output directory")
    let mut results := #[]
    for depth in [:9] do
      for successorCase in [false, true] do
        results := results.push (← Borrow.runCase depth successorCase)
    if !IxIR2.Borrow.Examples.guards.all (·.2) then
      throw (IO.userError "borrow ownership or resource rejection guard failed")
    IO.FS.createDirAll directory
    for result in results do writeJson (directory / s!"{result.name}.json") result.snapshot
    writeJson (directory / "report.json") (Json.mkObj [
      ("format", toJson "compilatrix/source-borrow/1"),
      ("policy", toJson "closed-scalar-borrow/1"),
      ("peak_policy", toJson "nonincreasing-peak-live-heap-nodes"),
      ("cases", toJson (results.map (·.row))),
      ("negative_guards", toJson IxIR2.Borrow.Examples.guards)])
    let compileMs := results.foldl (fun total result => total + result.compileMs) 0
    let borrowMs := results.foldl (fun total result => total + result.borrowMs) 0
    IO.println s!"source-borrow ok: {results.size} accepted Ixon cases; RC 5 -> 3, peak 2, full reclamation; compile {compileMs} ms, borrow checks {borrowMs} ms"
    return 0
  catch error =>
    IO.eprintln s!"source-borrow: {error}"
    return 1
