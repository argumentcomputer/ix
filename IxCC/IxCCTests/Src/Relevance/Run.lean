import IxCCTests.Src.Relevance.Checker
import IxCCTests.Src.Relevance.Census
import IxCCTests.Src.Relevance.Mutation
import IxCCTests.Src.Relevance.Stuck

/-! The `tests-relevance` suite: checker rules on
synthetic programs, the census on `k1.ixe`, annotation mutation on the
bench-k1 closures, and the stuck-cause census on `k1.ixe`, bench-k1 and
`src-sortpoly`. `--report PATH` writes the census JSON and
`--stuck-report PATH` the stuck-cause census JSON. -/

namespace IxCCTests.Src.Relevance.Run

open IxCCTests.Src

def part (a : Assert) (label : String) (action : IO Unit) : IO Unit := do
  let before ← a.get
  let ((), ms) ← timed action
  IO.println s!"  {label}: {(← a.get) - before} assertions, {ms} ms"
  (← IO.getStdout).flush

def main (args : List String) : IO UInt32 := do
  let flag := fun (name : String) =>
    match args.dropWhile (· != name) with
    | _ :: path :: _ => some (System.FilePath.mk path)
    | _ => none
  let reportPath := flag "--report"
  let stuckPath := flag "--stuck-report"
  let a ← IO.mkRef 0
  try
    IO.println "tests-relevance"
    part a "checker rules" (Checker.run a)
    part a "census on k1.ixe" do
      for line in ← Census.run a reportPath do IO.println s!"    {line}"
    part a "annotation mutation" do
      for line in ← Mutation.run a do IO.println s!"    {line}"
    part a "stuck-cause census" do
      for line in ← Stuck.run a stuckPath do IO.println s!"    {line}"
    IO.println s!"tests-relevance: {← a.get} assertions passed"
    return 0
  catch e =>
    IO.eprintln s!"tests-relevance: FAILED after {← a.get} assertions: {e}"
    return 1

end IxCCTests.Src.Relevance.Run
