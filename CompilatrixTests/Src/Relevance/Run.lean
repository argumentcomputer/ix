import CompilatrixTests.Src.Relevance.Checker
import CompilatrixTests.Src.Relevance.Census
import CompilatrixTests.Src.Relevance.Mutation

/-! The `tests-relevance` suite (design note 02 §3, §13): checker rules on
synthetic programs, the census on `k1.ixe`, and annotation mutation on the
bench-k1 closures. `--report PATH` writes the census JSON. -/

namespace CompilatrixTests.Src.Relevance.Run

open CompilatrixTests.Src

def part (a : Assert) (label : String) (action : IO Unit) : IO Unit := do
  let before ← a.get
  let ((), ms) ← timed action
  IO.println s!"  {label}: {(← a.get) - before} assertions, {ms} ms"
  (← IO.getStdout).flush

def main (args : List String) : IO UInt32 := do
  let reportPath := match args with
    | ["--report", path] => some (System.FilePath.mk path)
    | _ => none
  let a ← IO.mkRef 0
  try
    IO.println "tests-relevance"
    part a "checker rules" (Checker.run a)
    part a "census on k1.ixe" do
      for line in ← Census.run a reportPath do IO.println s!"    {line}"
    part a "annotation mutation" do
      for line in ← Mutation.run a do IO.println s!"    {line}"
    IO.println s!"tests-relevance: {← a.get} assertions passed"
    return 0
  catch e =>
    IO.eprintln s!"tests-relevance: FAILED after {← a.get} assertions: {e}"
    return 1

end CompilatrixTests.Src.Relevance.Run
