import IxCCTests.Lam.Eval
import IxCCTests.Lam.Erase
import IxCCTests.Lam.EvaluationOrder
import IxCCTests.Lam.Differential
import IxCCTests.Lam.Mutation
import IxCCTests.Lam.KernelEval
import IxCCTests.Lam.KernelK1.Fib

/-! The `tests-lam` suite (design note 02 §4–5, §13): Lam's rules and clock
monotonicity; erasure on synthetic programs; SrcEval against Lam on
`k1.ixe`, the bench-k1 closures (roots and first-order constants) and
`src-sortpoly`; Lam against native Lean and the bench-k1 entries at their
test sizes; annotation mutation through erasure; erased sizes. `--entry
NAME` runs one bench entry through Lam (the child process of the deep
`sum-loop` run). Building the suite also evaluates erasure in the kernel
(`IxCCTests.Lam.KernelEval`) and the front end's recheck path with
erasure on the fib bench-k1 artifact (`IxCCTests.Lam.KernelK1.Fib`;
`IxCCTests.Lam.KernelK1` adds tak and gcd). -/

namespace IxCCTests.Lam.Run

open IxCCTests.Src

def part (a : Assert) (label : String) (action : IO Unit) : IO Unit := do
  let before ← a.get
  let ((), ms) ← timed action
  IO.println s!"  {label}: {(← a.get) - before} assertions, {ms} ms"
  (← IO.getStdout).flush

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--entry", name] =>
    IO.println (← Differential.runEntry name)
    return 0
  | _ => pure ()
  let a ← IO.mkRef 0
  try
    IO.println "tests-lam"
    if args == ["--only", "evaluation-order"] then
      part a "synthetic rechecked evaluation order" (EvaluationOrder.run a)
      IO.println s!"tests-lam: {← a.get} assertions passed"
      return 0
    part a "Lam rules and clock monotonicity" (Eval.run a)
    part a "erasure on synthetic programs" do
      for line in ← Erase.run a do IO.println s!"    {line}"
    part a "synthetic rechecked evaluation order" (EvaluationOrder.run a)
    part a "SrcEval against Lam on k1.ixe and bench-k1" do
      for line in ← Differential.packs a do IO.println s!"    {line}"
    part a "src-sortpoly" do
      for line in ← Differential.sortpoly a do IO.println s!"    {line}"
    part a "fallback route (recursors at run time)" do
      for line in ← Differential.fallback a do IO.println s!"    {line}"
    part a "least clocks on the K1 roots" do
      for line in ← Differential.leastClocks a do IO.println s!"    {line}"
    part a "Lam against native Lean" (Differential.native a)
    part a "bench-k1 entries through Lam" do
      for line in ← Differential.bench a (← IO.appPath) do IO.println s!"    {line}"
    part a "erased sizes (entry roots)" do
      for line in ← Differential.benchSizes a do IO.println s!"    {line}"
    part a "annotation mutation through erasure" do
      for line in ← Mutation.run a do IO.println s!"    {line}"
    IO.println s!"tests-lam: {← a.get} assertions passed"
    return 0
  catch e =>
    IO.eprintln s!"tests-lam: FAILED after {← a.get} assertions: {e}"
    return 1

end IxCCTests.Lam.Run
