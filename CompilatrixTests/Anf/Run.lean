import CompilatrixTests.Anf.Eval
import CompilatrixTests.Anf.Differential
import CompilatrixTests.Anf.Shapes
import CompilatrixTests.Anf.Generated
import CompilatrixTests.Anf.KernelEval

/-! The `tests-anf` suite (design note 02 §6–8, §13): Anf's rules and clock
monotonicity; Lam against Anf after every step of the Phase 1 pipeline on
every root and first-order constant of `k1.ixe` and the bench-k1 closures
(readback, traps, the timeout clause, tick dominance, `WellScoped`); the K1
shape expectations, certificate replay and shrink idempotence, sizes and
least clocks; the bench-k1 entries at their test sizes through the
pipeline's output (`sum-loop` 10⁶ in a child process with a larger stack);
generated Lam programs under random oracles. `--entry NAME` runs one bench
entry (the child-process mode); `--dump NAME` prints a bench entry's Anf
after every step. Building the suite also runs the passes in the kernel
(`CompilatrixTests.Anf.KernelEval`). -/

namespace CompilatrixTests.Anf.Run

open CompilatrixTests.Src

def part (a : Assert) (label : String) (action : IO Unit) : IO Unit := do
  let before ← a.get
  let ((), ms) ← timed action
  IO.println s!"  {label}: {(← a.get) - before} assertions, {ms} ms"
  (← IO.getStdout).flush

def stages : Differential.Stages := fun L => do
  let t ← Compilatrix.Anf.Pipeline.produce {} L
  return t.stages.zipIdx.map fun ((n, P), i) => (s!"{i}:{n}", P)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--entry", name] =>
    IO.println (← Shapes.runEntry name)
    return 0
  | ["--dump", name] =>
    let l ← loadBench name
    let e ← CompilatrixTests.Lam.eraseLoaded l
    for (stage, A) in ← IO.ofExcept (stages e.lam) do
      IO.println s!"== {stage}\n{A.render}"
    return 0
  | _ => pure ()
  let a ← IO.mkRef 0
  try
    IO.println "tests-anf"
    part a "Anf rules and clock monotonicity" (Eval.run a)
    part a "Lam against Anf on k1.ixe and bench-k1, after every step" do
      for line in ← Differential.packs a stages do IO.println s!"    {line}"
    part a "K1 shapes after the pipeline (02 §13.4), replay, idempotence, least clocks" do
      for line in ← Shapes.run a do IO.println s!"    {line}"
    part a "bench-k1 entries through the pipeline's output" do
      for line in ← Shapes.entries a (← IO.appPath) do IO.println s!"    {line}"
    part a "generated Lam programs under random oracles" do
      for line in ← Generated.run a 400 do IO.println s!"    {line}"
    IO.println s!"tests-anf: {← a.get} assertions passed"
    return 0
  catch e =>
    IO.eprintln s!"tests-anf: FAILED after {← a.get} assertions: {e}"
    return 1

end CompilatrixTests.Anf.Run
