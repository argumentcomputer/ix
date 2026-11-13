import IxCCTests.Anf.Eval
import IxCCTests.Anf.Differential
import IxCCTests.Anf.Shapes
import IxCCTests.Anf.Generated
import IxCCTests.Anf.KernelEval
import IxCCTests.Anf.LeanRender
import IxCCTests.Anf.Defun
import IxCCTests.Anf.SuccBle
import IxCCTests.Anf.FoldGuard

/-! The `tests-anf` suite: the shrink walk's bound on literal folding
(`IxCCTests.Anf.FoldGuard`, first, so that its memory bound reads the part's
own peak); Anf's rules and clock
monotonicity; Lam against Anf after every step of the Phase 1 pipeline on
every root and first-order constant of `k1.ixe` and the bench-k1 closures
(readback, traps, the timeout clause, tick dominance, `WellScoped`); the K1
shape expectations, certificate replay and shrink idempotence, sizes and
least clocks; the bench-k1 entries at their test sizes through the
pipeline's output (`sum-loop` 10⁶ in a child process with a larger stack);
generated Lam programs under random oracles; P8 (`Anf.defun`, not yet in the
pipeline) on hand-written and generated programs, Anf before against Anf
after (`IxCCTests.Anf.Defun`). `--entry NAME` runs one bench
entry (the child-process mode); `--dump NAME` prints a bench entry's Anf
after every step; `--defun N` runs the P8 section alone on `N` generated
programs. Building the suite also runs the passes in the kernel
(`IxCCTests.Anf.KernelEval`). -/

namespace IxCCTests.Anf.Run

open IxCCTests.Src

def part (a : Assert) (label : String) (action : IO Unit) : IO Unit := do
  let before ← a.get
  let ((), ms) ← timed action
  IO.println s!"  {label}: {(← a.get) - before} assertions, {ms} ms"
  (← IO.getStdout).flush

def stages : Differential.Stages := fun L => do
  let t ← IxCC.Anf.Pipeline.produce {} L
  return t.stages.zipIdx.map fun ((n, P), i) => (s!"{i}:{n}", P)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--entry", name] =>
    IO.println (← Shapes.runEntry name)
    return 0
  | ["--generated", n] =>
    -- a longer campaign of generated programs alone
    let a ← IO.mkRef 0
    for line in ← Generated.run a n.toNat! do IO.println line
    IO.println s!"tests-anf --generated {n}: {← a.get} assertions passed"
    return 0
  | ["--defun", n] =>
    let a ← IO.mkRef 0
    for line in ← Defun.run a n.toNat! do IO.println line
    IO.println s!"tests-anf --defun {n}: {← a.get} assertions passed"
    return 0
  | ["--kernel-probe", name] =>
    -- a module re-running the middle end on a bench entry in the kernel
    let e ← IxCCTests.Lam.eraseLoaded (← loadBench name)
    let t ← IO.ofExcept (IxCC.Anf.Pipeline.produce {} e.lam)
    let final := ((t.stages.getLast?).map (·.2)).getD default
    let (g, n) := size final
    IO.println (LeanRender.module name e.lam t.cert g n)
    return 0
  | ["--dump", name] =>
    let l ← loadBench name
    let e ← IxCCTests.Lam.eraseLoaded l
    for (stage, A) in ← IO.ofExcept (stages e.lam) do
      IO.println s!"== {stage}\n{A.render}"
    return 0
  | _ => pure ()
  let a ← IO.mkRef 0
  try
    IO.println "tests-anf"
    part a "the shrink walk's bound on literal folding: decisions, mutants, exactness, the middle end" do
      for line in ← FoldGuard.run a do IO.println s!"    {line}"
    part a "Anf rules and clock monotonicity" (Eval.run a)
    part a "Lam against Anf on k1.ixe and bench-k1, after every step" do
      for line in ← Differential.packs a stages do IO.println s!"    {line}"
    part a "the fallback route (recursors at run time), after every step" do
      for line in ← Differential.fallback a stages do IO.println s!"    {line}"
    part a "src-sortpoly, after every step" do
      for line in ← Differential.sortpoly a stages do IO.println s!"    {line}"
    part a "the shrink walk's succBle rule: where it applies, exactness at the boundary, mutants" do
      for line in ← SuccBle.run a do IO.println s!"    {line}"
    part a "K1 shapes after the pipeline (02 §13.4), replay, idempotence, least clocks" do
      for line in ← Shapes.run a do IO.println s!"    {line}"
    part a "bench-k1 entries through the pipeline's output" do
      for line in ← Shapes.entries a (← IO.appPath) do IO.println s!"    {line}"
    part a "generated Lam programs under random oracles" do
      for line in ← Generated.run a 1000 do IO.println s!"    {line}"
    part a "P8 (defunctionalisation), Anf before against Anf after" do
      for line in ← Defun.run a 300 do IO.println s!"    {line}"
    IO.println s!"tests-anf: {← a.get} assertions passed"
    return 0
  catch e =>
    IO.eprintln s!"tests-anf: FAILED after {← a.get} assertions: {e}"
    return 1

end IxCCTests.Anf.Run
