import IxCCTests.Fir.Differential
import IxCCTests.Fir.Rules
import IxCCTests.Fir.Gen
import IxCCTests.Fir.Bench
import IxCCTests.Fir.Render

/-! The `tests-fir` suite (design note 03 §11, M1.F5): the rules of Fir, the
Phase 1 Own fragment and Cfg; every root and first-order constant of the K1
fixtures through Anf → Fir → Own → Cfg; the fallback route declined at Fir;
generated programs; the bench-k1 entries at their test sizes. Building the
suite runs the lowerings in the kernel (`IxCCTests.Fir.KernelEval`).

Modes: `--entry NAME LEVEL` runs one bench entry at one level (the child
process for `sum-loop`'s deep big-step runs); `--generated N` a longer
campaign of generated programs; `--dump NAME` a bench entry's program at
every level. -/

namespace IxCCTests.Fir.Run

open IxCCTests.Src

def part (a : Assert) (label : String) (action : IO (Array String)) : IO Unit := do
  let before ← a.get
  let (lines, ms) ← timed action
  IO.println s!"  {label}: {(← a.get) - before} assertions, {ms} ms"
  for line in lines do IO.println s!"    {line}"
  (← IO.getStdout).flush

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--entry", name, level] =>
    IO.println (← Bench.runEntry name level)
    return 0
  | ["--generated", n] =>
    let a ← IO.mkRef 0
    for line in ← Gen.firstOrder a n.toNat! do IO.println line
    for line in ← Gen.lamGen a n.toNat! do IO.println line
    IO.println s!"tests-fir --generated {n}: {← a.get} assertions passed"
    return 0
  | ["--dump", name] =>
    let (L, root) ← Bench.entryLevels name
    IO.println s!"== Anf (root g{root})\n{L.anf.render}\n== Fir\n{L.fir.render}\n== Cfg\n{L.cfg.render}"
    return 0
  | ["--render-artifacts"] =>
    let mut entries := #[]
    for name in benchNames do
      let (L, _) ← Bench.entryLevels name
      entries := entries.push (Bench.ident name, L.anf)
    IO.print (Render.module entries.toList)
    return 0
  | _ => pure ()
  let a ← IO.mkRef 0
  try
    IO.println "tests-fir"
    part a "rules of Fir, Own and Cfg; hand-written Anf; well-formedness" (Rules.run a)
    part a "k1.ixe and bench-k1: Anf → Fir → Own → Cfg" (Differential.packs a)
    part a "the fallback route, declined at Fir" (Differential.fallback a)
    part a "generated first-order Anf programs" (Gen.firstOrder a 1000)
    part a "generated Lam programs through the Anf pipeline" (Gen.lamGen a 300)
    part a "bench-k1 entries at their test sizes" (Bench.entries a (← IO.appPath))
    part a "kernel artifacts (the lowerings re-run by decide +kernel at build time)"
      (Bench.kernelArtifacts a)
    IO.println s!"tests-fir: {← a.get} assertions passed"
    return 0
  catch e =>
    IO.eprintln s!"tests-fir: FAILED after {← a.get} assertions: {e}"
    return 1

end IxCCTests.Fir.Run
