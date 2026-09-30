import CompilatrixTests.Fir.Differential

/-! The `tests-fir` suite (design note 03 §11, M1.F5): Fir, the Phase 1 Own
fragment and Cfg on the K1 fixtures, the fallback route's decline,
generated programs and the bench-k1 entries at their test sizes. -/

namespace CompilatrixTests.Fir.Run

open CompilatrixTests.Src

def part (a : Assert) (label : String) (action : IO (Array String)) : IO Unit := do
  let before ← a.get
  let (lines, ms) ← timed action
  IO.println s!"  {label}: {(← a.get) - before} assertions, {ms} ms"
  for line in lines do IO.println s!"    {line}"
  (← IO.getStdout).flush

def main (_args : List String) : IO UInt32 := do
  let a ← IO.mkRef 0
  try
    IO.println "tests-fir"
    part a "k1.ixe and bench-k1: Anf → Fir → Own → Cfg" (Differential.packs a)
    part a "the fallback route, declined at Fir" (Differential.fallback a)
    IO.println s!"tests-fir: {← a.get} assertions passed"
    return 0
  catch e =>
    IO.eprintln s!"tests-fir: FAILED after {← a.get} assertions: {e}"
    return 1

end CompilatrixTests.Fir.Run
