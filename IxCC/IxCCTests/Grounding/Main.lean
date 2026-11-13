import IxCCTests.Grounding.Run
import IxCCTests.Grounding.NoCanon
import IxCCTests.Grounding.Zeta

/-- `tests-grounding` runs the grounding check on the committed closures, with its negative
controls (`IxCCTests.Grounding.Run`), the canonicity-free family's decided fact on the
accepted corpus closures (`IxCCTests.Grounding.NoCanon`), and step C's `let` cases on the corpus
closures the check still refuses and planted on `fib` (`IxCCTests.Grounding.Zeta`). -/
def main : IO UInt32 := do
  let ok1 ← IxCCTests.Grounding.run
  let ok2 ← IxCCTests.Grounding.NoCanon.run
  let ok3 ← IxCCTests.Grounding.Zeta.run
  return if ok1 && ok2 && ok3 then 0 else 1
