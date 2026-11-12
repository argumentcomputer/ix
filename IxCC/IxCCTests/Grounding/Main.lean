import IxCCTests.Grounding.Run
import IxCCTests.Grounding.NoCanon

/-- `tests-grounding` runs the grounding check on the committed closures, with its negative
controls (`IxCCTests.Grounding.Run`), and the canonicity-free family's decided fact on the
accepted corpus closures (`IxCCTests.Grounding.NoCanon`). -/
def main : IO UInt32 := do
  let ok1 ← IxCCTests.Grounding.run
  let ok2 ← IxCCTests.Grounding.NoCanon.run
  return if ok1 && ok2 then 0 else 1
