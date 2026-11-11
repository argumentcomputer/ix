import IxCCTests.Grounding.Run

/-- `tests-grounding` runs the grounding check on the committed closures, with its negative
controls (`IxCCTests.Grounding.Run`). -/
def main : IO UInt32 := do
  return if ← IxCCTests.Grounding.run then 0 else 1
