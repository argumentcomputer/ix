import IxCCTests.Soundness.Run

/-! Thin entry point for the Wave 1 soundness & anti-DoS test suite. -/

def main : IO UInt32 := do
  return if ← IxCCTests.Soundness.run then 0 else 1
