import IxCCTests.X86.DriverSession.Controls
import IxCCTests.Ring0

/-! Thin root of tests-driver-session. -/
def main : IO Unit := do
  IxCCTests.X86.DriverSession.Controls.tests
  IxCCTests.Ring0.runRing0Tests
