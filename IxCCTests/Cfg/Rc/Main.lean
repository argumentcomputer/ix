import IxCCTests.Cfg.Rc.Runtime
import IxCCTests.Cfg.Rc.DecrementControls
import IxCCTests.Cfg.Rc.IncrementControls

/-! Run all original complete value/heap, timeout and bridge ownership controls. -/
def main : IO Unit := do
  IxCCTests.Cfg.Rc.Runtime.suite
  IxCCTests.Cfg.Rc.DecrementControls.tests
  IxCCTests.Cfg.Rc.IncrementControls.tests
