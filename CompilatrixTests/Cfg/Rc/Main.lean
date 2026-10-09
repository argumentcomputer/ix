import CompilatrixTests.Cfg.Rc.Runtime
import CompilatrixTests.Cfg.Rc.DecrementControls
import CompilatrixTests.Cfg.Rc.IncrementControls

/-! Run all original complete value/heap, timeout and bridge ownership controls. -/
def main : IO Unit := do
  CompilatrixTests.Cfg.Rc.Runtime.suite
  CompilatrixTests.Cfg.Rc.DecrementControls.tests
  CompilatrixTests.Cfg.Rc.IncrementControls.tests
