import IxCCTests.Aiur.Execution.ControlCases
import IxCCTests.Aiur.Execution.TraceCases

namespace IxCCTests.Aiur.Execution

def run : IO Unit := do
  let count ← IO.mkRef 0
  runOps count
  runControls count
  runTraces count
  IO.println s!"aiur-execution-tests-ok: {← count.get} assertions, all 34 opcodes, 4 controls, witness heap and advice"

end IxCCTests.Aiur.Execution
