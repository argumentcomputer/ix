import CompilatrixTests.Aiur.Execution.ControlCases
import CompilatrixTests.Aiur.Execution.TraceCases

namespace CompilatrixTests.Aiur.Execution

def run : IO Unit := do
  let count ← IO.mkRef 0
  runOps count
  runControls count
  runTraces count
  IO.println s!"aiur-execution-tests-ok: {← count.get} assertions, all 34 opcodes, 4 controls, witness heap and advice"

end CompilatrixTests.Aiur.Execution
