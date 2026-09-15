import CompilatrixTests.Aiur.Static.ProgramCases
import CompilatrixTests.Aiur.Static.PositiveCases
import CompilatrixTests.Aiur.Static.Rejections
import CompilatrixTests.Aiur.Static.IngressCases

namespace CompilatrixTests.Aiur.Static

def run : IO Unit := do
  let count ← IO.mkRef 0
  runPrograms count
  runPositive count
  runRejections count
  runIngress count
  IO.println s!"aiur-static-tests-ok: {← count.get} assertions, four counter modes, checked ranks, addressed execution"

end CompilatrixTests.Aiur.Static
