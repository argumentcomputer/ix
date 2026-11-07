import IxCCTests.Aiur.Static.ProgramCases
import IxCCTests.Aiur.Static.PositiveCases
import IxCCTests.Aiur.Static.Rejections
import IxCCTests.Aiur.Static.IngressCases

namespace IxCCTests.Aiur.Static

def run : IO Unit := do
  let count ← IO.mkRef 0
  runPrograms count
  runPositive count
  runRejections count
  runIngress count
  IO.println s!"aiur-static-tests-ok: {← count.get} assertions, four counter modes, checked ranks, addressed execution"

end IxCCTests.Aiur.Static
