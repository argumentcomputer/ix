import IxCCTests.IxonV3.Validation
import IxCCTests.IxonV3.Ingress
import IxCCTests.IxonV3.K1
import IxCCTests.IxonV3.Binding
import IxCC.Tools.Check

namespace IxCCTests.IxonV3

open IxCC.Ixon IxCC.Ixon.V3

def run : IO Bool := do
  try
    let root : System.FilePath := "fixtures/ixon-v4"
    let mut assertions := 0
    assertions := assertions + (← Ingress.run root)
    assertions := assertions + (← Validation.run root)
    assertions := assertions + (← K1.run root)
    assertions := assertions + (← Binding.run root)
    IO.println s!"ixon-v3-tests-ok: {assertions} v5 mode, wire, N6, R5/N2 ingress, validation, kernel acceptance and role-binding assertions"
    return true
  catch error =>
    IO.eprintln s!"FAIL: Ixon v5: {error}"
    return false

end IxCCTests.IxonV3
