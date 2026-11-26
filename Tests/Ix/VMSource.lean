import IxVM.Check

namespace Tests.Ix.VMSource

def run (env : Lean.Environment) : IO UInt32 := do
  let definitions ← IxVM.Check.checkDefinitions env
  let values ← IxVM.Check.checkPreparation env
  IO.println s!"[ixvm-source] values {values}"
  return if definitions && values then 0 else 1

end Tests.Ix.VMSource
