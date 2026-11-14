import IxVM.Check

namespace Tests.Ix.VMSource

def run (env : Lean.Environment) : IO UInt32 := do
  let definitions ← IxVM.Check.checkDefinitions env
  let files ← IxVM.Check.checkFiles
  let values ← IxVM.Check.checkPreparation env
  IO.println s!"[ixvm-source] files {files}, values {values}"
  return if definitions && files && values then 0 else 1

end Tests.Ix.VMSource
