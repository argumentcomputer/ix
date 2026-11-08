import IxVM.CheckedCheck

/-! The checked IxVM source (`IxVM.Checked.source`, the object the
refinement statements are about) is `IxVM.program` prepared for
`IxVM::verify_claim`: its files are the native preparation's rendering, and
its program and static tables are the preparation's values. -/

namespace Tests.Ix.CheckedSource

def run : IO UInt32 := do
  let files ← IxVM.CheckedCheck.checkFiles
  let values ← IxVM.CheckedCheck.checkPreparation
  IO.println s!"[ixvm-checked-source] files {files}, values {values}"
  return if files && values then 0 else 1

end Tests.Ix.CheckedSource
