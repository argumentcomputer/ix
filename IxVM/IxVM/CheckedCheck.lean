import Aiur.Execution.Interface
import IxVM.Checked
import IxVM.CheckedGen

/-! The native checks that tie `IxVM.Checked.source` to `IxVM.program`
(the test suite `ixvm-checked-source` runs them):

* `checkFiles`: the files under `IxVM/IxVM/Checked/` are the rendering of the
  native preparation;
* `checkPreparation`: the preparation's source is `IxVM.Checked.source`
  (program and static tables), it selects exactly the entry, and exporting
  execution bytecode from `IxVM.Checked.source` matches the preparation's
  export. -/

namespace IxVM.CheckedCheck

def checkFiles : IO Bool := do
  let prepared ← IO.ofExcept (Aiur.Modules.prepare IxVM.program [IxVM.CheckedGen.entry])
  let mut ok := true
  for (path, text) in IxVM.CheckedGen.render prepared do
    let existing ← try pure (some (← IO.FS.readFile path)) catch _ => pure none
    unless existing == some text do
      IO.eprintln s!"[ixvm-checked-source] {path} is not the rendering: run `lake exe ixvm/ixvm-checked`"
      ok := false
  return ok

def checkPreparation : IO Bool := do
  let prepared ← IO.ofExcept (Aiur.Modules.prepare IxVM.program [IxVM.Checked.entry])
  let src := prepared.environment.source
  let program := src.program == IxVM.Checked.program
  let tables := src.tables == IxVM.Checked.coreTables
  let entries := prepared.entries == [IxVM.Checked.entry]
  let prepExport ← IO.ofExcept prepared.exportExecution
  let chkExport ← IO.ofExcept (IxVM.Checked.source.exportExecution [IxVM.Checked.entry])
  let exported := prepExport.bytecode == chkExport.bytecode &&
    prepExport.interfaces == chkExport.interfaces
  IO.println s!"[ixvm-checked-source] program {program}, static tables {tables}, entries {entries}, export {exported}"
  return program && tables && entries && exported

end IxVM.CheckedCheck
