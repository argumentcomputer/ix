import Aiur.Execution.Interface
import IxVM.Source

/-! Native parity checks against full module preparation. The input is read from
Lean's imported declaration metadata, without another set of function constants. -/

namespace IxVM.Check

/-- The assembled program references the declared functions, rather than
embedding another copy of their ASTs. -/
def checkDefinitions (env : Lean.Environment) : IO Bool := do
  let some functions := env.find? ``IxVM.functions
    | throw (IO.userError "missing IxVM.functions")
  let some program := env.find? ``IxVM.program
    | throw (IO.userError "missing IxVM.program")
  let used := functions.value!.getUsedConstants
  let named := IxVM.program.functions.all fun f => used.contains (IxVM.Elab.functionName f.name)
  let assembled := program.value!.getUsedConstants.contains ``IxVM.functions
  IO.println s!"[ixvm-source] named definitions {named}, program references {assembled}"
  return named && assembled

def checkPreparation (env : Lean.Environment) : IO Bool := do
  let input ← IO.ofExcept (IxVM.Elab.moduleProgram env)
  let prepared ← IO.ofExcept (Aiur.Modules.prepare input [IxVM.entry])
  let src := prepared.environment.source
  let program := src.program == IxVM.program
  let tables := src.tables == IxVM.coreTables
  let entries := prepared.entries == [IxVM.entry]
  let prepExport ← IO.ofExcept prepared.exportExecution
  let chkExport ← IO.ofExcept (IxVM.source.exportExecution [IxVM.entry])
  let exported := prepExport.bytecode == chkExport.bytecode &&
    prepExport.interfaces == chkExport.interfaces
  IO.println s!"[ixvm-source] program {program}, static tables {tables}, entries {entries}, export {exported}"
  return program && tables && entries && exported

end IxVM.Check
