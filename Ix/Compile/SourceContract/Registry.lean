module

public import Ix.Compile.SourceContract.Resolve
public import Lean.EnvExtension

/-!
# Persistent source-contract registration

The extension is an elaboration convenience. Export produces the explicit pure
CompileInput consumed by validation; the extension itself is never a compiler
input. Keep imported registration patches instead of overwriting by declaration,
so conflicting contracts from different modules are diagnosed during export.
-/

public section

namespace Ix.Compile

abbrev ContractRegistry := Std.HashMap Lean.Name (Array SourceContract)

private def addContract (state : ContractRegistry) (entry : SourceContract) : ContractRegistry :=
  state.insert entry.source.name ((state[entry.source.name]?.getD #[]).push entry)

initialize sourceContractExtension :
    Lean.SimplePersistentEnvExtension SourceContract ContractRegistry ←
  Lean.registerSimplePersistentEnvExtension {
    addEntryFn := addContract
    addImportedFn := Lean.mkStateFromImportedEntries addContract {} }

abbrev MeasureRegistry := Std.HashMap Lean.Name (Array MeasureHint)

private def addMeasure (state : MeasureRegistry) (entry : MeasureHint) : MeasureRegistry :=
  state.insert entry.source.name ((state[entry.source.name]?.getD #[]).push entry)

initialize sourceMeasureExtension :
    Lean.SimplePersistentEnvExtension MeasureHint MeasureRegistry ←
  Lean.registerSimplePersistentEnvExtension {
    addEntryFn := addMeasure
    addImportedFn := Lean.mkStateFromImportedEntries addMeasure {} }

private def mergeContracts (actual : Lean.ConstantInfo) (patches : Array SourceContract) :
    Except SourceContractError SourceContract := do
  let mut binders := #[]
  let regions := (patches[0]?.map (·.regions)).getD #[]
  for patch in patches do
    if patch.source != actual then throw (.staleSource patch.source.name)
    if patch.regions != regions then throw (.conflictingRegions actual.name)
    binders := binders ++ patch.binders
  return { source := actual, binders, regions }

/-- Register a checked patch. Disjoint patches accumulate; duplicate or
conflicting occurrences fail even when their requested modes are identical. -/
def registerSourceContract (env : Lean.Environment) (contract : SourceContract) :
    Except SourceContractError Lean.Environment := do
  let name := contract.source.name
  let some actual := env.find? name | throw (.missingDeclaration name)
  let previous := (sourceContractExtension.getState env)[name]?.getD #[]
  let merged ← mergeContracts actual (previous.push contract)
  let _ ← merged.resolve actual
  return sourceContractExtension.addEntry env contract

def registerMeasureHint (env : Lean.Environment) (hint : MeasureHint) :
    Except SourceContractError Lean.Environment := do
  let name := hint.source.name
  let some actual := env.find? name | throw (.missingDeclaration name)
  let previous := (sourceMeasureExtension.getState env)[name]?.getD #[]
  if !previous.isEmpty then throw (.duplicateMeasure name)
  let _ ← hint.resolve actual
  return sourceMeasureExtension.addEntry env hint

/-- Export the selected declarations' loaded registrations, including imports.
Unselected declarations' annotations are outside this input. Dangling, stale,
or conflicting records in the selected input are rejected by the pure checker. -/
def compileInputFromEnv (env : Lean.Environment)
    (constants : List (Lean.Name × Lean.ConstantInfo)) : Except SourceContractError CompileInput := do
  let registry := sourceContractExtension.getState env
  let hints := sourceMeasureExtension.getState env
  let mut contracts := #[]
  let mut measureHints := #[]
  for (name, actual) in constants do
    if let some patches := registry[name]? then
      contracts := contracts.push (← mergeContracts actual patches)
    measureHints := measureHints ++ (hints[name]?.getD #[])
  let input := { constants, contracts, measureHints : CompileInput }
  let _ ← input.resolve
  return input

end Ix.Compile

end
