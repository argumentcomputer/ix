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

structure DefAssertsEntry where
  source : Lean.ConstantInfo
  asserts : Ixon.DefAsserts
  deriving Repr, Inhabited

abbrev DefAssertsRegistry := Std.HashMap Lean.Name (Array DefAssertsEntry)

private def addDefAsserts (state : DefAssertsRegistry) (entry : DefAssertsEntry) :
    DefAssertsRegistry :=
  state.insert entry.source.name ((state[entry.source.name]?.getD #[]).push entry)

initialize sourceDefAssertsExtension :
    Lean.SimplePersistentEnvExtension DefAssertsEntry DefAssertsRegistry ←
  Lean.registerSimplePersistentEnvExtension {
    addEntryFn := addDefAsserts
    addImportedFn := Lean.mkStateFromImportedEntries addDefAsserts {} }

abbrev MeasureRegistry := Std.HashMap Lean.Name (Array MeasureHint)

private def addMeasure (state : MeasureRegistry) (entry : MeasureHint) : MeasureRegistry :=
  state.insert entry.source.name ((state[entry.source.name]?.getD #[]).push entry)

initialize sourceMeasureExtension :
    Lean.SimplePersistentEnvExtension MeasureHint MeasureRegistry ←
  Lean.registerSimplePersistentEnvExtension {
    addEntryFn := addMeasure
    addImportedFn := Lean.mkStateFromImportedEntries addMeasure {} }

/-- Combine two `DefAsserts` records on one declaration, rejecting duplicate or
conflicting allocation / stack assertions. -/
def mergeDefAsserts (name : Lean.Name) (a b : Ixon.DefAsserts) :
    Except SourceContractError Ixon.DefAsserts := do
  let alloc ←
    if a.alloc == .unrestricted then pure b.alloc
    else if b.alloc == .unrestricted then pure a.alloc
    else if a.alloc == b.alloc then
      throw (.conflictingDefAsserts name s!"duplicate allocation assertion ({repr a.alloc})")
    else
      throw (.conflictingDefAsserts name
        "conflicting allocation assertions: @[no_alloc] and @[no_rc] cannot both be specified")
  if a.boundedStack && b.boundedStack then
    throw (.conflictingDefAsserts name "duplicate @[bounded_stack] assertion")
  return { alloc, boundedStack := a.boundedStack || b.boundedStack }

private def mergeDefAssertsEntries (actual : Lean.ConstantInfo) (entries : Array DefAssertsEntry) :
    Except SourceContractError Ixon.DefAsserts := do
  let mut acc : Ixon.DefAsserts := {}
  for entry in entries do
    if entry.source != actual then throw (.staleSource entry.source.name)
    acc ← mergeDefAsserts actual.name acc entry.asserts
  validateDefAsserts actual acc
  return acc

private def mergeContracts (actual : Lean.ConstantInfo) (patches : Array SourceContract) :
    Except SourceContractError SourceContract := do
  let mut binders := #[]
  let mut fieldModes := #[]
  let mut defAsserts : Ixon.DefAsserts := {}
  for patch in patches do
    if patch.source != actual then throw (.staleSource patch.source.name)
    binders := binders ++ patch.binders
    fieldModes := fieldModes ++ patch.fieldModes
    defAsserts ← mergeDefAsserts actual.name defAsserts patch.defAsserts
  return { source := actual, binders, fieldModes, defAsserts }

/-- Register a checked patch. Disjoint patches accumulate; duplicate or
conflicting occurrences fail even when their requested modes are identical. -/
def registerSourceContract (env : Lean.Environment) (contract : SourceContract) :
    Except SourceContractError Lean.Environment := do
  let name := contract.source.name
  let some actual := (env.setExporting false).find? name | throw (.missingDeclaration name)
  let previous := (sourceContractExtension.getState env)[name]?.getD #[]
  let merged ← mergeContracts actual (previous.push contract)
  let _ ← merged.resolve actual
  return sourceContractExtension.addEntry env contract

/-- Register a checked `DefAsserts` attribute entry (`@[no_rc]`, `@[no_alloc]`,
`@[bounded_stack]`). Independent allocation and stack assertions combine;
duplicate or conflicting assertions and invalid targets (`theorem`, `partial`,
`unsafe`, non-definitions) fail immediately. -/
def registerDefAsserts (env : Lean.Environment) (entry : DefAssertsEntry) :
    Except SourceContractError Lean.Environment := do
  let name := entry.source.name
  let lookupEnv := env.setExporting false
  let some actual := lookupEnv.find? name | throw (.missingDeclaration name)
  if entry.source != actual then throw (.staleSource name)
  if (lookupEnv.find? (name ++ `_unsafe_rec)).isSome then
    throw (.invalidDefAsserts name
      "definition assertions (@[no_rc], @[no_alloc], @[bounded_stack]) are not allowed on partial or unsafe definitions")
  validateDefAsserts actual entry.asserts
  let previous := (sourceDefAssertsExtension.getState env)[name]?.getD #[]
  let _ ← mergeDefAssertsEntries actual (previous.push entry)
  return sourceDefAssertsExtension.addEntry env entry

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
  let assertsReg := sourceDefAssertsExtension.getState env
  let hints := sourceMeasureExtension.getState env
  let mut contracts := #[]
  let mut measureHints := #[]
  for (name, actual) in constants do
    let baseContract? : Option SourceContract ←
      if let some patches := registry[name]? then
        some <$> mergeContracts actual patches
      else if sourceHasAnnotations actual then
        some <$> SourceContract.fromAnnotations actual
      else
        pure none
    let extraAsserts? : Option Ixon.DefAsserts ←
      if let some entries := assertsReg[name]? then
        some <$> mergeDefAssertsEntries actual entries
      else
        pure none
    match baseContract?, extraAsserts? with
    | some c, none => contracts := contracts.push c
    | some c, some a =>
      let merged ← mergeDefAsserts name c.defAsserts a
      contracts := contracts.push { c with defAsserts := merged }
    | none, some a =>
      contracts := contracts.push { source := actual, defAsserts := a }
    | none, none => pure ()
    measureHints := measureHints ++ (hints[name]?.getD #[])
  let input := { constants, contracts, measureHints : CompileInput }
  let _ ← input.resolve
  return input

end Ix.Compile

end
