module

public import Lean.EnvExtension
public import Lean.Data.Name
public import Std.Data.HashSet

/-!
# Persistent circuit-schedule sidecar registration (`Ix.Compile.CircuitContract.Basic`)

Stores purely operational circuit-lowering and budget directives in a Lean
`SimplePersistentEnvExtension`, keyed by declaration `Lean.Name`.

**Critical invariant**: registration NEVER modifies the elaborated
`Lean.ConstantInfo` (type, body, universe parameters, metadata wrappers, or
flags) and therefore NEVER mutates any Ixon content address. After
`compileCertified` computes `Name → Ixon.Address`, `Ix.Compile.CircuitContract.Emit`
exports an address-keyed `"ixcc/circuit-schedule/1"` JSON sidecar consumed by
`IxCC.AiurBackend.ScheduleJson.fromJson`.
-/

set_option autoImplicit false

public section

namespace Ix.Compile.CircuitContract

/-- Per-function inlining directive, matching `IxCC.AiurBackend.Schedule.InlinePolicy`. -/
inductive CircuitInlinePolicy where
  | auto
  | always
  | never
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Range-check table strategy, matching `IxCC.AiurBackend.Schedule.RangeCheckMode`. -/
inductive CircuitRangeCheckMode where
  | smallTable
  | pairTable
  | auto
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Fail-closed circuit compilation budget ceilings, matching `IxCC.AiurBackend.Schedule.Budget`.
`none` leaves a bound unchecked. -/
structure CircuitBudget where
  maxChips : Option Nat := none
  maxColumns : Option Nat := none
  maxCallsPerChip : Option Nat := none
  maxMemoryPerChip : Option Nat := none
  maxTotalColumns : Option Nat := none
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Sidecar linkage for a Tier-2 non-deterministic `guess f c θ [θc]` definition
(registered via `checked def` or `@[circuit_guess c θ [θc]]`): records the ordinary Lean
checker predicate `checkDecl`, kernel-checked soundness/uniqueness theorem `uniqueThm`,
and optional completeness theorem `compThm` without touching `f`'s `ConstantInfo`. -/
structure CircuitCheckedMeta where
  checkDecl : Lean.Name
  uniqueThm : Lean.Name
  compThm : Option Lean.Name := none
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Alias for `CircuitCheckedMeta` matching `IxCC.Src.Table.Guess`'s `guess f c θ [θc]` model. -/
abbrev CircuitGuessSpec := CircuitCheckedMeta

/-- A single registered attribute patch on a Lean declaration `declName`.
Multiple disjoint attributes on the same declaration accumulate in
`circuitAttrExtension` and are merged deterministically on export. -/
structure CircuitAttrEntry where
  declName : Lean.Name
  inline : Option CircuitInlinePolicy := none
  group : Option String := none
  unroll : Option Nat := none
  lanes : Option Nat := none
  budget : Option CircuitBudget := none
  rangeCheck : Option CircuitRangeCheckMode := none
  checked : Option CircuitCheckedMeta := none
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Errors raised when registering or exporting conflicting circuit schedule directives. -/
inductive CircuitContractError where
  | missingDeclaration (name : Lean.Name)
  | conflictingInline (name : Lean.Name) (prev next : CircuitInlinePolicy)
  | duplicateGroup (name : Lean.Name) (prev next : String)
  | emptyGroupName (name : Lean.Name)
  | duplicateUnroll (name : Lean.Name) (prev next : Nat)
  | invalidUnroll (name : Lean.Name)
  | duplicateLanes (name : Lean.Name) (prev next : Nat)
  | invalidLanes (name : Lean.Name)
  | duplicateBudget (name : Lean.Name)
  | conflictingRangeCheck (name : Lean.Name) (prev next : CircuitRangeCheckMode)
  | duplicateChecked (name : Lean.Name)
  | missingGuessTarget (subject target : Lean.Name) (role : String)
  | invalidAddress (name : Lean.Name) (addr : String)
  | conflictingAddressSchedule (addr : String) (detail : String)
  | conflictingAddressGuess (addr : String) (detail : String)
  | conflictingClosureRangeCheck (prev next : CircuitRangeCheckMode)
  deriving BEq, DecidableEq, Repr

instance : ToString CircuitContractError where
  toString
    | .missingDeclaration name =>
      s!"circuit contract: declaration '{name}' not found in environment"
    | .conflictingInline name prev next =>
      s!"circuit contract: conflicting inline directives on '{name}' ({repr prev} vs {repr next})"
    | .duplicateGroup name prev next =>
      s!"circuit contract: duplicate @[circuit_group] on '{name}' (\"{prev}\" vs \"{next}\")"
    | .emptyGroupName name =>
      s!"circuit contract: @[circuit_group] on '{name}' requires a non-empty group name"
    | .duplicateUnroll name prev next =>
      s!"circuit contract: duplicate @[circuit_unroll] on '{name}' ({prev} vs {next})"
    | .invalidUnroll name =>
      s!"circuit contract: @[circuit_unroll] factor on '{name}' must be positive (>= 1)"
    | .duplicateLanes name prev next =>
      s!"circuit contract: duplicate @[circuit_lanes] on '{name}' ({prev} vs {next})"
    | .invalidLanes name =>
      s!"circuit contract: @[circuit_lanes] width on '{name}' must be positive (>= 1)"
    | .duplicateBudget name =>
      s!"circuit contract: duplicate @[circuit_budget] on '{name}'"
    | .conflictingRangeCheck name prev next =>
      s!"circuit contract: conflicting @[circuit_range_table] on '{name}' ({repr prev} vs {repr next})"
    | .duplicateChecked name =>
      s!"circuit contract: duplicate guess/checked-def witness registration on '{name}'"
    | .missingGuessTarget subject target role =>
      s!"circuit contract: guess {role} '{target}' for '{subject}' is missing from the compiled closure or environment"
    | .invalidAddress name addr =>
      s!"circuit contract: invalid 64-hex Ixon address '{addr}' for declaration '{name}'"
    | .conflictingAddressSchedule addr detail =>
      s!"circuit contract: conflicting directives at shared address '{addr}': {detail}"
    | .conflictingAddressGuess addr detail =>
      s!"circuit contract: conflicting guess specifications at shared address '{addr}': {detail}"
    | .conflictingClosureRangeCheck prev next =>
      s!"circuit contract: conflicting closure-wide rangeCheck modes ({repr prev} vs {repr next})"

/-- True iff `b` sets no bounds. -/
def CircuitBudget.isEmpty (b : CircuitBudget) : Bool :=
  b.maxChips.isNone && b.maxColumns.isNone && b.maxCallsPerChip.isNone &&
  b.maxMemoryPerChip.isNone && b.maxTotalColumns.isNone

/-- Combine two optional ceilings fail-closed by taking the stricter (minimum) bound. -/
def mergeBound (a b : Option Nat) : Option Nat :=
  match a, b with
  | some x, some y => some (min x y)
  | some x, none => some x
  | none, some y => some y
  | none, none => none

/-- Combine two `CircuitBudget`s fail-closed (minimum bound per ceiling). -/
def mergeBudget (a b : CircuitBudget) : CircuitBudget :=
  { maxChips := mergeBound a.maxChips b.maxChips
    maxColumns := mergeBound a.maxColumns b.maxColumns
    maxCallsPerChip := mergeBound a.maxCallsPerChip b.maxCallsPerChip
    maxMemoryPerChip := mergeBound a.maxMemoryPerChip b.maxMemoryPerChip
    maxTotalColumns := mergeBound a.maxTotalColumns b.maxTotalColumns }

/-- True iff `e` sets at least one per-function scheduling directive emitted under `byAddress`. -/
def CircuitAttrEntry.hasFnDirective (e : CircuitAttrEntry) : Bool :=
  e.inline.isSome || e.group.isSome || e.unroll.isSome || e.lanes.isSome

/-- Validate a single attribute patch before adding it to the extension. -/
def validateAttrEntry (entry : CircuitAttrEntry) : Except CircuitContractError Unit := do
  if let some g := entry.group then
    if g.isEmpty then throw (.emptyGroupName entry.declName)
  if let some u := entry.unroll then
    if u == 0 then throw (.invalidUnroll entry.declName)
  if let some l := entry.lanes then
    if l == 0 then throw (.invalidLanes entry.declName)

/-- Merge two disjoint attribute patches targeting the same declaration, rejecting
duplicate or conflicting directives. -/
def mergeAttrEntry (name : Lean.Name) (acc next : CircuitAttrEntry) :
    Except CircuitContractError CircuitAttrEntry := do
  let inline ← match acc.inline, next.inline with
    | none, v => pure v
    | v, none => pure v
    | some prev, some cur => throw (.conflictingInline name prev cur)
  let group ← match acc.group, next.group with
    | none, v => pure v
    | v, none => pure v
    | some prev, some cur => throw (.duplicateGroup name prev cur)
  let unroll ← match acc.unroll, next.unroll with
    | none, v => pure v
    | v, none => pure v
    | some prev, some cur => throw (.duplicateUnroll name prev cur)
  let lanes ← match acc.lanes, next.lanes with
    | none, v => pure v
    | v, none => pure v
    | some prev, some cur => throw (.duplicateLanes name prev cur)
  let budget ← match acc.budget, next.budget with
    | none, v => pure v
    | v, none => pure v
    | some _, some _ => throw (.duplicateBudget name)
  let rangeCheck ← match acc.rangeCheck, next.rangeCheck with
    | none, v => pure v
    | v, none => pure v
    | some prev, some cur => throw (.conflictingRangeCheck name prev cur)
  let checked ← match acc.checked, next.checked with
    | none, v => pure v
    | v, none => pure v
    | some _, some _ => throw (.duplicateChecked name)
  return { declName := name, inline, group, unroll, lanes, budget, rangeCheck, checked }

/-- Fold and validate all accumulated patches for declaration `name`. -/
def mergeAttrEntries (name : Lean.Name) (entries : Array CircuitAttrEntry) :
    Except CircuitContractError CircuitAttrEntry := do
  let mut acc : CircuitAttrEntry := { declName := name }
  for entry in entries do
    validateAttrEntry entry
    acc ← mergeAttrEntry name acc entry
  return acc

/-- Persistent registry mapping `Lean.Name` to all registered attribute patches
(including imported patches, never overwriting silently). -/
abbrev CircuitAttrRegistry := Std.HashMap Lean.Name (Array CircuitAttrEntry)

private def addCircuitAttr (state : CircuitAttrRegistry) (entry : CircuitAttrEntry) :
    CircuitAttrRegistry :=
  state.insert entry.declName ((state[entry.declName]?.getD #[]).push entry)

initialize circuitAttrExtension :
    Lean.SimplePersistentEnvExtension CircuitAttrEntry CircuitAttrRegistry ←
  Lean.registerSimplePersistentEnvExtension {
    addEntryFn := addCircuitAttr
    addImportedFn := Lean.mkStateFromImportedEntries addCircuitAttr {} }

/-- Register a checked `CircuitAttrEntry` in `circuitAttrExtension`.
Verifies that `entry.declName` (and any `checked` guess companion declarations) exist in
`env`, validates bounds, and checks compatibility with prior patches without modifying
any `ConstantInfo`. -/
def registerCircuitAttr (env : Lean.Environment) (entry : CircuitAttrEntry) :
    Except CircuitContractError Lean.Environment := do
  let name := entry.declName
  let lookupEnv := env.setExporting false
  if (lookupEnv.find? name).isNone then
    throw (.missingDeclaration name)
  if let some g := entry.checked then
    if (lookupEnv.find? g.checkDecl).isNone then
      throw (.missingGuessTarget name g.checkDecl "checker")
    if (lookupEnv.find? g.uniqueThm).isNone then
      throw (.missingGuessTarget name g.uniqueThm "soundness theorem")
    if let some comp := g.compThm then
      if (lookupEnv.find? comp).isNone then
        throw (.missingGuessTarget name comp "completeness theorem")
  validateAttrEntry entry
  let previous := (circuitAttrExtension.getState env)[name]?.getD #[]
  let _ ← mergeAttrEntries name (previous.push entry)
  return circuitAttrExtension.addEntry env entry

/-- Look up and merge all circuit attributes registered on `name`, if any. -/
def getCircuitAttr? (env : Lean.Environment) (name : Lean.Name) :
    Except CircuitContractError (Option CircuitAttrEntry) := do
  match (circuitAttrExtension.getState env)[name]? with
  | none => return none
  | some entries => some <$> mergeAttrEntries name entries

/-- True iff `name` has at least one registered circuit attribute patch. -/
def hasCircuitAttrs (env : Lean.Environment) (name : Lean.Name) : Bool :=
  (circuitAttrExtension.getState env).contains name

/-- All registered `(declName, patches)` entries sorted deterministically by `Name.toString`. -/
def registeredEntries (env : Lean.Environment) : Array (Lean.Name × Array CircuitAttrEntry) :=
  (circuitAttrExtension.getState env).toArray.qsort fun a b =>
    a.1.toString < b.1.toString

/-- Companion declarations (`checkDecl`, `uniqueThm`, optional `compThm`) of every
`@[circuit_guess]` / `checked def` subject in `present` that are not yet in `present`,
sorted deterministically by `Name.toString`. -/
def guessCompanionNames (env : Lean.Environment) (present : Std.HashSet Lean.Name) :
    Array Lean.Name := Id.run do
  let reg := circuitAttrExtension.getState env
  let mut extra : Std.HashSet Lean.Name := {}
  for (name, patches) in reg do
    if present.contains name then
      for p in patches do
        if let some g := p.checked then
          if !present.contains g.checkDecl then
            extra := extra.insert g.checkDecl
          if !present.contains g.uniqueThm then
            extra := extra.insert g.uniqueThm
          if let some comp := g.compThm then
            if !present.contains comp then
              extra := extra.insert comp
  return extra.toArray.qsort fun a b => a.toString < b.toString

/-- Checker declaration names (`checkDecl`) of all `@[circuit_guess]` / `checked def`
subjects in `present`, sorted deterministically by `Name.toString`. -/
def guessCheckerNames (env : Lean.Environment) (present : Std.HashSet Lean.Name) :
    Array Lean.Name := Id.run do
  let reg := circuitAttrExtension.getState env
  let mut checkers : Std.HashSet Lean.Name := {}
  for (name, patches) in reg do
    if present.contains name then
      for p in patches do
        if let some g := p.checked then
          checkers := checkers.insert g.checkDecl
  return checkers.toArray.qsort fun a b => a.toString < b.toString

end Ix.Compile.CircuitContract

end
