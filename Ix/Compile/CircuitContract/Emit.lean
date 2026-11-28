module

public import Lean.Data.Json.Basic
public import Lean.Data.Json.Printer
public import Ix.Compile.CircuitContract.Basic

/-!
# Address-keyed `"ixcc/circuit-schedule/1"` sidecar exporter (`Ix.Compile.CircuitContract.Emit`)

Reads registered `CircuitAttrEntry` patches from `circuitAttrExtension` and joins
them against the `Lean.Name → String` (64-hex `Ixon.Address`) map produced by
`compileCertified`, emitting the exact `"ixcc/circuit-schedule/1"` JSON consumed
by `IxCC.AiurBackend.ScheduleJson.fromJson`.

* **Closure-scoped**: only declarations present in `nameToAddr` contribute to the
  emitted sidecar; unrelated annotated declarations in imported modules never leak.
* **Deterministic**: selected entries are sorted by `(normalizedHexAddr, declName)`
  prior to folding so output is independent of `Std.HashMap` bucket order.
* **Zero content-address mutation**: operates purely on the sidecar environment
  extension after `compileCertified` has already hashed the untouched `ConstantInfo`s.
-/

set_option autoImplicit false

public section

namespace Ix.Compile.CircuitContract

open Lean (Json)

/-- Wire format tag matching `IxCC.AiurBackend.ScheduleJson.formatVersion`. -/
def scheduleFormatVersion : String := "ixcc/circuit-schedule/1"

/-- Wire format tag matching `IxCC.Src.Hints.ofK1Json`. -/
def k1HintsFormatVersion : String := "ixcc/k1-equations/1"

/-- Mirror of `Aiur.Optimized.Config` for sidecar emission without depending on `Aiur`. -/
structure AiurOptimizerOptions where
  maxDegree : Nat := 3
  shareAuxiliaries : Bool := true
  eliminateSelectors : Bool := true
  propagateScopes : Bool := true
  simplifyConstraints : Bool := true
  propagateValues : Bool := true
  mergeLookups : Bool := true
  deduplicate : Bool := true
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Optional top-level schedule defaults/overrides supplied at export time. -/
structure ScheduleExportOptions where
  defaultRangeCheck : CircuitRangeCheckMode := .auto
  autoInline : Bool := true
  inlineMaxNodes : Nat := 48
  filterJpCaptures : Bool := true
  demandLink : Bool := true
  groups : List (String × List String) := []
  aiurConfig : AiurOptimizerOptions := {}
  baseBudget : CircuitBudget := {}
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Internal per-address aggregated function schedule.
Extended fields (`isStatic`, `repr`, `intrinsic`, `splitFastpath`) are omitted from
emitted JSON when default/none so legacy `"ixcc/circuit-schedule/1"` output stays
byte-identical. -/
structure EmittedFnSchedule where
  inline : CircuitInlinePolicy := .auto
  group : Option String := none
  unroll : Option Nat := none
  lanes : Option Nat := none
  isStatic : Bool := false
  repr : Option CircuitRepr := none
  intrinsic : Option String := none
  splitFastpath : Bool := false
  deriving BEq, DecidableEq, Repr, Inhabited

/-! ## Hex address validation and normalization -/

private def isHexChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

private def lowerAsciiHex (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'F' then Char.ofNat (c.toNat + 32) else c

/-- True iff `s` is a valid 64-character hexadecimal 32-byte Ixon address. -/
def isValidHexAddress (s : String) : Bool :=
  s.length == 64 && s.toList.all isHexChar

/-- Canonical lowercase hexadecimal spelling of an address string. -/
def normalizeHexAddress (s : String) : String :=
  String.ofList (s.toList.map lowerAsciiHex)

/-! ## JSON encoders matching `IxCC.AiurBackend.ScheduleJson` -/

def rangeCheckModeToJson : CircuitRangeCheckMode → Json
  | .smallTable => .str "small"
  | .pairTable => .str "pair"
  | .auto => .str "auto"

def inlinePolicyToJson : CircuitInlinePolicy → Json
  | .auto => .str "auto"
  | .always => .str "always"
  | .never => .str "never"

def circuitReprToJson : CircuitRepr → Json
  | .field => .str "field"
  | .u32 => .str "u32"
  | .u64 => .str "u64"
  | .limbs k b =>
    Json.mkObj [("kind", .str "limbs"), ("count", Json.num k), ("bits", Json.num b)]
  | .flatArray n =>
    Json.mkObj [("kind", .str "flat_array"), ("len", Json.num n)]
  | .wordStream => .str "word_stream"

def fnScheduleToJson (fs : EmittedFnSchedule) : Json :=
  let fields : List (String × Json) :=
    [("inline", inlinePolicyToJson fs.inline)] ++
    (match fs.group with | some g => [("group", .str g)] | none => []) ++
    (match fs.unroll with | some u => [("unroll", Json.num u)] | none => []) ++
    (match fs.lanes with | some l => [("lanes", Json.num l)] | none => []) ++
    (if fs.isStatic then [("static", .bool true)] else []) ++
    (match fs.repr with | some r => [("repr", circuitReprToJson r)] | none => []) ++
    (match fs.intrinsic with | some i => [("intrinsic", .str i)] | none => []) ++
    (if fs.splitFastpath then [("splitFastpath", .bool true)] else [])
  Json.mkObj fields

def budgetToJson (b : CircuitBudget) : Json :=
  let fields : List (String × Json) :=
    (match b.maxChips with | some n => [("maxChips", Json.num n)] | none => []) ++
    (match b.maxColumns with | some n => [("maxColumns", Json.num n)] | none => []) ++
    (match b.maxCallsPerChip with | some n => [("maxCallsPerChip", Json.num n)] | none => []) ++
    (match b.maxMemoryPerChip with | some n => [("maxMemoryPerChip", Json.num n)] | none => []) ++
    (match b.maxTotalColumns with | some n => [("maxTotalColumns", Json.num n)] | none => [])
  Json.mkObj fields

def aiurConfigToJson (c : AiurOptimizerOptions) : Json :=
  Json.mkObj [
    ("maxDegree", Json.num c.maxDegree),
    ("shareAuxiliaries", .bool c.shareAuxiliaries),
    ("eliminateSelectors", .bool c.eliminateSelectors),
    ("propagateScopes", .bool c.propagateScopes),
    ("simplifyConstraints", .bool c.simplifyConstraints),
    ("propagateValues", .bool c.propagateValues),
    ("mergeLookups", .bool c.mergeLookups),
    ("deduplicate", .bool c.deduplicate)
  ]

def groupsToJson (groups : List (String × List String)) : Json :=
  Json.mkObj (groups.map fun (name, chips) => (name, Json.arr (chips.map Json.str).toArray))

/-! ## Merging helpers for export -/

private def fnScheduleOfEntry (e : CircuitAttrEntry) : EmittedFnSchedule :=
  { inline := e.inline.getD .auto
    group := e.group
    unroll := e.unroll
    lanes := e.lanes
    isStatic := e.isStatic.getD false
    repr := e.repr
    intrinsic := e.intrinsic
    splitFastpath := e.splitFastpath.getD false }

/-- Strict merge of two per-address function schedules (used when two alpha-equivalent
Lean declarations share one Ixon content address). -/
private def mergeFnScheduleChecked (addr : String) (a b : EmittedFnSchedule) :
    Except CircuitContractError EmittedFnSchedule := do
  let inline ←
    if a.inline == .auto then pure b.inline
    else if b.inline == .auto || a.inline == b.inline then pure a.inline
    else throw (.conflictingAddressSchedule addr s!"inline {repr a.inline} vs {repr b.inline}")
  let group ← match a.group, b.group with
    | none, v => pure v
    | v, none => pure v
    | some x, some y =>
      if x == y then pure (some x)
      else throw (.conflictingAddressSchedule addr s!"group \"{x}\" vs \"{y}\"")
  let unroll ← match a.unroll, b.unroll with
    | none, v => pure v
    | v, none => pure v
    | some x, some y =>
      if x == y then pure (some x)
      else throw (.conflictingAddressSchedule addr s!"unroll {x} vs {y}")
  let lanes ← match a.lanes, b.lanes with
    | none, v => pure v
    | v, none => pure v
    | some x, some y =>
      if x == y then pure (some x)
      else throw (.conflictingAddressSchedule addr s!"lanes {x} vs {y}")
  let isStatic := a.isStatic || b.isStatic
  let repr ← match a.repr, b.repr with
    | none, v => pure v
    | v, none => pure v
    | some x, some y =>
      if x == y then pure (some x)
      else throw (.conflictingAddressSchedule addr s!"repr {repr x} vs {repr y}")
  let intrinsic ← match a.intrinsic, b.intrinsic with
    | none, v => pure v
    | v, none => pure v
    | some x, some y =>
      if x == y then pure (some x)
      else throw (.conflictingAddressSchedule addr s!"intrinsic \"{x}\" vs \"{y}\"")
  let splitFastpath := a.splitFastpath || b.splitFastpath
  return { inline, group, unroll, lanes, isStatic, repr, intrinsic, splitFastpath }

/-- Total deterministic merge of two per-address function schedules. -/
private def mergeFnScheduleTotal (a b : EmittedFnSchedule) : EmittedFnSchedule :=
  { inline := if a.inline != .auto then a.inline else b.inline
    group := a.group.orElse fun _ => b.group
    unroll := a.unroll.orElse fun _ => b.unroll
    lanes := a.lanes.orElse fun _ => b.lanes
    isStatic := a.isStatic || b.isStatic
    repr := a.repr.orElse fun _ => b.repr
    intrinsic := a.intrinsic.orElse fun _ => b.intrinsic
    splitFastpath := a.splitFastpath || b.splitFastpath }

/-- Strict closure-wide merge of `@[circuit_range_table]` directives. -/
private def mergeRangeCheckChecked (acc next : CircuitRangeCheckMode) :
    Except CircuitContractError CircuitRangeCheckMode :=
  match acc, next with
  | .auto, m => pure m
  | m, .auto => pure m
  | .smallTable, .smallTable => pure .smallTable
  | .pairTable, .pairTable => pure .pairTable
  | a, b => throw (.conflictingClosureRangeCheck a b)

/-- Total deterministic merge of `@[circuit_range_table]` directives
(`.pairTable` dominates `.smallTable` dominates `.auto`). -/
private def mergeRangeCheckTotal (acc next : CircuitRangeCheckMode) : CircuitRangeCheckMode :=
  match acc, next with
  | .pairTable, _ | _, .pairTable => .pairTable
  | .smallTable, _ | _, .smallTable => .smallTable
  | .auto, .auto => .auto

/-- Total deterministic fold of patches for one declaration (used by total `exportScheduleJson`). -/
private def foldEntriesTotal (name : Lean.Name) (entries : Array CircuitAttrEntry) :
    CircuitAttrEntry :=
  entries.foldl (init := { declName := name }) fun acc e =>
    { declName := name
      inline := acc.inline.orElse fun _ => e.inline
      group := acc.group.orElse fun _ => e.group
      unroll := acc.unroll.orElse fun _ => e.unroll
      lanes := acc.lanes.orElse fun _ => e.lanes
      budget := match acc.budget, e.budget with
        | some a, some b => some (mergeBudget a b)
        | some a, none => some a
        | none, b => b
      rangeCheck := match acc.rangeCheck, e.rangeCheck with
        | some a, some b => some (mergeRangeCheckTotal a b)
        | some a, none => some a
        | none, b => b
      checked := acc.checked.orElse fun _ => e.checked
      isStatic := acc.isStatic.orElse fun _ => e.isStatic
      repr := acc.repr.orElse fun _ => e.repr
      intrinsic := acc.intrinsic.orElse fun _ => e.intrinsic
      splitFastpath := acc.splitFastpath.orElse fun _ => e.splitFastpath }

private def assembleScheduleJson (opts : ScheduleExportOptions)
    (rangeCheck : CircuitRangeCheckMode) (byAddr : List (String × EmittedFnSchedule))
    (budget : CircuitBudget) : Json :=
  Json.mkObj [
    ("format", .str scheduleFormatVersion),
    ("rangeCheck", rangeCheckModeToJson rangeCheck),
    ("autoInline", .bool opts.autoInline),
    ("inlineMaxNodes", Json.num opts.inlineMaxNodes),
    ("filterJpCaptures", .bool opts.filterJpCaptures),
    ("demandLink", .bool opts.demandLink),
    ("byAddress", Json.mkObj (byAddr.map fun (a, fs) => (a, fnScheduleToJson fs))),
    ("byFun", Json.mkObj []),
    ("groups", groupsToJson opts.groups),
    ("aiurConfig", aiurConfigToJson opts.aiurConfig),
    ("budget", budgetToJson budget)
  ]

/-- Select and deterministically sort all registered entries whose declaration is
present in `nameToAddr`. -/
private def selectSorted (env : Lean.Environment) (nameToAddr : Std.HashMap Lean.Name String) :
    Array (String × Lean.Name × Array CircuitAttrEntry) :=
  let reg := circuitAttrExtension.getState env
  let selected := reg.fold (init := #[]) fun acc name entries =>
    match nameToAddr[name]? with
    | some addr => acc.push (normalizeHexAddress addr, name, entries)
    | none => acc
  selected.qsort fun a b =>
    if a.1 != b.1 then a.1 < b.1 else a.2.1.toString < b.2.1.toString

/-! ## Public sidecar export entry points -/

/-- Strict fail-closed export of registered `Ix.Circuit` attributes for the closure
described by `nameToAddr` into canonical `"ixcc/circuit-schedule/1"` JSON.

Validates that:
* every selected address in `nameToAddr` is a valid 64-hex string,
* per-declaration attribute patches do not conflict,
* alpha-equivalent declarations sharing an Ixon address do not conflict,
* closure-wide `@[circuit_range_table]` directives do not contradict each other. -/
def exportScheduleJsonChecked (env : Lean.Environment)
    (nameToAddr : Std.HashMap Lean.Name String)
    (opts : ScheduleExportOptions := {}) : Except CircuitContractError Json := do
  let selected := selectSorted env nameToAddr
  let mut byAddrMap : Std.HashMap String EmittedFnSchedule := {}
  let mut rangeCheck : CircuitRangeCheckMode := opts.defaultRangeCheck
  let mut budget : CircuitBudget := opts.baseBudget
  for (addr, name, patches) in selected do
    if !isValidHexAddress addr then
      throw (.invalidAddress name addr)
    let merged ← mergeAttrEntries name patches
    if merged.hasFnDirective then
      let fs := fnScheduleOfEntry merged
      let combined ← match byAddrMap[addr]? with
        | some prev => mergeFnScheduleChecked addr prev fs
        | none => pure fs
      byAddrMap := byAddrMap.insert addr combined
    if let some b := merged.budget then
      budget := mergeBudget budget b
    if let some rc := merged.rangeCheck then
      rangeCheck ← mergeRangeCheckChecked rangeCheck rc
  let byAddr := (byAddrMap.toArray.qsort fun a b => a.1 < b.1).toList
  return assembleScheduleJson opts rangeCheck byAddr budget

/-- Total deterministic export with optional top-level `ScheduleExportOptions`. -/
def exportScheduleJsonWith (env : Lean.Environment)
    (nameToAddr : Std.HashMap Lean.Name String)
    (opts : ScheduleExportOptions := {}) : Json := Id.run do
  let selected := selectSorted env nameToAddr
  let mut byAddrMap : Std.HashMap String EmittedFnSchedule := {}
  let mut rangeCheck : CircuitRangeCheckMode := opts.defaultRangeCheck
  let mut budget : CircuitBudget := opts.baseBudget
  for (addr, name, patches) in selected do
    let merged := foldEntriesTotal name patches
    if merged.hasFnDirective then
      let fs := fnScheduleOfEntry merged
      let combined := match byAddrMap[addr]? with
        | some prev => mergeFnScheduleTotal prev fs
        | none => fs
      byAddrMap := byAddrMap.insert addr combined
    if let some b := merged.budget then
      budget := mergeBudget budget b
    if let some rc := merged.rangeCheck then
      rangeCheck := mergeRangeCheckTotal rangeCheck rc
  let byAddr := (byAddrMap.toArray.qsort fun a b => a.1 < b.1).toList
  return assembleScheduleJson opts rangeCheck byAddr budget

/-- Export all `Ix.Circuit` attributes registered in `env` for the declarations in
`nameToAddr` (`Lean.Name → 64-hex Ixon.Address`) as an `"ixcc/circuit-schedule/1"`
`Lean.Json` sidecar directly consumable by `IxCC.AiurBackend.ScheduleJson.fromJson`. -/
def exportScheduleJson (env : Lean.Environment)
    (nameToAddr : Std.HashMap Lean.Name String) : Json :=
  exportScheduleJsonWith env nameToAddr {}

/-- Pretty-printed `"ixcc/circuit-schedule/1"` JSON text with trailing newline. -/
def exportScheduleJsonString (env : Lean.Environment)
    (nameToAddr : Std.HashMap Lean.Name String) : String :=
  (exportScheduleJson env nameToAddr).pretty ++ "\n"

/-- Build a `Std.HashMap Lean.Name String` from an explicit list of `(name, hexAddr)` pairs. -/
def nameAddrMapOfList (pairs : List (Lean.Name × String)) : Std.HashMap Lean.Name String :=
  pairs.foldl (init := {}) fun m (n, a) => m.insert n a

/-- List all Tier-2 `checked def` / `@[circuit_guess]` registrations in the selected closure as
`(hexAddr, declName, CircuitCheckedMeta)` sorted deterministically by `(hexAddr, declName)`. -/
def exportCheckedDefs (env : Lean.Environment)
    (nameToAddr : Std.HashMap Lean.Name String) :
    List (String × Lean.Name × CircuitCheckedMeta) := Id.run do
  let selected := selectSorted env nameToAddr
  let mut out : Array (String × Lean.Name × CircuitCheckedMeta) := #[]
  for (addr, name, patches) in selected do
    let merged := foldEntriesTotal name patches
    if let some metaInfo := merged.checked then
      out := out.push (addr, name, metaInfo)
  return out.toList

/-! ## Tier-2 `guess` sidecar export (`ixcc/k1-equations/1`) -/

/-- One address-keyed Tier-2 `guess f c θ [θc]` entry ready for `IxCC.Src.Hints.ofK1Json`. -/
structure EmittedGuess where
  subject : Lean.Name
  subjectAddress : String
  checker : Lean.Name
  checkerAddress : String
  theoremName : Lean.Name
  theoremAddress : String
  compName? : Option Lean.Name := none
  compAddress? : Option String := none
  deriving BEq, DecidableEq, Repr, Inhabited

private def lookupValidGuessAddr (nameToAddr : Std.HashMap Lean.Name String)
    (subject target : Lean.Name) (role : String) : Except CircuitContractError String := do
  let some raw := nameToAddr[target]?
    | throw (.missingGuessTarget subject target role)
  let norm := normalizeHexAddress raw
  if !isValidHexAddress norm then
    throw (.invalidAddress target raw)
  return norm

/-- Strict fail-closed collection of all Tier-2 `@[circuit_guess]` / `checked def`
declarations in the closure described by `nameToAddr`, keyed and deterministically sorted
by lowercase 64-hex Ixon content address.

Validates that:
* every selected subject, checker, soundness theorem, and optional completeness theorem
  is present in `nameToAddr` with a valid 64-hex address,
* per-declaration attribute patches do not conflict,
* alpha-equivalent subjects sharing an Ixon address do not register conflicting guess
  specifications (identical specifications deduplicate deterministically). -/
def exportGuessesChecked (env : Lean.Environment)
    (nameToAddr : Std.HashMap Lean.Name String) :
    Except CircuitContractError (Array EmittedGuess) := do
  let selected := selectSorted env nameToAddr
  let mut byAddr : Std.HashMap String EmittedGuess := {}
  for (addr, name, patches) in selected do
    if !isValidHexAddress addr then
      throw (.invalidAddress name addr)
    let merged ← mergeAttrEntries name patches
    if let some spec := merged.checked then
      let checkerAddress ← lookupValidGuessAddr nameToAddr name spec.checkDecl "checker"
      let theoremAddress ← lookupValidGuessAddr nameToAddr name spec.uniqueThm "soundness theorem"
      let compAddress? ← match spec.compThm with
        | none => pure none
        | some comp => some <$> lookupValidGuessAddr nameToAddr name comp "completeness theorem"
      let cur : EmittedGuess := {
        subject := name
        subjectAddress := addr
        checker := spec.checkDecl
        checkerAddress
        theoremName := spec.uniqueThm
        theoremAddress
        compName? := spec.compThm
        compAddress?
      }
      match byAddr[addr]? with
      | none => byAddr := byAddr.insert addr cur
      | some prev =>
        if prev.checkerAddress != cur.checkerAddress ||
           prev.theoremAddress != cur.theoremAddress ||
           prev.compAddress? != cur.compAddress? then
          throw (.conflictingAddressGuess addr
            s!"'{prev.subject}' vs '{cur.subject}' disagree on checker/theorem/completeness addresses")
  let out := byAddr.toArray.map (·.2)
  return out.qsort fun a b =>
    if a.subjectAddress != b.subjectAddress then a.subjectAddress < b.subjectAddress
    else a.subject.toString < b.subject.toString

/-- Encode one `EmittedGuess` into the JSON object schema parsed by `IxCC.Src.Hints.ofK1Json`. -/
def guessToJson (g : EmittedGuess) : Json :=
  let fields : List (String × Json) :=
    [ ("subject", .str g.subject.toString)
    , ("subject_address", .str g.subjectAddress)
    , ("checker", .str g.checker.toString)
    , ("checker_address", .str g.checkerAddress)
    , ("theorem", .str g.theoremName.toString)
    , ("theorem_address", .str g.theoremAddress) ] ++
    (match g.compName?, g.compAddress? with
      | some cn, some ca =>
        [ ("completeness", .str cn.toString)
        , ("completeness_address", .str ca) ]
      | _, _ => [])
  Json.mkObj fields

/-- Emit the canonical deterministic JSON array (`"guesses"`) keyed by 64-hex Ixon addresses
for every `@[circuit_guess]` / `checked def` declaration in the compiled closure `nameToAddr`. -/
def emitGuessesJson (env : Lean.Environment)
    (nameToAddr : Std.HashMap Lean.Name String) : Except CircuitContractError Json := do
  let guesses ← exportGuessesChecked env nameToAddr
  return Json.arr (guesses.map guessToJson)

/-- Emit a canonical `"ixcc/k1-equations/1"` JSON sidecar directly consumable by
`IxCC.Src.Hints.ofK1Json`, carrying resolved `"roots"`, `"equations"` (empty by default,
or address-resolved pairs), optional `"theorems"`, `"guesses"`, and `"failures": []`.

Deterministic, closure-scoped, and zero content-address mutation. -/
def emitK1HintsWithGuessesJson (env : Lean.Environment)
    (nameToAddr : Std.HashMap Lean.Name String)
    (roots : List Lean.Name)
    (source : String := "")
    (equations : Array (Lean.Name × Lean.Name) := #[])
    (wordTheorems : Array (String × Lean.Name × Lean.Name) := #[]) :
    Except CircuitContractError Json := do
  let guesses ← exportGuessesChecked env nameToAddr
  let mut seenRoots : Std.HashSet String := {}
  let mut rootEntries : Array (String × String) := #[]
  for r in roots do
    if let some raw := nameToAddr[r]? then
      let norm := normalizeHexAddress raw
      if !isValidHexAddress norm then
        throw (.invalidAddress r raw)
      let rName := r.toString
      if !seenRoots.contains rName then
        seenRoots := seenRoots.insert rName
        rootEntries := rootEntries.push (rName, norm)
  let rootRows : Array Json := rootEntries.map fun (rName, addr) =>
    Json.mkObj [
      ("name", .str rName),
      ("address", .str addr)
    ]
  let mut eqEntries : Array (String × String × String × String) := #[]
  for (defName, eqName) in equations do
    if let (some rawDef, some rawEq) := (nameToAddr[defName]?, nameToAddr[eqName]?) then
      let normDef := normalizeHexAddress rawDef
      let normEq := normalizeHexAddress rawEq
      if !isValidHexAddress normDef then throw (.invalidAddress defName rawDef)
      if !isValidHexAddress normEq then throw (.invalidAddress eqName rawEq)
      eqEntries := eqEntries.push (normDef, normEq, defName.toString, eqName.toString)
  let sortedEqs := eqEntries.qsort fun a b =>
    if a.1 != b.1 then a.1 < b.1
    else if a.2.1 != b.2.1 then a.2.1 < b.2.1
    else a.2.2.1 < b.2.2.1
  let eqRows : Array Json := sortedEqs.map fun (defAddr, eqAddr, defStr, eqStr) =>
    Json.mkObj [
      ("definition", .str defStr),
      ("definition_address", .str defAddr),
      ("equation", .str eqStr),
      ("equation_address", .str eqAddr)
    ]
  let mut thmEntries : Array (String × String × String × String × String) := #[]
  for (kind, subjName, thmName) in wordTheorems do
    if let (some rawSubj, some rawThm) := (nameToAddr[subjName]?, nameToAddr[thmName]?) then
      let normSubj := normalizeHexAddress rawSubj
      let normThm := normalizeHexAddress rawThm
      if !isValidHexAddress normSubj then throw (.invalidAddress subjName rawSubj)
      if !isValidHexAddress normThm then throw (.invalidAddress thmName rawThm)
      thmEntries := thmEntries.push (kind, normSubj, normThm, subjName.toString, thmName.toString)
  let sortedThms := thmEntries.qsort fun a b =>
    if a.1 != b.1 then a.1 < b.1
    else if a.2.1 != b.2.1 then a.2.1 < b.2.1
    else a.2.2.1 < b.2.2.1
  let thmRows : Array Json := sortedThms.map fun (kind, subjAddr, thmAddr, subjStr, thmStr) =>
    Json.mkObj [
      ("kind", .str kind),
      ("subject", .str subjStr),
      ("subject_address", .str subjAddr),
      ("theorem", .str thmStr),
      ("theorem_address", .str thmAddr)
    ]
  let guessRows : Array Json := guesses.map guessToJson
  let fields : List (String × Json) :=
    [ ("format", .str k1HintsFormatVersion) ] ++
    (if source.isEmpty then [] else [("source", .str source)]) ++
    [ ("roots", Json.arr rootRows)
    , ("equations", Json.arr eqRows) ] ++
    (if thmRows.isEmpty then [] else [("theorems", Json.arr thmRows)]) ++
    [ ("guesses", Json.arr guessRows)
    , ("failures", Json.arr #[]) ]
  return Json.mkObj fields

/-- Pretty-printed `"ixcc/k1-equations/1"` JSON text with trailing newline. -/
def emitK1HintsWithGuessesJsonString (env : Lean.Environment)
    (nameToAddr : Std.HashMap Lean.Name String)
    (roots : List Lean.Name)
    (source : String := "") : Except CircuitContractError String :=
  (·.pretty ++ "\n") <$> emitK1HintsWithGuessesJson env nameToAddr roots source

end Ix.Compile.CircuitContract

end
