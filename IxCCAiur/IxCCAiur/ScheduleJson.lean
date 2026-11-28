import IxCCAiur.Schedule
import IxCC.Ixon.V3.Support
import IxCC.Src.Hints
import Lean.Data.Json.Basic
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer

/-! # Circuit Schedule JSON Codec (`ixcc/circuit-schedule/1`)

Pure, deterministic, strictly total JSON encoder and decoder for
`IxCC.AiurBackend.Schedule.CircuitSchedule`.

## Format (`"ixcc/circuit-schedule/1"`)

```json
{
  "format": "ixcc/circuit-schedule/1",
  "rangeCheck": "auto",
  "autoInline": true,
  "inlineMaxNodes": 48,
  "filterJpCaptures": true,
  "demandLink": true,
  "byAddress": {
    "<64-hex-ixon-address>": {
      "inline": "always",
      "group": "sha_round",
      "unroll": 4,
      "lanes": 2
    }
  },
  "byFun": {
    "0": { "inline": "never" }
  },
  "groups": {
    "sha_round": ["Prog::f0", "Prog::f1"]
  },
  "aiurConfig": {
    "maxDegree": 3,
    "shareAuxiliaries": true,
    "eliminateSelectors": true,
    "propagateScopes": true,
    "simplifyConstraints": true,
    "propagateValues": true,
    "mergeLookups": true,
    "deduplicate": true
  },
  "budget": {
    "maxChips": 16,
    "maxColumns": 256,
    "maxCallsPerChip": 64,
    "maxMemoryPerChip": 128,
    "maxTotalColumns": 4096
  }
}
```

* **Fail-closed schema validation**: unknown keys in the top-level object,
  `FnSchedule`, `Budget`, or `aiurConfig` are rejected so a typo (e.g.
  `"maxColums"`) can never silently disable a budget ceiling or directive.
* **Canonical determinism**: `Lean.Json.mkObj` orders keys canonically by
  lexicographic string order, `byAddress` keys are normalized 64-char lowercase
  hex strings, and `byFun` decodes in ascending numeric `FunId` order.
* **Hostile-JSON guard**: `fromJsonString` checks size, nesting depth, and
  numeric token bounds via `IxCC.Src.Hints.checkJsonText` before parsing.
-/

set_option autoImplicit false

namespace IxCC.AiurBackend.ScheduleJson

open Lean (Json)
open IxCC.Ixon
open IxCC.AiurBackend.Schedule

/-- Wire format tag for address-keyed circuit schedule sidecars. -/
def formatVersion : String := "ixcc/circuit-schedule/1"

/-! ## Low-level total helpers -/

private def checkAllowedKeys (ctx : String) (allowed : List String)
    (entries : List (String × Json)) : Except String Unit := do
  for (k, _) in entries do
    if !(allowed.contains k) then
      throw s!"circuit-schedule: unknown key '{k}' in {ctx}"

private def lookup? (entries : List (String × Json)) (key : String) : Option Json :=
  (entries.find? (·.1 == key)).map (·.2)

private def optField {α : Type} (entries : List (String × Json)) (key : String)
    (default : α) (decode : Json → Except String α) : Except String α :=
  match lookup? entries key with
  | none => .ok default
  | some v => decode v

private def optNullableField {α : Type} (entries : List (String × Json)) (key : String)
    (decode : Json → Except String α) : Except String (Option α) :=
  match lookup? entries key with
  | none => .ok none
  | some .null => .ok none
  | some v => some <$> decode v

private def expectNat (ctx : String) (j : Json) : Except String Nat :=
  match j.getNat? with
  | .ok n => .ok n
  | .error _ => .error s!"circuit-schedule: expected natural number for {ctx}, got {j.compress}"

private def expectBool (ctx : String) (j : Json) : Except String Bool :=
  match j.getBool? with
  | .ok b => .ok b
  | .error _ => .error s!"circuit-schedule: expected boolean for {ctx}, got {j.compress}"

private def expectStr (ctx : String) (j : Json) : Except String String :=
  match j.getStr? with
  | .ok s => .ok s
  | .error _ => .error s!"circuit-schedule: expected string for {ctx}, got {j.compress}"

private def expectObjEntries (ctx : String) (j : Json) : Except String (List (String × Json)) :=
  match j.getObj? with
  | .ok m => .ok m.toList
  | .error _ => .error s!"circuit-schedule: expected JSON object for {ctx}, got {j.compress}"

/-- Parse a strict canonical decimal natural number (no leading zeros except `"0"`,
no sign, non-empty). -/
private def parseCanonicalNat? (s : String) : Option Nat :=
  match s.toList with
  | [] => none
  | ['0'] => some 0
  | '0' :: _ => none
  | cs => go cs 0
where
  go : List Char → Nat → Option Nat
    | [], acc => some acc
    | c :: rest, acc =>
      if '0' ≤ c && c ≤ '9' then
        go rest (acc * 10 + (c.toNat - '0'.toNat))
      else
        none

/-- Pure total insertion sort by a `Nat` key (ascending). -/
private def sortByNat {α : Type} (key : α → Nat) : List α → List α
  | [] => []
  | x :: xs => insert x (sortByNat key xs)
where
  insert (x : α) : List α → List α
    | [] => [x]
    | y :: ys =>
      if key x ≤ key y then x :: y :: ys
      else y :: insert x ys

/-- Parse a 64-character hexadecimal `Ixon.Address`. -/
def addressFromHex (s : String) : Except String Address :=
  if s.length != 64 then
    .error s!"circuit-schedule: invalid 64-hex address '{s}' (length {s.length})"
  else
    match Address.fromString s with
    | some a => .ok a
    | none => .error s!"circuit-schedule: invalid hex digit in address '{s}'"

/-! ## Component codecs -/

def rangeCheckModeToJson : RangeCheckMode → Json
  | .smallTable => .str "small"
  | .pairTable => .str "pair"
  | .auto => .str "auto"

def rangeCheckModeFromJson : Json → Except String RangeCheckMode
  | .str "small" => .ok .smallTable
  | .str "pair" => .ok .pairTable
  | .str "auto" => .ok .auto
  | j => .error s!"circuit-schedule: invalid rangeCheck '{j.compress}' (expected \"small\", \"pair\", or \"auto\")"

def inlinePolicyToJson : InlinePolicy → Json
  | .auto => .str "auto"
  | .always => .str "always"
  | .never => .str "never"

def inlinePolicyFromJson : Json → Except String InlinePolicy
  | .str "auto" => .ok .auto
  | .str "always" => .ok .always
  | .str "never" => .ok .never
  | j => .error s!"circuit-schedule: invalid inline policy '{j.compress}' (expected \"auto\", \"always\", or \"never\")"

def circuitReprToJson : CircuitRepr → Json
  | .field => .str "field"
  | .u32 => .str "u32"
  | .u64 => .str "u64"
  | .limbs k b =>
    Json.mkObj [("kind", .str "limbs"), ("count", Json.num k), ("bits", Json.num b)]
  | .flatArray n =>
    Json.mkObj [("kind", .str "flat_array"), ("len", Json.num n)]
  | .wordStream => .str "word_stream"

private def limbsReprAllowedKeys : List String :=
  ["kind", "count", "bits"]

private def flatArrayReprAllowedKeys : List String :=
  ["kind", "len"]

def circuitReprFromJson : Json → Except String CircuitRepr
  | .str "field" => .ok .field
  | .str "u32" => .ok .u32
  | .str "u64" => .ok .u64
  | .str "word_stream" => .ok .wordStream
  | .obj m => do
    let entries := m.toList
    let some kindJson := lookup? entries "kind"
      | throw "circuit-schedule: CircuitRepr object missing required 'kind' field"
    let kind ← expectStr "CircuitRepr.kind" kindJson
    match kind with
    | "limbs" =>
      checkAllowedKeys "CircuitRepr.limbs" limbsReprAllowedKeys entries
      let some countJson := lookup? entries "count"
        | throw "circuit-schedule: CircuitRepr.limbs missing required 'count' field"
      let some bitsJson := lookup? entries "bits"
        | throw "circuit-schedule: CircuitRepr.limbs missing required 'bits' field"
      let count ← expectNat "CircuitRepr.limbs.count" countJson
      let bits ← expectNat "CircuitRepr.limbs.bits" bitsJson
      if count == 0 || bits == 0 then
        throw s!"circuit-schedule: CircuitRepr.limbs count ({count}) and bits ({bits}) must be positive"
      return .limbs count bits
    | "flat_array" =>
      checkAllowedKeys "CircuitRepr.flat_array" flatArrayReprAllowedKeys entries
      let some lenJson := lookup? entries "len"
        | throw "circuit-schedule: CircuitRepr.flat_array missing required 'len' field"
      let len ← expectNat "CircuitRepr.flat_array.len" lenJson
      if len == 0 then
        throw "circuit-schedule: CircuitRepr.flat_array len must be positive"
      return .flatArray len
    | other =>
      throw s!"circuit-schedule: invalid CircuitRepr kind '{other}' (expected \"limbs\" or \"flat_array\")"
  | j =>
    .error s!"circuit-schedule: invalid CircuitRepr '{j.compress}'"

def fnScheduleToJson (fs : FnSchedule) : Json :=
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

private def fnScheduleAllowedKeys : List String :=
  ["inline", "group", "unroll", "lanes", "static", "repr", "intrinsic", "splitFastpath"]

def fnScheduleFromJson (j : Json) : Except String FnSchedule := do
  let entries ← expectObjEntries "FnSchedule" j
  checkAllowedKeys "FnSchedule" fnScheduleAllowedKeys entries
  let inline ← optField entries "inline" .auto inlinePolicyFromJson
  let group ← optNullableField entries "group" (expectStr "FnSchedule.group")
  let unroll ← optNullableField entries "unroll" (expectNat "FnSchedule.unroll")
  let lanes ← optNullableField entries "lanes" (expectNat "FnSchedule.lanes")
  let isStatic ← optField entries "static" false (expectBool "FnSchedule.static")
  let repr ← optNullableField entries "repr" circuitReprFromJson
  let intrinsic ← optNullableField entries "intrinsic" fun v => do
    let s ← expectStr "FnSchedule.intrinsic" v
    if s.isEmpty then
      throw "circuit-schedule: FnSchedule.intrinsic must be non-empty"
    return s
  let splitFastpath ← optField entries "splitFastpath" false (expectBool "FnSchedule.splitFastpath")
  return { inline, group, unroll, lanes, isStatic, repr, intrinsic, splitFastpath }

def budgetToJson (b : Budget) : Json :=
  let fields : List (String × Json) :=
    (match b.maxChips with | some n => [("maxChips", Json.num n)] | none => []) ++
    (match b.maxColumns with | some n => [("maxColumns", Json.num n)] | none => []) ++
    (match b.maxCallsPerChip with | some n => [("maxCallsPerChip", Json.num n)] | none => []) ++
    (match b.maxMemoryPerChip with | some n => [("maxMemoryPerChip", Json.num n)] | none => []) ++
    (match b.maxTotalColumns with | some n => [("maxTotalColumns", Json.num n)] | none => [])
  Json.mkObj fields

private def budgetAllowedKeys : List String :=
  ["maxChips", "maxColumns", "maxCallsPerChip", "maxMemoryPerChip", "maxTotalColumns"]

def budgetFromJson (j : Json) : Except String Budget := do
  let entries ← expectObjEntries "budget" j
  checkAllowedKeys "budget" budgetAllowedKeys entries
  let maxChips ← optNullableField entries "maxChips" (expectNat "budget.maxChips")
  let maxColumns ← optNullableField entries "maxColumns" (expectNat "budget.maxColumns")
  let maxCallsPerChip ← optNullableField entries "maxCallsPerChip" (expectNat "budget.maxCallsPerChip")
  let maxMemoryPerChip ← optNullableField entries "maxMemoryPerChip" (expectNat "budget.maxMemoryPerChip")
  let maxTotalColumns ← optNullableField entries "maxTotalColumns" (expectNat "budget.maxTotalColumns")
  return { maxChips, maxColumns, maxCallsPerChip, maxMemoryPerChip, maxTotalColumns }

def aiurConfigToJson (c : Aiur.Optimized.Config) : Json :=
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

private def aiurConfigAllowedKeys : List String :=
  [ "maxDegree", "shareAuxiliaries", "eliminateSelectors", "propagateScopes",
    "simplifyConstraints", "propagateValues", "mergeLookups", "deduplicate" ]

def aiurConfigFromJson (j : Json) : Except String Aiur.Optimized.Config := do
  let entries ← expectObjEntries "aiurConfig" j
  checkAllowedKeys "aiurConfig" aiurConfigAllowedKeys entries
  let dflt : Aiur.Optimized.Config := {}
  let maxDegree ← optField entries "maxDegree" dflt.maxDegree (expectNat "aiurConfig.maxDegree")
  let shareAuxiliaries ← optField entries "shareAuxiliaries" dflt.shareAuxiliaries
    (expectBool "aiurConfig.shareAuxiliaries")
  let eliminateSelectors ← optField entries "eliminateSelectors" dflt.eliminateSelectors
    (expectBool "aiurConfig.eliminateSelectors")
  let propagateScopes ← optField entries "propagateScopes" dflt.propagateScopes
    (expectBool "aiurConfig.propagateScopes")
  let simplifyConstraints ← optField entries "simplifyConstraints" dflt.simplifyConstraints
    (expectBool "aiurConfig.simplifyConstraints")
  let propagateValues ← optField entries "propagateValues" dflt.propagateValues
    (expectBool "aiurConfig.propagateValues")
  let mergeLookups ← optField entries "mergeLookups" dflt.mergeLookups
    (expectBool "aiurConfig.mergeLookups")
  let deduplicate ← optField entries "deduplicate" dflt.deduplicate
    (expectBool "aiurConfig.deduplicate")
  return {
    maxDegree, shareAuxiliaries, eliminateSelectors, propagateScopes,
    simplifyConstraints, propagateValues, mergeLookups, deduplicate
  }

def byAddressToJson (entries : List (Address × FnSchedule)) : Json :=
  Json.mkObj (entries.map fun (addr, fs) => (addr.toHex, fnScheduleToJson fs))

def byAddressFromJson (j : Json) : Except String (List (Address × FnSchedule)) := do
  let entries ← expectObjEntries "byAddress" j
  entries.mapM fun (hex, v) => do
    let addr ← addressFromHex hex
    let fs ← fnScheduleFromJson v
    return (addr, fs)

def byFunToJson (entries : List (Fir.FunId × FnSchedule)) : Json :=
  Json.mkObj (entries.map fun (fid, fs) => (toString fid, fnScheduleToJson fs))

def byFunFromJson (j : Json) : Except String (List (Fir.FunId × FnSchedule)) := do
  let entries ← expectObjEntries "byFun" j
  let decoded ← entries.mapM fun (k, v) => do
    let some fid := parseCanonicalNat? k
      | throw s!"circuit-schedule: invalid FunId key '{k}' in byFun"
    let fs ← fnScheduleFromJson v
    return (fid, fs)
  return sortByNat (·.1) decoded

def groupsToJson (groups : List (String × List String)) : Json :=
  Json.mkObj (groups.map fun (name, chips) => (name, Json.arr (chips.map Json.str).toArray))

def groupsFromJson (j : Json) : Except String (List (String × List String)) := do
  let entries ← expectObjEntries "groups" j
  entries.mapM fun (name, v) => do
    let arr ← match v.getArr? with
      | .ok a => .ok a
      | .error _ => .error s!"circuit-schedule: expected array of chip names for group '{name}'"
    let chips ← arr.toList.mapM (expectStr s!"groups.{name}[]")
    return (name, chips)

/-! ## Top-level `CircuitSchedule` codec -/

private def scheduleAllowedKeys : List String :=
  [ "format", "rangeCheck", "autoInline", "inlineMaxNodes", "filterJpCaptures",
    "demandLink", "byAddress", "byFun", "groups", "aiurConfig", "budget" ]

/-- Deterministically encode a `CircuitSchedule` as `"ixcc/circuit-schedule/1"` JSON. -/
def toJson (sched : CircuitSchedule) : Json :=
  Json.mkObj [
    ("format", .str formatVersion),
    ("rangeCheck", rangeCheckModeToJson sched.rangeCheck),
    ("autoInline", .bool sched.autoInline),
    ("inlineMaxNodes", Json.num sched.inlineMaxNodes),
    ("filterJpCaptures", .bool sched.filterJpCaptures),
    ("demandLink", .bool sched.demandLink),
    ("byAddress", byAddressToJson sched.byAddress),
    ("byFun", byFunToJson sched.byFun),
    ("groups", groupsToJson sched.groups),
    ("aiurConfig", aiurConfigToJson sched.aiurConfig),
    ("budget", budgetToJson sched.budget)
  ]

/-- Decode a `"ixcc/circuit-schedule/1"` JSON value into a `CircuitSchedule`. -/
def fromJson (j : Json) : Except String CircuitSchedule := do
  let entries ← expectObjEntries "CircuitSchedule" j
  checkAllowedKeys "CircuitSchedule" scheduleAllowedKeys entries
  let some fmtJson := lookup? entries "format"
    | throw "circuit-schedule: missing required 'format' field"
  let fmt ← expectStr "format" fmtJson
  unless fmt == formatVersion do
    throw s!"circuit-schedule: unsupported format '{fmt}' (expected '{formatVersion}')"
  let dflt := CircuitSchedule.default
  let rangeCheck ← optField entries "rangeCheck" dflt.rangeCheck rangeCheckModeFromJson
  let autoInline ← optField entries "autoInline" dflt.autoInline (expectBool "autoInline")
  let inlineMaxNodes ← optField entries "inlineMaxNodes" dflt.inlineMaxNodes (expectNat "inlineMaxNodes")
  let filterJpCaptures ← optField entries "filterJpCaptures" dflt.filterJpCaptures
    (expectBool "filterJpCaptures")
  let demandLink ← optField entries "demandLink" dflt.demandLink (expectBool "demandLink")
  let byAddress ← optField entries "byAddress" [] byAddressFromJson
  let byFun ← optField entries "byFun" [] byFunFromJson
  let groups ← optField entries "groups" [] groupsFromJson
  let aiurConfig ← optField entries "aiurConfig" dflt.aiurConfig aiurConfigFromJson
  let budget ← optField entries "budget" dflt.budget budgetFromJson
  return {
    rangeCheck, autoInline, inlineMaxNodes, filterJpCaptures, demandLink,
    byAddress, byFun, groups, aiurConfig, budget
  }

/-- Pretty-print a `CircuitSchedule` as canonical `"ixcc/circuit-schedule/1"` JSON text. -/
def toJsonString (sched : CircuitSchedule) : String :=
  (toJson sched).pretty ++ "\n"

/-- Parse and decode untrusted `"ixcc/circuit-schedule/1"` JSON text, guarded by
`IxCC.Src.Hints.checkJsonText`. -/
def fromJsonString (text : String) : Except String CircuitSchedule := do
  IxCC.Src.Hints.checkJsonText text
  let j ← Json.parse text
  fromJson j

/-! ## Equality helper and verified round-trip checks -/

/-- Structural boolean equality on `CircuitSchedule` (mirrors all 10 fields). -/
def beqSchedule (a b : CircuitSchedule) : Bool :=
  a.rangeCheck == b.rangeCheck &&
  a.autoInline == b.autoInline &&
  a.inlineMaxNodes == b.inlineMaxNodes &&
  a.filterJpCaptures == b.filterJpCaptures &&
  a.demandLink == b.demandLink &&
  a.byAddress == b.byAddress &&
  a.byFun == b.byFun &&
  a.groups == b.groups &&
  a.aiurConfig == b.aiurConfig &&
  a.budget == b.budget

theorem rangeCheckMode_roundTrip (m : RangeCheckMode) :
    rangeCheckModeFromJson (rangeCheckModeToJson m) = .ok m := by
  cases m <;> rfl

theorem inlinePolicy_roundTrip (p : InlinePolicy) :
    inlinePolicyFromJson (inlinePolicyToJson p) = .ok p := by
  cases p <;> rfl

/-- Concrete sample schedule exercising every field of `CircuitSchedule`
(in canonical sorted key order for `byAddress`, `byFun`, and `groups`). -/
def sampleSchedule : CircuitSchedule :=
  { rangeCheck := .pairTable
    autoInline := false
    inlineMaxNodes := 64
    filterJpCaptures := false
    demandLink := true
    byAddress :=
      [ (Address.replicate 0x01,
          { inline := .always, group := some "hash_round", unroll := some 4, lanes := some 2 })
      , (Address.replicate 0xab,
          { inline := .never, group := none, unroll := none, lanes := some 8 }) ]
    byFun :=
      [ (0, { inline := .never, group := some "entry" })
      , (3, { inline := .always, unroll := some 2 }) ]
    groups :=
      [ ("entry", ["Prog::main0"])
      , ("hash_round", ["Prog::f1", "Prog::f2"]) ]
    aiurConfig :=
      { maxDegree := 4
        shareAuxiliaries := true
        eliminateSelectors := false
        propagateScopes := true
        simplifyConstraints := true
        propagateValues := false
        mergeLookups := true
        deduplicate := false }
    budget :=
      { maxChips := some 16
        maxColumns := some 256
        maxCallsPerChip := some 64
        maxMemoryPerChip := some 128
        maxTotalColumns := some 4096 } }

private def roundTrips (s : CircuitSchedule) : Bool :=
  match fromJson (toJson s) with
  | .ok decoded => beqSchedule decoded s
  | .error _ => false

/-- Kernel-checked round-trip of `sampleSchedule` through `toJson` / `fromJson`. -/
theorem sampleSchedule_roundTrip : roundTrips sampleSchedule = true := by
  decide

/-- Kernel-checked round-trip of `CircuitSchedule.default`. -/
theorem defaultSchedule_roundTrip : roundTrips CircuitSchedule.default = true := by
  decide

/-- Unsupported format tag is rejected. -/
theorem badFormat_rejected :
    (fromJson (Json.mkObj [("format", .str "ixcc/circuit-schedule/999")])).isOk = false := by
  decide

/-- Non-64-hex address key in `byAddress` is rejected. -/
theorem badAddress_rejected :
    (fromJson (Json.mkObj [
      ("format", .str formatVersion),
      ("byAddress", Json.mkObj [("deadbeef", Json.mkObj [])])
    ])).isOk = false := by
  decide

/-- Unknown key in `budget` (typo protection) is rejected fail-closed. -/
theorem unknownBudgetKey_rejected :
    (fromJson (Json.mkObj [
      ("format", .str formatVersion),
      ("budget", Json.mkObj [("maxColums", Json.num 10)])
    ])).isOk = false := by
  decide

/-- Concrete extended schedule exercising all 4 Wave-2 `Ix.Circuit` attributes
(`static`, `repr` across all 6 `CircuitRepr` constructors, `intrinsic`, and
`splitFastpath`) in canonical sorted key order. -/
def sampleExtendedSchedule : CircuitSchedule :=
  { rangeCheck := .smallTable
    autoInline := true
    inlineMaxNodes := 48
    filterJpCaptures := true
    demandLink := true
    byAddress :=
      [ (Address.replicate 0x01,
          { inline := .always, isStatic := true, repr := some .field })
      , (Address.replicate 0x02,
          { inline := .never, repr := some .u32, intrinsic := some "field.add" })
      , (Address.replicate 0x03,
          { inline := .auto, repr := some .u64, splitFastpath := true })
      , (Address.replicate 0x04,
          { inline := .never, repr := some (.limbs 4 64), intrinsic := some "field.mul" })
      , (Address.replicate 0x05,
          { inline := .auto, repr := some (.flatArray 16), isStatic := true, splitFastpath := true })
      , (Address.replicate 0x06,
          { inline := .never, group := some "stream", repr := some .wordStream,
            intrinsic := some "field.inv" }) ]
    byFun :=
      [ (0, { inline := .never, isStatic := true, repr := some .field })
      , (1, { inline := .always, intrinsic := some "field.sub", splitFastpath := true }) ]
    groups := [("stream", ["Prog::f2"])]
    aiurConfig := { maxDegree := 5 }
    budget := { maxChips := some 8 } }

/-- Kernel-checked round-trip of `sampleExtendedSchedule` covering all 4 Wave-2
attributes and all 6 `CircuitRepr` constructors. -/
theorem sampleExtendedSchedule_roundTrip : roundTrips sampleExtendedSchedule = true := by
  decide

/-- Legacy `FnSchedule` omits all 4 extended keys when set to defaults, keeping
encoded JSON identical to pre-Wave-2 output. -/
theorem legacyFnSchedule_omitsExtendedKeys :
    fnScheduleToJson { inline := .always, group := some "g", unroll := some 4, lanes := some 2 } =
      Json.mkObj [
        ("inline", .str "always"),
        ("group", .str "g"),
        ("unroll", Json.num 4),
        ("lanes", Json.num 2)
      ] :=
  rfl

/-- Unknown key in `FnSchedule` is rejected fail-closed. -/
theorem unknownFnScheduleKey_rejected :
    (fnScheduleFromJson (Json.mkObj [("statik", .bool true)])).isOk = false := by
  decide

/-- Non-boolean `"static"` field is rejected fail-closed. -/
theorem badStaticType_rejected :
    (fnScheduleFromJson (Json.mkObj [("static", Json.num 1)])).isOk = false := by
  decide

/-- Non-boolean `"splitFastpath"` field is rejected fail-closed. -/
theorem badSplitFastpathType_rejected :
    (fnScheduleFromJson (Json.mkObj [("splitFastpath", .str "yes")])).isOk = false := by
  decide

/-- Empty `"intrinsic"` string is rejected fail-closed. -/
theorem emptyIntrinsic_rejected :
    (fnScheduleFromJson (Json.mkObj [("intrinsic", .str "")])).isOk = false := by
  decide

/-- Invalid string `"repr"` tag is rejected fail-closed. -/
theorem badReprString_rejected :
    (circuitReprFromJson (.str "float")).isOk = false := by
  decide

/-- Unknown `"kind"` in structured `"repr"` object is rejected fail-closed. -/
theorem badReprKind_rejected :
    (circuitReprFromJson (Json.mkObj [("kind", .str "matrix")])).isOk = false := by
  decide

/-- Zero `count` or `bits` in `"limbs"` `CircuitRepr` is rejected fail-closed. -/
theorem zeroLimbsRepr_rejected :
    (circuitReprFromJson (Json.mkObj [("kind", .str "limbs"), ("count", Json.num 0), ("bits", Json.num 64)])).isOk = false ∧
    (circuitReprFromJson (Json.mkObj [("kind", .str "limbs"), ("count", Json.num 4), ("bits", Json.num 0)])).isOk = false := by
  decide

/-- Zero `len` in `"flat_array"` `CircuitRepr` is rejected fail-closed. -/
theorem zeroFlatArrayRepr_rejected :
    (circuitReprFromJson (Json.mkObj [("kind", .str "flat_array"), ("len", Json.num 0)])).isOk = false := by
  decide

/-- Unknown extra key inside structured `"repr"` object is rejected fail-closed. -/
theorem unknownReprKey_rejected :
    (circuitReprFromJson (Json.mkObj [("kind", .str "flat_array"), ("len", Json.num 4), ("extra", Json.num 1)])).isOk = false := by
  decide

end IxCC.AiurBackend.ScheduleJson
