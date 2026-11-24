import Lean

/-!
# Merge mechanical trust-ledger pins (`IxCC/docs/trusted-externs.json`)

Pure Lean 4 replacement for `IxCC/tools/record-ledger-pins.jq`.

Merges the mechanical pins printed by `check-trusted-externs --record` into
`docs/trusted-externs.json`, preserving every object's key order and exact
2-space pretty-printed JSON layout:

* `integrity.tracked_files`: changed values replaced in place, removed keys
  dropped, new keys appended in the order printed by `--record`.
* `integrity.repository_files`: initialized to `{}` if absent/null, then merged
  with the same key-order rule.
* `integrity.flake_nodes`: merged with the same key-order rule.
* `ci_actions`: each entry keeps its key order and fields (`version`, `use`, …)
  and updates `commit` when its `repository` appears in `pins.ci_actions`; new
  action repositories are not added here so the audit names them.
* Everything else (`schema_version`, `last_reviewed`, `seed_and_build_trust`,
  `specification_assumptions`, `lean_dependencies`, `csimp_theorems`,
  `required_checks`, …) is preserved verbatim.

## Usage

```
lean --run IxCC/tools/RecordLedgerPins.lean <pins.json> <ledger.json> [--out <path>]
lean --run IxCC/tools/RecordLedgerPins.lean --closure <pkg> <closure.json> <ledger.json> [--out <path>]
lean --run IxCC/tools/RecordLedgerPins.lean --selftest
```

When `--out` is omitted, `<ledger.json>` is updated atomically in place.
Pass `--out -` to write to standard output.
-/

namespace RecordLedgerPins

open System

/-! ## Order-preserving JSON AST, parser, and 2-space pretty-printer -/

inductive OrdJson where
  | null
  | bool (b : Bool)
  | num (raw : String)
  | str (s : String)
  | arr (items : Array OrdJson)
  | obj (entries : Array (String × OrdJson))
  deriving BEq, Repr, Inhabited

namespace Parser

structure State where
  bs : ByteArray
  pos : Nat

abbrev M := ExceptT String (StateM State)

@[inline] def getPos : M Nat := return (← get).pos
@[inline] def getBytes : M ByteArray := return (← get).bs
@[inline] def eof : M Bool := do let s ← get; return s.pos ≥ s.bs.size

@[inline] def peek? : M (Option UInt8) := do
  let s ← get
  if h : s.pos < s.bs.size then return some (s.bs[s.pos]) else return none

@[inline] def setPos (p : Nat) : M Unit :=
  modify fun s => { s with pos := p }

@[inline] def bump : M Unit :=
  modify fun s => { s with pos := s.pos + 1 }

def skipWs : M Unit := do
  let s ← get
  let mut p := s.pos
  let n := s.bs.size
  while p < n do
    let b := s.bs[p]!
    if b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0D then
      p := p + 1
    else
      break
  setPos p

def expectByte (want : UInt8) (what : String) : M Unit := do
  match ← peek? with
  | some b =>
    if b == want then bump
    else throw s!"expected {what} at byte {← getPos}"
  | none => throw s!"unexpected EOF, expected {what}"

def hexDigit? (b : UInt8) : Option Nat :=
  if 0x30 ≤ b && b ≤ 0x39 then some (b - 0x30).toNat
  else if 0x61 ≤ b && b ≤ 0x66 then some ((b - 0x61).toNat + 10)
  else if 0x41 ≤ b && b ≤ 0x46 then some ((b - 0x41).toNat + 10)
  else none

def parseHex4 : M Nat := do
  let mut acc := 0
  for _ in [0:4] do
    match ← peek? with
    | some b =>
      match hexDigit? b with
      | some d => acc := acc * 16 + d; bump
      | none => throw s!"invalid hex digit in \\u escape at byte {← getPos}"
    | none => throw "unexpected EOF in \\u escape"
  return acc

def pushUtf8 (out : ByteArray) (c : Char) : ByteArray :=
  out ++ (String.singleton c).toUTF8

def parseString : M String := do
  expectByte 0x22 "'\"'"
  let bs ← getBytes
  let n := bs.size
  let start ← getPos
  -- Fast path: scan until '"' or '\\'
  let mut p := start
  while p < n do
    let b := bs[p]!
    if b == 0x22 then
      let slice := bs.extract start p
      setPos (p + 1)
      match String.fromUTF8? slice with
      | some s => return s
      | none => throw s!"invalid UTF-8 in string ending at byte {p}"
    else if b == 0x5C then
      break
    else if b < 0x20 then
      throw s!"unescaped control byte {b} in string at byte {p}"
    else
      p := p + 1
  -- Slow path: string contains escape sequences
  let mut acc : ByteArray := bs.extract start p
  setPos p
  while true do
    let cur ← getPos
    if cur ≥ n then throw "unterminated JSON string"
    let b := bs[cur]!
    if b == 0x22 then
      setPos (cur + 1)
      match String.fromUTF8? acc with
      | some s => return s
      | none => throw s!"invalid UTF-8 in escaped string ending at byte {cur}"
    else if b == 0x5C then
      setPos (cur + 1)
      match ← peek? with
      | none => throw "unexpected EOF after '\\' in string"
      | some esc =>
        bump
        match esc with
        | 0x22 => acc := acc.push 0x22
        | 0x5C => acc := acc.push 0x5C
        | 0x2F => acc := acc.push 0x2F
        | 0x62 => acc := acc.push 0x08
        | 0x66 => acc := acc.push 0x0C
        | 0x6E => acc := acc.push 0x0A
        | 0x72 => acc := acc.push 0x0D
        | 0x74 => acc := acc.push 0x09
        | 0x75 =>
          let u1 ← parseHex4
          if 0xD800 ≤ u1 && u1 ≤ 0xDBFF then
            -- High surrogate: must be followed by \uDC00..\uDFFF
            expectByte 0x5C "'\\' for low surrogate"
            expectByte 0x75 "'u' for low surrogate"
            let u2 ← parseHex4
            unless 0xDC00 ≤ u2 && u2 ≤ 0xDFFF do
              throw s!"invalid low surrogate \\u{Nat.toDigits 16 u2 |> String.ofList}"
            let cp := 0x10000 + ((u1 - 0xD800) <<< 10) + (u2 - 0xDC00)
            acc := pushUtf8 acc (Char.ofNat cp)
          else if 0xDC00 ≤ u1 && u1 ≤ 0xDFFF then
            throw s!"unpaired low surrogate at byte {← getPos}"
          else
            acc := pushUtf8 acc (Char.ofNat u1)
        | _ => throw s!"invalid escape byte {esc} at byte {← getPos}"
    else if b < 0x20 then
      throw s!"unescaped control byte {b} in string at byte {cur}"
    else
      -- Copy contiguous non-escape chunk
      let mut q := cur + 1
      while q < n && bs[q]! != 0x22 && bs[q]! != 0x5C && bs[q]! ≥ 0x20 do
        q := q + 1
      acc := acc ++ bs.extract cur q
      setPos q
  throw "unreachable"

def isDigit (b : UInt8) : Bool := 0x30 ≤ b && b ≤ 0x39

def parseNumber : M String := do
  let bs ← getBytes
  let n := bs.size
  let start ← getPos
  let mut p := start
  if p < n && bs[p]! == 0x2D then p := p + 1
  if p ≥ n || !isDigit bs[p]! then
    throw s!"invalid JSON number at byte {start}"
  if bs[p]! == 0x30 then
    p := p + 1
  else
    while p < n && isDigit bs[p]! do p := p + 1
  if p < n && bs[p]! == 0x2E then
    p := p + 1
    if p ≥ n || !isDigit bs[p]! then
      throw s!"invalid fraction in JSON number at byte {p}"
    while p < n && isDigit bs[p]! do p := p + 1
  if p < n && (bs[p]! == 0x65 || bs[p]! == 0x45) then
    p := p + 1
    if p < n && (bs[p]! == 0x2B || bs[p]! == 0x2D) then p := p + 1
    if p ≥ n || !isDigit bs[p]! then
      throw s!"invalid exponent in JSON number at byte {p}"
    while p < n && isDigit bs[p]! do p := p + 1
  setPos p
  match String.fromUTF8? (bs.extract start p) with
  | some s => return s
  | none => throw s!"invalid UTF-8 in number at byte {start}"

def expectLiteral (lit : String) : M Unit := do
  let bs ← getBytes
  let pat := lit.toUTF8
  let p ← getPos
  if p + pat.size > bs.size then
    throw s!"unexpected EOF, expected '{lit}'"
  for j in [0:pat.size] do
    if bs[p + j]! != pat[j]! then
      throw s!"expected '{lit}' at byte {p}"
  setPos (p + pat.size)

partial def parseValue : M OrdJson := do
  skipWs
  match ← peek? with
  | none => throw s!"unexpected EOF at byte {← getPos}"
  | some 0x6E => expectLiteral "null"; return .null
  | some 0x74 => expectLiteral "true"; return .bool true
  | some 0x66 => expectLiteral "false"; return .bool false
  | some 0x22 => return .str (← parseString)
  | some 0x5B =>
    bump
    skipWs
    let mut items : Array OrdJson := #[]
    if (← peek?) == some 0x5D then
      bump
      return .arr items
    while true do
      items := items.push (← parseValue)
      skipWs
      match ← peek? with
      | some 0x2C => bump
      | some 0x5D => bump; break
      | _ => throw s!"expected ',' or ']' in array at byte {← getPos}"
    return .arr items
  | some 0x7B =>
    bump
    skipWs
    let mut entries : Array (String × OrdJson) := #[]
    let mut indexByKey : Std.HashMap String Nat := {}
    if (← peek?) == some 0x7D then
      bump
      return .obj entries
    while true do
      skipWs
      let key ← parseString
      skipWs
      expectByte 0x3A "':'"
      let val ← parseValue
      -- Keep jq's last-wins behavior if a key appears twice in an input object.
      match indexByKey.get? key with
      | some idx => entries := entries.set! idx (key, val)
      | none =>
        indexByKey := indexByKey.insert key entries.size
        entries := entries.push (key, val)
      skipWs
      match ← peek? with
      | some 0x2C => bump
      | some 0x7D => bump; break
      | _ => throw s!"expected ',' or '}}' in object at byte {← getPos}"
    return .obj entries
  | some b =>
    if b == 0x2D || isDigit b then
      return .num (← parseNumber)
    throw s!"unexpected byte {b} at byte {← getPos}"

def parse (text : String) : Except String OrdJson :=
  let (res, st) := (do
    let v ← parseValue
    skipWs
    unless ← eof do
      throw s!"trailing characters after JSON value at byte {← getPos}"
    return v).run { bs := text.toUTF8, pos := 0 }
  let _ := st
  res

end Parser

def hexNibble (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n) else Char.ofNat (0x61 + (n - 10))

/-- JSON string encoding matching RFC 8259 and `jq` (UTF-8 passed verbatim). -/
def encodeString (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    match c with
    | '"'  => out := out ++ "\\\""
    | '\\' => out := out ++ "\\\\"
    | '\x08' => out := out ++ "\\b"
    | '\x0c' => out := out ++ "\\f"
    | '\n' => out := out ++ "\\n"
    | '\r' => out := out ++ "\\r"
    | '\t' => out := out ++ "\\t"
    | c =>
      let code := c.toNat
      if code < 0x20 then
        out := out ++ "\\u00" ++ String.singleton (hexNibble (code / 16))
          ++ String.singleton (hexNibble (code % 16))
      else
        out := out.push c
  return out.push '"'

def spaces (n : Nat) : String :=
  String.ofList (List.replicate n ' ')

partial def render (indent : Nat) : OrdJson → String
  | .null => "null"
  | .bool true => "true"
  | .bool false => "false"
  | .num raw => raw
  | .str s => encodeString s
  | .arr items =>
    if items.isEmpty then "[]"
    else
      let childIndent := indent + 2
      let pad := spaces childIndent
      let body := ",\n".intercalate (items.toList.map fun item => pad ++ render childIndent item)
      s!"[\n{body}\n{spaces indent}]"
  | .obj entries =>
    if entries.isEmpty then "{}"
    else
      let childIndent := indent + 2
      let pad := spaces childIndent
      let body := ",\n".intercalate (entries.toList.map fun (k, v) =>
        s!"{pad}{encodeString k}: {render childIndent v}")
      s!"\{\n{body}\n{spaces indent}}"

def pretty (j : OrdJson) : String :=
  render 0 j ++ "\n"

/-! ## Object helpers & merge logic (matching `record-ledger-pins.jq`) -/

def asObj (label : String) : OrdJson → Except String (Array (String × OrdJson))
  | .obj kvs => .ok kvs
  | _ => .error s!"expected JSON object for {label}"

def asArr (label : String) : OrdJson → Except String (Array OrdJson)
  | .arr xs => .ok xs
  | _ => .error s!"expected JSON array for {label}"

def findKey? (kvs : Array (String × OrdJson)) (key : String) : Option OrdJson :=
  (kvs.find? (fun kv => kv.1 == key)).map (·.2)

def setKeyInPlace (kvs : Array (String × OrdJson)) (key : String) (val : OrdJson) :
    Array (String × OrdJson) :=
  match kvs.findIdx? (fun kv => kv.1 == key) with
  | some idx => kvs.set! idx (key, val)
  | none => kvs.push (key, val)

/-- Order-preserving object merge matching `record-ledger-pins.jq`:
kept keys stay in `old`'s order with `new`'s values, keys missing from `new`
are dropped, and keys new in `new` are appended in `new`'s order. -/
def mergeEntries (old new : Array (String × OrdJson)) : Array (String × OrdJson) := Id.run do
  let mut newMap : Std.HashMap String OrdJson := {}
  for (k, v) in new do
    newMap := newMap.insert k v
  let mut out : Array (String × OrdJson) := Array.emptyWithCapacity new.size
  let mut seen : Std.HashSet String := {}
  for (k, _) in old do
    if let some nv := newMap.get? k then
      out := out.push (k, nv)
      seen := seen.insert k
  for (k, v) in new do
    if !seen.contains k then
      out := out.push (k, v)
  return out

def requireField (kvs : Array (String × OrdJson)) (key parent : String) : Except String OrdJson :=
  match findKey? kvs key with
  | some v => .ok v
  | none => .error s!"missing field '{key}' in {parent}"

/-- Merge mechanical pins printed by `check-trusted-externs --record` into the ledger. -/
def mergePins (ledger pins : OrdJson) : Except String OrdJson := do
  let ledgerKvs ← asObj "ledger" ledger
  let pinsKvs ← asObj "pins" pins

  let pinsTracked ← asObj "pins.tracked_files" (← requireField pinsKvs "tracked_files" "pins")
  let pinsRepo ← asObj "pins.repository_files" (← requireField pinsKvs "repository_files" "pins")
  let pinsFlake ← asObj "pins.flake_nodes" (← requireField pinsKvs "flake_nodes" "pins")
  let pinsCi ← asObj "pins.ci_actions" (← requireField pinsKvs "ci_actions" "pins")

  let mut ciMap : Std.HashMap String OrdJson := {}
  for (repo, commit) in pinsCi do
    if commit != .null then
      ciMap := ciMap.insert repo commit

  let integrityKvs ← asObj "ledger.integrity" (← requireField ledgerKvs "integrity" "ledger")
  let oldTracked ← asObj "ledger.integrity.tracked_files"
    (← requireField integrityKvs "tracked_files" "ledger.integrity")
  let oldRepo ← match findKey? integrityKvs "repository_files" with
    | none | some .null => pure #[]
    | some v => asObj "ledger.integrity.repository_files" v
  let oldFlake ← asObj "ledger.integrity.flake_nodes"
    (← requireField integrityKvs "flake_nodes" "ledger.integrity")

  let newIntegrity :=
    setKeyInPlace
      (setKeyInPlace
        (setKeyInPlace integrityKvs "tracked_files" (.obj (mergeEntries oldTracked pinsTracked)))
        "repository_files" (.obj (mergeEntries oldRepo pinsRepo)))
      "flake_nodes" (.obj (mergeEntries oldFlake pinsFlake))

  let oldCiActions ← asArr "ledger.ci_actions" (← requireField ledgerKvs "ci_actions" "ledger")
  let newCiActions ← oldCiActions.mapM fun entry => do
    let kvs ← asObj "ledger.ci_actions[]" entry
    match findKey? kvs "repository" with
    | some (.str repo) =>
      match ciMap.get? repo with
      | some newCommit => return .obj (setKeyInPlace kvs "commit" newCommit)
      | none => return entry
    | _ => return entry

  let updated :=
    setKeyInPlace
      (setKeyInPlace ledgerKvs "integrity" (.obj newIntegrity))
      "ci_actions" (.arr newCiActions)
  return .obj updated

/-- Update `.lean_dependencies[lake_package == pkg].closure` hashes in place while
preserving key order and leaving every other field untouched. -/
def mergeClosure (ledger closureJson : OrdJson) (lakePkg : String) : Except String OrdJson := do
  let ledgerKvs ← asObj "ledger" ledger
  let closureKvs ← asObj "closure" closureJson
  let mut closureMap : Std.HashMap String OrdJson := {}
  for (k, v) in closureKvs do
    if v != .null then
      closureMap := closureMap.insert k v

  let deps ← asArr "ledger.lean_dependencies" (← requireField ledgerKvs "lean_dependencies" "ledger")
  let newDeps ← deps.mapM fun dep => do
    let depKvs ← asObj "ledger.lean_dependencies[]" dep
    if findKey? depKvs "lake_package" == some (.str lakePkg) then
      let oldClosure ← asObj s!"lean_dependencies[{lakePkg}].closure"
        (← requireField depKvs "closure" s!"lean_dependencies[{lakePkg}]")
      let updatedClosure := oldClosure.map fun (path, oldHash) =>
        match closureMap.get? path with
        | some newHash => (path, newHash)
        | none => (path, oldHash)
      return .obj (setKeyInPlace depKvs "closure" (.obj updatedClosure))
    else
      return dep
  return .obj (setKeyInPlace ledgerKvs "lean_dependencies" (.arr newDeps))

/-! ## Atomic output and `Lean.Json` validation -/

def writeOutput (target : Option FilePath) (ledgerPath : FilePath) (rendered : String) : IO Unit := do
  -- Sanity-check rendered output with Lean's own JSON parser.
  match Lean.Json.parse rendered with
  | .error e => throw <| IO.userError s!"internal error: rendered invalid JSON: {e}"
  | .ok _ => pure ()
  match target with
  | some (FilePath.mk "-") =>
    IO.print rendered
  | some outPath =>
    if let some parent := outPath.parent then
      if !parent.toString.isEmpty then IO.FS.createDirAll parent
    let tmp : FilePath := outPath.toString ++ ".tmp"
    IO.FS.writeFile tmp rendered
    IO.FS.rename tmp outPath
  | none =>
    let tmp : FilePath := ledgerPath.toString ++ ".tmp"
    IO.FS.writeFile tmp rendered
    IO.FS.rename tmp ledgerPath

/-! ## Built-in unit self-tests -/

def assertEq (label got want : String) : IO Unit := do
  unless got == want do
    throw <| IO.userError s!"selftest FAILED [{label}]:\n--- got ---\n{got}--- want ---\n{want}"

def runSelfTests : IO Unit := do
  let sampleLedger :=
    "{\n\
     \x20 \"schema_version\": 2,\n\
     \x20 \"last_reviewed\": \"2026-11-21\",\n\
     \x20 \"native_interfaces\": [],\n\
     \x20 \"integrity\": {\n\
     \x20   \"tracked_files\": {\n\
     \x20     \"b.lean\": \"old-b\",\n\
     \x20     \"removed.sh\": \"old-rm\",\n\
     \x20     \"a.lean\": \"same-a\"\n\
     \x20   },\n\
     \x20   \"flake_nodes\": {\n\
     \x20     \"nixpkgs\": \"old-nix\",\n\
     \x20     \"dropped\": \"old-drop\"\n\
     \x20   }\n\
     \x20 },\n\
     \x20 \"ci_actions\": [\n\
     \x20   {\n\
     \x20     \"repository\": \"actions/checkout\",\n\
     \x20     \"version\": \"v4\",\n\
     \x20     \"commit\": \"old-sha\",\n\
     \x20     \"use\": \"checkout\"\n\
     \x20   },\n\
     \x20   {\n\
     \x20     \"repository\": \"unmentioned/action\",\n\
     \x20     \"commit\": \"keep-sha\"\n\
     \x20   }\n\
     \x20 ],\n\
     \x20 \"lean_dependencies\": [\n\
     \x20   {\n\
     \x20     \"lake_package\": \"«ix-ck»\",\n\
     \x20     \"closure\": {\n\
     \x20       \"z.lean\": \"hz0\",\n\
     \x20       \"a.lean\": \"ha0\"\n\
     \x20     }\n\
     \x20   }\n\
     \x20 ],\n\
     \x20 \"required_checks\": [\n\
     \x20   \"build\"\n\
     \x20 ]\n\
     }\n"

  -- 1. Round-trip fidelity (exact key order, empty arrays, UTF-8 «ix-ck», 2-space indent)
  let parsedLedger ← IO.ofExcept (Parser.parse sampleLedger)
  assertEq "roundtrip formatting" (pretty parsedLedger) sampleLedger

  -- 2. Merge pins: preserve key order, drop removed, append new, init missing repository_files,
  --    update known ci_actions in place, ignore unknown ci_actions, preserve unrelated fields.
  let samplePins :=
    "{\n\
     \x20 \"tracked_files\": {\n\
     \x20   \"a.lean\": \"same-a\",\n\
     \x20   \"b.lean\": \"new-b\",\n\
     \x20   \"c.lean\": \"new-c\"\n\
     \x20 },\n\
     \x20 \"repository_files\": {\n\
     \x20   \".github/workflows/ixcc.yml\": \"wf-sha\"\n\
     \x20 },\n\
     \x20 \"flake_nodes\": {\n\
     \x20   \"lean4-nix\": \"new-lean\",\n\
     \x20   \"nixpkgs\": \"new-nix\"\n\
     \x20 },\n\
     \x20 \"ci_actions\": {\n\
     \x20   \"actions/checkout\": \"new-sha\",\n\
     \x20   \"extra/untracked\": \"ignored-sha\"\n\
     \x20 }\n\
     }\n"

  let wantMerged :=
    "{\n\
     \x20 \"schema_version\": 2,\n\
     \x20 \"last_reviewed\": \"2026-11-21\",\n\
     \x20 \"native_interfaces\": [],\n\
     \x20 \"integrity\": {\n\
     \x20   \"tracked_files\": {\n\
     \x20     \"b.lean\": \"new-b\",\n\
     \x20     \"a.lean\": \"same-a\",\n\
     \x20     \"c.lean\": \"new-c\"\n\
     \x20   },\n\
     \x20   \"flake_nodes\": {\n\
     \x20     \"nixpkgs\": \"new-nix\",\n\
     \x20     \"lean4-nix\": \"new-lean\"\n\
     \x20   },\n\
     \x20   \"repository_files\": {\n\
     \x20     \".github/workflows/ixcc.yml\": \"wf-sha\"\n\
     \x20   }\n\
     \x20 },\n\
     \x20 \"ci_actions\": [\n\
     \x20   {\n\
     \x20     \"repository\": \"actions/checkout\",\n\
     \x20     \"version\": \"v4\",\n\
     \x20     \"commit\": \"new-sha\",\n\
     \x20     \"use\": \"checkout\"\n\
     \x20   },\n\
     \x20   {\n\
     \x20     \"repository\": \"unmentioned/action\",\n\
     \x20     \"commit\": \"keep-sha\"\n\
     \x20   }\n\
     \x20 ],\n\
     \x20 \"lean_dependencies\": [\n\
     \x20   {\n\
     \x20     \"lake_package\": \"«ix-ck»\",\n\
     \x20     \"closure\": {\n\
     \x20       \"z.lean\": \"hz0\",\n\
     \x20       \"a.lean\": \"ha0\"\n\
     \x20     }\n\
     \x20   }\n\
     \x20 ],\n\
     \x20 \"required_checks\": [\n\
     \x20   \"build\"\n\
     \x20 ]\n\
     }\n"

  let parsedPins ← IO.ofExcept (Parser.parse samplePins)
  let merged1 ← IO.ofExcept (mergePins parsedLedger parsedPins)
  assertEq "mergePins" (pretty merged1) wantMerged

  -- 3. Idempotence
  let merged2 ← IO.ofExcept (mergePins merged1 parsedPins)
  assertEq "mergePins idempotence" (pretty merged2) wantMerged

  -- 4. Closure update preserving key order
  let closureUpdate ← IO.ofExcept (Parser.parse "{\"a.lean\": \"ha1\", \"unused.lean\": \"hu\"}")
  let mergedCl ← IO.ofExcept (mergeClosure merged1 closureUpdate "«ix-ck»")
  let mergedCl2 ← IO.ofExcept (mergeClosure mergedCl closureUpdate "«ix-ck»")
  assertEq "mergeClosure idempotence" (pretty mergedCl2) (pretty mergedCl)
  unless ((pretty mergedCl).splitOn "\"z.lean\": \"hz0\",\n        \"a.lean\": \"ha1\"").length == 2 do
    throw <| IO.userError s!"selftest FAILED [mergeClosure]: unexpected output:\n{pretty mergedCl}"

  -- 5. Escapes & Lean.Json cross-check
  let escSample := "{\"s\": \"a\\\"b\\\\c/d\\ne\\tf\\rg\\b\\f\\u0001«–¬»\", \"empty\": {}}\n"
  let parsedEsc ← IO.ofExcept (Parser.parse escSample)
  match Lean.Json.parse (pretty parsedEsc) with
  | .error e => throw <| IO.userError s!"selftest FAILED [Lean.Json cross-check]: {e}"
  | .ok j =>
    let some (.str s) := (j.getObjVal? "s").toOption
      | throw <| IO.userError "selftest FAILED [escape lookup]"
    unless s == "a\"b\\c/d\ne\tf\rg\x08\x0c\x01«–¬»" do
      throw <| IO.userError s!"selftest FAILED [escape decode]: got {repr s}"

  IO.println "[record-ledger-pins] selftest passed (all 6 assertions)"

/-! ## CLI entry point -/

def usageText : String :=
  "Usage:\n\
   \x20 lean --run IxCC/tools/RecordLedgerPins.lean <pins.json> <ledger.json> [--out <path>]\n\
   \x20 lean --run IxCC/tools/RecordLedgerPins.lean --closure <pkg> <closure.json> <ledger.json> [--out <path>]\n\
   \x20 lean --run IxCC/tools/RecordLedgerPins.lean --selftest\n\
   \n\
   Omit --out to update <ledger.json> atomically in place; pass --out - for stdout."

inductive Mode where
  | help
  | selftest
  | pins (pinsPath ledgerPath : FilePath) (outPath : Option FilePath)
  | closure (pkg : String) (closurePath ledgerPath : FilePath) (outPath : Option FilePath)

def parseArgs (args : List String) : Except String Mode := do
  match args with
  | ["--help"] | ["-h"] => return .help
  | ["--selftest"] => return .selftest
  | "--closure" :: pkg :: closurePath :: ledgerPath :: rest =>
    match rest with
    | [] => return .closure pkg closurePath ledgerPath none
    | ["--out", outPath] => return .closure pkg closurePath ledgerPath (some outPath)
    | _ => throw s!"unexpected arguments: {rest}"
  | pinsPath :: ledgerPath :: rest =>
    if pinsPath.startsWith "-" then throw s!"unknown option: {pinsPath}"
    match rest with
    | [] => return .pins pinsPath ledgerPath none
    | ["--out", outPath] => return .pins pinsPath ledgerPath (some outPath)
    | _ => throw s!"unexpected arguments: {rest}"
  | _ => throw "expected <pins.json> <ledger.json> [--out <path>] (try --help)"

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error e =>
    IO.eprintln s!"record-ledger-pins: {e}\n{usageText}"
    return 2
  | .ok .help =>
    IO.println usageText
    return 0
  | .ok .selftest =>
    runSelfTests
    return 0
  | .ok (.pins pinsPath ledgerPath outPath) =>
    let pins ← IO.ofExcept (Parser.parse (← IO.FS.readFile pinsPath))
    let ledger ← IO.ofExcept (Parser.parse (← IO.FS.readFile ledgerPath))
    let merged ← IO.ofExcept (mergePins ledger pins)
    writeOutput outPath ledgerPath (pretty merged)
    return 0
  | .ok (.closure pkg closurePath ledgerPath outPath) =>
    let cl ← IO.ofExcept (Parser.parse (← IO.FS.readFile closurePath))
    let ledger ← IO.ofExcept (Parser.parse (← IO.FS.readFile ledgerPath))
    let merged ← IO.ofExcept (mergeClosure ledger cl pkg)
    writeOutput outPath ledgerPath (pretty merged)
    return 0

end RecordLedgerPins

def main (args : List String) : IO UInt32 := RecordLedgerPins.main args
