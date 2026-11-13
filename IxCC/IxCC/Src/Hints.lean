import IxCC.Src.Syntax
import IxCC.Ixon.V3.Support
import Lean.Data.Json.Basic
import Lean.Data.Json.Parser

/-! # Unfolding-table hints

Untrusted, unauthenticated proposals for the unfolding table. Every address must resolve in the
closure and every proposal must pass its `Table.Check` check. Ordinary missing or refused hints
degrade to the kernel body; an explicit resource checked-pair claim instead requires its
equation to be selected. Names are diagnostic only. -/

namespace IxCC.Src

open IxCC.Ixon Lean

inductive ProposalKind where
  | eqn
  | csimp
  | lazy
  | inline
  | case
  /-- A fixed-width word operation and its stored equation (stage W1, the sidecar's `theorems`
  list, kind `word`). -/
  | word
  deriving BEq, DecidableEq, Repr, Inhabited

/-- One untrusted table proposal: `eqn f thm`, `csimp f g thm`, `lazy f a`,
`inline f`, `case f` or `word f thm`. -/
structure Proposal where
  kind : ProposalKind
  subject : Ixon.Address
  theorem? : Option Ixon.Address := none
  target? : Option Ixon.Address := none
  arity? : Option Nat := none
  /-- Untrusted name from the sidecar, for diagnostics only. -/
  name? : Option String := none
  deriving Repr, Inhabited

/-- A parsed sidecar: the roots it names and its proposals. -/
structure Hints where
  roots : Array (Ixon.Address × Option String) := #[]
  proposals : Array Proposal := #[]
  resource : Option Resource.Context := none
  deriving Inhabited

namespace Hints

private def str (j : Json) (key : String) : Except String String := do
  (← j.getObjVal? key).getStr?

private def address (j : Json) (key : String) : Except String Ixon.Address := do
  let text ← str j key
  match Ixon.Address.fromString text with
  | some a => pure a
  | none => throw s!"hints: invalid address {text}"

private def hexBytes (text : String) : Except String ByteArray := do
  unless text.length ≤ 2 * 1024 * 1024 do throw "hints: resource profile byte budget exceeded"
  let digit := fun c =>
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none
  let rec go : List Char → ByteArray → Except String ByteArray
    | [], bytes => pure bytes
    | a :: b :: rest, bytes => do
      let some a := digit a | throw "hints: noncanonical profile hex"
      let some b := digit b | throw "hints: noncanonical profile hex"
      go rest (bytes.push (16 * a + b).toUInt8)
    | [_], _ => throw "hints: odd profile hex length"
  go text.toList .empty

private def header (j : Json) : Except String Resource.Header := do
  let position ← (← j.getObjVal? "position").getNat?
  let _ ← str j "binder" -- diagnostic spelling has no identity role
  let uses ← match ← str j "uses" with
    | "erased" => pure Uses.erased
    | "linear" => pure .linear
    | "affine" => pure .affine
    | "many" => pure .many
    | _ => throw "hints: unknown header usage"
  let owned ← match ← str j "owned" with
    | "shared" => pure Owned.shared
    | "unique" => pure .unique
    | _ => throw "hints: unknown header ownership"
  let locality ← match ← str j "locality" with
    | "unrestricted" => pure V3.Locality.unrestricted
    | "local" => pure .local
    | _ => throw "hints: unknown header locality"
  return { position, contract := { uses, value := { owned, locality } } }

/-- Optional only when both keys are absent. A present malformed record never
degrades into the legacy no-resource path. -/
def resourceOfJson (j : Json) : Except String (Option Resource.Context) := do
  match j.getObjVal? "resource_profile", j.getObjVal? "resource_checked" with
  | .error _, .error _ => pure none
  | .ok profile, .ok pairs => do
    let profileAddress ← address profile "address"
    let bytes ← hexBytes (← str profile "bytes")
    let pairs ← (← pairs.getArr?).toList.mapM fun pair => do
      let _ ← str pair "definition"
      let _ ← str pair "equation"
      return ({ definition := ← address pair "definition_address"
                equation := ← address pair "equation_address"
                profile := ← address pair "profile"
                contracts := ← (← (← pair.getObjVal? "contracts").getArr?).toList.mapM header } : Resource.Pair)
    return some { address := profileAddress, bytes, pairs }
  | _, _ => throw "hints: resource profile and checked pairs must occur together"

/-- The kinds of the sidecar's `theorems` list (a theorem named with its subject and a kind; only
`word` so far). -/
def theoremKind : String → Except String ProposalKind
  | "word" => pure .word
  | k => throw s!"hints: unknown theorem kind {k}"

/-- Read an `ixcc/k1-equations/1` file: the roots, one `eqn`
proposal per `(definition_address, equation_address)` pair, and, from the optional
`theorems` list, one proposal of the entry's kind per
`(subject_address, theorem_address)` pair. -/
def ofK1Json (j : Json) : Except String Hints := do
  let format ← str j "format"
  unless format == "ixcc/k1-equations/1" do
    throw s!"hints: unsupported format {format}"
  let mut roots := #[]
  for r in ← (← j.getObjVal? "roots").getArr? do
    roots := roots.push (← address r "address", (str r "name").toOption)
  let mut proposals := #[]
  for e in ← (← j.getObjVal? "equations").getArr? do
    proposals := proposals.push {
      kind := .eqn, subject := ← address e "definition_address"
      theorem? := some (← address e "equation_address")
      name? := (str e "definition").toOption }
  let theorems ← match j.getObjVal? "theorems" with
    | .ok t => t.getArr?
    | .error _ => pure #[]
  for e in theorems do
    proposals := proposals.push {
      kind := ← theoremKind (← str e "kind"), subject := ← address e "subject_address"
      theorem? := some (← address e "theorem_address")
      name? := (str e "subject").toOption }
  return { roots, proposals, resource := ← resourceOfJson j }

/-- Maximum JSON text size in UTF-8 bytes (64 MiB). -/
def maxJsonTextBytes : Nat := 67108864

/-- Maximum JSON container nesting depth. -/
def maxJsonDepth : Nat := 512

/-- Maximum digits in a JSON number token. -/
def maxJsonDigits : Nat := 32

/-- What one pass over a JSON text measures outside its string literals (`scanJson`): the
deepest nesting of `[` and `{`, the longest number token, and whether a number has an exponent
or a fraction. -/
structure JsonScan where
  inString : Bool := false
  escaped : Bool := false
  depth : Nat := 0
  maxDepth : Nat := 0
  digits : Nat := 0
  maxDigits : Nat := 0
  expOrFrac : Bool := false

/-- One character of the scan. -/
def JsonScan.step (s : JsonScan) (c : Char) : JsonScan :=
  if s.inString then
    if s.escaped then { s with escaped := false }
    else if c == '\\' then { s with escaped := true }
    else if c == '"' then { s with inString := false }
    else s
  else if c == '"' then { s with inString := true, digits := 0 }
  else if c.isDigit then
    let d := s.digits + 1
    { s with digits := d, maxDigits := max s.maxDigits d }
  else if s.digits > 0 && (c == 'e' || c == 'E' || c == '.') then
    { s with expOrFrac := true, digits := 0 }
  else if c == '[' || c == '{' then
    let d := s.depth + 1
    { s with depth := d, maxDepth := max s.maxDepth d, digits := 0 }
  else if c == ']' || c == '}' then { s with depth := s.depth - 1, digits := 0 }
  else { s with digits := 0 }

/-- A linear scan of `text` (a loop over its characters, no list). -/
def scanJson (text : String) : JsonScan := text.foldl JsonScan.step {}

/-- Run before parsing any untrusted JSON (certificates and the equations sidecar): refuses a text
over `maxJsonTextBytes`, nested deeper than `maxJsonDepth`, with a number token longer than
`maxJsonDigits`, or with an exponent or a fraction (`Lean.Json.parse` materialises an exponent as a
`Nat` and panics, uncatchably, on `1e100000000000`). Each refusal names its limit and the value
measured on the whole text. -/
def checkJsonText (text : String) : Except String Unit :=
  if text.utf8ByteSize > maxJsonTextBytes then
    .error s!"JSON text size {text.utf8ByteSize} exceeds maximum {maxJsonTextBytes}"
  else
    let s := scanJson text
    if s.maxDepth > maxJsonDepth then
      .error s!"JSON nesting depth {s.maxDepth} exceeds maximum {maxJsonDepth}"
    else if s.maxDigits > maxJsonDigits then
      .error s!"JSON number token of {s.maxDigits} digits exceeds maximum {maxJsonDigits}"
    else if s.expOrFrac then .error "scientific or fractional number"
    else .ok ()

def ofK1String (text : String) : Except String Hints := do
  checkJsonText text
  ofK1Json (← Json.parse text)

end Hints

end IxCC.Src
