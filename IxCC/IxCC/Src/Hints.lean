import IxCC.Src.Syntax
import IxCC.Ixon.V3.Support
import Lean.Data.Json.Basic
import Lean.Data.Json.Parser

/-! # Unfolding-table hints

Untrusted, unauthenticated proposals for the unfolding table. Every address must resolve in the
closure and every proposal must pass its `Table.Check` check. Missing or refused hints
degrade to the kernel body. Names are diagnostic only. -/

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
  /-- A Phase 2.2 Tier-2 guess-and-verify proposal (`guess f c θ [θc]`). -/
  | guess
  deriving BEq, DecidableEq, Repr, Inhabited

/-- One untrusted table proposal: `eqn f thm`, `csimp f g thm`, `lazy f a`,
`inline f`, `case f`, `word f thm` or `guess f c thm [comp?]`. -/
structure Proposal where
  kind : ProposalKind
  subject : Ixon.Address
  theorem? : Option Ixon.Address := none
  target? : Option Ixon.Address := none
  arity? : Option Nat := none
  /-- Checker constant address for a `guess` proposal (`c` in `guess f c θ [θc]`). -/
  checker? : Option Ixon.Address := none
  /-- Optional completeness theorem address for a `guess` proposal (`θc` in `guess f c θ [θc]`). -/
  comp? : Option Ixon.Address := none
  /-- Untrusted name from the sidecar, for diagnostics only. -/
  name? : Option String := none
  deriving Repr, Inhabited

/-- A parsed sidecar: the roots it names and its proposals. -/
structure Hints where
  roots : Array (Ixon.Address × Option String) := #[]
  proposals : Array Proposal := #[]
  deriving Inhabited

namespace Hints

private def str (j : Json) (key : String) : Except String String := do
  (← j.getObjVal? key).getStr?

private def address (j : Json) (key : String) : Except String Ixon.Address := do
  let text ← str j key
  match Ixon.Address.fromString text with
  | some a => pure a
  | none => throw s!"hints: invalid address {text}"

/-- The kinds of the sidecar's `theorems` list (a theorem named with its subject and a kind; only
`word` so far). -/
def theoremKind : String → Except String ProposalKind
  | "word" => pure .word
  | k => throw s!"hints: unknown theorem kind {k}"

/-- Read an `ixcc/k1-equations/1` file: the roots, one `eqn`
proposal per `(definition_address, equation_address)` pair, from the optional
`theorems` list one proposal of the entry's kind per `(subject_address, theorem_address)` pair,
and from the optional `guesses` list one `guess` proposal per
`(subject_address, checker_address, theorem_address, [completeness_address])` entry. -/
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
  let guesses ← match j.getObjVal? "guesses" with
    | .ok g => g.getArr?
    | .error _ => pure #[]
  for e in guesses do
    let comp? ← match e.getObjVal? "completeness_address" with
      | .ok .null => pure none
      | .ok _ => some <$> address e "completeness_address"
      | .error _ => pure none
    proposals := proposals.push {
      kind := .guess
      subject := ← address e "subject_address"
      checker? := some (← address e "checker_address")
      theorem? := some (← address e "theorem_address")
      comp?
      name? := (str e "subject").toOption }
  return { roots, proposals }

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

/-- Serialize `Hints` (roots, `.eqn` equations, `.word` theorems, and `.guess` entries) into
canonical `ixcc/k1-equations/1` JSON that round-trips through `ofK1Json`. -/
def toK1Json (h : Hints) (source : String := "<auto-hints>") : Json :=
  let rootRows := h.roots.map fun (addr, name?) =>
    let base := [("address", Json.str (toString addr))]
    Json.mkObj (match name? with | some n => ("name", Json.str n) :: base | none => base)
  let eqRows := h.proposals.filterMap fun p =>
    if p.kind == .eqn then
      p.theorem?.map fun thm =>
        let base := [
          ("definition_address", Json.str (toString p.subject)),
          ("equation_address", Json.str (toString thm))
        ]
        Json.mkObj (match p.name? with | some n => ("definition", Json.str n) :: base | none => base)
    else none
  let thmRows := h.proposals.filterMap fun p =>
    if p.kind == .word then
      p.theorem?.map fun thm =>
        let base := [
          ("kind", Json.str "word"),
          ("subject_address", Json.str (toString p.subject)),
          ("theorem_address", Json.str (toString thm))
        ]
        Json.mkObj (match p.name? with | some n => ("subject", Json.str n) :: base | none => base)
    else none
  let guessRows := h.proposals.filterMap fun p =>
    if p.kind == .guess then
      match p.checker?, p.theorem? with
      | some chk, some thm =>
        let base := [
          ("subject_address", Json.str (toString p.subject)),
          ("checker_address", Json.str (toString chk)),
          ("theorem_address", Json.str (toString thm))
        ] ++ (match p.comp? with
          | some comp => [("completeness_address", Json.str (toString comp))]
          | none => [])
        some (Json.mkObj (match p.name? with | some n => ("subject", Json.str n) :: base | none => base))
      | _, _ => none
    else none
  let fields : List (String × Json) :=
    [ ("format", Json.str "ixcc/k1-equations/1")
    , ("source", Json.str source)
    , ("roots", Json.arr rootRows)
    , ("equations", Json.arr eqRows) ] ++
    (if thmRows.isEmpty then [] else [("theorems", Json.arr thmRows)]) ++
    (if guessRows.isEmpty then [] else [("guesses", Json.arr guessRows)]) ++
    [ ("failures", Json.arr #[]) ]
  Json.mkObj fields

end Hints

end IxCC.Src
