import IxCC.Src.Syntax
import IxCC.Ixon.V3.Tc.Support
import Lean.Data.Json.Basic
import Lean.Data.Json.Parser

/-! # Unfolding-table hints

Untrusted, unauthenticated proposals for the unfolding table (design note
01 §4.3). Every address must resolve in the closure and every proposal must
pass its `Table.Check` check. Ordinary missing or refused hints degrade to the
kernel body; an explicit resource checked-pair claim instead requires its
equation to be selected. Names are diagnostic only. -/

namespace IxCC.Src

open IxCC.Ixon Lean

inductive ProposalKind where
  | eqn
  | csimp
  | lazy
  | inline
  | case
  deriving BEq, DecidableEq, Repr, Inhabited

/-- One untrusted table proposal: `eqn f thm`, `csimp f g thm`, `lazy f a`,
`inline f` or `case f`. -/
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

/-- Read an `ixcc/k1-equations/1` file: the roots and one `eqn`
proposal per `(definition_address, equation_address)` pair. -/
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
  return { roots, proposals, resource := ← resourceOfJson j }

def ofK1String (text : String) : Except String Hints := do
  ofK1Json (← Json.parse text)

end Hints

end IxCC.Src
