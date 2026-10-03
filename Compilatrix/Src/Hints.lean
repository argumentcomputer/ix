import Compilatrix.Src.Syntax
import Compilatrix.Ixon.V3.Tc.Support
import Lean.Data.Json.Basic
import Lean.Data.Json.Parser

/-! # Unfolding-table hints

Untrusted, unauthenticated proposals for the unfolding table (design note
01 §4.3). Every address must resolve in the closure and every proposal must
pass its `Table.Check` check; a missing or refused hint only degrades to the
kernel body. Names are diagnostic only. -/

namespace Compilatrix.Src

open Compilatrix.Ixon Lean

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
  deriving Inhabited

namespace Hints

private def str (j : Json) (key : String) : Except String String := do
  (← j.getObjVal? key).getStr?

private def address (j : Json) (key : String) : Except String Ixon.Address := do
  let text ← str j key
  match Ixon.Address.fromString text with
  | some a => pure a
  | none => throw s!"hints: invalid address {text}"

/-- Read a `compilatrix/k1-equations/1` file: the roots and one `eqn`
proposal per `(definition_address, equation_address)` pair. -/
def ofK1Json (j : Json) : Except String Hints := do
  let format ← str j "format"
  unless format == "compilatrix/k1-equations/1" do
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
  return { roots, proposals }

def ofK1String (text : String) : Except String Hints := do
  ofK1Json (← Json.parse text)

end Hints

end Compilatrix.Src
