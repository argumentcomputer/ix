module

public import Ix.Claim
public import Ix.SpecDigest
public import IxC.Kernel.Ixon.Prelude
public import IxC.Kernel.Ixon.RoleTable

/-! # Building a claim's context

A typing claim is relative to a `ClaimContext`: the specification digest,
the role binding's hash and the axioms beyond the standard three. A claim
made today names this specification set (`Ix.SpecDigest.specDigest`) and
no further axiom; only the binding varies.

## Literal classes

A claim compiled from another Lean toolchain names that toolchain's role
binding, which may bind some roles to other constants (4.33.1 defines
`Nat.land`, `Nat.lor` and `Nat.xor` differently from 4.34.1). Roles a term
references by address are ordinary dependencies, so typing does not depend
on which constants other roles are bound to. A few roles the checker uses
without a reference: a literal's type, the constructor forms the checker
unfolds a literal to, and the standard axioms the axiom policy recognizes
through the binding (`classRoles`). Two bindings that bind those roles alike
have the same **literal class** (`literalClassOf`), and a claim validated
under one of them holds under the other. A `checkEnv` claim under a literal
class (`ClaimContext.literalClass`, validator `erased-lean-v2-class`) states
that, and aggregation joins claims of one class in it (`ix_aggr` shape 15).

`classRoles` must list every role the checker uses without a reference to it:
a checker change that fabricates a reference to another role must add that
role here, or claims under a literal class would transfer typing between
bindings that the change tells apart. -/

@[expose] public section

namespace Ix.ClaimContext

open Ix.Kernel (Role RoleTable)

/-- The context of a claim over the role binding with hash `binding`. -/
def ofBinding (binding : Address) : Except String ClaimContext := do
  return { spec := ← Ix.SpecDigest.specDigest, binding, axioms := none }

/-- The context of a claim over an environment's own role binding. -/
def ofEnv (env : Ixon.Env) : Except String ClaimContext :=
  match env.roleBinding with
  | some binding => ofBinding binding.address
  | none => throw "claim context: the environment carries no role binding"

/-- The context of a claim over the default role table
(`Ix.Kernel.Reader.defaultTable`), the generated table of the compiled
`Init`. Like that table, for tests and the command line only. -/
def ofDefaultTable : Except String ClaimContext := do
  ofBinding (← Ix.Kernel.Reader.defaultTableAddress)

/-- The roles the checker uses without a reference to them, in role order:
- `Nat`, `Nat.zero` and `Nat.succ`: a `Nat` literal's type and constructor
  forms (IxVM `k_infer_lit`, `Whnf.lean`; IxC `litNatKeys`);
- `List`, `List.nil`, `List.cons`, `String`, `String.ofList`, `Char` and
  `Char.ofNat`: a `String` literal's type and constructor form (IxVM
  `str_lit_to_ctor`; IxC `litStrKeys`);
- `propext` and `Classical.choice`: the standard axioms the axiom policy
  admits as the binding binds them (IxVM `axiom_standing`; IxC `stdAxiomOk`).
`Quot.sound` and the quotient block are fixed by their specifications. -/
def classRoles : List Role :=
  [.nat, .natZero, .natSucc, .list, .listNil, .listCons, .string, .stringOfList,
   .char, .charOfNat, .propext, .choice]

/-- The class roles' indices in a binding section: `ix_aggr` reads a complete
table's entries for them at these positions. -/
theorem classRoles_idx :
    classRoles.map Role.idx = [0, 1, 2, 29, 30, 31, 37, 38, 39, 40, 56, 57] := by
  decide

/-- The tag of a literal class preimage: `N4(0xE, 12)`, after the binding
section's `E8 03`. -/
def literalClassTag : ByteArray := ⟨#[0xE8, 0x04]⟩

/-- The literal class of a role table that binds every role: BLAKE3 of
`literalClassTag` followed by the addresses it binds to `classRoles`, in
role order. -/
def literalClassOf (table : RoleTable) : Except String Address := do
  unless table.bound.size == Role.all.length do
    throw "literal class: the role table does not bind every role"
  let mut bytes := literalClassTag
  for r in classRoles do
    let some (_, a) := table.bound.find? (·.1 == r)
      | throw s!"literal class: the role table does not bind {r.leanName}"
    bytes := bytes ++ a.hash
  return Address.blake3 bytes

/-- The literal class of a binding section's bytes. -/
def literalClassOfBytes (bytes : ByteArray) : Except String Address := do
  let some table := RoleTable.ofBytes bytes
    | throw "literal class: not a role binding section"
  literalClassOf table

/-- The context of a `checkEnv` claim under the literal class `klass`. -/
def ofLiteralClass (klass : Address) : Except String ClaimContext := do
  return { spec := ← Ix.SpecDigest.specDigest, binding := klass, axioms := none,
           literalClass := true }

end Ix.ClaimContext

end
