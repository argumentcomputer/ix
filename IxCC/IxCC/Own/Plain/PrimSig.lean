import IxCC.Lam.Syntax

/-! # Ownership signatures of primitives

What a primitive does with its arguments and its result, as the ownership checker sees it
(`Own.Plain.primStep`, `Owned.lean`). Each argument is an immediate once the primitive has
returned (`imm`), read (`read`) or consumed (`consume`); the result is an immediate (`imm`), a
value the caller owns (`fresh`) or a field of an argument not yet incremented (`borrowed`); and
`release` says whether the primitive may free a cell.

A signature replaces the rule "every argument and the result of a primitive is an immediate",
which is true of the primitives of today (`Lam.Prim`: `Nat` and fixed-width word operations, read
as `Nat` literals) and of no primitive over a heap value. Today's rule is the signature
`PrimSig.scalar`, which `lamSig` gives every primitive: the checker's step under it is the old
step (`primStep_conservative`, `Proof/Owned/PrimStep.lean`). Design: `plans/ONE-PIPELINE.md`,
section 3.2. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

/-- How a primitive uses one argument. -/
inductive ArgUse where
  /-- An immediate by construction once the primitive has returned (it read a `Nat` literal
  below `2^63`, a word held raw, `□`): today's rule for every argument. -/
  | imm
  /-- Read for the duration of the primitive: the caller's tokens stay, and it must still hold
  the value after the consumed arguments are taken. -/
  | read
  /-- One token taken: the value moves into the result, or the primitive releases it. -/
  | consume
  deriving DecidableEq, Repr, Inhabited

def ArgUse.isImm : ArgUse → Bool
  | .imm => true
  | _ => false

/-- What a primitive's result is to the ownership checker. -/
inductive ResUse where
  /-- An immediate: no token. -/
  | imm
  /-- A value the caller owns one token of; `unique`: a cell just made, with one reference. It
  may be an immediate at run time (a small `Nat`): its token is then vacuous, as for any
  field-less constructor today. -/
  | fresh (unique : Bool)
  /-- A field of argument `ofArg`, not yet incremented: usable until the next release, as a
  projection's result is (`Ctx.setBorrow`). -/
  | borrowed (ofArg : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- **A primitive's ownership signature.** `release`: the primitive may free a cell (it drops an
overwritten element, or the last reference of a consumed array), which ends every epoch borrow. -/
structure PrimSig where
  args : List ArgUse
  result : ResUse
  release : Bool
  deriving Repr, Inhabited

/-- The signature of every primitive today: literals in, an immediate out. -/
def PrimSig.scalar (arity : Nat) : PrimSig :=
  { args := List.replicate arity .imm, result := .imm, release := false }

/-- A `Nat` primitive once `Nat` is arbitrary precision: an operand may be a limb cell, so it is
read; the result may be one, so it is owned. (Where the shape certificate gives every operand and
the result a bound below `2^63`, the signature is `scalar` again.) No primitive has this
signature yet. -/
def PrimSig.bigNat (arity : Nat) (isPredicate : Bool) : PrimSig :=
  { args := List.replicate arity .read
    result := if isPredicate then .imm else .fresh false
    release := false }

/-- Today's primitives under today's representation (`Nat` below `2^63`, words tagged). -/
def lamSig (_op : Lam.Prim) (arity : Nat) : PrimSig := PrimSig.scalar arity

end IxCC.Own.Plain
