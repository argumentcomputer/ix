module

public import IxC.Kernel.Env

@[expose] public section

/-!
# Basis names

The reserved names of the pinned basis blocks (see `Ix.Kernel.Basis`).
-/

namespace Ix.Kernel

/-- The name of the basis equality type. -/
abbrev eqName : Key md := roleKey .eq

/-- The name of the basis equality constructor. -/
abbrev eqReflName : Key md := roleKey .eqRefl

/-- The name of the basis equality recursor. -/
abbrev eqRecName : Key md := roleKey .eqRec

/-- The name of the basis unit type. -/
abbrev punitName : Key md := roleKey .punit

/-- The name of the basis unit type's recursor.  A top-level constant
so the unit-like head test (`isUnitLikeTy`, task #161 item C1) does not
rebuild it on every proof-irrelevance attempt. -/
abbrev punitRecName : Key md := roleKey .punitRec

/-- The name `Nat`. -/
abbrev natName : Key md := roleKey .nat

/-- The name `Nat.zero`. -/
abbrev natZeroName : Key md := roleKey .natZero

/-- The name `Nat.succ`. -/
abbrev natSuccName : Key md := roleKey .natSucc

/-- The name `Nat.rec`. -/
abbrev natRecName : Key md := roleKey .natRec

/-- The name of the basis unit constructor. -/
abbrev punitUnitName : Key md := roleKey .punitUnit

/-- The name of the basis empty type. -/
abbrev emptyName : Key md := roleKey .empty

/-- The name `Empty.rec`. -/
abbrev emptyRecName : Key md := roleKey .emptyRec

/-- The name of the pinned `False` basis type (task #181): the
zero-constructor `Prop`, pinned like `Empty` so that the consistency
corollary about `False` needs no hypothesis about how a stream declares
it. -/
abbrev falseName : Key md := roleKey .false

/-- The name `False.rec`. -/
abbrev falseRecName : Key md := roleKey .falseRec

/-- The name of the basis quotient type. -/
abbrev quotName : Key md := roleKey .quot

/-- The name of the basis quotient constructor. -/
abbrev quotMkName : Key md := roleKey .quotMk

/-- The name of the basis quotient lift eliminator. -/
abbrev quotLiftName : Key md := roleKey .quotLift

/-- The name of the basis quotient induction eliminator. -/
abbrev quotIndName : Key md := roleKey .quotInd

/-- The name of the basis quotient soundness axiom. -/
abbrev quotSoundName : Key md := roleKey .quotSound

/-! The names of the string-literal support constants (see
`strLitSupported` in `Ix.Kernel.Core`).  These are *not* basis
names — the constants are ordinary stream-installed declarations
(inductive blocks and plain definitions); the names are
pinned only so that a string literal knows what it unfolds to
(`strLitToConstructor`), exactly like the `Nat` literal names above. -/

/-- The name `String`. -/
abbrev stringName : Key md := roleKey .string

/-- The name `String.ofList`. -/
abbrev stringOfListName : Key md := roleKey .stringOfList

/-- The name `List`. -/
abbrev listName : Key md := roleKey .list

/-- The name `List.nil`. -/
abbrev listNilName : Key md := roleKey .listNil

/-- The name `List.cons`. -/
abbrev listConsName : Key md := roleKey .listCons

/-- The name `Char`. -/
abbrev charName : Key md := roleKey .char

/-- The name `And`: the one propositional structure whose recursor is
rescued on a stuck proof (`majorToCtor`'s `And` branch,
`IxC/Kernel/Core.lean`).  `And` is pinned by the built-in prelude
(`pins/<toolchain>.prelude.ndjson`, installed first in every fold; a
stream's own `And` is dropped as an identical copy or declines the
stream), so the name always denotes the toolchain's `And`. -/
abbrev andName : Key md := roleKey .and

/-- The name `And.intro`. -/
abbrev andIntroName : Key md := roleKey .andIntro

/-- The name `Char.ofNat`. -/
abbrev charOfNatName : Key md := roleKey .charOfNat

/-- Names reserved for the pinned basis blocks; no other declaration
may use them.  `PSigma'` is not among them (task #175 W6): the
modelled basis's tight pair installs through the direct
simple-structure path as an ordinary two-field structure. -/
def reservedBasisNames : List (Key md) :=
  [eqName, eqReflName, eqRecName,
   natName, natZeroName, natSuccName, natRecName,
   punitName, punitUnitName, punitRecName,
   emptyName, emptyRecName,
   falseName, falseRecName,
   quotName, quotMkName, quotLiftName, quotIndName, quotSoundName]

/-- A derived key is not reserved. -/
theorem reservedBasisNames_contains_auxKey (k : Key md) (d : Derived) :
    reservedBasisNames.contains (auxKey k d) = false := by
  simp [reservedBasisNames, eqName, eqReflName, eqRecName, natName, natZeroName, natSuccName,
    natRecName, punitName, punitUnitName, punitRecName, emptyName, emptyRecName, falseName,
    falseRecName, quotName, quotMkName, quotLiftName, quotIndName, quotSoundName]

/-! ## The tolerated axiom

`sorryAx` is the one axiom the checker tolerates as a *declaration*:
an export declares it whenever the module it came from mentions
`sorry`, whether or not anything uses it, so a stream that merely
DECLARES it must not be turned away.  Its record installs nothing —
there is no set model for `∀ (α : Sort u), Bool → α` and there cannot
be one — and therefore any USE of it is a positively detected
unsupported feature: a decline, at the record that uses it
(`unknownConstError`, `IxC/Kernel/Core.lean`).  The name lives
here, at the bottom of the kernel, because the decline is decided
where a constant fails to resolve — inside the inference body. -/

/-- The name `sorryAx`. -/
abbrev sorryAxName : Key md := roleKey .sorryAx

end Ix.Kernel
