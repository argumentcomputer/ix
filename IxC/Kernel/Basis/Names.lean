module

public import IxC.Kernel.Env

@[expose] public section

/-!
# Basis names

The reserved names of the pinned basis blocks (see `Ix.Kernel.Basis`).
-/

namespace Ix.Kernel

/-- The name of the basis equality type. -/
def eqName : Key := roleKey .eq

/-- The name of the basis equality constructor. -/
def eqReflName : Key := roleKey .eqRefl

/-- The name of the basis equality recursor. -/
def eqRecName : Key := roleKey .eqRec

/-- The name of the basis unit type. -/
def punitName : Key := roleKey .punit

/-- The name of the basis unit type's recursor.  A top-level constant
so the unit-like head test (`isUnitLikeTy`, task #161 item C1) does not
rebuild it on every proof-irrelevance attempt. -/
def punitRecName : Key := roleKey .punitRec

/-- The name `Nat`. -/
def natName : Key := roleKey .nat

/-- The name `Nat.zero`. -/
def natZeroName : Key := roleKey .natZero

/-- The name `Nat.succ`. -/
def natSuccName : Key := roleKey .natSucc

/-- The name `Nat.rec`. -/
def natRecName : Key := roleKey .natRec

/-- The name of the basis unit constructor. -/
def punitUnitName : Key := roleKey .punitUnit

/-- The name of the basis empty type. -/
def emptyName : Key := roleKey .empty

/-- The name `Empty.rec`. -/
def emptyRecName : Key := roleKey .emptyRec

/-- The name of the pinned `False` basis type (task #181): the
zero-constructor `Prop`, pinned like `Empty` so that the consistency
corollary about `False` needs no hypothesis about how a stream declares
it. -/
def falseName : Key := roleKey .false

/-- The name `False.rec`. -/
def falseRecName : Key := roleKey .falseRec

/-- The name of the basis quotient type. -/
def quotName : Key := roleKey .quot

/-- The name of the basis quotient constructor. -/
def quotMkName : Key := roleKey .quotMk

/-- The name of the basis quotient lift eliminator. -/
def quotLiftName : Key := roleKey .quotLift

/-- The name of the basis quotient induction eliminator. -/
def quotIndName : Key := roleKey .quotInd

/-- The name of the basis quotient soundness axiom. -/
def quotSoundName : Key := roleKey .quotSound

/-! The names of the string-literal support constants (see
`strLitSupported` in `Ix.Kernel.Core`).  These are *not* basis
names — the constants are ordinary stream-installed declarations
(inductive blocks and plain definitions); the names are
pinned only so that a string literal knows what it unfolds to
(`strLitToConstructor`), exactly like the `Nat` literal names above. -/

/-- The name `String`. -/
def stringName : Key := roleKey .string

/-- The name `String.ofList`. -/
def stringOfListName : Key := roleKey .stringOfList

/-- The name `List`. -/
def listName : Key := roleKey .list

/-- The name `List.nil`. -/
def listNilName : Key := roleKey .listNil

/-- The name `List.cons`. -/
def listConsName : Key := roleKey .listCons

/-- The name `Char`. -/
def charName : Key := roleKey .char

/-- The name `And`: the one propositional structure whose recursor is
rescued on a stuck proof (`majorToCtor`'s `And` branch,
`IxC/Kernel/Core.lean`).  `And` is pinned by the built-in prelude
(`pins/<toolchain>.prelude.ndjson`, installed first in every fold; a
stream's own `And` is dropped as an identical copy or declines the
stream), so the name always denotes the toolchain's `And`. -/
def andName : Key := roleKey .and

/-- The name `And.intro`. -/
def andIntroName : Key := roleKey .andIntro

/-- The name `Char.ofNat`. -/
def charOfNatName : Key := roleKey .charOfNat

/-- Names reserved for the pinned basis blocks; no other declaration
may use them.  `PSigma'` is not among them (task #175 W6): the
modelled basis's tight pair installs through the direct
simple-structure path as an ordinary two-field structure. -/
def reservedBasisNames : List Key :=
  [eqName, eqReflName, eqRecName,
   natName, natZeroName, natSuccName, natRecName,
   punitName, punitUnitName, punitRecName,
   emptyName, emptyRecName,
   falseName, falseRecName,
   quotName, quotMkName, quotLiftName, quotIndName, quotSoundName]

/-- A derived key is not reserved. -/
theorem reservedBasisNames_contains_auxKey (k : Key) (d : Derived) :
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
def sorryAxName : Key := roleKey .sorryAx

end Ix.Kernel
