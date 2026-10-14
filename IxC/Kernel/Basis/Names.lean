module

public import IxC.Kernel.Env

@[expose] public section

/-!
# Basis names

The reserved names of the pinned basis blocks (see `Ix.Kernel.Basis`).
-/

namespace Ix.Kernel

open Name (anonymous)

/-- The name of the basis equality type. -/
def eqName : Key := anonymous |>.str "Eq"

/-- The name of the basis equality constructor. -/
def eqReflName : Key := eqName |>.str "refl"

/-- The name of the basis unit type. -/
def punitName : Key := anonymous |>.str "PUnit"

/-- The name of the basis unit type's recursor.  A top-level constant
so the unit-like head test (`isUnitLikeTy`, task #161 item C1) does not
rebuild it on every proof-irrelevance attempt. -/
def punitRecName : Key := punitName |>.str "rec"

/-- The name `Nat`. -/
def natName : Key := anonymous |>.str "Nat"

/-- The name `Nat.zero`. -/
def natZeroName : Key := natName |>.str "zero"

/-- The name `Nat.succ`. -/
def natSuccName : Key := natName |>.str "succ"

/-- The name of the basis unit constructor. -/
def punitUnitName : Key := punitName |>.str "unit"

def emptyName : Key := anonymous |>.str "Empty"

/-- The name of the pinned `False` basis type (task #181): the
zero-constructor `Prop`, pinned like `Empty` so that the consistency
corollary about `False` needs no hypothesis about how a stream declares
it. -/
def falseName : Key := anonymous |>.str "False"

/-- The name of the basis quotient type. -/
def quotName : Key := anonymous |>.str "Quot"

/-- The name of the basis quotient constructor. -/
def quotMkName : Key := quotName |>.str "mk"

/-- The name of the basis quotient lift eliminator. -/
def quotLiftName : Key := quotName |>.str "lift"

/-- The name of the basis quotient induction eliminator. -/
def quotIndName : Key := quotName |>.str "ind"

/-- The name of the basis quotient soundness axiom. -/
def quotSoundName : Key := quotName |>.str "sound"

/-! The names of the string-literal support constants (see
`strLitSupported` in `Ix.Kernel.Core`).  These are *not* basis
names — the constants are ordinary stream-installed declarations
(inductive blocks and plain definitions); the names are
pinned only so that a string literal knows what it unfolds to
(`strLitToConstructor`), exactly like the `Nat` literal names above. -/

/-- The name `String`. -/
def stringName : Key := anonymous |>.str "String"

/-- The name `String.ofList`. -/
def stringOfListName : Key := stringName.str "ofList"

/-- The name `List`. -/
def listName : Key := anonymous |>.str "List"

/-- The name `List.nil`. -/
def listNilName : Key := listName.str "nil"

/-- The name `List.cons`. -/
def listConsName : Key := listName.str "cons"

/-- The name `Char`. -/
def charName : Key := anonymous |>.str "Char"

/-- The name `And`: the one propositional structure whose recursor is
rescued on a stuck proof (`majorToCtor`'s `And` branch,
`IxC/Kernel/Core.lean`).  `And` is pinned by the built-in prelude
(`pins/<toolchain>.prelude.ndjson`, installed first in every fold; a
stream's own `And` is dropped as an identical copy or declines the
stream), so the name always denotes the toolchain's `And`. -/
def andName : Key := anonymous |>.str "And"

/-- The name `And.intro`. -/
def andIntroName : Key := andName.str "intro"

/-- The name `Char.ofNat`. -/
def charOfNatName : Key := charName.str "ofNat"

/-- Names reserved for the pinned basis blocks; no other declaration
may use them.  `PSigma'` is not among them (task #175 W6): the
modelled basis's tight pair installs through the direct
simple-structure path as an ordinary two-field structure. -/
def reservedBasisNames : List Key :=
  [eqName, eqReflName, eqName.str "rec",
   natName, natZeroName, natSuccName, natName.str "rec",
   punitName, punitUnitName, punitName.str "rec",
   emptyName, emptyName.str "rec",
   falseName, falseName.str "rec",
   quotName, quotMkName, quotLiftName, quotIndName, quotSoundName]

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
def sorryAxName : Key := anonymous |>.str "sorryAx"

end Ix.Kernel
