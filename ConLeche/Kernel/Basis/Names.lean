module

public import ConLeche.Kernel.Env

@[expose] public section

/-!
# Basis names

The reserved names of the pinned basis blocks (see `ConLeche.Kernel.Basis`).
-/

namespace ConLeche

open Name (anonymous)

/-- The name of the basis equality type. -/
def eqName : Name := anonymous |>.str "Eq"

/-- The name of the basis equality constructor. -/
def eqReflName : Name := eqName |>.str "refl"

/-- The name of the basis unit type. -/
def punitName : Name := anonymous |>.str "PUnit"

/-- The name of the basis unit type's recursor.  A top-level constant
so the unit-like head test (`isUnitLikeTy`, task #161 item C1) does not
rebuild it on every proof-irrelevance attempt. -/
def punitRecName : Name := punitName |>.str "rec"

/-- The name `Nat`. -/
def natName : Name := anonymous |>.str "Nat"

/-- The name `Nat.zero`. -/
def natZeroName : Name := natName |>.str "zero"

/-- The name `Nat.succ`. -/
def natSuccName : Name := natName |>.str "succ"

/-- The name of the basis unit constructor. -/
def punitUnitName : Name := punitName |>.str "unit"

def emptyName : Name := anonymous |>.str "Empty"

/-- The name of the pinned `False` basis type (task #181): the
zero-constructor `Prop`, pinned like `Empty` so that the consistency
corollary about `False` needs no hypothesis about how a stream declares
it. -/
def falseName : Name := anonymous |>.str "False"

/-- The name of the basis quotient type. -/
def quotName : Name := anonymous |>.str "Quot"

/-- The name of the basis quotient constructor. -/
def quotMkName : Name := quotName |>.str "mk"

/-- The name of the basis quotient lift eliminator. -/
def quotLiftName : Name := quotName |>.str "lift"

/-- The name of the basis quotient induction eliminator. -/
def quotIndName : Name := quotName |>.str "ind"

/-- The name of the basis quotient soundness axiom. -/
def quotSoundName : Name := quotName |>.str "sound"

/-! The names of the string-literal support constants (see
`strLitSupported` in `ConLeche.Kernel.Core`).  These are *not* basis
names — the constants are ordinary stream-installed declarations
(inductive blocks and plain definitions); the names are
pinned only so that a string literal knows what it unfolds to
(`strLitToConstructor`), exactly like the `Nat` literal names above. -/

/-- The name `String`. -/
def stringName : Name := anonymous |>.str "String"

/-- The name `String.ofList`. -/
def stringOfListName : Name := stringName.str "ofList"

/-- The name `List`. -/
def listName : Name := anonymous |>.str "List"

/-- The name `List.nil`. -/
def listNilName : Name := listName.str "nil"

/-- The name `List.cons`. -/
def listConsName : Name := listName.str "cons"

/-- The name `Char`. -/
def charName : Name := anonymous |>.str "Char"

/-- The name `And`: the one propositional structure whose recursor is
rescued on a stuck proof (`majorToCtor`'s `And` branch,
`ConLeche/Kernel/Core.lean`).  `And` is pinned by the built-in prelude
(`pins/<toolchain>.prelude.ndjson`, installed first in every fold; a
stream's own `And` is dropped as an identical copy or declines the
stream), so the name always denotes the toolchain's `And`. -/
def andName : Name := anonymous |>.str "And"

/-- The name `And.intro`. -/
def andIntroName : Name := andName.str "intro"

/-- The name `Char.ofNat`. -/
def charOfNatName : Name := charName.str "ofNat"

/-- Names reserved for the pinned basis blocks; no other declaration
may use them.  `PSigma'` is not among them (task #175 W6): the
modelled basis's tight pair installs through the direct
simple-structure path as an ordinary two-field structure. -/
def reservedBasisNames : List Name :=
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
(`unknownConstError`, `ConLeche/Kernel/Core.lean`).  The name lives
here, at the bottom of the kernel, because the decline is decided
where a constant fails to resolve — inside the inference body. -/

/-- The name `sorryAx`. -/
def sorryAxName : Name := anonymous |>.str "sorryAx"

end ConLeche
