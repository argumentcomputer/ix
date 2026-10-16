/-
  Ix.Compile.LibraryNames: the library constants that the compiler's own
  constructions build terms from (the `And`/`True` and `PProd`/`PUnit`
  packings, `Eq` for computation rules), as `Ix.Name`s.

  Each name is spelled with a double-backtick literal, so a renamed or
  removed library constant breaks the build instead of silently failing a
  lookup. One table, for every construction that needs these constants: the
  image generator (`Ix.Compile.Image`) reads it today.
-/
module
public import Ix.Environment
public section

namespace Ix.Compile.LibraryNames

open Ix (Name)

/-- The `Ix.Name` of a Lean constant name. -/
def leanName (n : Lean.Name) : Name := Name.fromLeanName n

def nPProd : Name := leanName ``PProd
def nPProdMk : Name := leanName ``PProd.mk
def nPProdFst : Name := leanName ``PProd.fst
def nPProdSnd : Name := leanName ``PProd.snd
def nPUnit : Name := leanName ``PUnit
def nPUnitUnit : Name := leanName ``PUnit.unit
def nAnd : Name := leanName ``And
def nAndIntro : Name := leanName ``And.intro
def nTrue : Name := leanName ``True
def nTrueIntro : Name := leanName ``True.intro
def nEq : Name := leanName ``Eq
def nEqRefl : Name := leanName ``Eq.refl

end Ix.Compile.LibraryNames

end
