import IxC.Kernel.Model.GuardClassifier

/-! # A propositional structure with a quantified field: its raw syntax

    structure P : Prop where
      h : ∀ n : Nat, n = n
      k : True

The declared type of `Eq`, the first field's domain and the constructor's telescope as the raw
dictionary reads them (address keys, binder data erased), and the sorts the rules tier infers
for the two field domains. Kept apart from the theorems about them so that a program can
compare them with the readings of a compiled store.
-/

namespace IxVM.Refinement.Guard.QuantifiedField

open Ix.Kernel (Expr Level)

/-- `Eq.{u} : {α : Sort u} → α → α → Prop` at the level `u`, as the raw dictionary answers. -/
def eqType (u : Level) : Expr .anon :=
  .forallE (.sort u)
    (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero) default) default) default

/-- `∀ n : Nat, @Eq.{1} Nat n n`, raw. -/
def quantifiedField (aNat aEq : _root_.Address) : Expr .anon :=
  .forallE (.const (.id aNat) [])
    (.app (.app (.app (.const (.id aEq) [.succ .zero]) (.const (.id aNat) [])) (.bvar 0))
      (.bvar 0))
    default

/-- The constructor's raw telescope: `(h : ∀ n : Nat, n = n) → (k : True) → P`. -/
def ctorType (aNat aEq aTrue aP : _root_.Address) : Expr .anon :=
  .forallE (quantifiedField aNat aEq)
    (.forallE (.const (.id aTrue) []) (.const (.id aP) []) default) default

/-- The sorts the rules tier infers for the two field domains (`Infer.forallE` gives
`imax u v` unsimplified): `imax 1 0` for the quantified field, `0` for `True`. -/
def sorts : List Level := [.imax (.succ .zero) .zero, .zero]

end IxVM.Refinement.Guard.QuantifiedField
