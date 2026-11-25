import IxCC.Anf.Proof.Rel.Basic
import IxCC.Sem.ValModel

/-! # Every Anf relation of the `Base` shape respects Anf's value model

`Anf.model` (`Anf/Semantics.lean`) reads and builds what the array primitives
(`Src.ArrOp.eval`) need: a `Nat` literal and an array (decision D1 of `plans/ONE-PIPELINE.md`: a
constructor value under the reserved key `Key.CtorKey.arr`, one field per element).

`Rel.Base.modelRel`: **every value relation of the `Base` shape is a `Sem.ModelRel`** of the
model with itself. `Base` is the shape of the value relation of the Anf-to-Anf passes whose
proofs use `Rel.Basic` (literals and □ to themselves, constructors pointwise, and inversion), so
each gets every array primitive from the one parametricity theorem `Src.ArrOp.parametric` at its
own relation, with nothing about arrays in the pass. Under encoding D1 this needs no exception:
an array is a constructor value, which `Base` already relates pointwise. -/

set_option autoImplicit false

namespace IxCC.Anf.Rel

open IxCC.Sem (Forall2 ModelRel)

theorem Pw.toForall2 {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, Pw R as bs → Forall2 R as bs
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h (Pw.toForall2 hs)

theorem Pw.ofForall2 {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, Forall2 R as bs → Pw R as bs
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h (Pw.ofForall2 hs)

variable {R : Val → Val → Prop}

/-- **Every `Base` relation respects Anf's value model**, so the array primitives are
parametric in it (`Src.ArrOp.parametric`). -/
theorem Base.modelRel (hS : Base R) : ModelRel model model R where
  nat _ := hS.lit _
  asNat {v w n} h hv := by
    cases v with
    | lit l =>
      cases l with
      | nat m => rw [hS.invLit _ w h]; exact hv
      | str _ => simp [model, Val.asNat] at hv
    | clos => simp [model, Val.asNat] at hv
    | con => simp [model, Val.asNat] at hv
    | box => simp [model, Val.asNat] at hv
  arr h := hS.con _ _ _ (Pw.ofForall2 h)
  asArr {v w xs} h hv := by
    cases v with
    | con c fs =>
      cases c with
      | arr =>
        simp only [model, Val.asArr, Option.some.injEq] at hv
        subst hv
        obtain ⟨ws, rfl, hws⟩ := hS.invCon _ _ w h
        exact ⟨ws, rfl, Pw.toForall2 hws⟩
      | src _ => simp [model, Val.asArr] at hv
      | clo _ _ => simp [model, Val.asArr] at hv
    | clos => simp [model, Val.asArr] at hv
    | lit => simp [model, Val.asArr] at hv
    | box => simp [model, Val.asArr] at hv
  list _ := hS.box
  asList _ hv := by simp [model] at hv

end IxCC.Anf.Rel
