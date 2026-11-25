import IxCC.Anf.Proof.Defun.Rel
import IxCC.Sem.ValModel

/-! # The closure-conversion relation respects Anf's value model

`Defun.Proof.DV` relates a source closure to the target's closure constructor, which is not the
`Rel.Base` shape (a closure relates to a constructor value), so it gets its own proof that it is
a `Sem.ModelRel` of `Anf.model` with itself: literals relate to themselves, and a constructor value
(an array among them, decision D1) relates only to a constructor value with the same key and
related fields. So closure conversion gets every array primitive from `Src.ArrOp.parametric`, and
an array of closures is related to the array of their closure constructors element by element. -/

set_option autoImplicit false

namespace IxCC.Anf.Defun.Proof

open IxCC.Sem (Forall2 ModelRel)

variable {X : Setting}

theorem DVs.toForall2 : ∀ {vs ws : List Val}, DVs X vs ws → Forall2 (DV X) vs ws
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h (DVs.toForall2 hs)

theorem DVs.ofForall2 : ∀ {vs ws : List Val}, Forall2 (DV X) vs ws → DVs X vs ws
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h (DVs.ofForall2 hs)

/-- **Closure conversion's value relation respects Anf's value model.** -/
theorem dv_modelRel : ModelRel model model (DV X) where
  nat _ := .lit
  asNat {v w n} h hv := by
    cases h with
    | lit => exact hv
    | box => simp [model, Val.asNat] at hv
    | con _ => simp [model, Val.asNat] at hv
    | lam => simp [model, Val.asNat] at hv
    | glob => simp [model, Val.asNat] at hv
  arr h := .con (DVs.ofForall2 h)
  asArr {v w xs} h hv := by
    cases h with
    | @con c vs ws hvs =>
      cases c with
      | arr =>
        simp only [model, Val.asArr, Option.some.injEq] at hv
        subst hv
        exact ⟨ws, rfl, DVs.toForall2 hvs⟩
      | src _ => simp [model, Val.asArr] at hv
      | clo _ _ => simp [model, Val.asArr] at hv
    | lit => simp [model, Val.asArr] at hv
    | box => simp [model, Val.asArr] at hv
    | lam => simp [model, Val.asArr] at hv
    | glob => simp [model, Val.asArr] at hv
  list _ := .box
  asList _ hv := by simp [model] at hv

end IxCC.Anf.Defun.Proof
