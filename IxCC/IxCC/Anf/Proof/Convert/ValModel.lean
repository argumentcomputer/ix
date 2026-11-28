import IxCC.Anf.Proof.Convert.Rel
import IxCC.Sem.ValModel

/-! # Lam-to-Anf conversion's value relation relates the two value models

`Convert.Proof.VR` relates Lam's plain values to Anf's: literals and □ to themselves, constructor
values pointwise under the same key, and a Lam closure to the Anf closure built for it. It is a
`Sem.ModelRel` from `Lam.model` to `Anf.model` (decision D1: an array is a constructor value under
the reserved key `Key.CtorKey.arr` at both levels), so the conversion gets every array primitive
from `Src.ArrOp.parametric`. -/

set_option autoImplicit false

namespace IxCC.Anf.Convert.Proof

open IxCC.Sem (Forall2 ModelRel)

variable {A : Arities} {G : Src.NatMap Lam.ModesOk.GInfo}

theorem VRs.toForall2 : ∀ {vs : List Lam.Val} {ws : List Val}, VRs A G vs ws → Forall2 (VR A G) vs ws
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h (VRs.toForall2 hs)

theorem VRs.ofForall2 : ∀ {vs : List Lam.Val} {ws : List Val}, Forall2 (VR A G) vs ws → VRs A G vs ws
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h (VRs.ofForall2 hs)

/-- A Lam value related to an Anf closure conversion is a Lam closure. -/
theorem CloR.lam_clos {tk : List Lam.Kind} {j : Nat} {v : Lam.Val} {w : Val}
    (h : CloR A G tk j v w) : ∃ ρ b, v = .clos ρ b := by
  cases h with
  | mk _ _ _ _ _ _ _ _ hv _ => exact ⟨_, _, hv⟩

/-- **Lam-to-Anf conversion's value relation relates Lam's value model to Anf's.** -/
theorem vr_modelRel : ModelRel Lam.model model (VR A G) where
  nat _ := .lit
  asNat {v w n} h hv := by
    cases h with
    | @lit l => cases l <;> simp_all [Lam.model, model, Lam.Val.asNat, Val.asNat]
    | box => simp [Lam.model, Lam.Val.asNat] at hv
    | con _ => simp [Lam.model, Lam.Val.asNat] at hv
    | clo hc _ =>
      obtain ⟨ρ, b, rfl⟩ := CloR.lam_clos hc
      simp [Lam.model, Lam.Val.asNat] at hv
  arr h := .con (VRs.ofForall2 h)
  asArr {v w xs} h hv := by
    cases h with
    | @con c fs ws hfs =>
      cases c with
      | arr =>
        simp only [Lam.model, Lam.Val.asArr, Option.some.injEq] at hv
        subst hv
        exact ⟨ws, rfl, VRs.toForall2 hfs⟩
      | src _ => simp [Lam.model, Lam.Val.asArr] at hv
      | clo _ _ => simp [Lam.model, Lam.Val.asArr] at hv
    | lit => simp [Lam.model, Lam.Val.asArr] at hv
    | box => simp [Lam.model, Lam.Val.asArr] at hv
    | clo hc _ =>
      obtain ⟨ρ, b, rfl⟩ := CloR.lam_clos hc
      simp [Lam.model, Lam.Val.asArr] at hv
  list _ := .box
  asList _ hv := by simp [Lam.model] at hv

end IxCC.Anf.Convert.Proof
