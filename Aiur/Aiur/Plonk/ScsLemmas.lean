import Aiur.Plonk.Scs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The exported gate form is the intended gate

`GGate.ofCoeffs` rescales `L·a + R·b + O·c + M·a·b + C` by a nonzero factor,
so the gate the loader passes to gnark holds exactly when the intended
relation does.
-/

namespace Aiur.Plonk

variable {F : Type} [Field F] [DecidableEq F]

private theorem sel_scaled (lam x : F) : sel (decide (x ≠ 0)) (lam * x) = lam * x := by
  by_cases h : x = 0 <;> simp [sel, h]

omit [DecidableEq F] in
private theorem holds_iff_of_scale {g : Gate F} {w : Nat → F} {e lam : F} (hl : lam ≠ 0)
    (he : g.qL * w g.a + g.qR * w g.b + g.qO * w g.c + g.qM * (w g.a * w g.b) + g.qC = lam * e) :
    g.Holds w ↔ e = 0 := by
  unfold Gate.Holds; rw [he]; simp [hl]

theorem GGate.ofCoeffs_holds {a b c : Nat} {L R O M C : F} {g : GGate F}
    (h : GGate.ofCoeffs a b c L R O M C = some g) (w : Nat → F) :
    g.toGate.Holds w ↔ L * w a + R * w b + O * w c + M * (w a * w b) + C = 0 := by
  unfold GGate.ofCoeffs at h
  by_cases hC : C = 0 <;> by_cases hM : M = 0 <;> by_cases hL : L = 0 <;> by_cases hR : R = 0 <;>
    by_cases hMC : M * C = L * R <;>
    simp only [hC, hM, hL, hR, hMC, ne_eq, not_false_eq_true, not_true_eq_false, and_true, and_false,
      true_and, false_and, ite_true, ite_false, Option.some.injEq, reduceCtorEq] at h <;>
    (try subst h) <;>
    first
    | (apply holds_iff_of_scale (lam := (1 : F)) one_ne_zero
       by_cases hO : O = 0 <;>
         simp only [GGate.toGate, sel, hC, hM, hL, hR, hO, not_true_eq_false, not_false_eq_true,
           decide_true, decide_false, ite_true, ite_false, Bool.false_eq_true, Int.cast_zero, Int.cast_one,
           mul_zero, zero_mul, add_zero, mul_one, one_mul] <;> (field_simp; done))
    | (apply holds_iff_of_scale (lam := C⁻¹) (inv_ne_zero hC)
       by_cases hO : O = 0 <;>
         simp only [GGate.toGate, sel, hM, hL, hR, hO, not_true_eq_false, not_false_eq_true,
           decide_true, decide_false, ite_true, ite_false, Bool.false_eq_true, Int.cast_one,
           mul_zero, zero_mul, add_zero, mul_one] <;> field_simp <;> ring1)
    | (apply holds_iff_of_scale (lam := M / (L * R)) (div_ne_zero hM (mul_ne_zero hL hR))
       by_cases hO : O = 0 <;>
         simp only [GGate.toGate, sel, hC, hO, not_true_eq_false, not_false_eq_true,
           decide_true, decide_false, ite_true, ite_false, Bool.false_eq_true, Int.cast_zero, Int.cast_one,
           mul_zero, zero_mul, add_zero] <;> (field_simp; done))
    | (apply holds_iff_of_scale (lam := M / (L * R)) (div_ne_zero hM (mul_ne_zero hL hR))
       have hc : C = L * R / M := by field_simp; linear_combination hMC
       rw [hc]
       by_cases hO : O = 0 <;>
         simp only [GGate.toGate, sel, hO, not_true_eq_false, not_false_eq_true,
           decide_true, decide_false, ite_true, ite_false, Bool.false_eq_true, Int.cast_one,
           mul_zero, zero_mul, add_zero] <;> field_simp)

end Aiur.Plonk
