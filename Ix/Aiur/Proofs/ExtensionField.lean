/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.Extension
import Ix.Aiur.Proofs.GoldilocksInverse

/-! The native relation `u² = 7` gives a field. A kernel-evaluated Euler
certificate and the proved Goldilocks Fermat theorem exclude square roots
of seven. The norm is therefore nonzero on every nonzero extension value,
which validates the concrete inverse formula used by the native backend.
-/

namespace Aiur.G

theorem seven_euler_certificate : G.pow 7 ((gSize.toNat - 1) / 2) = 0 - 1 := by
  decide +kernel

theorem seven_not_square (a : G) : a * a ≠ 7 := by
  intro square
  have nonzero : a ≠ 0 := by
    intro zero
    rw [zero, G.mul_zero] at square
    exact (by decide : (0 : G) ≠ 7) square
  have raised := congrArg (fun value : G => value ^ ((gSize.toNat - 1) / 2)) square
  rw [Lean.Grind.CommSemiring.mul_pow, ← Lean.Grind.Semiring.pow_add] at raised
  have twice : (gSize.toNat - 1) / 2 + (gSize.toNat - 1) / 2 = gSize.toNat - 1 := by decide
  rw [twice, fermat a nonzero, ← G.pow_eq _ _ (by decide), seven_euler_certificate] at raised
  exact (by decide : (1 : G) ≠ 0 - 1) raised

theorem square_ratio (x y inverse : G) (square : x * x = 7 * (y * y))
    (cancel : y * inverse = 1) : (x * inverse) * (x * inverse) = 7 := by
  grind

end Aiur.G

namespace Aiur.NativeAIR.ProofCodec.Extension

theorem norm_zero_iff (a : Extension) : a.norm = 0 ↔ a = 0 := by
  constructor
  · intro zero
    have square : a.c0 * a.c0 = 7 * (a.c1 * a.c1) := by
      change a.c0 * a.c0 - 7 * (a.c1 * a.c1) = 0 at zero
      exact (G.sub_eq_zero_iff _ _).mp zero
    by_cases last : a.c1 = 0
    · rw [last, G.mul_zero, G.mul_zero] at square
      have first := (G.mul_eq_zero_iff _ _).mp square
      apply ext
      · exact first.elim id id
      · exact last
    · have inverse := G.mul_inverse_cancel a.c1 last
      exact False.elim (G.seven_not_square (a.c0 * a.c1.inverse) (G.square_ratio _ _ _ square inverse))
  · intro zero
    rw [zero]
    rfl

theorem mul_eq_zero_iff (a b : Extension) : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro zero
    have norms := congrArg norm zero
    rw [norm_mul] at norms
    change a.norm * b.norm = 0 at norms
    rcases (G.mul_eq_zero_iff _ _).mp norms with left | right
    · exact Or.inl ((norm_zero_iff a).mp left)
    · exact Or.inr ((norm_zero_iff b).mp right)
  · rintro (rfl | rfl) <;> grind

theorem one_ne_zero : (1 : Extension) ≠ 0 := by decide

theorem mul_left_cancel {a b c : Extension} (nonzero : a ≠ 0) (equal : a * b = a * c) : b = c := by
  have zero : a * (b - c) = 0 := by grind
  have equal := (mul_eq_zero_iff _ _).mp zero |>.resolve_left nonzero
  grind

theorem inverse_correct (a : Extension) (nonzero : a ≠ 0) :
    a.tryInverse = some (a.conjugate.scale a.norm.inverse) ∧
      a * (a.conjugate.scale a.norm.inverse) = 1 := by
  constructor
  · simp only [tryInverse, beq_iff_eq, if_neg nonzero]
  · have normNonzero : a.norm ≠ 0 := fun zero => nonzero ((norm_zero_iff a).mp zero)
    rw [scale_eq_mul, ← mul_assoc, mul_conjugate, ← ofBase_mul, G.mul_inverse_cancel _ normNonzero]
    rfl

theorem tryInverse_none_iff (a : Extension) : a.tryInverse = none ↔ a = 0 := by
  simp only [tryInverse, beq_iff_eq]
  split <;> simp_all

theorem tryInverse_some_iff (a b : Extension) : a.tryInverse = some b ↔ a * b = 1 := by
  constructor
  · intro accepted
    have nonzero : a ≠ 0 := by
      intro zero
      rw [zero, tryInverse] at accepted
      cases accepted
    obtain ⟨returned, correct⟩ := inverse_correct a nonzero
    have same := Option.some.inj (accepted.symm.trans returned)
    exact same ▸ correct
  · intro inverse
    have nonzero : a ≠ 0 := by
      intro zero
      rw [zero, zero_mul] at inverse
      exact one_ne_zero inverse.symm
    obtain ⟨returned, correct⟩ := inverse_correct a nonzero
    have result := mul_left_cancel nonzero (inverse.trans correct.symm)
    exact result.symm ▸ returned

end Aiur.NativeAIR.ProofCodec.Extension
