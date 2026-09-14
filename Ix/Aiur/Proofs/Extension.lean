/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Extension
import Ix.Aiur.Proofs.GoldilocksAlgebra

/-! Algebra of the native quadratic coordinates, with base embedding,
conjugation, norm and the working operations used by expression reflection.
Ring laws alone do not establish that the quadratic algebra is a field.
-/

namespace Aiur.NativeAIR.ProofCodec.Extension

theorem ext {a b : Extension} (c0 : a.c0 = b.c0) (c1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases c0; cases c1; rfl

theorem ofBase_injective {a b : G} (equal : ofBase a = ofBase b) : a = b :=
  congrArg Extension.c0 equal

theorem ofBase_add (a b : G) : ofBase (a + b) = ofBase a + ofBase b := by
  apply ext
  · rfl
  · change (0 : G) = 0 + 0; grind

theorem ofBase_sub (a b : G) : ofBase (a - b) = ofBase a - ofBase b := by
  apply ext
  · rfl
  · change (0 : G) = 0 - 0; grind

theorem ofBase_neg (a : G) : ofBase (-a) = -ofBase a := by
  apply ext
  · rfl
  · change (0 : G) = 0 - 0; grind

theorem ofBase_mul (a b : G) : ofBase (a * b) = ofBase a * ofBase b := by
  apply ext
  · change a * b = a * b + 0 * (0 * 7); grind
  · change (0 : G) = a * 0 + 0 * b; grind

theorem add_zero (a : Extension) : a + 0 = a := by
  apply ext
  · exact G.add_zero a.c0
  · exact G.add_zero a.c1

theorem add_comm (a b : Extension) : a + b = b + a :=
  ext (G.add_comm _ _) (G.add_comm _ _)

theorem add_assoc (a b c : Extension) : a + b + c = a + (b + c) :=
  ext (G.add_assoc _ _ _) (G.add_assoc _ _ _)

theorem mul_one (a : Extension) : a * 1 = a := by
  apply ext
  · change a.c0 * 1 + a.c1 * (0 * 7) = a.c0; grind
  · change a.c0 * 0 + a.c1 * 1 = a.c1; grind

theorem zero_mul (a : Extension) : 0 * a = 0 := by
  apply ext
  · change 0 * a.c0 + 0 * (a.c1 * 7) = (0 : G); grind
  · change 0 * a.c1 + 0 * a.c0 = (0 : G); grind

theorem mul_comm (a b : Extension) : a * b = b * a := by
  apply ext
  · change a.c0 * b.c0 + a.c1 * (b.c1 * 7) = b.c0 * a.c0 + b.c1 * (a.c1 * 7); grind
  · change a.c0 * b.c1 + a.c1 * b.c0 = b.c0 * a.c1 + b.c1 * a.c0; grind

theorem mul_assoc (a b c : Extension) : a * b * c = a * (b * c) := by
  apply ext
  · change (a.c0 * b.c0 + a.c1 * (b.c1 * 7)) * c.c0 +
      (a.c0 * b.c1 + a.c1 * b.c0) * (c.c1 * 7) =
      a.c0 * (b.c0 * c.c0 + b.c1 * (c.c1 * 7)) + a.c1 * ((b.c0 * c.c1 + b.c1 * c.c0) * 7)
    grind
  · change (a.c0 * b.c0 + a.c1 * (b.c1 * 7)) * c.c1 +
      (a.c0 * b.c1 + a.c1 * b.c0) * c.c0 =
      a.c0 * (b.c0 * c.c1 + b.c1 * c.c0) + a.c1 * (b.c0 * c.c0 + b.c1 * (c.c1 * 7))
    grind

theorem left_distrib (a b c : Extension) : a * (b + c) = a * b + a * c := by
  apply ext
  · change a.c0 * (b.c0 + c.c0) + a.c1 * ((b.c1 + c.c1) * 7) =
      (a.c0 * b.c0 + a.c1 * (b.c1 * 7)) + (a.c0 * c.c0 + a.c1 * (c.c1 * 7))
    grind
  · change a.c0 * (b.c1 + c.c1) + a.c1 * (b.c0 + c.c0) =
      (a.c0 * b.c1 + a.c1 * b.c0) + (a.c0 * c.c1 + a.c1 * c.c0)
    grind

theorem neg_add_cancel (a : Extension) : -a + a = 0 := by
  apply ext
  · exact G.neg_add_cancel a.c0
  · exact G.neg_add_cancel a.c1

theorem sub_eq_add_neg (a b : Extension) : a - b = a + -b :=
  ext (G.sub_eq_add_neg _ _) (G.sub_eq_add_neg _ _)

instance natCast : NatCast Extension := ⟨fun n => ofBase (G.ofNat n)⟩
instance intCast : IntCast Extension := ⟨fun n => ofBase (G.ofInt n)⟩
instance nsmul : SMul Nat Extension := ⟨fun n a => ofBase (G.ofNat n) * a⟩
instance zsmul : SMul Int Extension := ⟨fun n a => ofBase (G.ofInt n) * a⟩
instance npow : HPow Extension Nat Extension := ⟨fun a n => npowRec n a⟩

theorem neg_mul (a b : Extension) : -a * b = -(a * b) := by
  apply ext
  · change (0 - a.c0) * b.c0 + (0 - a.c1) * (b.c1 * 7) =
      0 - (a.c0 * b.c0 + a.c1 * (b.c1 * 7))
    grind
  · change (0 - a.c0) * b.c1 + (0 - a.c1) * b.c0 =
      0 - (a.c0 * b.c1 + a.c1 * b.c0)
    grind

instance commRing : Lean.Grind.CommRing Extension where
  add_zero := add_zero
  add_comm := add_comm
  add_assoc := add_assoc
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  mul_one := mul_one
  left_distrib := left_distrib
  zero_mul := zero_mul
  mul_zero a := by rw [mul_comm, zero_mul]
  pow_zero _ := rfl
  pow_succ _ _ := rfl
  ofNat_succ n := by
    change ofBase (G.ofNat (n + 1)) = ofBase (G.ofNat n) + ofBase 1
    rw [G.ofNat_add, ofBase_add]
    rfl
  neg_add_cancel := neg_add_cancel
  sub_eq_add_neg := sub_eq_add_neg
  intCast_neg n := by
    change ofBase (G.ofInt (-n)) = -ofBase (G.ofInt n)
    rw [G.ofInt_neg, ofBase_neg]
  neg_zsmul n a := by
    change ofBase (G.ofInt (-n)) * a = -(ofBase (G.ofInt n) * a)
    rw [G.ofInt_neg, ofBase_neg, neg_mul]

theorem basis_square : basis * basis = ofBase 7 := by decide +kernel

theorem coordinates (a : Extension) : a = ofBase a.c0 + ofBase a.c1 * basis := by
  apply ext
  · change a.c0 = a.c0 + (a.c1 * 0 + 0 * (1 * 7)); grind
  · change a.c1 = 0 + (a.c1 * 1 + 0 * 0); grind

theorem scale_eq_mul (a : Extension) (b : G) : a.scale b = a * ofBase b := by
  apply ext
  · change a.c0 * b = a.c0 * b + a.c1 * (0 * 7); grind
  · change a.c1 * b = a.c0 * 0 + a.c1 * b; grind

theorem conjugate_conjugate (a : Extension) : a.conjugate.conjugate = a := by
  apply ext
  · rfl
  · exact G.neg_neg a.c1

theorem mul_conjugate (a : Extension) : a * a.conjugate = ofBase a.norm := by
  apply ext
  · change a.c0 * a.c0 + a.c1 * ((0 - a.c1) * 7) = a.c0 * a.c0 - 7 * (a.c1 * a.c1)
    grind
  · change a.c0 * (0 - a.c1) + a.c1 * a.c0 = (0 : G); grind

theorem conjugate_mul (a b : Extension) : (a * b).conjugate = a.conjugate * b.conjugate := by
  apply ext
  · change a.c0 * b.c0 + a.c1 * (b.c1 * 7) = a.c0 * b.c0 + (0 - a.c1) * ((0 - b.c1) * 7)
    grind
  · change 0 - (a.c0 * b.c1 + a.c1 * b.c0) = a.c0 * (0 - b.c1) + (0 - a.c1) * b.c0
    grind

theorem norm_mul (a b : Extension) : (a * b).norm = a.norm * b.norm := by
  apply ofBase_injective
  rw [ofBase_mul, ← mul_conjugate, ← mul_conjugate, ← mul_conjugate, conjugate_mul]
  grind

theorem evalLaws : EvalLaws evalOps where
  konst_add := ofBase_add
  konst_sub := ofBase_sub
  konst_mul := ofBase_mul
  konst_neg := ofBase_neg
  add_zero := add_zero
  zero_add a := by change 0 + a = a; grind
  sub_zero a := by change a - 0 = a; grind
  zero_sub a := by change 0 - a = -a; grind
  mul_zero a := by change a * 0 = 0; grind
  zero_mul := zero_mul
  mul_one := mul_one
  one_mul a := by change 1 * a = a; grind
  neg_neg a := by change - - a = a; grind

theorem powBits_eq (a : Extension) (n fuel : Nat) (bounded : n < 2 ^ fuel) :
    powBits a n fuel = a ^ n := by
  induction fuel generalizing n with
  | zero =>
    have zero : n = 0 := by simpa using bounded
    subst n
    rfl
  | succ fuel ih =>
    by_cases zero : n = 0
    · subst n
      rfl
    · have half : n / 2 < 2 ^ fuel :=
        (Nat.div_lt_iff_lt_mul (by decide)).mpr (by simpa only [Nat.pow_succ] using bounded)
      simp only [powBits, beq_iff_eq, if_neg zero, ih _ half]
      by_cases even : n % 2 = 0
      · rw [if_pos even, ← Lean.Grind.Semiring.pow_add]
        congr 1
        omega
      · rw [if_neg even, ← Lean.Grind.Semiring.pow_add, ← Lean.Grind.Semiring.pow_succ]
        congr 1
        omega

theorem power_eq (a : Extension) (n : Nat) : power a n = a ^ n :=
  powBits_eq a n _ Nat.lt_log2_self

theorem ofBase_power (a : G) (n : Nat) : ofBase (a ^ n) = ofBase a ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Lean.Grind.Semiring.pow_succ, Lean.Grind.Semiring.pow_succ, ofBase_mul, ih]

theorem inverse_formula (a : Extension) :
    a.tryInverse = if a = 0 then none else some (a.conjugate * ofBase (a.norm ^ (gSize.toNat - 2))) := by
  simp only [tryInverse, beq_iff_eq, scale_eq_mul, G.inverse_eq_power]

end Aiur.NativeAIR.ProofCodec.Extension
