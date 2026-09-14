/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.FrontendExpressions
import Init.GrindInstances.Ring.Fin
import Batteries.Tactic.OpenPrivate

/-! Ring operations for the actual canonical Goldilocks representation.
The residue map proves the laws without changing the runtime operations.
Natural powers in the ring instance are the mathematical recursive powers;
the existing bounded repeated-squaring routine has a separate specification.
-/

namespace Aiur.G

open Fin.NatCast Fin.IntCast
open private Aiur.G.pow.go from Ix.Aiur.Goldilocks

instance characteristicNeZero : NeZero gSize.toNat := ⟨by decide⟩

def residue (value : G) : Fin gSize.toNat :=
  ⟨value.n, UInt64.lt_iff_toNat_lt.mp value.property⟩

theorem residue_injective {a b : G} (equal : residue a = residue b) : a = b := by
  have numeric := congrArg (fun x : Fin gSize.toNat => x.val) equal
  exact G.ext_n numeric

theorem residue_ofNat (n : Nat) : residue (G.ofNat n) = Fin.ofNat _ n := by
  apply Fin.ext
  exact G.n_ofNat n

theorem residue_add (a b : G) : residue (a + b) = residue a + residue b := by
  apply Fin.ext
  exact G.n_add a b

theorem residue_mul (a b : G) : residue (a * b) = residue a * residue b := by
  apply Fin.ext
  exact G.n_mul a b

theorem residue_sub (a b : G) : residue (a - b) = residue a - residue b := by
  apply Fin.ext
  simp only [Fin.sub_def, residue]
  rw [G.n_sub, Nat.add_sub_assoc (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp b.property)), Nat.add_comm]

instance neg : Neg G := ⟨(0 - ·)⟩
instance natCast : NatCast G := ⟨G.ofNat⟩

def ofInt : Int → G
  | .ofNat n => G.ofNat n
  | .negSucc n => -G.ofNat (n + 1)

instance intCast : IntCast G := ⟨ofInt⟩
instance nsmul : SMul Nat G := ⟨fun n a => G.ofNat n * a⟩
instance zsmul : SMul Int G := ⟨fun n a => ofInt n * a⟩
instance npow : HPow G Nat G := ⟨fun a n => npowRec n a⟩

theorem residue_numeral (n : Nat) : residue (OfNat.ofNat n : G) = OfNat.ofNat n :=
  residue_ofNat n

theorem residue_zero : residue 0 = 0 := rfl
theorem residue_one : residue 1 = 1 := rfl

theorem residue_neg (a : G) : residue (-a) = -residue a := by
  change residue (0 - a) = -residue a
  rw [residue_sub, residue_numeral]
  grind

theorem residue_ofInt (n : Int) : residue (ofInt n) = Int.cast n := by
  cases n with
  | ofNat n => exact residue_ofNat n
  | negSucc n =>
    change residue (-G.ofNat (n + 1)) = Int.cast (Int.negSucc n)
    rw [residue_neg, residue_ofNat]
    rfl

theorem left_distrib (a b c : G) : a * (b + c) = a * b + a * c := by
  apply residue_injective
  simp only [residue_add, residue_mul]
  grind

theorem neg_add_cancel (a : G) : -a + a = 0 := by
  apply residue_injective
  simp only [residue_add, residue_neg, residue_zero]
  grind

theorem sub_eq_add_neg (a b : G) : a - b = a + -b := by
  apply residue_injective
  simp only [residue_sub, residue_add, residue_neg]
  grind

theorem ofInt_neg (n : Int) : ofInt (-n) = -ofInt n := by
  apply residue_injective
  simp only [residue_ofInt, residue_neg]
  exact Lean.Grind.Ring.intCast_neg n

theorem neg_mul (a b : G) : -a * b = -(a * b) := by
  apply residue_injective
  simp only [residue_mul, residue_neg]
  grind

instance commRing : Lean.Grind.CommRing G where
  add_zero := G.add_zero
  add_comm := G.add_comm
  add_assoc := G.add_assoc
  mul_assoc := G.mul_assoc
  mul_comm := G.mul_comm
  mul_one := G.mul_one
  left_distrib := left_distrib
  zero_mul a := by rw [G.mul_comm, G.mul_zero]
  mul_zero := G.mul_zero
  pow_zero _ := rfl
  pow_succ _ _ := rfl
  ofNat_succ n := G.ofNat_add n 1
  neg_add_cancel := neg_add_cancel
  sub_eq_add_neg := sub_eq_add_neg
  intCast_neg := ofInt_neg
  neg_zsmul n a := by
    change ofInt (-n) * a = -(ofInt n * a)
    rw [ofInt_neg, neg_mul]

theorem pow_go_eq (a : G) (n fuel : Nat) (bounded : n < 2 ^ fuel) :
    Aiur.G.pow.go a n fuel = a ^ n := by
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
      simp only [Aiur.G.pow.go, beq_iff_eq, if_neg zero, ih _ half]
      by_cases even : n % 2 = 0
      · rw [if_pos even, ← Lean.Grind.Semiring.pow_add]
        congr 1
        omega
      · rw [if_neg even, ← Lean.Grind.Semiring.pow_add, ← Lean.Grind.Semiring.pow_succ]
        congr 1
        omega

theorem pow_eq (a : G) (n : Nat) (bounded : n < 2 ^ 64) : G.pow a n = a ^ n :=
  pow_go_eq a n 64 bounded

theorem inverse_eq_power (a : G) : G.inverse a = a ^ (gSize.toNat - 2) :=
  pow_eq a _ (by decide)

theorem n_power (a : G) (n : Nat) : (a ^ n).n = a.n ^ n % gSize.toNat := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Lean.Grind.Semiring.pow_succ, G.n_mul, ih, Nat.mod_mul_mod, Nat.pow_succ]

end Aiur.G
