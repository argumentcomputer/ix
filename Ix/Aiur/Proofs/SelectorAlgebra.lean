/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ExtensionField

/-! Polynomial identities underlying the native domain selectors.
The divided-power polynomial is symbolic: native evaluation uses the
checked rational formula away from roots, without enumerating the domain.
-/

namespace Aiur.NativeAIR.Domain.Algebra

open Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

variable {R : Type} [CommRing R]

theorem power_zero (n : Nat) (positive : 0 < n) : (0 : R) ^ n = 0 := by
  have successor : n = (n - 1) + 1 := by omega
  rw [successor, Semiring.pow_succ, Semiring.mul_zero]

theorem power_mul (a : R) (m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero => simp only [Nat.mul_zero, Semiring.pow_zero]
  | succ n ih => rw [Nat.mul_succ, Semiring.pow_add, ih, Semiring.pow_succ]

theorem power_period (a : R) {period : Nat} (order : a ^ period = 1) (n : Nat) :
    a ^ n = a ^ (n % period) := by
  conv => lhs; rw [← Nat.mod_add_div n period]
  rw [Semiring.pow_add, power_mul, order, Semiring.one_pow, Semiring.mul_one]

theorem power_inverse (a inverse : R) (cancel : a * inverse = 1) (n : Nat) :
    a ^ n * inverse ^ n = 1 := by
  rw [← CommSemiring.mul_pow, cancel, Semiring.one_pow]

theorem predecessor_inverse (a inverse : R) {n : Nat} (positive : 0 < n)
    (order : a ^ n = 1) (cancel : a * inverse = 1) : a ^ (n - 1) = inverse := by
  have successor : n = (n - 1) + 1 := by omega
  rw [successor, Semiring.pow_succ] at order
  have multiplied := congrArg (fun x => x * inverse) order
  grind

/-- `sum (x^(n-1-j) * a^j)`, kept out of runtime initialization. -/
noncomputable def dividedPowers (x a : R) : Nat → R
  | 0 => 0
  | n + 1 => x ^ n + a * dividedPowers x a n

theorem dividedPowers_factor (x a : R) (n : Nat) :
    (x - a) * dividedPowers x a n = x ^ n - a ^ n := by
  induction n with
  | zero => simp only [dividedPowers, Semiring.pow_zero]; grind
  | succ n ih => rw [dividedPowers, Semiring.pow_succ, Semiring.pow_succ]; grind

theorem dividedPowers_diagonal (a : R) (n : Nat) :
    dividedPowers a a n = (n : R) * a ^ (n - 1) := by
  induction n with
  | zero => simp only [dividedPowers, Semiring.natCast_zero, Semiring.zero_mul]
  | succ n ih =>
    rw [dividedPowers, ih, Semiring.natCast_succ]
    cases n with
    | zero => simp only [Nat.zero_sub, Nat.add_sub_cancel, Semiring.pow_zero,
        Semiring.natCast_zero]; grind
    | succ n => simp only [Nat.add_sub_cancel, Semiring.pow_succ]; grind

theorem root_dividedPowers (x a : R) {n : Nat} (root : a ^ n = 1) :
    (x - a) * dividedPowers x a n = x ^ n - 1 := by
  rw [dividedPowers_factor, root]

theorem dividedPowers_off_root (x a inverse : R) {n : Nat}
    (root : a ^ n = 1) (cancel : (x - a) * inverse = 1) :
    (x ^ n - 1) * inverse = dividedPowers x a n := by
  have factor := root_dividedPowers x a root
  have multiplied := congrArg (fun z => z * inverse) factor
  grind

end Aiur.NativeAIR.Domain.Algebra
