/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.Lookup
import Init.Data.Nat.Coprime
import Init.Data.List.Nat.Range
import Init.Data.List.Perm

/-!
Primality and local field consequences for the actual Goldilocks model.

A kernel-checked certificate gives a unit of order `2^32` modulo every
nontrivial divisor of `2^64 - 2^32 + 1`. Its first `2^32` powers are distinct,
so each such divisor is at least `2^32`. Two nontrivial factors would have
product at least `2^64`, proving primality. Only 32 modular squarings are
evaluated; the proof neither enumerates the field nor evaluates enormous
unreduced powers. It uses no native-evaluation axiom or external field oracle.

The resulting no-zero-divisors theorem discharges boolean-selector and
equality-test polynomial implications. These are arithmetic facts about
Lean's `G`; extraction from native constraint expressions remains separate.
-/

namespace Aiur.GoldilocksProof

/-- Repeated modular squaring, with an explicit modulus and base. -/
def squareMod (modulus base : Nat) : Nat → Nat
  | 0 => base % modulus
  | n + 1 => let previous := squareMod modulus base n; previous * previous % modulus

theorem squareMod_eq (modulus base n : Nat) :
    squareMod modulus base n = base ^ (2 ^ n) % modulus := by
  induction n with
  | zero => simp [squareMod]
  | succ n ih =>
    rw [squareMod, ih, Nat.pow_succ, Nat.pow_mul]
    simp only [Nat.pow_two, Nat.mul_mod_mod, Nat.mod_mul_mod]

theorem squareMod_half : squareMod gSize.toNat 1753635133440165772 31 = gSize.toNat - 1 := by
  decide +kernel

theorem squareMod_full : squareMod gSize.toNat 1753635133440165772 32 = 1 := by
  decide +kernel

theorem pow_mod_period {modulus base period : Nat} (hmod : 1 < modulus)
    (hperiod : base ^ period % modulus = 1) (exponent : Nat) :
    base ^ exponent % modulus = base ^ (exponent % period) % modulus := by
  conv => lhs; rw [← Nat.mod_add_div exponent period]
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod (base ^ period), hperiod]
  simp only [Nat.one_pow, Nat.mod_eq_of_lt hmod, Nat.mul_one, Nat.mod_mod]

theorem pow_mod_gcd {modulus base : Nat} (hmod : 1 < modulus) (a b : Nat)
    (ha : base ^ a % modulus = 1) (hb : base ^ b % modulus = 1) :
    base ^ (Nat.gcd a b) % modulus = 1 := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    by_cases hz : a = 0
    · subst a; simpa only [Nat.gcd_zero_left] using hb
    · rw [Nat.gcd_rec]
      apply ih (b % a) (Nat.mod_lt _ (Nat.pos_of_ne_zero hz)) a
      · exact (pow_mod_period hmod ha b).symm.trans hb
      · exact ha

theorem divisor_two_pow {d n : Nat} (divides : d ∣ 2 ^ n) :
    ∃ k, k ≤ n ∧ d = 2 ^ k := by
  induction n generalizing d with
  | zero => exact ⟨0, Nat.le_refl _, Nat.eq_one_of_dvd_one divides⟩
  | succ n ih =>
    rw [Nat.pow_succ, Nat.dvd_mul] at divides
    obtain ⟨a, b, ha, hb, equal⟩ := divides
    obtain ⟨k, hk, rfl⟩ := ih ha
    have bound : b ≤ 2 := Nat.le_of_dvd (by decide) hb
    have positive : 0 < b := Nat.pos_of_dvd_of_pos hb (by decide)
    have cases : b = 1 ∨ b = 2 := by omega
    rcases cases with rfl | rfl
    · exact ⟨k, by omega, by simpa only [Nat.mul_one] using equal.symm⟩
    · exact ⟨k + 1, by omega, by simpa only [Nat.pow_succ] using equal.symm⟩

theorem proper_divisor_two_pow {d n : Nat} (divides : d ∣ 2 ^ (n + 1))
    (proper : d < 2 ^ (n + 1)) : d ∣ 2 ^ n := by
  obtain ⟨k, hk, rfl⟩ := divisor_two_pow divides
  apply Nat.pow_dvd_pow
  have ne : k ≠ n + 1 := by intro equal; subst k; exact Nat.lt_irrefl _ proper
  omega

theorem pow_mod_ne_one {modulus base n : Nat} (hmod : 1 < modulus)
    (full : base ^ (2 ^ (n + 1)) % modulus = 1)
    (half : base ^ (2 ^ n) % modulus ≠ 1)
    {k : Nat} (positive : 0 < k) (small : k < 2 ^ (n + 1)) :
    base ^ k % modulus ≠ 1 := by
  intro equal
  have hg := pow_mod_gcd hmod k (2 ^ (n + 1)) equal full
  have gd : Nat.gcd k (2 ^ (n + 1)) ∣ 2 ^ n := by
    apply proper_divisor_two_pow (Nat.gcd_dvd_right _ _)
    exact Nat.lt_of_le_of_lt (Nat.gcd_le_left _ positive) small
  apply half
  rw [pow_mod_period hmod hg, Nat.mod_eq_zero_of_dvd gd]
  exact Nat.mod_eq_of_lt hmod

theorem pow_mod_injective {modulus base n : Nat} (hmod : 1 < modulus)
    (full : base ^ (2 ^ (n + 1)) % modulus = 1)
    (half : base ^ (2 ^ n) % modulus ≠ 1)
    {i j : Nat} (hi : i < 2 ^ (n + 1)) (hj : j < 2 ^ (n + 1))
    (equal : base ^ i % modulus = base ^ j % modulus) : i = j := by
  suffices step : ∀ i j, i < j → j < 2 ^ (n + 1) →
      base ^ i % modulus = base ^ j % modulus → False by
    by_cases h : i < j
    · exact False.elim (step i j h hj equal)
    · by_cases h' : j < i
      · exact False.elim (step j i h' hi equal.symm)
      · omega
  intro i j lt bound same
  have translated : base ^ (i + (2 ^ (n + 1) - i)) % modulus =
      base ^ (j + (2 ^ (n + 1) - i)) % modulus := by
    rw [Nat.pow_add base i, Nat.pow_add base j,
      Nat.mul_mod (base ^ i), Nat.mul_mod (base ^ j), same]
  have left : i + (2 ^ (n + 1) - i) = 2 ^ (n + 1) := by omega
  have right : j + (2 ^ (n + 1) - i) = (j - i) + 2 ^ (n + 1) := by omega
  rw [left, full, right, Nat.pow_add, Nat.mul_mod, full, Nat.mul_one, Nat.mod_mod] at translated
  exact pow_mod_ne_one hmod full half (by omega) (by omega) translated.symm

theorem two_pow_le_modulus {modulus base n : Nat} (hmod : 1 < modulus)
    (full : base ^ (2 ^ (n + 1)) % modulus = 1)
    (half : base ^ (2 ^ n) % modulus ≠ 1) : 2 ^ (n + 1) ≤ modulus := by
  let residues := List.ofFn fun i : Fin (2 ^ (n + 1)) => base ^ i.val % modulus
  have distinct : residues.Nodup := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj lt same
    simp only [residues, List.getElem_ofFn] at same
    have hi' : i < 2 ^ (n + 1) := by simpa only [residues, List.length_ofFn] using hi
    have hj' : j < 2 ^ (n + 1) := by simpa only [residues, List.length_ofFn] using hj
    have equal := pow_mod_injective hmod full half hi' hj' same
    omega
  have subset : residues ⊆ List.range modulus := by
    intro value member
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
    exact List.mem_range.mpr (Nat.mod_lt _ (by omega))
  have bound := distinct.length_le_of_subset subset
  simpa only [residues, List.length_ofFn, List.length_range] using bound

/-- A power-of-two order certificate forces every nontrivial divisor to
contain at least that many distinct residues. -/
theorem two_power_divisor_bound {modulus base n : Nat}
    (certificateFull : squareMod modulus base (n + 1) = 1)
    (certificateHalf : Nat.gcd modulus (squareMod modulus base n - 1) = 1)
    {d : Nat} (divides : d ∣ modulus) (nontrivial : 1 < d) : 2 ^ (n + 1) ≤ d := by
  have full : base ^ (2 ^ (n + 1)) % d = 1 := by
    have h := congrArg (· % d) certificateFull
    rw [squareMod_eq, Nat.mod_mod_of_dvd _ divides, Nat.mod_eq_of_lt nontrivial] at h
    exact h
  have half : base ^ (2 ^ n) % d ≠ 1 := by
    intro equal
    have h : squareMod modulus base n % d = 1 := by
      rw [squareMod_eq, Nat.mod_mod_of_dvd _ divides, equal]
    have hd : d ∣ squareMod modulus base n - 1 :=
      Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq
        (h.trans (Nat.mod_eq_of_lt nontrivial).symm))
    have one := Nat.dvd_gcd divides hd
    rw [certificateHalf] at one
    have := Nat.eq_one_of_dvd_one one
    omega
  exact two_pow_le_modulus nontrivial full half

theorem nontrivial_divisor_large {d : Nat} (divides : d ∣ gSize.toNat)
    (nontrivial : 1 < d) : 2 ^ 32 ≤ d := by
  apply two_power_divisor_bound (modulus := gSize.toNat) (base := 1753635133440165772)
    (n := 31) squareMod_full ?_ divides nontrivial
  rw [squareMod_half]
  decide +kernel

theorem goldilocks_divisors {d : Nat} (divides : d ∣ gSize.toNat) :
    d = 1 ∨ d = gSize.toNat := by
  obtain ⟨e, product⟩ := divides
  by_cases hd : d = 1
  · exact Or.inl hd
  · by_cases he : e = 1
    · exact Or.inr (by simpa only [he, Nat.mul_one] using product.symm)
    · have positiveD : 0 < d := Nat.pos_of_dvd_of_pos ⟨e, product⟩ (by decide)
      have dividesE : e ∣ gSize.toNat := ⟨d, product.trans (Nat.mul_comm _ _)⟩
      have positiveE : 0 < e := Nat.pos_of_dvd_of_pos dividesE (by decide)
      have boundD := nontrivial_divisor_large ⟨e, product⟩ (by omega)
      have boundE := nontrivial_divisor_large dividesE (by omega)
      have impossible := Nat.mul_le_mul boundD boundE
      rw [← product] at impossible
      have bad : ¬(2 ^ 32 * 2 ^ 32 ≤ gSize.toNat) := by decide +kernel
      exact False.elim (bad impossible)

end Aiur.GoldilocksProof

namespace Aiur

/-- Primality stated explicitly as the nontriviality and divisor criterion. -/
theorem gSize_prime : 1 < gSize.toNat ∧
    ∀ d : Nat, d ∣ gSize.toNat → d = 1 ∨ d = gSize.toNat :=
  ⟨by decide, fun _ => GoldilocksProof.goldilocks_divisors⟩

theorem G.n_eq_zero_iff (a : G) : a.n = 0 ↔ a = 0 := by
  constructor
  · intro equal
    rw [← G.ofNat_n a, equal]
    rfl
  · intro equal; subst a; rfl

theorem G.coprime_characteristic_of_ne_zero {a : G} (nonzero : a ≠ 0) :
    Nat.Coprime gSize.toNat a.n := by
  have positive : 0 < a.n := Nat.pos_of_ne_zero fun equal => nonzero ((G.n_eq_zero_iff a).mp equal)
  have bounded : a.n < gSize.toNat := UInt64.lt_iff_toNat_lt.mp a.property
  rcases GoldilocksProof.goldilocks_divisors (Nat.gcd_dvd_left gSize.toNat a.n) with one | whole
  · exact one
  · have small := Nat.gcd_le_right gSize.toNat positive
    rw [whole] at small
    omega

theorem G.mul_eq_zero_iff (a b : G) : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro equal
    by_cases zero : a = 0
    · exact Or.inl zero
    · apply Or.inr
      have numeric := congrArg G.n equal
      rw [G.n_mul] at numeric
      have divides : gSize.toNat ∣ b.n :=
        (G.coprime_characteristic_of_ne_zero zero).dvd_of_dvd_mul_left
          (Nat.dvd_of_mod_eq_zero numeric)
      have bound : b.n < gSize.toNat := UInt64.lt_iff_toNat_lt.mp b.property
      apply (G.n_eq_zero_iff b).mp
      by_cases z : b.n = 0
      · exact z
      · have large := Nat.le_of_dvd (Nat.pos_of_ne_zero z) divides
        omega
  · rintro (rfl | rfl)
    · rw [G.mul_comm, G.mul_zero]
    · exact G.mul_zero a

theorem G.mul_eq_zero_of_left_ne_zero {a b : G} (nonzero : a ≠ 0) (zero : a * b = 0) :
    b = 0 := (G.mul_eq_zero_iff a b).mp zero |>.resolve_left nonzero

theorem G.boolean_of_constraint {value : G} (satisfied : value * (value - 1) = 0) :
    value = 0 ∨ value = 1 := by
  rcases (G.mul_eq_zero_iff _ _).mp satisfied with zero | one
  · exact Or.inl zero
  · exact Or.inr ((G.sub_eq_zero_iff value 1).mp one)

theorem G.boolean_of_one_sub_constraint {value : G} (satisfied : value * (1 - value) = 0) :
    value = 0 ∨ value = 1 := by
  rcases (G.mul_eq_zero_iff _ _).mp satisfied with zero | one
  · exact Or.inl zero
  · exact Or.inr (((G.sub_eq_zero_iff 1 value).mp one).symm)

theorem G.eqZero_of_constraints {input inverse output : G}
    (annihilate : input * output = 0)
    (complement : input * inverse + output - 1 = 0) : output = G.eqZero input := by
  by_cases zero : input = 0
  · rw [zero, G.mul_comm (0 : G), G.mul_zero, G.zero_add] at complement
    rw [G.eqZero, if_pos zero]
    exact (G.sub_eq_zero_iff output 1).mp complement
  · rw [G.eqZero, if_neg zero]
    exact G.mul_eq_zero_of_left_ne_zero zero annihilate

theorem G.ne_zero_of_inverse_constraint {input inverse : G}
    (satisfied : input * inverse - 1 = 0) : input ≠ 0 := by
  intro zero
  rw [zero, G.mul_comm (0 : G), G.mul_zero] at satisfied
  exact G.one_ne_zero ((G.sub_eq_zero_iff (0 : G) 1).mp satisfied).symm

end Aiur
