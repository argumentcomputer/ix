/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Domain
import Ix.Aiur.Proofs.SelectorAlgebra

/-! Exact orders and row locations for all 33 native trace-domain generators.
The finite certificates evaluate bounded repeated squaring in the kernel;
the domain itself is represented by an index function, without enumeration.
-/

namespace Aiur.NativeAIR.Domain

open Lean.Grind

theorem ofLogSize_some {bits : Nat} {domain : Subgroup}
    (accepted : ofLogSize bits = some domain) : domain.val = bits := by
  simp only [ofLogSize] at accepted
  split at accepted
  · exact congrArg Fin.val (Option.some.inj accepted).symm
  · cases accepted

theorem ofLogSize_defined (bits : Nat) : (ofLogSize bits).isSome = (bits < 33) := by
  simp only [ofLogSize]
  split <;> simp_all

theorem size_positive (domain : Subgroup) : 0 < size domain := Nat.two_pow_pos _

theorem size_bound (domain : Subgroup) : size domain ≤ 2 ^ 32 := by
  apply Nat.pow_le_pow_right (by decide)
  have := domain.isLt
  omega

theorem size_lt_characteristic (domain : Subgroup) : size domain < gSize.toNat :=
  Nat.lt_of_le_of_lt (size_bound domain) (by decide)

theorem size_lt_u64 (domain : Subgroup) : size domain < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (size_bound domain) (by decide)

theorem generator_zero : generator 0 = 1 := by decide +kernel

theorem generator_square_certificate : ∀ index : Fin 32,
    generator ⟨index.val + 1, by omega⟩ * generator ⟨index.val + 1, by omega⟩ =
      generator ⟨index.val, by omega⟩ := by
  decide +kernel

theorem generator_full_certificate : ∀ domain : Subgroup,
    G.pow (generator domain) (size domain) = 1 := by
  decide +kernel

theorem generator_half_certificate : ∀ index : Fin 32,
    G.pow (generator ⟨index.val + 1, by omega⟩) (2 ^ index.val) = 0 - 1 := by
  decide +kernel

theorem generator_power (domain : Subgroup) : generator domain ^ size domain = 1 := by
  rw [← G.pow_eq _ _ (size_lt_u64 domain)]
  exact generator_full_certificate domain

theorem generator_half (index : Fin 32) :
    generator ⟨index.val + 1, by omega⟩ ^ (2 ^ index.val) = 0 - 1 := by
  rw [← G.pow_eq _ _ (by
    apply Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt index.isLt))
    decide)]
  exact generator_half_certificate index

theorem generator_nonzero (domain : Subgroup) : generator domain ≠ 0 := by
  intro zero
  have power := generator_power domain
  have positive := size_positive domain
  have successor : size domain = (size domain - 1) + 1 := by omega
  rw [zero, successor, Semiring.pow_succ, G.mul_zero] at power
  exact G.one_ne_zero power.symm

theorem point_eq (domain : Subgroup) (index : Fin (size domain)) :
    point domain index = generator domain ^ index.val :=
  G.pow_eq _ _ (Nat.lt_trans index.isLt (size_lt_u64 domain))

theorem point_injective (domain : Subgroup) {i j : Fin (size domain)}
    (equal : point domain i = point domain j) : i = j := by
  apply Fin.ext
  cases domain with
  | mk bits bounded =>
    cases bits with
    | zero => have := i.isLt; have := j.isLt; simp only [size, Nat.pow_zero] at *; omega
    | succ bits =>
      have full := congrArg G.n (generator_power ⟨bits + 1, bounded⟩)
      have half := congrArg G.n (generator_half ⟨bits, by omega⟩)
      have same := congrArg G.n equal
      simp only [point_eq, G.n_power] at same
      simp only [G.n_power, size] at full half
      apply GoldilocksProof.pow_mod_injective (by decide) full
        (fun h => (by decide : G.n (0 - 1) ≠ 1) (half.symm.trans h)) i.isLt j.isLt same

theorem generator_order (domain : Subgroup) (n : Nat) :
    generator domain ^ n = 1 ↔ size domain ∣ n := by
  have period := Algebra.power_period (generator domain) (generator_power domain) n
  constructor
  · intro equal
    have same : point domain ⟨n % size domain, Nat.mod_lt _ (size_positive domain)⟩ =
        point domain ⟨0, size_positive domain⟩ := by
      simp only [point_eq, Semiring.pow_zero]
      exact period.symm.trans equal
    have zero := congrArg Fin.val (point_injective domain same)
    exact Nat.dvd_of_mod_eq_zero zero
  · intro divides
    rw [period, Nat.mod_eq_zero_of_dvd divides, Semiring.pow_zero]

theorem point_zero (domain : Subgroup) : point domain ⟨0, size_positive domain⟩ = 1 := by
  rw [point_eq, Semiring.pow_zero]

theorem point_power (domain : Subgroup) (index : Fin (size domain)) :
    point domain index ^ size domain = 1 := by
  rw [point_eq, ← Algebra.power_mul, Nat.mul_comm, Algebra.power_mul,
    generator_power, Semiring.one_pow]

theorem point_nonzero (domain : Subgroup) (index : Fin (size domain)) :
    point domain index ≠ 0 := by
  intro zero
  have power := point_power domain index
  rw [zero, Algebra.power_zero _ (size_positive domain)] at power
  exact G.one_ne_zero power.symm

theorem point_next (domain : Subgroup) (index : Fin (size domain)) :
    point domain ⟨(index.val + 1) % size domain, Nat.mod_lt _ (size_positive domain)⟩ =
      point domain index * generator domain := by
  rw [point_eq, point_eq, ← Algebra.power_period _ (generator_power domain), Semiring.pow_succ]

theorem point_first_iff (domain : Subgroup) (index : Fin (size domain)) :
    point domain index = 1 ↔ index.val = 0 := by
  constructor
  · intro equal
    exact congrArg Fin.val (point_injective domain (equal.trans (point_zero domain).symm))
  · intro zero
    rw [point_eq, zero, Semiring.pow_zero]

theorem lastPoint_eq_power (domain : Subgroup) :
    lastPoint domain = generator domain ^ (size domain - 1) := by
  exact (Algebra.predecessor_inverse _ _ (size_positive domain) (generator_power domain)
    (G.mul_inverse_cancel _ (generator_nonzero domain))).symm

theorem point_last (domain : Subgroup) :
    point domain ⟨size domain - 1, by have := size_positive domain; omega⟩ = lastPoint domain := by
  rw [point_eq, lastPoint_eq_power]

theorem lastPoint_power (domain : Subgroup) : lastPoint domain ^ size domain = 1 := by
  rw [← point_last domain]
  exact point_power _ _

theorem point_last_iff (domain : Subgroup) (index : Fin (size domain)) :
    point domain index = lastPoint domain ↔ index.val = size domain - 1 := by
  constructor
  · intro equal
    exact congrArg Fin.val (point_injective domain (equal.trans (point_last domain).symm))
  · intro equal
    rw [point_eq, equal, lastPoint_eq_power]

theorem lastPoint_nonzero (domain : Subgroup) : lastPoint domain ≠ 0 := by
  rw [← point_last domain]
  exact point_nonzero _ _

theorem lastPoint_inverse (domain : Subgroup) : lastPoint domain * generator domain = 1 := by
  rw [G.mul_comm]
  exact G.mul_inverse_cancel _ (generator_nonzero domain)

theorem lastPoint_predecessor (domain : Subgroup) :
    lastPoint domain ^ (size domain - 1) = generator domain :=
  Algebra.predecessor_inverse _ _ (size_positive domain) (lastPoint_power domain)
    (lastPoint_inverse domain)

theorem normalizer_nonzero (domain : Subgroup) : normalizer domain ≠ 0 := by
  intro zero
  have factors := (G.mul_eq_zero_iff _ _).mp zero
  exact factors.elim
    (G.ofNat_ne_zero_of_lt (size_positive domain) (size_lt_characteristic domain))
    (generator_nonzero domain)

end Aiur.NativeAIR.Domain
