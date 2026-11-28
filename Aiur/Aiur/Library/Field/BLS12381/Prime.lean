import Aiur.Library.U32
import Aiur.Library.U64
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.Prime

/-! Lucas primality certificates for the BLS12-381 scalar field modulus.
Every factorization and modular-power check is proved in Lean; no primality
oracle or additional axiom is part of the field instance. -/
namespace Aiur.Library.Field.BLS12381

abbrev modulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

abbrev F := ZMod modulus

section Primality

set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

private theorem prime_10177 : Nat.Prime 10177 := by
  apply lucas_primality 10177 (7 : ZMod 10177)
  · reduce_mod_char
  · intro q hq hd
    have factors : 10177 - 1 = 2^6 * 3 * 53 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_20921 : Nat.Prime 20921 := by
  apply lucas_primality 20921 (3 : ZMod 20921)
  · reduce_mod_char
  · intro q hq hd
    have factors : 20921 - 1 = 2^3 * 5 * 523 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_125527 : Nat.Prime 125527 := by
  apply lucas_primality 125527 (5 : ZMod 125527)
  · reduce_mod_char
  · intro q hq hd
    have factors : 125527 - 1 = 2 * 3 * 20921 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_20921 | norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_47737 : Nat.Prime 47737 := by
  apply lucas_primality 47737 (5 : ZMod 47737)
  · reduce_mod_char
  · intro q hq hd
    have factors : 47737 - 1 = 2^3 * 3^3 * 13 * 17 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_859267 : Nat.Prime 859267 := by
  apply lucas_primality 859267 (2 : ZMod 859267)
  · reduce_mod_char
  · intro q hq hd
    have factors : 859267 - 1 = 2 * 3^2 * 47737 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_47737 | norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_906349 : Nat.Prime 906349 := by
  apply lucas_primality 906349 (2 : ZMod 906349)
  · reduce_mod_char
  · intro q hq hd
    have factors : 906349 - 1 = 2^2 * 3 * 47 * 1607 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_2508409 : Nat.Prime 2508409 := by
  apply lucas_primality 2508409 (11 : ZMod 2508409)
  · reduce_mod_char
  · intro q hq hd
    have factors : 2508409 - 1 = 2^3 * 3^4 * 7^2 * 79 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_18329 : Nat.Prime 18329 := by
  apply lucas_primality 18329 (3 : ZMod 18329)
  · reduce_mod_char
  · intro q hq hd
    have factors : 18329 - 1 = 2^3 * 29 * 79 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_2529403 : Nat.Prime 2529403 := by
  apply lucas_primality 2529403 (2 : ZMod 2529403)
  · reduce_mod_char
  · intro q hq hd
    have factors : 2529403 - 1 = 2 * 3 * 23 * 18329 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_18329 | norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_609743 : Nat.Prime 609743 := by
  apply lucas_primality 609743 (5 : ZMod 609743)
  · reduce_mod_char
  · intro q hq hd
    have factors : 609743 - 1 = 2 * 7 * 97 * 449 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_52437899 : Nat.Prime 52437899 := by
  apply lucas_primality 52437899 (2 : ZMod 52437899)
  · reduce_mod_char
  · intro q hq hd
    have factors : 52437899 - 1 = 2 * 43 * 609743 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_609743 | norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_110573 : Nat.Prime 110573 := by
  apply lucas_primality 110573 (3 : ZMod 110573)
  · reduce_mod_char
  · intro q hq hd
    have factors : 110573 - 1 = 2^2 * 7 * 11 * 359 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_2653753 : Nat.Prime 2653753 := by
  apply lucas_primality 2653753 (5 : ZMod 2653753)
  · reduce_mod_char
  · intro q hq hd
    have factors : 2653753 - 1 = 2^3 * 3 * 110573 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_110573 | norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_63690073 : Nat.Prime 63690073 := by
  apply lucas_primality 63690073 (7 : ZMod 63690073)
  · reduce_mod_char
  · intro q hq hd
    have factors : 63690073 - 1 = 2^3 * 3 * 2653753 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_2653753 | norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_254760293 : Nat.Prime 254760293 := by
  apply lucas_primality 254760293 (2 : ZMod 254760293)
  · reduce_mod_char
  · intro q hq hd
    have factors : 254760293 - 1 = 2^2 * 63690073 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul] at hd
    rcases hd with hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_63690073 | norm_num)] at hd
      subst q
      reduce_mod_char
      decide

theorem modulus_prime : Nat.Prime modulus := by
  apply lucas_primality modulus (7 : ZMod modulus)
  · reduce_mod_char
  · intro q hq hd
    have factors : modulus - 1 =
        2^32 * 3 * 11 * 19 * 10177 * 125527 * 859267 * 906349^2 * 2508409 *
          2529403 * 52437899 * 254760293^2 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by
        first
        | exact prime_10177
        | exact prime_125527
        | exact prime_859267
        | exact prime_906349
        | exact prime_2508409
        | exact prime_2529403
        | exact prime_52437899
        | exact prime_254760293
        | norm_num)] at hd
      subst q
      reduce_mod_char
      decide

end Primality

instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

theorem modulus_pos : 0 < modulus := by norm_num

theorem two_lt_modulus : 2 < modulus := by norm_num

theorem two_pow_63_lt_modulus : 2 ^ 63 < modulus := by norm_num

theorem two_pow_254_lt_modulus : 2 ^ 254 < modulus := by norm_num

theorem modulus_lt_two_pow_255 : modulus < 2 ^ 255 := by norm_num

theorem modulus_lt_two_pow_256 : modulus < 2 ^ 256 := by norm_num

theorem u32_compatible : U32.Compatible F :=
  U32.compatible_of_charP F modulus (by decide)

theorem u64_compatible : U64.Compatible F :=
  U64.compatible_of_charP F modulus (by decide)

end Aiur.Library.Field.BLS12381
