import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.Prime

/-! Lucas certificates for the BN254 scalar modulus. Every factorization and
modular-power check is proved in Lean; no primality oracle or additional
axiom is part of the field instance. -/
namespace Aiur.Library.Field.BN254

abbrev modulus :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

private theorem prime_237073 : Nat.Prime 237073 := by
  apply lucas_primality 237073 (15 : ZMod 237073)
  · reduce_mod_char
  · intro q hq hd
    have factors : 237073 - 1 = 2^4 * 3 * 11 * 449 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_405928799 : Nat.Prime 405928799 := by
  apply lucas_primality 405928799 (22 : ZMod 405928799)
  · reduce_mod_char
  · intro q hq hd
    have factors : 405928799 - 1 = 2 * 11 * 4999 * 3691 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_93001 : Nat.Prime 93001 := by
  apply lucas_primality 93001 (14 : ZMod 93001)
  · reduce_mod_char
  · intro q hq hd
    have factors : 93001 - 1 = 2^3 * 3 * 5^3 * 31 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_12048837557 : Nat.Prime 12048837557 := by
  apply lucas_primality 12048837557 (2 : ZMod 12048837557)
  · reduce_mod_char
  · intro q hq hd
    have factors : 12048837557 - 1 = 2^2 * 7^2 * 661 * 93001 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_93001 | norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_5156902474397 : Nat.Prime 5156902474397 := by
  apply lucas_primality 5156902474397 (2 : ZMod 5156902474397)
  · reduce_mod_char
  · intro q hq hd
    have factors : 5156902474397 - 1 = 2^2 * 107 * 12048837557 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_12048837557 | norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_1670836401704629 : Nat.Prime 1670836401704629 := by
  apply lucas_primality 1670836401704629 (2 : ZMod 1670836401704629)
  · reduce_mod_char
  · intro q hq hd
    have factors : 1670836401704629 - 1 = 2^2 * 3^4 * 5156902474397 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_5156902474397 | norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_1593227 : Nat.Prime 1593227 := by
  apply lucas_primality 1593227 (2 : ZMod 1593227)
  · reduce_mod_char
  · intro q hq hd
    have factors : 1593227 - 1 = 2 * 19 * 41927 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_639533339 : Nat.Prime 639533339 := by
  apply lucas_primality 639533339 (2 : ZMod 639533339)
  · reduce_mod_char
  · intro q hq hd
    have factors : 639533339 - 1 = 2 * 229 * 853 * 1637 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_65865678001877903 : Nat.Prime 65865678001877903 := by
  apply lucas_primality 65865678001877903 (5 : ZMod 65865678001877903)
  · reduce_mod_char
  · intro q hq hd
    have factors : 65865678001877903 - 1 = 2 * 83 * 379 * 1637 * 639533339 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_639533339 | norm_num)] at hd
      subst q
      reduce_mod_char
      decide

private theorem prime_13818364434197438864469338081 : Nat.Prime 13818364434197438864469338081 := by
  apply lucas_primality 13818364434197438864469338081 (3 : ZMod 13818364434197438864469338081)
  · reduce_mod_char
  · intro q hq hd
    have factors : 13818364434197438864469338081 - 1 =
        2^5 * 5 * 823 * 1593227 * 65865678001877903 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by
        first | exact prime_1593227 | exact prime_65865678001877903 | norm_num)] at hd
      subst q
      reduce_mod_char
      decide

theorem modulus_prime : Nat.Prime modulus := by
  apply lucas_primality modulus (5 : ZMod modulus)
  · reduce_mod_char
  · intro q hq hd
    have factors : modulus - 1 =
        2^28 * 3^2 * 13 * 29 * 983 * 237073 * 11003 * 405928799 *
          1670836401704629 * 13818364434197438864469338081 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd | hd | hd | hd | hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by
        first
        | exact prime_237073
        | exact prime_405928799
        | exact prime_1670836401704629
        | exact prime_13818364434197438864469338081
        | norm_num)] at hd
      subst q
      reduce_mod_char
      decide

end Aiur.Library.Field.BN254
