import Mathlib.Tactic

/-! Arithmetic identities used by the ordinary Aiur byte library to reuse
XOR's fixed lookup for AND/OR. Proved by binary recursion on `Nat.bitwise`,
then lifted to any field in which two is nonzero. -/
namespace Aiur.Library.U8

theorem nat_xor_and_sum (n m : Nat) :
    n + m = Nat.xor n m + 2 * Nat.land n m := by
  induction n using Nat.strongRecOn generalizing m with
  | ind n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    have hrec := ih (n / 2) (Nat.div_lt_self (by omega) (by omega)) (m / 2)
    unfold Nat.xor Nat.land at hrec ⊢
    rw [Nat.bitwise, Nat.bitwise]
    dsimp only
    simp only [hn, hm, ↓reduceIte]
    rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hn2 | hn2 <;>
      rcases (by omega : m % 2 = 0 ∨ m % 2 = 1) with hm2 | hm2
    · have h1 : decide (n % 2 = 1) = false := by simp [hn2]
      have h2 : decide (m % 2 = 1) = false := by simp [hm2]
      simp [h1, h2]; omega
    · have h1 : decide (n % 2 = 1) = false := by simp [hn2]
      have h2 : decide (m % 2 = 1) = true := by simp [hm2]
      simp [h1, h2]; omega
    · have h1 : decide (n % 2 = 1) = true := by simp [hn2]
      have h2 : decide (m % 2 = 1) = false := by simp [hm2]
      simp [h1, h2]; omega
    · have h1 : decide (n % 2 = 1) = true := by simp [hn2]
      have h2 : decide (m % 2 = 1) = true := by simp [hm2]
      simp [h1, h2]; omega

theorem nat_xor_or_sum (n m : Nat) :
    2 * Nat.lor n m = n + m + Nat.xor n m := by
  induction n using Nat.strongRecOn generalizing m with
  | ind n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp; omega
    rcases eq_or_ne m 0 with rfl | hm
    · simp; omega
    have hrec := ih (n / 2) (Nat.div_lt_self (by omega) (by omega)) (m / 2)
    unfold Nat.lor Nat.xor at hrec ⊢
    rw [Nat.bitwise, Nat.bitwise]
    dsimp only
    simp only [hn, hm, ↓reduceIte]
    rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hn2 | hn2 <;>
      rcases (by omega : m % 2 = 0 ∨ m % 2 = 1) with hm2 | hm2
    · have h1 : decide (n % 2 = 1) = false := by simp [hn2]
      have h2 : decide (m % 2 = 1) = false := by simp [hm2]
      simp [h1, h2]; omega
    · have h1 : decide (n % 2 = 1) = false := by simp [hn2]
      have h2 : decide (m % 2 = 1) = true := by simp [hm2]
      simp [h1, h2]; omega
    · have h1 : decide (n % 2 = 1) = true := by simp [hn2]
      have h2 : decide (m % 2 = 1) = false := by simp [hm2]
      simp [h1, h2]; omega
    · have h1 : decide (n % 2 = 1) = true := by simp [hn2]
      have h2 : decide (m % 2 = 1) = true := by simp [hm2]
      simp [h1, h2]; omega

theorem xor_and_sum (a b : BitVec 8) :
    a.toNat + b.toNat = (a ^^^ b).toNat + 2 * (a &&& b).toNat := by
  rw [BitVec.toNat_xor, BitVec.toNat_and]
  exact nat_xor_and_sum a.toNat b.toNat

theorem xor_or_sum (a b : BitVec 8) :
    2 * (a ||| b).toNat = a.toNat + b.toNat + (a ^^^ b).toNat := by
  rw [BitVec.toNat_or, BitVec.toNat_xor]
  exact nat_xor_or_sum a.toNat b.toNat

theorem and_field {F : Type*} [Field F] (two : (2 : F) ≠ 0) (a b : BitVec 8) :
    ((a.toNat : F) + b.toNat - (a ^^^ b).toNat) / 2 = ((a &&& b).toNat : F) := by
  have h := congrArg (fun n : Nat => (n : F)) (xor_and_sum a b)
  push_cast at h
  apply (div_eq_iff two).mpr
  linear_combination h

theorem or_field {F : Type*} [Field F] (two : (2 : F) ≠ 0) (a b : BitVec 8) :
    ((a.toNat : F) + b.toNat + (a ^^^ b).toNat) / 2 = ((a ||| b).toNat : F) := by
  have h := congrArg (fun n : Nat => (n : F)) (xor_or_sum a b)
  push_cast at h
  apply (div_eq_iff two).mpr
  linear_combination -h

end Aiur.Library.U8

namespace Aiur.Library.U8Facts

theorem xor_lt_256 {a b : Nat} (ha : a < 256) (hb : b < 256) :
    Nat.xor a b < 256 := by
  have h : Nat.xor a b = (BitVec.ofNat 8 a ^^^ BitVec.ofNat 8 b).toNat := by
    simp [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rw [h]
  exact (BitVec.ofNat 8 a ^^^ BitVec.ofNat 8 b).isLt

theorem xor_and_identity (a b : Nat) :
    a + b = Nat.xor a b + 2 * Nat.land a b :=
  U8.nat_xor_and_sum a b

theorem xor_or_identity (a b : Nat) :
    2 * Nat.lor a b = a + b + Nat.xor a b :=
  U8.nat_xor_or_sum a b

theorem land_128_div {a : Nat} (ha : a < 256) :
    Nat.land a 128 / 128 = a / 128 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h1 : (128 : Nat) = 2 ^ 7 := rfl
  have hland : Nat.land a (2 ^ 7) = a &&& 2 ^ 7 := rfl
  rw [h1, hland, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow,
      Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.testBit_and]
  rcases i with _ | i
  · have : Nat.testBit 128 7 = true := rfl
    simp [this]
  · have hlt : a < 2 ^ (7 + (i + 1)) := by
      calc a < 2 ^ 8 := ha
      _ ≤ 2 ^ (7 + (i + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
    simp [Nat.testBit_lt_two_pow hlt]

end Aiur.Library.U8Facts
