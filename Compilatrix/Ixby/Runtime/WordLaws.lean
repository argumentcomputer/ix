import Compilatrix.Ixby.Runtime.ConversionLaws

/-! The Nat and cached-word calculations agree after modular reduction.
In particular, the subtraction cache is justified before it is re-observed. -/

namespace Compilatrix.Ixby.Runtime.Words

open Ix.Ixby Representation Conversion

abbrev cachedValue (layout : NumberLayout) (n : Nat) : Value :=
  .ctor layout.cached #[.scalar (.nat n), .scalar (.word32 n.toUInt32)]

theorem lowWord_mod (n bits : Nat) (width : 32 ≤ bits) :
    n.toUInt32 = (n % 2 ^ bits).toUInt32 := by
  apply UInt32.toNat_inj.mp
  simp only [Nat.toUInt32, UInt32.toNat_ofNat']
  exact (Nat.mod_mod_of_dvd n (Nat.pow_dvd_pow 2 width)).symm

theorem lowWord_mask8 (n : Nat) :
    n.toUInt32 &&& (255 : UInt32) = (n % 256).toUInt32 := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_and, Nat.toUInt32, UInt32.toNat_ofNat']
  change (n % 2 ^ 32) &&& (2 ^ 8 - 1) = n % 2 ^ 8 % 2 ^ 32
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by decide),
    Nat.mod_mod_of_dvd' (by decide)]

theorem lowWord_subtract (a b bits : Nat) (width : 32 ≤ bits) (bounded : b < 2 ^ bits) :
    a.toUInt32 - b.toUInt32 = (a + 2 ^ bits - b).toUInt32 := by
  have zero : UInt32.ofNat (2 ^ bits) = 0 := by
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_ofNat']
    exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 width)
  simp only [Nat.toUInt32, UInt32.ofNat_sub (show b ≤ a + 2 ^ bits by omega),
    UInt32.ofNat_add, zero, UInt32.add_zero]

theorem subtract_nat (a b modulus : Nat) (bounded : b < modulus) :
    a + modulus - b = modulus - b + a := by omega

theorem masked_count (word : UInt32) (bits : Nat) (width : bits = 8 ∨ bits = 32) :
    (word &&& (bits - 1).toUInt32).toNat = word.toNat % bits := by
  rcases width with rfl | rfl
  · exact Nat.and_two_pow_sub_one_eq_mod word.toNat 3
  · exact Nat.and_two_pow_sub_one_eq_mod word.toNat 5

theorem masked_count_lt (word : UInt32) (bits : Nat) (width : bits = 8 ∨ bits = 32) :
    word &&& (bits - 1).toUInt32 < (32 : UInt32) := by
  rw [UInt32.lt_iff_toNat_lt, masked_count word bits width]
  have positive : 0 < bits := by rcases width with rfl | rfl <;> decide
  have bound := Nat.mod_lt word.toNat positive
  rcases width with rfl | rfl <;> change _ < 32 <;> omega

end Compilatrix.Ixby.Runtime.Words
