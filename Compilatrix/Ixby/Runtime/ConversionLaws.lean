import Compilatrix.Ixby.Runtime.ConversionCode
import Compilatrix.Ixby.Runtime.Execution

namespace Compilatrix.Ixby.Runtime.Conversion

open Ix.Ixby Execution Representation ScalarFunction

@[simp] theorem validate_word32 (limits : Limits) (word : UInt32) :
    (Scalar.word32 word).validate limits = .ok () := rfl

@[simp] theorem validate_bool (limits : Limits) (value : Bool) :
    (Scalar.bool value).validate limits = .ok () := rfl

@[simp] theorem validate_zero (limits : Limits) :
    (Scalar.nat 0).validate limits = .ok () := rfl

theorem validate_nat_of_lt {limits : Limits} {n : Nat} (fits : n < 2 ^ limits.natBits) :
    (Scalar.nat n).validate limits = .ok () := by
  by_cases zero : n = 0
  · simp [Scalar.validate, zero]
  · have bound := (Nat.log2_lt zero).mpr fits
    simp [Scalar.validate, show ¬n.log2 ≥ limits.natBits by omega]

theorem validate_nat_of_bits {limits : Limits} {n bits : Nat}
    (fits : n < 2 ^ bits) (capacity : bits ≤ limits.natBits) :
    (Scalar.nat n).validate limits = .ok () :=
  validate_nat_of_lt (Nat.lt_of_lt_of_le fits
    (Nat.pow_le_pow_right (by decide : 0 < 2) capacity))

theorem validate_nat_mono {limits : Limits} {n m : Nat} (smaller : m ≤ n)
    (valid : (Scalar.nat n).validate limits = .ok ()) :
    (Scalar.nat m).validate limits = .ok () := by
  by_cases zero : n = 0
  · have : m = 0 := by omega
    simp [Scalar.validate, this]
  · have bound : n < 2 ^ limits.natBits := by
      apply (Nat.log2_lt zero).mp
      simp [Scalar.validate, zero] at valid
      omega
    exact validate_nat_of_lt (Nat.lt_of_le_of_lt smaller bound)

theorem word_shl_four (word : UInt32) : word <<< (4 : UInt32) = word * 16 := by
  apply UInt32.toNat_inj.mp
  simp [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq, UInt32.toNat_mul]

theorem word_shr_four (word : UInt32) : (word >>> (4 : UInt32)).toNat = word.toNat / 16 := by
  simp [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

theorem word_and_fifteen (word : UInt32) : (word &&& (15 : UInt32)).toNat = word.toNat % 16 := by
  rw [UInt32.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod word.toNat 4

end Compilatrix.Ixby.Runtime.Conversion
