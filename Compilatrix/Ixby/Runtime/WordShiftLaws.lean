import Compilatrix.Ixby.Runtime.WordLaws

/-! Source word shifts reduce the count modulo the source width. The Ixby
primitives use a range check, so the emitted masks establish that range. -/

namespace Compilatrix.Ixby.Runtime.Words

theorem u8_lowWord (a : UInt8) : a.toNat.toUInt32 = a.toUInt32 := by
  apply UInt32.toNat_inj.mp
  simp only [Nat.toUInt32, UInt32.toNat_ofNat', UInt8.toNat_toUInt32]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.toNat_lt (by decide))

theorem u8_shiftLeft_nat (a b : UInt8) :
    ((a.toUInt32 <<< (b.toUInt32 &&& 7)) &&& 255).toNat = (a <<< b).toNat := by
  have count := masked_count b.toUInt32 8 (Or.inl rfl)
  simp only [Nat.toUInt32, Nat.reduceSub, UInt8.toNat_toUInt32] at count
  have countSmall : b.toNat % 8 < 32 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  rw [UInt32.toNat_and, UInt32.toNat_shiftLeft]
  change (a.toUInt32.toNat <<< ((b.toUInt32 &&& 7).toNat % 32) % 2 ^ 32) &&& (2 ^ 8 - 1) = _
  rw [show (b.toUInt32 &&& 7).toNat = b.toNat % 8 from count,
    Nat.mod_eq_of_lt countSmall, UInt8.toNat_toUInt32, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (by decide)]
  exact (UInt8.toNat_shiftLeft a b).symm

theorem u8_shiftRight_nat (a b : UInt8) :
    ((a.toUInt32 >>> (b.toUInt32 &&& 7)) &&& 255).toNat = (a >>> b).toNat := by
  have count := masked_count b.toUInt32 8 (Or.inl rfl)
  simp only [Nat.toUInt32, Nat.reduceSub, UInt8.toNat_toUInt32] at count
  have countSmall : b.toNat % 8 < 32 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  rw [UInt32.toNat_and, UInt32.toNat_shiftRight]
  change (a.toUInt32.toNat >>> ((b.toUInt32 &&& 7).toNat % 32)) &&& (2 ^ 8 - 1) = _
  rw [show (b.toUInt32 &&& 7).toNat = b.toNat % 8 from count,
    Nat.mod_eq_of_lt countSmall, UInt8.toNat_toUInt32, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) a.toNat_lt)]
  exact (UInt8.toNat_shiftRight a b).symm

theorem u32_shiftLeft_nat (a b : UInt32) :
    (a <<< (b &&& 31)).toNat = (a <<< b).toNat := by
  have count := masked_count b 32 (Or.inr rfl)
  simp only [Nat.toUInt32, Nat.reduceSub] at count
  simp only [UInt32.toNat_shiftLeft, show (b &&& 31).toNat = b.toNat % 32 from count, Nat.mod_mod]

theorem u32_shiftRight_nat (a b : UInt32) :
    (a >>> (b &&& 31)).toNat = (a >>> b).toNat := by
  have count := masked_count b 32 (Or.inr rfl)
  simp only [Nat.toUInt32, Nat.reduceSub] at count
  simp only [UInt32.toNat_shiftRight, show (b &&& 31).toNat = b.toNat % 32 from count, Nat.mod_mod]

end Compilatrix.Ixby.Runtime.Words
