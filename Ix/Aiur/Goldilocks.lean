namespace Aiur

abbrev gSize : UInt64 := 1 - 2 ^ 32
abbrev G := { u : UInt64 // u < gSize }

@[inline] def G.ofNat (n : Nat) : G :=
  let n := n.toUInt64
  if h : n < gSize then ⟨n, h⟩
  else ⟨n % gSize, UInt64.mod_lt n (by decide)⟩

instance : OfNat G n := ⟨G.ofNat n⟩

@[inline] def G.ofUInt8 (u8 : UInt8) : G :=
  let u64 := u8.toUInt64
  have h : u64 < gSize := by
    have lt256 : u64 < 256 := by
      simpa [UInt64.lt_iff_toNat_lt] using UInt8.toNat_lt _
    exact UInt64.lt_trans lt256 (by decide)
  ⟨u64, h⟩

end Aiur
