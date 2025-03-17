@[extern "c_u16_to_le_bytes"]
opaque UInt16.toLEBytes : UInt16 → ByteArray

@[extern "c_u32_to_le_bytes"]
opaque UInt32.toLEBytes : UInt32 → ByteArray

@[extern "c_u64_to_le_bytes"]
opaque UInt64.toLEBytes : UInt64 → ByteArray

@[extern "c_usize_to_le_bytes"]
opaque USize.toLEBytes : USize → ByteArray

private opaque GenericNonempty : NonemptyType

def UInt128 : Type := GenericNonempty.type

instance : Nonempty UInt128 := GenericNonempty.property

namespace UInt128

@[extern "c_u128_of_lo_hi"]
opaque ofLoHi : (lo : UInt64) → (hi : UInt64) → UInt128

def ofNat (n : Nat) (_ : n < 2^128 := by decide) : UInt128 :=
  let lo := n % UInt64.size |>.toUInt64
  let hi := n / UInt64.size |>.toUInt64
  ofLoHi lo hi

instance : OfNat UInt128 n where
  ofNat :=
    let pow := 2^128
    if h : n < pow then ofNat n h
    else ofNat (n % pow) (Nat.mod_lt n (by decide))

@[extern "c_u128_to_le_bytes"]
opaque toLEBytes : @& UInt128 → ByteArray

end UInt128
