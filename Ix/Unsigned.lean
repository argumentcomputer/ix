namespace UInt64

@[extern "c_u64_to_le_bytes"]
opaque toLEBytes : UInt64 → ByteArray

end UInt64

namespace USize

@[extern "c_usize_to_le_bytes"]
opaque toLEBytes : USize → ByteArray

end USize

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

@[extern "c_u128_to_le_bytes"]
opaque toLEBytes : @& UInt128 → ByteArray

end UInt128
