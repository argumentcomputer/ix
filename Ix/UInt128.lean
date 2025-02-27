private opaque GenericNonempty : NonemptyType

def UInt128 : Type := GenericNonempty.type

instance : Nonempty UInt128 := GenericNonempty.property

namespace UInt128

@[extern "c_rs_u128_of_hi_lo"]
opaque ofHiLo : (hi : UInt64) → (lo : UInt64) → UInt128

def ofNat (n : Nat) (_ : n < 2^128 := by norm_cast) : UInt128 :=
  let hi := n / UInt64.size |>.toUInt64
  let lo := n % UInt64.size |>.toUInt64
  ofHiLo hi lo

@[extern "rs_u128_to_le_bytes"]
opaque toLEBytes : @& UInt128 → ByteArray

end UInt128
