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

abbrev size := 2^128

@[extern "c_u128_of_lo_hi"]
opaque ofLoHi : (lo : UInt64) → (hi : UInt64) → UInt128

instance : Inhabited UInt128 where
  default := ofLoHi 0 0

def ofNatCore (n : Nat) (_ : n < size := by decide) : UInt128 :=
  let lo := n % UInt64.size |>.toUInt64
  let hi := n / UInt64.size |>.toUInt64
  ofLoHi lo hi

def ofNatWrap (n : Nat) : UInt128 :=
  if h : n < size then ofNatCore n h
  else ofNatCore (n % size) (Nat.mod_lt n (by decide))

instance : OfNat UInt128 n := ⟨ofNatWrap n⟩

@[extern "c_u128_to_lo_hi"]
opaque toLoHi : @& UInt128 → UInt64 × UInt64

@[extern "c_rs_exterior_mul_u64"]
opaque exteriorMul : @& UInt64 → @& UInt64 → UInt128

def toNat (u128 : @& UInt128) : Nat :=
  let (lo, hi) := u128.toLoHi
  lo.toNat + (hi.toNat * UInt64.size)

instance : Repr UInt128 where
  reprPrec x prec := reprPrec x.toNat prec

instance : ToString UInt128 where
  toString x := toString x.toNat

@[extern "c_u128_cmp"]
def cmpCore (a : @& UInt128) (b : @& UInt128) : Ordering :=
  compare a.toNat b.toNat

instance : Ord UInt128 where
  compare := cmpCore

instance : LT UInt128 where
  lt a b := compare a b = .lt

@[extern "c_u128_to_le_bytes"]
opaque toLEBytes : @& UInt128 → ByteArray

end UInt128
