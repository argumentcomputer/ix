import Ix.Unsigned

namespace Archon

inductive TowerField
  | b1 | b2 | b4 | b8 | b16 | b32 | b64 | b128

def TowerField.logDegree : TowerField → USize
  | .b1 => 0
  | .b2 => 1
  | .b4 => 2
  | .b8 => 3
  | .b16 => 4
  | .b32 => 5
  | .b64 => 6
  | .b128 => 7

instance : ToString TowerField where
  toString
    | .b1 => "b1"
    | .b2 => "b2"
    | .b4 => "b4"
    | .b8 => "b8"
    | .b16 => "b16"
    | .b32 => "b32"
    | .b64 => "b64"
    | .b128 => "b128"

@[extern "c_rs_add_u128_in_binary_field"]
opaque addUInt128InBinaryField : @& UInt128 → @& UInt128 → UInt128

@[extern "c_rs_mul_u128_in_binary_field"]
opaque mulUInt128InBinaryField : @& UInt128 → @& UInt128 → UInt128

@[extern "rs_mul_u64_in_binary_field"]
opaque mulUInt64InBinaryField : @& UInt64 → @& UInt64 → UInt64

@[extern "rs_pow_u64_in_binary_field"]
opaque powUInt64InBinaryField : @& UInt64 → @& UInt64 → UInt64

@[extern "rs_inv_u64_in_binary_field"]
opaque invUInt64InBinaryField : @& UInt64 → UInt64

end Archon
