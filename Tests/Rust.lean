import LSpec
import Ix.ByteArray

open LSpec

@[extern "add_u32s"]
opaque addUInt32s : UInt32 → UInt32 → UInt32

@[extern "byte_array_sum"]
opaque ByteArray.sum : @& ByteArray → UInt8

@[extern "byte_array_zeros"]
opaque ByteArray.zeros : USize → ByteArray

def main := lspecIO $
  test "addUInt32s works" (addUInt32s 5 3 = 8) $
  test "ByteArray.sum works" ((ByteArray.mk #[1, 8, 10]).sum = 19) $
  test "ByteArray.zeros works" (ByteArray.zeros 5 == .mk #[0, 0, 0, 0, 0])
