import Ix.Unsigned

namespace Binius

abbrev BinaryField1b.towerLevel : UInt8 := 0

abbrev BinaryField8b.towerLevel : UInt8 := 3
abbrev BinaryField8b.generator : UInt8 := 45

abbrev BinaryField16b.towerLevel : UInt8 := 4
abbrev BinaryField16b.generator : UInt16 := 58078

abbrev BinaryField32b.towerLevel : UInt8 := 5
abbrev BinaryField32b.generator : UInt32 := 65150186

abbrev BinaryField64b.towerLevel : UInt8 := 6
abbrev BinaryField64b.generator : UInt64 := 508773776270040456

abbrev BinaryField128b.towerLevel : UInt8 := 7
abbrev BinaryField128b.generator : UInt128 := 61857528091874184034011775247790689018

inductive BinaryFieldValue
  | u8 : UInt8 → BinaryFieldValue
  | u16 : UInt16 → BinaryFieldValue
  | u32 : UInt32 → BinaryFieldValue
  | u64 : UInt64 → BinaryFieldValue
  | u128 : UInt128 → BinaryFieldValue

end Binius
