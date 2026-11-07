import IxCC.Vendor.Ix.Aiur.Stages.Bytecode
import IxCC.Aiur.Wire.Primitives

namespace IxCC.Aiur.Wire

open _root_.Aiur.Bytecode
open IxCC.Ixon
open IxCC.IxIR

/-! All 34 pinned opcodes. Explicit tags preserve upstream constructor order;
all indices, sizes, flags, messages, and optional debug values are retained. -/

def opBytes : Op → ByteArray
  | .const v0 => Encoding.tag 0 ++ fieldBytes v0
  | .add v0 v1 => Encoding.tag 1 ++ Encoding.nat v0 ++ Encoding.nat v1
  | .sub v0 v1 => Encoding.tag 2 ++ Encoding.nat v0 ++ Encoding.nat v1
  | .mul v0 v1 => Encoding.tag 3 ++ Encoding.nat v0 ++ Encoding.nat v1
  | .eqZero v0 => Encoding.tag 4 ++ Encoding.nat v0
  | .call v0 v1 v2 v3 => Encoding.tag 5 ++ Encoding.nat v0 ++ natArrayBytes v1 ++ Encoding.nat v2 ++ Encoding.bool v3
  | .store v0 => Encoding.tag 6 ++ natArrayBytes v0
  | .load v0 v1 => Encoding.tag 7 ++ Encoding.nat v0 ++ Encoding.nat v1
  | .assertEq v0 v1 v2 => Encoding.tag 8 ++ natArrayBytes v0 ++ natArrayBytes v1 ++ (optionBytes Encoding.string) v2
  | .ioGetInfo v0 v1 => Encoding.tag 9 ++ Encoding.nat v0 ++ natArrayBytes v1
  | .ioSetInfo v0 v1 v2 v3 => Encoding.tag 10 ++ Encoding.nat v0 ++ natArrayBytes v1 ++ Encoding.nat v2 ++ Encoding.nat v3
  | .ioRead v0 v1 v2 => Encoding.tag 11 ++ Encoding.nat v0 ++ Encoding.nat v1 ++ Encoding.nat v2
  | .ioWrite v0 v1 => Encoding.tag 12 ++ Encoding.nat v0 ++ natArrayBytes v1
  | .u8BitDecomposition v0 => Encoding.tag 13 ++ Encoding.nat v0
  | .u8ShiftLeft v0 => Encoding.tag 14 ++ Encoding.nat v0
  | .u8ShiftRight v0 => Encoding.tag 15 ++ Encoding.nat v0
  | .u8Xor v0 v1 => Encoding.tag 16 ++ Encoding.nat v0 ++ Encoding.nat v1
  | .u8Add v0 v1 => Encoding.tag 17 ++ Encoding.nat v0 ++ Encoding.nat v1
  | .u8Mul v0 v1 => Encoding.tag 18 ++ Encoding.nat v0 ++ Encoding.nat v1
  | .u8Sub v0 v1 => Encoding.tag 19 ++ Encoding.nat v0 ++ Encoding.nat v1
  | .u8And v0 v1 => Encoding.tag 20 ++ Encoding.nat v0 ++ Encoding.nat v1
  | .u8Or v0 v1 => Encoding.tag 21 ++ Encoding.nat v0 ++ Encoding.nat v1
  | .u8LessThan v0 v1 => Encoding.tag 22 ++ Encoding.nat v0 ++ Encoding.nat v1
  | .u32LessThan v0 v1 => Encoding.tag 23 ++ Encoding.nat v0 ++ Encoding.nat v1
  | .u8XorSplit7 v0 v1 => Encoding.tag 24 ++ Encoding.nat v0 ++ Encoding.nat v1
  | .u8XorSplit4 v0 v1 => Encoding.tag 25 ++ Encoding.nat v0 ++ Encoding.nat v1
  | .debug v0 v1 => Encoding.tag 26 ++ Encoding.string v0 ++ (optionBytes natArrayBytes) v1
  | .u8RangeCheck v0 v1 => Encoding.tag 27 ++ Encoding.nat v0 ++ Encoding.nat v1
  | .unconstrainedBigUintDivMod v0 v1 => Encoding.tag 28 ++ Encoding.nat v0 ++ Encoding.nat v1
  | .unconstrainedGToBytes v0 => Encoding.tag 29 ++ Encoding.nat v0
  | .unconstrainedGInverse v0 => Encoding.tag 30 ++ Encoding.nat v0
  | .unconstrainedU32Add v0 v1 => Encoding.tag 31 ++ natArrayBytes v0 ++ natArrayBytes v1
  | .unconstrainedU32Add3 v0 v1 v2 => Encoding.tag 32 ++ natArrayBytes v0 ++ natArrayBytes v1 ++ natArrayBytes v2
  | .u32ToField v0 => Encoding.tag 33 ++ natArrayBytes v0

def opFits (limits : Bounded.Limits) : Op → Bool
  | .const _ => true
  | .add v0 v1 => Bounded.natFits limits v0 && Bounded.natFits limits v1
  | .sub v0 v1 => Bounded.natFits limits v0 && Bounded.natFits limits v1
  | .mul v0 v1 => Bounded.natFits limits v0 && Bounded.natFits limits v1
  | .eqZero v0 => Bounded.natFits limits v0
  | .call v0 v1 v2 _ => Bounded.natFits limits v0 && natArrayFits limits v1 && Bounded.natFits limits v2
  | .store v0 => natArrayFits limits v0
  | .load v0 v1 => Bounded.natFits limits v0 && Bounded.natFits limits v1
  | .assertEq v0 v1 v2 => natArrayFits limits v0 && natArrayFits limits v1 && optionFits (Bounded.stringFits limits) v2
  | .ioGetInfo v0 v1 => Bounded.natFits limits v0 && natArrayFits limits v1
  | .ioSetInfo v0 v1 v2 v3 => Bounded.natFits limits v0 && natArrayFits limits v1 && Bounded.natFits limits v2 && Bounded.natFits limits v3
  | .ioRead v0 v1 v2 => Bounded.natFits limits v0 && Bounded.natFits limits v1 && Bounded.natFits limits v2
  | .ioWrite v0 v1 => Bounded.natFits limits v0 && natArrayFits limits v1
  | .u8BitDecomposition v0 => Bounded.natFits limits v0
  | .u8ShiftLeft v0 => Bounded.natFits limits v0
  | .u8ShiftRight v0 => Bounded.natFits limits v0
  | .u8Xor v0 v1 => Bounded.natFits limits v0 && Bounded.natFits limits v1
  | .u8Add v0 v1 => Bounded.natFits limits v0 && Bounded.natFits limits v1
  | .u8Mul v0 v1 => Bounded.natFits limits v0 && Bounded.natFits limits v1
  | .u8Sub v0 v1 => Bounded.natFits limits v0 && Bounded.natFits limits v1
  | .u8And v0 v1 => Bounded.natFits limits v0 && Bounded.natFits limits v1
  | .u8Or v0 v1 => Bounded.natFits limits v0 && Bounded.natFits limits v1
  | .u8LessThan v0 v1 => Bounded.natFits limits v0 && Bounded.natFits limits v1
  | .u32LessThan v0 v1 => Bounded.natFits limits v0 && Bounded.natFits limits v1
  | .u8XorSplit7 v0 v1 => Bounded.natFits limits v0 && Bounded.natFits limits v1
  | .u8XorSplit4 v0 v1 => Bounded.natFits limits v0 && Bounded.natFits limits v1
  | .debug v0 v1 => Bounded.stringFits limits v0 && optionFits (natArrayFits limits) v1
  | .u8RangeCheck v0 v1 => Bounded.natFits limits v0 && Bounded.natFits limits v1
  | .unconstrainedBigUintDivMod v0 v1 => Bounded.natFits limits v0 && Bounded.natFits limits v1
  | .unconstrainedGToBytes v0 => Bounded.natFits limits v0
  | .unconstrainedGInverse v0 => Bounded.natFits limits v0
  | .unconstrainedU32Add v0 v1 => natArrayFits limits v0 && natArrayFits limits v1
  | .unconstrainedU32Add3 v0 v1 v2 => natArrayFits limits v0 && natArrayFits limits v1 && natArrayFits limits v2
  | .u32ToField v0 => natArrayFits limits v0

def getOpTag (limits : Bounded.Limits) : UInt8 → GetM Op
  | 0 => do
      let v0 ← getField
      return .const v0
  | 1 => do
      let v0 ← Bounded.getNat limits
      let v1 ← Bounded.getNat limits
      return .add v0 v1
  | 2 => do
      let v0 ← Bounded.getNat limits
      let v1 ← Bounded.getNat limits
      return .sub v0 v1
  | 3 => do
      let v0 ← Bounded.getNat limits
      let v1 ← Bounded.getNat limits
      return .mul v0 v1
  | 4 => do
      let v0 ← Bounded.getNat limits
      return .eqZero v0
  | 5 => do
      let v0 ← Bounded.getNat limits
      let v1 ← getNatArray limits
      let v2 ← Bounded.getNat limits
      let v3 ← Decode.getBool
      return .call v0 v1 v2 v3
  | 6 => do
      let v0 ← getNatArray limits
      return .store v0
  | 7 => do
      let v0 ← Bounded.getNat limits
      let v1 ← Bounded.getNat limits
      return .load v0 v1
  | 8 => do
      let v0 ← getNatArray limits
      let v1 ← getNatArray limits
      let v2 ← getOption (Bounded.getString limits)
      return .assertEq v0 v1 v2
  | 9 => do
      let v0 ← Bounded.getNat limits
      let v1 ← getNatArray limits
      return .ioGetInfo v0 v1
  | 10 => do
      let v0 ← Bounded.getNat limits
      let v1 ← getNatArray limits
      let v2 ← Bounded.getNat limits
      let v3 ← Bounded.getNat limits
      return .ioSetInfo v0 v1 v2 v3
  | 11 => do
      let v0 ← Bounded.getNat limits
      let v1 ← Bounded.getNat limits
      let v2 ← Bounded.getNat limits
      return .ioRead v0 v1 v2
  | 12 => do
      let v0 ← Bounded.getNat limits
      let v1 ← getNatArray limits
      return .ioWrite v0 v1
  | 13 => do
      let v0 ← Bounded.getNat limits
      return .u8BitDecomposition v0
  | 14 => do
      let v0 ← Bounded.getNat limits
      return .u8ShiftLeft v0
  | 15 => do
      let v0 ← Bounded.getNat limits
      return .u8ShiftRight v0
  | 16 => do
      let v0 ← Bounded.getNat limits
      let v1 ← Bounded.getNat limits
      return .u8Xor v0 v1
  | 17 => do
      let v0 ← Bounded.getNat limits
      let v1 ← Bounded.getNat limits
      return .u8Add v0 v1
  | 18 => do
      let v0 ← Bounded.getNat limits
      let v1 ← Bounded.getNat limits
      return .u8Mul v0 v1
  | 19 => do
      let v0 ← Bounded.getNat limits
      let v1 ← Bounded.getNat limits
      return .u8Sub v0 v1
  | 20 => do
      let v0 ← Bounded.getNat limits
      let v1 ← Bounded.getNat limits
      return .u8And v0 v1
  | 21 => do
      let v0 ← Bounded.getNat limits
      let v1 ← Bounded.getNat limits
      return .u8Or v0 v1
  | 22 => do
      let v0 ← Bounded.getNat limits
      let v1 ← Bounded.getNat limits
      return .u8LessThan v0 v1
  | 23 => do
      let v0 ← Bounded.getNat limits
      let v1 ← Bounded.getNat limits
      return .u32LessThan v0 v1
  | 24 => do
      let v0 ← Bounded.getNat limits
      let v1 ← Bounded.getNat limits
      return .u8XorSplit7 v0 v1
  | 25 => do
      let v0 ← Bounded.getNat limits
      let v1 ← Bounded.getNat limits
      return .u8XorSplit4 v0 v1
  | 26 => do
      let v0 ← Bounded.getString limits
      let v1 ← getOption (getNatArray limits)
      return .debug v0 v1
  | 27 => do
      let v0 ← Bounded.getNat limits
      let v1 ← Bounded.getNat limits
      return .u8RangeCheck v0 v1
  | 28 => do
      let v0 ← Bounded.getNat limits
      let v1 ← Bounded.getNat limits
      return .unconstrainedBigUintDivMod v0 v1
  | 29 => do
      let v0 ← Bounded.getNat limits
      return .unconstrainedGToBytes v0
  | 30 => do
      let v0 ← Bounded.getNat limits
      return .unconstrainedGInverse v0
  | 31 => do
      let v0 ← getNatArray limits
      let v1 ← getNatArray limits
      return .unconstrainedU32Add v0 v1
  | 32 => do
      let v0 ← getNatArray limits
      let v1 ← getNatArray limits
      let v2 ← getNatArray limits
      return .unconstrainedU32Add3 v0 v1 v2
  | 33 => do
      let v0 ← getNatArray limits
      return .u32ToField v0
  | tag => throw s!"Aiur opcode: invalid tag {tag}"

def getOp (limits : Bounded.Limits) : GetM Op := do
  getOpTag limits (← getU8)

end IxCC.Aiur.Wire
