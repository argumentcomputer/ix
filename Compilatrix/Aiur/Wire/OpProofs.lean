import Compilatrix.Aiur.Wire.Op
import Compilatrix.Aiur.Wire.PrimitiveProofs

namespace Compilatrix.Aiur.Wire

open _root_.Aiur.Bytecode
open Compilatrix.Ixon
open Compilatrix.IxIR

theorem getOp_spec (limits : Bounded.Limits) : ∀ op : Op,
    opFits limits op = true → GetSpec (getOp limits) (opBytes op) op
  | .const v0, admitted => by
      have payload := Decode.getSpecMap
        (getField_spec v0)
        Op.const
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 0) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .add v0 v1, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : Bounded.natFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap2
        (Bounded.getNat_spec limits v0 h0)
        (Bounded.getNat_spec limits v1 h1)
        Op.add
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 1) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .sub v0 v1, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : Bounded.natFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap2
        (Bounded.getNat_spec limits v0 h0)
        (Bounded.getNat_spec limits v1 h1)
        Op.sub
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 2) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .mul v0 v1, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : Bounded.natFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap2
        (Bounded.getNat_spec limits v0 h0)
        (Bounded.getNat_spec limits v1 h1)
        Op.mul
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 3) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .eqZero v0, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits]
      have payload := Decode.getSpecMap
        (Bounded.getNat_spec limits v0 h0)
        Op.eqZero
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 4) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .call v0 v1 v2 v3, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : natArrayFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h2 : Bounded.natFits limits v2 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap4
        (Bounded.getNat_spec limits v0 h0)
        (getNatArray_spec limits v1 h1)
        (Bounded.getNat_spec limits v2 h2)
        (Decode.getBool_spec v3)
        Op.call
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 5) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .store v0, admitted => by
      have h0 : natArrayFits limits v0 = true := by
        simp_all only [opFits]
      have payload := Decode.getSpecMap
        (getNatArray_spec limits v0 h0)
        Op.store
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 6) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .load v0 v1, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : Bounded.natFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap2
        (Bounded.getNat_spec limits v0 h0)
        (Bounded.getNat_spec limits v1 h1)
        Op.load
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 7) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .assertEq v0 v1 v2, admitted => by
      have h0 : natArrayFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : natArrayFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h2 : optionFits (Bounded.stringFits limits) v2 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap3
        (getNatArray_spec limits v0 h0)
        (getNatArray_spec limits v1 h1)
        (getOption_spec (Bounded.getString limits) Encoding.string (Bounded.stringFits limits) (Bounded.getString_spec limits) v2 h2)
        Op.assertEq
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 8) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .ioGetInfo v0 v1, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : natArrayFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap2
        (Bounded.getNat_spec limits v0 h0)
        (getNatArray_spec limits v1 h1)
        Op.ioGetInfo
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 9) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .ioSetInfo v0 v1 v2 v3, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : natArrayFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h2 : Bounded.natFits limits v2 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h3 : Bounded.natFits limits v3 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap4
        (Bounded.getNat_spec limits v0 h0)
        (getNatArray_spec limits v1 h1)
        (Bounded.getNat_spec limits v2 h2)
        (Bounded.getNat_spec limits v3 h3)
        Op.ioSetInfo
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 10) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .ioRead v0 v1 v2, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : Bounded.natFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h2 : Bounded.natFits limits v2 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap3
        (Bounded.getNat_spec limits v0 h0)
        (Bounded.getNat_spec limits v1 h1)
        (Bounded.getNat_spec limits v2 h2)
        Op.ioRead
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 11) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .ioWrite v0 v1, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : natArrayFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap2
        (Bounded.getNat_spec limits v0 h0)
        (getNatArray_spec limits v1 h1)
        Op.ioWrite
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 12) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .u8BitDecomposition v0, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits]
      have payload := Decode.getSpecMap
        (Bounded.getNat_spec limits v0 h0)
        Op.u8BitDecomposition
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 13) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .u8ShiftLeft v0, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits]
      have payload := Decode.getSpecMap
        (Bounded.getNat_spec limits v0 h0)
        Op.u8ShiftLeft
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 14) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .u8ShiftRight v0, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits]
      have payload := Decode.getSpecMap
        (Bounded.getNat_spec limits v0 h0)
        Op.u8ShiftRight
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 15) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .u8Xor v0 v1, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : Bounded.natFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap2
        (Bounded.getNat_spec limits v0 h0)
        (Bounded.getNat_spec limits v1 h1)
        Op.u8Xor
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 16) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .u8Add v0 v1, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : Bounded.natFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap2
        (Bounded.getNat_spec limits v0 h0)
        (Bounded.getNat_spec limits v1 h1)
        Op.u8Add
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 17) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .u8Mul v0 v1, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : Bounded.natFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap2
        (Bounded.getNat_spec limits v0 h0)
        (Bounded.getNat_spec limits v1 h1)
        Op.u8Mul
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 18) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .u8Sub v0 v1, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : Bounded.natFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap2
        (Bounded.getNat_spec limits v0 h0)
        (Bounded.getNat_spec limits v1 h1)
        Op.u8Sub
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 19) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .u8And v0 v1, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : Bounded.natFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap2
        (Bounded.getNat_spec limits v0 h0)
        (Bounded.getNat_spec limits v1 h1)
        Op.u8And
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 20) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .u8Or v0 v1, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : Bounded.natFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap2
        (Bounded.getNat_spec limits v0 h0)
        (Bounded.getNat_spec limits v1 h1)
        Op.u8Or
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 21) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .u8LessThan v0 v1, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : Bounded.natFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap2
        (Bounded.getNat_spec limits v0 h0)
        (Bounded.getNat_spec limits v1 h1)
        Op.u8LessThan
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 22) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .u32LessThan v0 v1, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : Bounded.natFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap2
        (Bounded.getNat_spec limits v0 h0)
        (Bounded.getNat_spec limits v1 h1)
        Op.u32LessThan
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 23) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .u8XorSplit7 v0 v1, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : Bounded.natFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap2
        (Bounded.getNat_spec limits v0 h0)
        (Bounded.getNat_spec limits v1 h1)
        Op.u8XorSplit7
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 24) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .u8XorSplit4 v0 v1, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : Bounded.natFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap2
        (Bounded.getNat_spec limits v0 h0)
        (Bounded.getNat_spec limits v1 h1)
        Op.u8XorSplit4
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 25) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .debug v0 v1, admitted => by
      have h0 : Bounded.stringFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : optionFits (natArrayFits limits) v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap2
        (Bounded.getString_spec limits v0 h0)
        (getOption_spec (getNatArray limits) natArrayBytes (natArrayFits limits) (getNatArray_spec limits) v1 h1)
        Op.debug
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 26) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .u8RangeCheck v0 v1, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : Bounded.natFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap2
        (Bounded.getNat_spec limits v0 h0)
        (Bounded.getNat_spec limits v1 h1)
        Op.u8RangeCheck
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 27) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .unconstrainedBigUintDivMod v0 v1, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : Bounded.natFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap2
        (Bounded.getNat_spec limits v0 h0)
        (Bounded.getNat_spec limits v1 h1)
        Op.unconstrainedBigUintDivMod
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 28) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .unconstrainedGToBytes v0, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits]
      have payload := Decode.getSpecMap
        (Bounded.getNat_spec limits v0 h0)
        Op.unconstrainedGToBytes
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 29) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .unconstrainedGInverse v0, admitted => by
      have h0 : Bounded.natFits limits v0 = true := by
        simp_all only [opFits]
      have payload := Decode.getSpecMap
        (Bounded.getNat_spec limits v0 h0)
        Op.unconstrainedGInverse
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 30) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .unconstrainedU32Add v0 v1, admitted => by
      have h0 : natArrayFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : natArrayFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap2
        (getNatArray_spec limits v0 h0)
        (getNatArray_spec limits v1 h1)
        Op.unconstrainedU32Add
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 31) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .unconstrainedU32Add3 v0 v1 v2, admitted => by
      have h0 : natArrayFits limits v0 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h1 : natArrayFits limits v1 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have h2 : natArrayFits limits v2 = true := by
        simp_all only [opFits, Bool.and_eq_true]
      have payload := Decode.getSpecMap3
        (getNatArray_spec limits v0 h0)
        (getNatArray_spec limits v1 h1)
        (getNatArray_spec limits v2 h2)
        Op.unconstrainedU32Add3
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 32) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total
  | .u32ToField v0, admitted => by
      have h0 : natArrayFits limits v0 = true := by
        simp_all only [opFits]
      have payload := Decode.getSpecMap
        (getNatArray_spec limits v0 h0)
        Op.u32ToField
      have total := GetSpec.bind (next := getOpTag limits)
        (Decode.getU8_tag_spec 33) payload
      simpa only [getOp, opBytes, ByteArray.append_assoc, ByteArray.append_empty] using total

end Compilatrix.Aiur.Wire
