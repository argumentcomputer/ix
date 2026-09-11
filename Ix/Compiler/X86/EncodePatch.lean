import Ix.Compiler.X86.EncodeLength
import Ix.Compiler.X86.EncodeWord

/-! The actual rel32 patcher replaces exactly its four-byte field. Range
checks recover the signed displacement; no layout or linker premise is hidden. -/

namespace Ix.Compiler.X86.Encode

theorem list_set_after (before after : List α) (index : Nat) (value : α) :
    (before ++ after).set (before.length + index) value = before ++ after.set index value := by
  rw [List.set_append_right _ _ (by omega)]
  simp

theorem patchSigned32_splice (before after : ByteArray) (a b c d : UInt8) (value : Int) :
    patchSigned32 (before ++ bytes [a, b, c, d] ++ after) before.size value =
      .ok (before ++ signed32Bytes value ++ after) := by
  simp only [patchSigned32, ByteArray.size_append, bytes_size, List.length_cons, List.length_nil]
  rw [if_pos (by omega)]
  simp only [List.range_succ, List.range_zero, List.foldl_append, List.foldl_cons, List.foldl_nil,
    List.nil_append, Nat.add_zero]
  congr 1
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [ByteArray.set!, Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds, ByteArray.toList_data_append,
    bytes_list, List.append_assoc]
  change ((((before.data.toList ++ a :: b :: c :: d :: after.data.toList).set
      (before.data.toList.length + 0) ((signed32Bytes value).get! 0)).set
      (before.data.toList.length + 1) ((signed32Bytes value).get! 1)).set
      (before.data.toList.length + 2) ((signed32Bytes value).get! 2)).set
      (before.data.toList.length + 3) ((signed32Bytes value).get! 3) = _
  simp only [list_set_after, List.set_cons_zero, List.set_cons_succ]
  simp [signed32Bytes, imm32Bytes, littleEndian, List.range_succ, ByteArray.get!]

theorem patchSigned32_reject (input : ByteArray) (offset : Nat) (value : Int)
    (outside : input.size < offset + 4) :
    patchSigned32 input offset value = .error (.invalidPatch offset input.size) := by
  simp [patchSigned32, Nat.not_le.mpr outside]

theorem rel32_patch (opcode : ByteArray) (target : FixupTarget) (value : Int) :
    patchSigned32 (rel32 opcode target).bytes opcode.size value = .ok (opcode ++ signed32Bytes value) := by
  simpa [rel32] using patchSigned32_splice opcode ByteArray.empty 0 0 0 0 value

theorem signed32_decode (value : Int) (rest : List UInt8) :
    Decode.readLE 4 ((signed32Bytes value).data.toList ++ rest) =
      some ((Int32.ofInt value).toUInt32.toUInt64, rest) := read_imm32 _ rest

theorem signed32_checked (value : Int) (fits : fitsSigned32 value = true) :
    (signExtend32 (Int32.ofInt value).toUInt32).toBitVec.toInt = value := by
  rw [signExtend32_ofInt _ fits]
  simp only [fitsSigned32, decide_eq_true_eq] at fits
  exact BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)

end Ix.Compiler.X86.Encode
