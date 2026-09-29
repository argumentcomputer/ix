import Compilatrix.X86.EncodeControl

/-! Instruction lengths and exact decoding at a supplied byte boundary. -/

namespace Compilatrix.X86.Encode

@[simp] theorem littleEndian_size (count : Nat) (value : Word) : (littleEndian count value).size = count := by
  simp [littleEndian]

@[simp] theorem imm32Bytes_size (value : Imm32) : (imm32Bytes value).size = 4 := by simp [imm32Bytes]

theorem dispBytes_length (mode : Nat) (displacement : Imm32) : (dispBytes mode displacement).length ≤ 4 := by
  unfold dispBytes
  split
  · simp
  · split <;> simp

theorem memoryTail_length (regField : Nat) (address : MemAddr) : (memoryTail regField address).bytes.length ≤ 6 := by
  unfold memoryTail
  split
  · simp
  · rename_i base _
    have disp := dispBytes_length (dispMode (registerLow (gprCode base)) address.displacement) address.displacement
    dsimp only
    split <;> simp <;> omega

theorem tail_length (enc : EncDesc) (f : Fields) :
    (tail enc f).bytes.length ≤ if enc.modrm == .none then 0 else 6 := by
  unfold tail
  cases hmodrm : enc.modrm with
  | none => simp
  | reg | digit _ =>
      simp only [reduceCtorEq, beq_iff_eq, ite_false]
      split
      · rename_i rm _
        cases rm with
        | reg register => simp [rmTail]
        | mem address => exact memoryTail_length _ address
        | imm value => simp [rmTail]
      · simp

theorem immBytes_length (kind : ImmKind) (value : Option Word) : (immBytes kind value).length ≤ kind.bytes := by
  cases value <;> simp [immBytes]

theorem rexPrefix_length (enc : EncDesc) (f : Fields) : (rexPrefix enc f).length ≤ 1 := by
  unfold rexPrefix
  dsimp only
  split <;> simp

theorem encodeList_length_le (o : Op) (args : List Arg) : (encodeList o args).length ≤ Table.maxLength o := by
  have tailBound := tail_length (desc o).enc (fields o.form args)
  have immBound := immBytes_length (desc o).enc.imm (fields o.form args).imm
  have rexBound := rexPrefix_length (desc o).enc (fields o.form args)
  unfold encodeList Table.maxLength
  simp only [List.length_append, opcodeBytes, List.length_cons, List.length_nil]
  split <;> split <;> simp_all <;> omega

theorem encodeList_length_pos (o : Op) (args : List Arg) : 0 < (encodeList o args).length := by
  unfold encodeList
  simp [opcodeBytes]
  omega

theorem encodeList_bounded {o : Op} (row : o ∈ Op.rows) (args : List Arg) : (encodeList o args).length ≤ 15 := by
  have bound := List.all_eq_true.mp table_bounded o row
  simp only [decide_eq_true_eq] at bound
  exact Nat.le_trans (encodeList_length_le o args) bound

theorem instruction_size_pos (instruction : Instr) : 0 < (encodeInstr instruction).bytes.size := by
  cases instruction <;> simp [encodeInstr, Chunk.raw, rel32_bytes, encodeOp, encodeList_length_pos]

theorem instruction_size (instruction : Instr) (wf : instruction.wellFormed = true) :
    0 < (encodeInstr instruction).bytes.size ∧ (encodeInstr instruction).bytes.size ≤ 15 := by
  refine ⟨instruction_size_pos instruction, ?_⟩
  cases instruction with
  | op o args =>
      simpa [encodeInstr, Chunk.raw, encodeOp] using encodeList_bounded (wellFormed_op wf).1 args
  | call target | callRuntime intrinsic =>
      simpa [encodeInstr, rel32_bytes, encodeOp] using encodeList_bounded control_rows.1 [.imm 0]

theorem compare_size (comparison : Compare) :
    0 < (encodeCompare comparison).size ∧ (encodeCompare comparison).size ≤ 15 := by
  simp only [encodeCompare, encodeOp, bytes_size]
  exact ⟨encodeList_length_pos _ _, encodeList_bounded (Compare.row_ok comparison).1 _⟩

/-- A local boundary theorem: arbitrary prefix and suffix bytes are allowed.
Complete stream boundary discovery and layout correspondence belong to E2. -/
theorem decodeAt_of_one (encoded before after : ByteArray) (operation : Decode.Operation)
    (decoded : Decode.one (encoded.data.toList ++ after.data.toList) =
      some (operation, after.data.toList))
    (positive : 0 < encoded.size) (short : encoded.size ≤ 15) :
    Decode.decodeAt (before ++ encoded ++ after) before.size = some ⟨operation, encoded.size⟩ := by
  simp only [← ByteArray.size_data] at positive short
  simp [Decode.decodeAt, ← ByteArray.size_data, decoded]
  omega

theorem instruction_decodeAt (instruction : Instr) (wf : instruction.wellFormed = true)
    (before after : ByteArray) :
    Decode.decodeAt (before ++ (encodeInstr instruction).bytes ++ after) before.size =
      some ⟨instructionOperation instruction, (encodeInstr instruction).bytes.size⟩ :=
  decodeAt_of_one _ before after _ (instruction_decode instruction wf after.data.toList)
    (instruction_size instruction wf).1 (instruction_size instruction wf).2

end Compilatrix.X86.Encode
