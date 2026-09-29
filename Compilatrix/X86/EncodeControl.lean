import Compilatrix.X86.EncodeForms
import Compilatrix.X86.EncodeWord
import Compilatrix.X86.ByteEval

/-! Control rows and typed instructions as instances of the class laws:
`call`/`jmp`/`jcc` rel32 and `ret` bytes, and the decoded operations of
typed instructions and terminators. -/

namespace Compilatrix.X86.Encode

theorem bytes_append (left right : List UInt8) : bytes left ++ bytes right = bytes (left ++ right) := by
  apply ByteArray.ext
  simp [bytes]

theorem leNat_mod (count value : Nat) : leNat count (value % 256 ^ count) = leNat count value := by
  induction count generalizing value with
  | zero => rfl
  | succ count ih =>
      simp only [leNat, List.cons.injEq]
      constructor
      · apply UInt8.toNat_inj.mp
        simp only [UInt8.toNat_ofNat']
        rw [Nat.pow_succ, Nat.mod_mul_left_mod]
      · rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self, ih]

theorem le_signExtend32 (value : Imm32) : le 4 (signExtend32 value) = le 4 value.toUInt64 := by
  unfold le
  rw [← leNat_mod 4 (signExtend32 value).toNat, show (256 : Nat) ^ 4 = 2 ^ 32 from rfl,
    signExtend32_low]
  simp

theorem control_rows : Op.callRel32 ∈ Op.rows ∧ Op.jmpRel32 ∈ Op.rows ∧ Op.retZO ∈ Op.rows := by decide

theorem jcc_row (condition : Condition) : Op.jccRel32 condition ∈ Op.rows := by
  cases condition <;> decide

theorem rel_ok (o : Op) (slots : (desc o).slots = [Table.relSlot]) (value : Imm32) :
    o.argsOk [.imm (signExtend32 value)] = true := by
  simp [Op.argsOk, slots, slotsAccept, Table.relSlot, ArgKind.accepts, norm_signExtend32]

theorem rel_bytes (o : Op) (plain : (desc o).enc = { opcode := (desc o).enc.opcode, imm := .imm32 })
    (form : o.form = .D32) (value : Imm32) :
    encodeList o [.imm (signExtend32 value)] = (desc o).enc.opcode :: le 4 value.toUInt64 := by
  unfold encodeList
  rw [plain, form]
  simp [fields, rexPrefix, rexR, tail, byteForce, opcodeBytes, immBytes, le_signExtend32, ImmKind.bytes]

theorem call_decode (displacement : Imm32) (rest : List UInt8) :
    Decode.one ((byte 0xe8 ++ imm32Bytes displacement).data.toList ++ rest) = some (.call displacement, rest) := by
  have bytesEq : (byte 0xe8 ++ imm32Bytes displacement).data.toList =
      encodeList Op.callRel32 [.imm (signExtend32 displacement)] := by
    rw [rel_bytes _ rfl rfl]
    simp [byte, imm32Bytes, littleEndian, bytes_append]
    rfl
  rw [bytesEq]
  exact row_decode _ _ control_rows.1 (rel_ok _ rfl _) rest

theorem jump_decode (displacement : Imm32) (rest : List UInt8) :
    Decode.one ((byte 0xe9 ++ imm32Bytes displacement).data.toList ++ rest) = some (.jump displacement, rest) := by
  have bytesEq : (byte 0xe9 ++ imm32Bytes displacement).data.toList =
      encodeList Op.jmpRel32 [.imm (signExtend32 displacement)] := by
    rw [rel_bytes _ rfl rfl]
    simp [byte, imm32Bytes, littleEndian, bytes_append]
    rfl
  rw [bytesEq]
  exact row_decode _ _ control_rows.2.1 (rel_ok _ rfl _) rest

theorem nearOpcode_eq (condition : Condition) : nearOpcode condition = 0x80 + condition.code := rfl

theorem branch_bytes (condition : Condition) (displacement : Imm32) :
    encodeList (Op.jccRel32 condition) [.imm (signExtend32 displacement)] =
      0x0f :: nearOpcode condition :: le 4 displacement.toUInt64 := by
  simp [encodeList, fields, Op.jccRel32, desc, Table.jccDesc, rexPrefix, rexR, tail, byteForce, opcodeBytes,
    immBytes, le_signExtend32, ImmKind.bytes, nearOpcode]

theorem branch_decode (condition : Condition) (displacement : Imm32) (rest : List UInt8) :
    Decode.one ((bytes [0x0f, nearOpcode condition] ++ imm32Bytes displacement).data.toList ++ rest) =
      some (.branch condition displacement, rest) := by
  have bytesEq : (bytes [0x0f, nearOpcode condition] ++ imm32Bytes displacement).data.toList =
      encodeList (Op.jccRel32 condition) [.imm (signExtend32 displacement)] := by
    rw [branch_bytes]
    simp [imm32Bytes, littleEndian, bytes_append]
  rw [bytesEq]
  exact row_decode _ _ (jcc_row condition) (rel_ok _ rfl _) rest

theorem ret_decode (rest : List UInt8) :
    Decode.one ((byte 0xc3).data.toList ++ rest) = some (.ret, rest) := by
  have bytesEq : (byte 0xc3).data.toList = encodeList Op.retZO [] := by
    simp [encodeList, fields, Op.retZO, desc, Table.retDesc, rexPrefix, rexR, tail, byteForce, opcodeBytes,
      immBytes, byte]
  rw [bytesEq]
  exact row_decode _ _ control_rows.2.2 (by decide) rest

/-! ## Typed instructions -/

/-- The operation the decoder recovers from a typed instruction's bytes;
calls carry the encoder's zero rel32 placeholder. -/
def instructionOperation : Instr → Decode.Operation
  | .op o args => .op o args
  | .call _ | .callRuntime _ => .call 0

theorem wellFormed_op {o : Op} {args : List Arg} (wf : (Instr.op o args).wellFormed = true) :
    o ∈ Op.rows ∧ o.linear = true ∧ o.argsOk args = true := by
  simp only [Instr.wellFormed, Bool.and_eq_true, List.contains_iff_mem] at wf
  exact ⟨wf.1.1, wf.1.2, wf.2⟩

theorem rel32_bytes (o : Op) (target : FixupTarget) : (rel32 o target).bytes = encodeOp o [.imm 0] := rfl

@[simp] theorem signExtend32_zero : signExtend32 0 = 0 := rfl

theorem call_placeholder (rest : List UInt8) :
    Decode.one (encodeList Op.callRel32 [.imm 0] ++ rest) = some (.call 0, rest) :=
  row_decode _ _ control_rows.1 (by decide) rest

theorem jump_placeholder (rest : List UInt8) :
    Decode.one (encodeList Op.jmpRel32 [.imm 0] ++ rest) = some (.jump 0, rest) :=
  row_decode _ _ control_rows.2.1 (by decide) rest

theorem branch_placeholder (condition : Condition) (rest : List UInt8) :
    Decode.one (encodeList (Op.jccRel32 condition) [.imm 0] ++ rest) = some (.branch condition 0, rest) :=
  row_decode _ _ (jcc_row condition) (by cases condition <;> decide) rest

theorem ret_row (rest : List UInt8) :
    Decode.one (encodeList Op.retZO [] ++ rest) = some (.ret, rest) :=
  row_decode _ _ control_rows.2.2 (by decide) rest

theorem instruction_decode (instruction : Instr) (wf : instruction.wellFormed = true) (rest : List UInt8) :
    Decode.one ((encodeInstr instruction).bytes.data.toList ++ rest) =
      some (instructionOperation instruction, rest) := by
  cases instruction with
  | op o args =>
      obtain ⟨row, _, ok⟩ := wellFormed_op wf
      exact encodeOp_decode o args row ok rest
  | call target | callRuntime intrinsic =>
      simpa [encodeInstr, rel32_bytes, encodeOp, instructionOperation] using call_placeholder rest

/-- The row of a comparison is listed and its operands have the row's kinds. -/
theorem Compare.row_ok (comparison : Compare) :
    comparison.row.1 ∈ Op.rows ∧ comparison.row.1.argsOk comparison.row.2 = true := by
  cases comparison with
  | mk width left right =>
    cases right with
    | reg right =>
        cases width <;> refine ⟨by simp only [Compare.row]; decide, ?_⟩ <;>
          simp [Compare.row, Op.argsOk, desc, Table.arithDesc, Table.cmpArith, Table.rmSlot, Table.regSlot,
            slotsAccept, ArgKind.accepts]
    | imm value =>
        cases width <;> refine ⟨by simp only [Compare.row, aluImmRow]; decide, ?_⟩ <;>
          simp [Compare.row, aluImmRow, Op.argsOk, desc, Table.arithDesc, Table.cmpArith, Table.rmSlot,
            Table.immSlot, Table.fullImm, Table.ImmKind.argKind, slotsAccept, ArgKind.accepts, norm_idem]

def terminatorOperations : Terminator → List Decode.Operation
  | .jump _ | .tailCall _ => [.jump 0]
  | .branch comparison condition _ _ =>
      [.op comparison.row.1 comparison.row.2, .branch condition 0, .jump 0]
  | .ret => [.ret]

theorem encodeCompare_decode (comparison : Compare) (rest : List UInt8) :
    Decode.one ((encodeCompare comparison).data.toList ++ rest) =
      some (.op comparison.row.1 comparison.row.2, rest) :=
  encodeOp_decode _ _ (Compare.row_ok comparison).1 (Compare.row_ok comparison).2 rest

theorem compare_list_decode (comparison : Compare) (rest : List UInt8) :
    Decode.one (encodeList comparison.row.1 comparison.row.2 ++ rest) =
      some (.op comparison.row.1 comparison.row.2, rest) :=
  row_decode _ _ (Compare.row_ok comparison).1 (Compare.row_ok comparison).2 rest

theorem terminator_decode (terminator : Terminator) (rest : List UInt8) :
    Decode.sequence (terminatorOperations terminator).length
      ((encodeTerminator terminator).bytes.data.toList ++ rest) =
        some (terminatorOperations terminator, rest) := by
  cases terminator with
  | jump target | tailCall target =>
      simp [terminatorOperations, encodeTerminator, rel32_bytes, encodeOp, Decode.sequence, jump_placeholder]
  | ret =>
      simp [terminatorOperations, encodeTerminator, Chunk.raw, encodeOp, Decode.sequence, ret_row]
  | branch comparison condition yes no =>
      simp [terminatorOperations, encodeTerminator, Chunk.append, Chunk.raw, rel32_bytes, encodeOp,
        encodeCompare, Decode.sequence, compare_list_decode, branch_placeholder, jump_placeholder]

end Compilatrix.X86.Encode
