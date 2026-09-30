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
calls carry the encoder's zero rel32 placeholder. A fused pair's first
operation is its producer. -/
def instructionOperation : Instr → Decode.Operation
  | .op o args => .op o args
  | .fused producer pargs _ _ => .op producer pargs
  | .unwind source => .op unwindRow [.reg .rsp, .mem source]
  | .call _ | .callRuntime _ => .call 0

/-- Every operation the decoder recovers from a typed instruction's bytes:
two for a fused pair, one otherwise. -/
def instructionOperations : Instr → List Decode.Operation
  | .fused producer pargs consumer cargs => [.op producer pargs, .op consumer cargs]
  | instruction => [instructionOperation instruction]

/-- Instructions the encoder emits as one decoded operation: all but fused
pairs. -/
def _root_.Compilatrix.X86.Instr.single : Instr → Bool
  | .fused .. => false
  | _ => true

theorem wellFormed_op {o : Op} {args : List Arg} (wf : (Instr.op o args).wellFormed = true) :
    o ∈ Op.rows ∧ o.linear = true ∧ o.argsOk args = true := by
  simp only [Instr.wellFormed, Bool.and_eq_true, List.contains_iff_mem] at wf
  exact ⟨wf.1.1, wf.1.2, wf.2⟩

/-- A well-formed fused pair: a listed linear producer that reads no flags
and writes only flags, a listed consumer, operands of their slot kinds, and
the producer setting every flag the consumer reads. -/
theorem wellFormed_fused {producer consumer : Op} {pargs cargs : List Arg}
    (wf : (Instr.fused producer pargs consumer cargs).wellFormed = true) :
    producer ∈ Op.rows ∧ producer.linear = true ∧ (desc producer).flagsIn = [] ∧ producer.flagsOnly = true ∧
      producer.argsOk pargs = true ∧ consumer ∈ Op.rows ∧ consumer.consumer = true ∧
      consumer.argsOk cargs = true ∧ FusedOk producer consumer = true := by
  simp only [Instr.wellFormed, Bool.and_eq_true, List.contains_iff_mem, List.isEmpty_iff] at wf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨row, linear⟩, free⟩, only⟩, pok⟩, crow⟩, consumes⟩, cok⟩, fused⟩ := wf
  exact ⟨row, linear, free, only, pok, crow, consumes, cok, fused⟩

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

theorem instruction_decode (instruction : Instr) (wf : instruction.wellFormed = true)
    (single : instruction.single = true) (rest : List UInt8) :
    Decode.one ((encodeInstr instruction).bytes.data.toList ++ rest) =
      some (instructionOperation instruction, rest) := by
  cases instruction with
  | op o args =>
      obtain ⟨row, _, ok⟩ := wellFormed_op wf
      exact encodeOp_decode o args row ok rest
  | fused => simp [Instr.single] at single
  | unwind source =>
      exact encodeOp_decode unwindRow _ (by decide) (by simpa [Instr.wellFormed] using wf) rest
  | call target | callRuntime intrinsic =>
      simpa [encodeInstr, rel32_bytes, encodeOp, instructionOperation] using call_placeholder rest

/-- A fused pair's bytes decode to its producer, then its consumer. -/
theorem fused_decode {producer consumer : Op} {pargs cargs : List Arg}
    (wf : (Instr.fused producer pargs consumer cargs).wellFormed = true) (rest : List UInt8) :
    Decode.sequence 2 ((encodeInstr (.fused producer pargs consumer cargs)).bytes.data.toList ++ rest) =
      some ([.op producer pargs, .op consumer cargs], rest) := by
  obtain ⟨row, _, _, _, pok, crow, _, cok, _⟩ := wellFormed_fused wf
  simp [encodeInstr, Chunk.raw, encodeOp, bytes, Decode.sequence, row_decode _ _ row pok,
    row_decode _ _ crow cok]

theorem instructions_decode (instruction : Instr) (wf : instruction.wellFormed = true) (rest : List UInt8) :
    Decode.sequence (instructionOperations instruction).length
      ((encodeInstr instruction).bytes.data.toList ++ rest) = some (instructionOperations instruction, rest) := by
  cases instruction with
  | fused producer pargs consumer cargs => exact fused_decode wf rest
  | op o args | call target | callRuntime intrinsic | unwind source =>
      simp [instructionOperations, Decode.sequence, instruction_decode _ wf rfl rest]

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
        simp only [Compare.row, aluImmRow]
        split
        · rename_i fits
          have narrow := fitsImm8_narrow fits
          cases width
          · contradiction
          all_goals
            refine ⟨by dsimp only; decide, ?_⟩
            simp [Op.argsOk, desc, Table.arithDesc, Table.cmpArith, Table.rmSlot, Table.immSlot,
              slotsAccept, ArgKind.accepts, norm_idem]
        · cases width <;> refine ⟨by dsimp only; decide, ?_⟩ <;>
            simp [Op.argsOk, desc, Table.arithDesc, Table.cmpArith, Table.rmSlot,
              Table.immSlot, Table.fullImm, Table.ImmKind.argKind, slotsAccept, ArgKind.accepts, norm_idem]

/-- A comparison's row is a straight-line row. -/
theorem _root_.Compilatrix.X86.Compare.row_linear (comparison : Compare) : comparison.row.1.linear = true := by
  cases comparison with
  | mk width left right =>
      cases right with
      | reg => rfl
      | imm => simp only [Compare.row, aluImmRow]; split <;> rfl

theorem _root_.Compilatrix.X86.Compare.row_flagsFree (comparison : Compare) : (desc comparison.row.1).flagsIn = [] := by
  cases comparison with
  | mk width left right =>
      cases right with
      | reg => rfl
      | imm => simp only [Compare.row, aluImmRow]; split <;> rfl

/-- A `cmp` row sets every flag any condition reads. -/
theorem _root_.Compilatrix.X86.Compare.row_fused (comparison : Compare) (condition : Condition) :
    FusedOk comparison.row.1 (Op.jccRel32 condition) = true := by
  cases comparison with
  | mk width left right =>
      cases right with
      | reg => cases condition <;> rfl
      | imm => simp only [Compare.row, aluImmRow]; split <;> cases condition <;> rfl

def terminatorOperations : Terminator → List Decode.Operation
  | .jump _ | .tailCall _ => [.jump 0]
  | .branch producer args condition _ _ .rel32 => [.op producer args, .branch condition 0, .jump 0]
  | .branch producer args condition _ _ .fall => [.op producer args, .branch condition 0]
  | .ret => [.ret]

/-- A well-formed branch's producer is a listed row with operands of its
slot kinds, linear, reading no flags, and setting every flag the condition
reads. -/
theorem wellFormed_branch {producer : Op} {args : List Arg} {condition : Condition} {yes no : BlockId}
    {reach : Reach} (wf : (Terminator.branch producer args condition yes no reach).wellFormed = true) :
    producer ∈ Op.rows ∧ producer.linear = true ∧ (desc producer).flagsIn = [] ∧
      producer.argsOk args = true ∧ FusedOk producer (Op.jccRel32 condition) = true := by
  simp only [Terminator.wellFormed, Bool.and_eq_true, List.contains_iff_mem, List.isEmpty_iff] at wf
  exact ⟨wf.1.1.1.1, wf.1.1.1.2, wf.1.1.2, wf.1.2, wf.2⟩

/-- A compare-and-branch is well-formed. -/
theorem _root_.Compilatrix.X86.Terminator.compare_wellFormed (comparison : Compare) (condition : Condition) (yes no : BlockId) :
    (Terminator.compare comparison condition yes no).wellFormed = true := by
  have ok := Compare.row_ok comparison
  have linear := Compare.row_linear comparison
  have free := Compare.row_flagsFree comparison
  have fused := Compare.row_fused comparison condition
  simp only [Terminator.compare, Terminator.wellFormed, Bool.and_eq_true, List.contains_iff_mem, List.isEmpty_iff]
  exact ⟨⟨⟨⟨ok.1, linear⟩, free⟩, ok.2⟩, fused⟩

theorem encodeCompare_decode (comparison : Compare) (rest : List UInt8) :
    Decode.one ((encodeCompare comparison).data.toList ++ rest) =
      some (.op comparison.row.1 comparison.row.2, rest) :=
  encodeOp_decode _ _ (Compare.row_ok comparison).1 (Compare.row_ok comparison).2 rest

theorem compare_list_decode (comparison : Compare) (rest : List UInt8) :
    Decode.one (encodeList comparison.row.1 comparison.row.2 ++ rest) =
      some (.op comparison.row.1 comparison.row.2, rest) :=
  row_decode _ _ (Compare.row_ok comparison).1 (Compare.row_ok comparison).2 rest

theorem terminator_decode (terminator : Terminator) (wf : terminator.wellFormed = true) (rest : List UInt8) :
    Decode.sequence (terminatorOperations terminator).length
      ((encodeTerminator terminator).bytes.data.toList ++ rest) =
        some (terminatorOperations terminator, rest) := by
  cases terminator with
  | jump target | tailCall target =>
      simp [terminatorOperations, encodeTerminator, rel32_bytes, encodeOp, Decode.sequence, jump_placeholder]
  | ret =>
      simp [terminatorOperations, encodeTerminator, Chunk.raw, encodeOp, Decode.sequence, ret_row]
  | branch producer args condition yes no reach =>
      obtain ⟨row, _, _, ok, _⟩ := wellFormed_branch wf
      cases reach <;>
        simp [terminatorOperations, encodeTerminator, Chunk.append, Chunk.raw, rel32_bytes, encodeOp,
          Decode.sequence, row_decode _ _ row ok, branch_placeholder, jump_placeholder]

end Compilatrix.X86.Encode

namespace Compilatrix.X86

/-! ## The typed constructors choose listed rows

Every typed constructor yields a well-formed instruction, so the E1 laws
stated for well-formed instructions hold for each of them without premise. -/

open Encode

attribute [local simp] Instr.wellFormed Op.argsOk desc Table.movDesc Table.movzxDesc Table.leaDesc
  Table.imulDesc Table.arithDesc Table.pushDesc Table.popDesc Table.rmSlot Table.regSlot Table.immSlot
  Table.ImmKind.argKind Table.moveImm Table.fullImm slotsAccept ArgKind.accepts norm_idem
  normalize_canonical Op.linear

theorem Instr.mov_wellFormed (width : Width) (destination : GPR) (source : MoveSource) :
    (Instr.mov width destination source).wellFormed = true := by
  cases source <;> cases width <;> simp only [Instr.mov, Instr.ofRow, movImmRow] <;> (try split) <;>
    (try split) <;> simp_all <;> decide

theorem Instr.alu_wellFormed (operation : AluOp) (width : Width) (destination : GPR) (source : AluSource) :
    (Instr.alu operation width destination source).wellFormed = true := by
  cases source with
  | reg => cases operation <;> cases width <;> simp [Instr.alu, AluOp.mnemonic] <;> decide
  | imm value =>
      simp only [Instr.alu, Instr.ofRow, aluImmRow]
      split
      · have narrow := fitsImm8_narrow ‹_›
        cases operation <;> cases width <;> first | contradiction | (simp [AluOp.mnemonic]; decide)
      · cases operation <;> cases width <;> simp [AluOp.mnemonic] <;> decide

theorem Instr.imul_wellFormed (width : MulWidth) (destination source : GPR) :
    (Instr.imul width destination source).wellFormed = true := by
  cases width <;> simp [Instr.imul, MulWidth.width] <;> decide

theorem Instr.imulImm_wellFormed (width : MulWidth) (destination source : GPR) (value : Imm32) :
    (Instr.imulImm width destination source value).wellFormed = true := by
  simp only [Instr.imulImm]
  split <;> cases width <;> simp [MulWidth.width] <;> decide

theorem Instr.load_wellFormed (width : Width) (destination : GPR) (source : MemAddr) :
    (Instr.load width destination source).wellFormed = true := by
  cases width <;> simp [Instr.load] <;> decide

theorem Instr.store_wellFormed (width : Width) (destination : MemAddr) (source : GPR) :
    (Instr.store width destination source).wellFormed = true := by
  cases width <;> simp [Instr.store] <;> decide

theorem Instr.lea_wellFormed (destination : GPR) (source : MemAddr) :
    (Instr.lea destination source).wellFormed = true := by
  simp [Instr.lea]
  decide

theorem Instr.push_wellFormed (source : GPR) : (Instr.push source).wellFormed = true := by
  simp [Instr.push]
  decide

theorem Instr.pop_wellFormed (destination : GPR) : (Instr.pop destination).wellFormed = true := by
  simp [Instr.pop]
  decide

theorem Instr.allocFrame_wellFormed (size : FrameSize) : (Instr.allocFrame size).wellFormed = true := by
  simp only [Instr.allocFrame, Instr.ofRow, aluImmRow]
  split <;> simp <;> decide

theorem Instr.freeFrame_wellFormed (size : FrameSize) : (Instr.freeFrame size).wellFormed = true := by
  simp only [Instr.freeFrame, Instr.ofRow, aluImmRow]
  split <;> simp <;> decide

theorem Instr.spill_wellFormed (slot : StackSlot) (source : GPR) : (Instr.spill slot source).wellFormed = true :=
  Instr.store_wellFormed _ _ _

theorem Instr.reload_wellFormed (destination : GPR) (slot : StackSlot) :
    (Instr.reload destination slot).wellFormed = true :=
  Instr.load_wellFormed _ _ _

end Compilatrix.X86
