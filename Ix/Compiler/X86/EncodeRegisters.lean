import Ix.Compiler.X86.EncodeFields

/-! Register and immediate instruction forms, proved from their encoded bytes. -/

namespace Ix.Compiler.X86.Encode

def moveOperand (width : Width) : MoveSource → Decode.Operand
  | .reg register => .reg register
  | .imm value => .imm (width.truncate value)

def aluOperand (width : Width) : AluSource → Decode.Operand
  | .reg register => .reg register
  | .imm value => .imm (normalizedImmediate width value)

theorem one_encodeRegReg (width : Width) (opcode : UInt8) (reg rm : GPR) (rest : List UInt8)
    (notStack : (0x50 ≤ opcode.toNat && opcode.toNat < 0x60) = false) :
    Decode.one ((encodeRegReg width opcode reg rm).data.toList ++ rest) =
      Decode.prefixed
        ⟨width == .w16, width == .w64, registerExtended (gprCode reg), false,
          registerExtended (gprCode rm)⟩
        (opcode :: modRM 3 (registerLow (gprCode reg)) (registerLow (gprCode rm)) :: rest) := by
  simp only [encodeRegReg, widthPrefixes, ByteArray.toList_data_append, bytes_list,
    List.append_assoc, List.cons_append, List.nil_append]
  exact one_prefixes _ _ _ _ _ _ _ notStack

theorem mov_register_decode (width : Width) (destination source : GPR) (rest : List UInt8) :
    Decode.one ((encodeMov width destination (.reg source)).data.toList ++ rest) =
      some (.mov width destination (.reg source), rest) := by
  cases width <;> simp only [encodeMov] <;>
    rw [one_encodeRegReg _ _ _ _ _ (by decide)] <;>
    simp [Decode.prefixed, moveOpcode, Decode.Prefix.width, Decode.Prefix.wide, registers_decode]

theorem alu_register_decode (operation : AluOp) (width : Width)
    (destination source : GPR) (rest : List UInt8) :
    Decode.one ((encodeAlu operation width destination (.reg source)).data.toList ++ rest) =
      some (.alu operation width destination (.reg source), rest) := by
  cases operation <;> cases width <;> simp only [encodeAlu] <;>
    rw [one_encodeRegReg _ _ _ _ _ (by decide)] <;>
    simp [Decode.prefixed, aluOpcode, Decode.aluRegisterOpcode, Decode.Prefix.width,
      Decode.Prefix.wide, registers_decode]

theorem compare_register_decode (width : Width) (left right : GPR) (rest : List UInt8) :
    Decode.one ((encodeCompare ⟨width, left, .reg right⟩).data.toList ++ rest) =
      some (.compare width left (.reg right), rest) := by
  cases width <;> simp only [encodeCompare] <;>
    rw [one_encodeRegReg _ _ _ _ _ (by decide)] <;>
    simp [Decode.prefixed, cmpOpcode, Decode.Prefix.width, Decode.Prefix.wide, registers_decode]

theorem mov_immediate_decode (width : Width) (destination : GPR) (value : Word)
    (rest : List UInt8) :
    Decode.one ((encodeMov width destination (.imm value)).data.toList ++ rest) =
      some (.mov width destination (.imm (width.truncate value)), rest) := by
  cases width <;> cases destination <;>
    simp [encodeMov, widthPrefixes, prefixes, byte, gprCode, registerLow, registerExtended,
      Decode.one, Decode.rex, Decode.prefixed, Decode.Prefix.width,
      Decode.Prefix.wide, Decode.register, read_immediate]

theorem mov_decode (width : Width) (destination : GPR) (source : MoveSource)
    (rest : List UInt8) :
    Decode.one ((encodeMov width destination source).data.toList ++ rest) =
      some (.mov width destination (moveOperand width source), rest) := by
  cases source with
  | reg source => exact mov_register_decode width destination source rest
  | imm value => exact mov_immediate_decode width destination value rest

def groupBytes (width : Width) (extension : Nat) (destination : GPR) (value : Imm32) : ByteArray :=
  widthPrefixes width false false (registerExtended (gprCode destination)) ++
    bytes [if width == .w8 then 0x80 else 0x81,
      modRM 3 extension (registerLow (gprCode destination))] ++
    groupImmediateBytes width value

theorem one_groupBytes (width : Width) (extension : Nat) (destination : GPR)
    (value : Imm32) (rest : List UInt8) :
    Decode.one ((groupBytes width extension destination value).data.toList ++ rest) =
      Decode.prefixed
        ⟨width == .w16, width == .w64, false, false, registerExtended (gprCode destination)⟩
        ((if width == .w8 then 0x80 else 0x81) ::
          modRM 3 extension (registerLow (gprCode destination)) ::
            ((groupImmediateBytes width value).data.toList ++ rest)) := by
  simp only [groupBytes, widthPrefixes, ByteArray.toList_data_append, bytes_list,
    List.append_assoc, List.cons_append, List.nil_append]
  apply one_prefixes
  cases width <;> decide

theorem alu_immediate_decode (operation : AluOp) (width : Width)
    (destination : GPR) (value : Imm32) (rest : List UInt8) :
    Decode.one ((encodeAlu operation width destination (.imm value)).data.toList ++ rest) =
      some (.alu operation width destination (.imm (normalizedImmediate width value)), rest) := by
  change Decode.one ((groupBytes width (aluExtension operation) destination value).data.toList ++ rest) = _
  rw [one_groupBytes]
  cases operation <;> cases width <;>
    simp [Decode.prefixed, aluExtension, Decode.Prefix.width, Decode.Prefix.wide,
      Decode.registers, Decode.aluGroup, read_groupImmediate] <;>
    simp [Decode.register]

theorem compare_immediate_decode (width : Width) (left : GPR) (value : Imm32)
    (rest : List UInt8) :
    Decode.one ((encodeCompare ⟨width, left, .imm value⟩).data.toList ++ rest) =
      some (.compare width left (.imm (normalizedImmediate width value)), rest) := by
  change Decode.one ((groupBytes width 7 left value).data.toList ++ rest) = _
  rw [one_groupBytes]
  cases width <;>
    simp [Decode.prefixed, Decode.Prefix.width, Decode.Prefix.wide, Decode.registers,
      read_groupImmediate] <;>
    simp [Decode.register]

theorem imul_list (width : MulWidth) (destination source : GPR) :
    (encodeImul width destination source).data.toList =
      (widthPrefixes width.width (registerExtended (gprCode destination)) false
        (registerExtended (gprCode source))).data.toList ++
      [0x0f, 0xaf, modRM 3 (registerLow (gprCode destination)) (registerLow (gprCode source))] := by
  cases width <;>
    simp [encodeImul, encodeRegReg, widthPrefixes, prefixes, byte, bytes, MulWidth.width,
      ByteArray.size]

theorem imul_decode (width : MulWidth) (destination source : GPR) (rest : List UInt8) :
    Decode.one ((encodeImul width destination source).data.toList ++ rest) =
      some (.imul width destination source, rest) := by
  rw [imul_list]
  simp only [widthPrefixes, List.append_assoc, List.cons_append, List.nil_append]
  rw [one_prefixes _ _ _ _ _ _ _ (by decide)]
  cases width <;>
    simp [Decode.prefixed, Decode.Prefix.mulWidth, Decode.Prefix.wide, MulWidth.width,
      registers_decode]

theorem push_decode (source : GPR) (rest : List UInt8) :
    Decode.one ((encodePush source).data.toList ++ rest) = some (.push source, rest) := by
  cases source <;>
    simp [encodePush, registerExtended, registerLow, gprCode, byte, Decode.one,
      Decode.stack, Decode.register]

theorem pop_decode (destination : GPR) (rest : List UInt8) :
    Decode.one ((encodePop destination).data.toList ++ rest) = some (.pop destination, rest) := by
  cases destination <;>
    simp [encodePop, registerExtended, registerLow, gprCode, byte, Decode.one,
      Decode.stack, Decode.register]

theorem alu_decode (operation : AluOp) (width : Width) (destination : GPR)
    (source : AluSource) (rest : List UInt8) :
    Decode.one ((encodeAlu operation width destination source).data.toList ++ rest) =
      some (.alu operation width destination (aluOperand width source), rest) := by
  cases source with
  | reg source => exact alu_register_decode operation width destination source rest
  | imm value => exact alu_immediate_decode operation width destination value rest

theorem compare_decode (comparison : Compare) (rest : List UInt8) :
    Decode.one ((encodeCompare comparison).data.toList ++ rest) =
      some (.compare comparison.width comparison.left
        (aluOperand comparison.width comparison.right), rest) := by
  cases comparison with
  | mk width left right =>
    cases right with
    | reg right => exact compare_register_decode width left right rest
    | imm value => exact compare_immediate_decode width left value rest

end Ix.Compiler.X86.Encode
