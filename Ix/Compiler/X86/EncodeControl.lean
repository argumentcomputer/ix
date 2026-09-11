import Ix.Compiler.X86.EncodeRegisters
import Ix.Compiler.X86.EncodeMemory

/-! Frame pseudo-operations and ordinary relative-control instruction bytes. -/

namespace Ix.Compiler.X86.Encode

theorem frame_bound (size : FrameSize) : size.bytes.toNat < 2 ^ 31 := by
  have bound := size.units16.toNat_lt_size
  simp only [FrameSize.bytes, UInt64.toNat_mul, UInt16.toNat_toUInt64]
  change (size.units16.toNat * 16) % 18446744073709551616 < 2147483648
  simp only [UInt16.size] at bound
  omega

theorem frame_decode (subtract : Bool) (size : FrameSize) (rest : List UInt8) :
    Decode.one ((frameBytes subtract size).data.toList ++ rest) =
      some (.alu (if subtract then .sub else .add) .w64 .rsp (.imm size.bytes), rest) := by
  have small := frame_bound size
  have read := read_word32 size.bytes (by omega) rest
  cases subtract <;>
    simp [frameBytes, Decode.one, Decode.rex, Decode.prefixed, Decode.Prefix.width,
      Decode.Prefix.wide, Decode.registers, Decode.modMode, Decode.modReg, Decode.modRM,
      Decode.register, Decode.groupImmediate, Decode.aluGroup, read, Decode.sign32,
      UInt64.lt_iff_toNat_lt, show size.bytes.toNat < 2147483648 from small]

theorem spill_decode (slot : StackSlot) (source : GPR) (rest : List UInt8) :
    Decode.one ((encodeSpill slot source).data.toList ++ rest) =
      some (.store .w64 (spillAddress slot) source, rest) := by
  simpa [encodeSpill, normalizedAddress, spillAddress] using
    store_decode .w64 (spillAddress slot) source rest

theorem reload_decode (destination : GPR) (slot : StackSlot) (rest : List UInt8) :
    Decode.one ((encodeReload destination slot).data.toList ++ rest) =
      some (.load .w64 destination (spillAddress slot), rest) := by
  simpa [encodeReload, normalizedAddress, spillAddress] using
    load_decode .w64 destination (spillAddress slot) rest

theorem call_decode (displacement : Imm32) (rest : List UInt8) :
    Decode.one ((byte 0xe8 ++ imm32Bytes displacement).data.toList ++ rest) =
      some (.call displacement, rest) := by
  simp [byte, Decode.one, read_imm32]

theorem jump_decode (displacement : Imm32) (rest : List UInt8) :
    Decode.one ((byte 0xe9 ++ imm32Bytes displacement).data.toList ++ rest) =
      some (.jump displacement, rest) := by
  simp [byte, Decode.one, read_imm32]

theorem branch_decode (condition : Condition) (displacement : Imm32) (rest : List UInt8) :
    Decode.one ((bytes [0x0f, nearOpcode condition] ++ imm32Bytes displacement).data.toList ++ rest) =
      some (.branch condition displacement, rest) := by
  cases condition <;> simp [Decode.one, nearOpcode, Decode.nearCondition, read_imm32]

theorem ret_decode (rest : List UInt8) :
    Decode.one ((byte 0xc3).data.toList ++ rest) = some (.ret, rest) := by
  simp [byte, Decode.one]

end Ix.Compiler.X86.Encode
