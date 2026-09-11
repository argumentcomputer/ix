import Ix.Compiler.X86.EncodeControl

/-! Every emitted typed form has a concrete, independently decoded recipe.
Control displacements here are the encoder's pre-layout placeholders; the
relative-field laws separately cover patched values. -/

namespace Ix.Compiler.X86.Encode

def instructionOperation : Instr → Decode.Operation
  | .mov width destination source => .mov width destination (moveOperand width source)
  | .load width destination source => .load width destination (normalizedAddress source)
  | .store width destination source => .store width (normalizedAddress destination) source
  | .lea destination source => .lea destination (normalizedAddress source)
  | .alu operation width destination source => .alu operation width destination (aluOperand width source)
  | .imul width destination source => .imul width destination source
  | .push source => .push source
  | .pop destination => .pop destination
  | .allocFrame size => .alu .sub .w64 .rsp (.imm size.bytes)
  | .freeFrame size => .alu .add .w64 .rsp (.imm size.bytes)
  | .spill slot source => .store .w64 (spillAddress slot) source
  | .reload destination slot => .load .w64 destination (spillAddress slot)
  | .call _ | .callRuntime _ => .call 0

theorem instruction_decode (instruction : Instr) (rest : List UInt8) :
    Decode.one ((encodeInstr instruction).bytes.data.toList ++ rest) =
      some (instructionOperation instruction, rest) := by
  cases instruction with
  | mov width destination source => exact mov_decode width destination source rest
  | load width destination source => exact load_decode width destination source rest
  | store width destination source => exact store_decode width destination source rest
  | lea destination source => exact lea_decode destination source rest
  | alu operation width destination source => exact alu_decode operation width destination source rest
  | imul width destination source => exact imul_decode width destination source rest
  | push source => exact push_decode source rest
  | pop destination => exact pop_decode destination rest
  | allocFrame size => exact frame_decode true size rest
  | freeFrame size => exact frame_decode false size rest
  | spill slot source => exact spill_decode slot source rest
  | reload destination slot => exact reload_decode destination slot rest
  | call target | callRuntime intrinsic =>
    simp [encodeInstr, instructionOperation, rel32, byte, Decode.one, Decode.readLE]

def terminatorOperations : Terminator → List Decode.Operation
  | .jump _ | .tailCall _ => [.jump 0]
  | .branch comparison condition _ _ =>
      [.compare comparison.width comparison.left (aluOperand comparison.width comparison.right),
        .branch condition 0, .jump 0]
  | .ret => [.ret]

theorem rel32_branch_decode (condition : Condition) (target : FixupTarget) (rest : List UInt8) :
    Decode.one ((rel32 (bytes [0x0f, nearOpcode condition]) target).bytes.data.toList ++ rest) =
      some (.branch condition 0, rest) := by
  cases condition <;>
    simp [rel32, Decode.one, nearOpcode, Decode.nearCondition, Decode.readLE]

theorem rel32_jump_decode (target : FixupTarget) (rest : List UInt8) :
    Decode.one ((rel32 (byte 0xe9) target).bytes.data.toList ++ rest) =
      some (.jump 0, rest) := by
  simp [rel32, byte, Decode.one, Decode.readLE]

theorem terminator_decode (terminator : Terminator) (rest : List UInt8) :
    Decode.sequence (terminatorOperations terminator).length
      ((encodeTerminator terminator).bytes.data.toList ++ rest) =
        some (terminatorOperations terminator, rest) := by
  cases terminator with
  | jump target | tailCall target =>
    simp [terminatorOperations, encodeTerminator, Decode.sequence, rel32_jump_decode]
  | ret =>
    simp [terminatorOperations, encodeTerminator, Chunk.raw, Decode.sequence, ret_decode]
  | branch comparison condition yes no =>
    simp only [terminatorOperations, List.length_cons, List.length_nil, encodeTerminator,
      Chunk.append, Chunk.raw, ByteArray.toList_data_append, List.append_assoc]
    rw [Decode.sequence, compare_decode]
    simp only [bind, Option.bind]
    rw [Decode.sequence, rel32_branch_decode]
    simp only [bind, Option.bind]
    rw [Decode.sequence, rel32_jump_decode]
    rfl

end Ix.Compiler.X86.Encode
