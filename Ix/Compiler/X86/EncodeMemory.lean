import Ix.Compiler.X86.EncodeFields

/-! Exact emitted addressing bytes, including displacement consumption. -/

namespace Ix.Compiler.X86.Encode

/-- Scale bits have no architectural effect in the absence of an index. -/
def normalizedAddress (address : MemAddr) : MemAddr :=
  { address with scale := if address.index.isSome then address.scale else .one }

@[simp] theorem normalizedAddress_eval (address : MemAddr) (core : Core) :
    (normalizedAddress address).eval core = address.eval core := by
  cases address with
  | mk base index scale displacement => cases index <;> rfl

theorem memoryTail_decode (operand16 w : Bool) (reg : GPR) (address : MemAddr)
    (make : GPR → MemAddr → Decode.Operation) (rest : List UInt8) :
    let tail := memoryTail (gprCode reg) address
    Decode.memoryOperation
      ⟨operand16, w, registerExtended (gprCode reg), tail.rexX, tail.rexB⟩ make
      (tail.bytes.data.toList ++ rest) = some (make reg (normalizedAddress address), rest) := by
  cases address with
  | mk base index scale displacement =>
    cases base with
    | none =>
      cases index <;>
        simp [memoryTail, Decode.memoryOperation, Decode.memory, normalizedAddress,
          read_imm32]
    | some base =>
      cases index with
      | none =>
        have baseDecoded := register_decode base
        by_cases useSib : registerLow (gprCode base) = 4 <;>
          simp_all [memoryTail, Decode.memoryOperation, Decode.memory, normalizedAddress,
            byte, read_imm32]
      | some index =>
        simp [memoryTail, Decode.memoryOperation, Decode.memory, normalizedAddress,
          read_imm32]

theorem memoryTail_head (reg : GPR) (address : MemAddr) :
    ∃ head tail, (memoryTail (gprCode reg) address).bytes.data.toList = head :: tail ∧
      Decode.modMode head ≠ 3 := by
  cases address with
  | mk base index scale displacement =>
    cases base with
    | none => simp [memoryTail]
    | some base =>
      by_cases useSib : index.isSome || registerLow (gprCode base) == 4 <;>
        simp [memoryTail, useSib, byte]

theorem one_encodeMemory (operand16 w : Bool) (opcode : UInt8) (extra : List UInt8)
    (reg : GPR) (address : MemAddr) (rest : List UInt8)
    (notStack : (0x50 ≤ opcode.toNat && opcode.toNat < 0x60) = false) :
    let tail := memoryTail (gprCode reg) address
    Decode.one ((encodeMemory operand16 w (bytes (opcode :: extra))
      (gprCode reg) address).data.toList ++ rest) =
        Decode.prefixed ⟨operand16, w, registerExtended (gprCode reg), tail.rexX, tail.rexB⟩
          (opcode :: (extra ++ tail.bytes.data.toList ++ rest)) := by
  simp only [encodeMemory, ByteArray.toList_data_append, bytes_list, List.append_assoc,
    List.cons_append]
  exact one_prefixes _ _ _ _ _ _ _ notStack

theorem load_decode (width : Width) (destination : GPR) (address : MemAddr)
    (rest : List UInt8) :
    Decode.one ((encodeLoad width destination address).data.toList ++ rest) =
      some (.load width destination (normalizedAddress address), rest) := by
  obtain ⟨head, tail, shape, mode⟩ := memoryTail_head destination address
  have decoded := fun rexW => memoryTail_decode false rexW destination address (.load width) rest
  cases width <;>
    simp only [encodeLoad, byte] <;>
    rw [one_encodeMemory _ _ _ _ _ _ _ (by decide)] <;>
    simp only [List.nil_append, shape, List.cons_append] at * <;>
    first
    | simpa [Decode.prefixed] using decoded true
    | simpa [Decode.prefixed] using decoded false

theorem store_decode (width : Width) (address : MemAddr) (source : GPR)
    (rest : List UInt8) :
    Decode.one ((encodeStore width address source).data.toList ++ rest) =
      some (.store width (normalizedAddress address) source, rest) := by
  obtain ⟨head, tail, shape, mode⟩ := memoryTail_head source address
  have decoded := memoryTail_decode (width == .w16) (width == .w64) source address
    (fun source address => .store width address source) rest
  cases width <;>
    simp only [encodeStore, byte] <;>
    rw [one_encodeMemory _ _ _ _ _ _ _ (by decide)] <;>
    simp only [List.nil_append, shape, List.cons_append] at * <;>
    simpa [Decode.prefixed, Decode.Prefix.width, Decode.Prefix.wide, mode] using decoded

theorem lea_decode (destination : GPR) (address : MemAddr) (rest : List UInt8) :
    Decode.one ((encodeLea destination address).data.toList ++ rest) =
      some (.lea destination (normalizedAddress address), rest) := by
  obtain ⟨head, tail, shape, mode⟩ := memoryTail_head destination address
  have decoded := memoryTail_decode false true destination address .lea rest
  simp only [encodeLea, byte]
  rw [one_encodeMemory _ _ _ _ _ _ _ (by decide)]
  simp only [List.nil_append, shape, List.cons_append] at *
  simpa [Decode.prefixed] using decoded

end Ix.Compiler.X86.Encode
