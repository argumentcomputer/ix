import Ix.Compiler.X86.EncodeForms

/-! Instruction lengths and exact decoding at a supplied byte boundary. -/

namespace Ix.Compiler.X86.Encode

@[simp] theorem bytes_size (values : List UInt8) : (bytes values).size = values.length := by
  simp [bytes, ByteArray.size]

@[simp] theorem byte_size (value : UInt8) : (byte value).size = 1 := by simp [byte]

@[simp] theorem littleEndian_size (count : Nat) (value : Word) : (littleEndian count value).size = count := by
  simp [littleEndian, ByteArray.size]

@[simp] theorem imm32Bytes_size (value : Imm32) : (imm32Bytes value).size = 4 := by simp [imm32Bytes]

@[simp] theorem prefixes_size (operand16 w r x b : Bool) :
    (prefixes operand16 w r x b).size = if operand16 then 2 else 1 := by
  cases operand16 <;> simp [prefixes]

@[simp] theorem widthPrefixes_size (width : Width) (r x b : Bool) :
    (widthPrefixes width r x b).size = if width == .w16 then 2 else 1 := by
  simp [widthPrefixes]

theorem memoryTail_size (reg : UInt8) (address : MemAddr) :
    5 ≤ (memoryTail reg address).bytes.size ∧ (memoryTail reg address).bytes.size ≤ 6 := by
  cases address with
  | mk base index scale displacement =>
    cases base with
    | none => simp [memoryTail, imm32Bytes]
    | some base =>
      by_cases useSib : index.isSome || registerLow (gprCode base) == 4 <;>
        simp [memoryTail, useSib, imm32Bytes]

@[simp] theorem immediateBytes_size (width : Width) (value : Word) :
    (immediateBytes width value).size = width.bytes := by
  cases width <;> simp [immediateBytes, Width.bytes]

@[simp] theorem groupImmediateBytes_size (width : Width) (value : Imm32) :
    (groupImmediateBytes width value).size = if width == .w64 then 4 else width.bytes := by
  cases width <;> simp [groupImmediateBytes, imm32Bytes, Width.bytes]

@[simp] theorem imul_size (width : MulWidth) (destination source : GPR) :
    (encodeImul width destination source).size = if width == .w16 then 5 else 4 := by
  have size := congrArg List.length (imul_list width destination source)
  simp only [List.length_append, List.length_cons, List.length_nil, Array.length_toList,
    ByteArray.size_data] at size
  cases width <;> simpa [MulWidth.width] using size

theorem instruction_size (instruction : Instr) :
    0 < (encodeInstr instruction).bytes.size ∧ (encodeInstr instruction).bytes.size ≤ 10 := by
  cases instruction with
  | mov width destination source =>
    cases source <;> cases width <;>
      simp [encodeInstr, Chunk.raw, encodeMov, encodeRegReg, Width.bytes]
  | load width destination address =>
    have bounds := memoryTail_size (gprCode destination) address
    cases width <;> simp_all [encodeInstr, Chunk.raw, encodeLoad, encodeMemory] <;> omega
  | store width address source =>
    have bounds := memoryTail_size (gprCode source) address
    cases width <;> simp_all [encodeInstr, Chunk.raw, encodeStore, encodeMemory] <;> omega
  | lea destination address =>
    have bounds := memoryTail_size (gprCode destination) address
    simp_all [encodeInstr, Chunk.raw, encodeLea, encodeMemory] <;> omega
  | alu operation width destination source =>
    cases source <;> cases width <;>
      simp [encodeInstr, Chunk.raw, encodeAlu, encodeRegReg, Width.bytes]
  | imul width destination source =>
    cases width <;> simp [encodeInstr, Chunk.raw]
  | push source =>
    simp only [encodeInstr, Chunk.raw, encodePush]
    split <;> simp
  | pop destination =>
    simp only [encodeInstr, Chunk.raw, encodePop]
    split <;> simp
  | allocFrame size | freeFrame size => simp [encodeInstr, Chunk.raw, frameBytes]
  | spill slot source =>
    have bounds := memoryTail_size (gprCode source) (spillAddress slot)
    simp_all [encodeInstr, Chunk.raw, encodeSpill, encodeStore, encodeMemory] <;> omega
  | reload destination slot =>
    have bounds := memoryTail_size (gprCode destination) (spillAddress slot)
    simp_all [encodeInstr, Chunk.raw, encodeReload, encodeLoad, encodeMemory] <;> omega
  | call target | callRuntime intrinsic => simp [encodeInstr, rel32]

theorem compare_size (comparison : Compare) :
    0 < (encodeCompare comparison).size ∧ (encodeCompare comparison).size ≤ 7 := by
  cases comparison with
  | mk width left right =>
    cases right <;> cases width <;> simp [encodeCompare, encodeRegReg, Width.bytes]

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

theorem instruction_decodeAt (instruction : Instr) (before after : ByteArray) :
    Decode.decodeAt (before ++ (encodeInstr instruction).bytes ++ after) before.size =
      some ⟨instructionOperation instruction, (encodeInstr instruction).bytes.size⟩ :=
  decodeAt_of_one _ before after _ (instruction_decode instruction after.data.toList)
    (instruction_size instruction).1 (Nat.le_trans (instruction_size instruction).2 (by decide))

end Ix.Compiler.X86.Encode
