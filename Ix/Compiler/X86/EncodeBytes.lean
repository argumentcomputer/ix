import Ix.Compiler.X86.Encode
import Ix.Compiler.X86.Decode
import Ix.Compiler.X86.Memory

/-! Kernel-checked byte-field laws for the actual encoder. -/

namespace Ix.Compiler.X86.Encode

@[simp] theorem bytes_list (values : List UInt8) : (bytes values).data.toList = values := by
  simp [bytes]

theorem littleEndian_list (count : Nat) (value : Word) :
    (littleEndian count value).data.toList =
      (List.range count).map (fun index => (value >>> UInt64.ofNat (8 * index)).toUInt8) := by
  simp [littleEndian]

theorem packByte (value : Word) : value.toUInt8.toUInt64 = Width.w8.truncate value := by
  apply UInt64.toBitVec_inj.mp
  simp only [Width.truncate, UInt64.toBitVec_and, UInt64.toBitVec_toUInt8,
    UInt8.toBitVec_toUInt64]
  change (value.toBitVec.setWidth 8).setWidth 64 =
    value.toBitVec &&& (BitVec.allOnes 8).setWidth 64
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_allOnes,
    decide_eq_true bound, Bool.true_and, Bool.and_comm]

theorem mask_bits (width : Width) :
    width.mask.toBitVec = (BitVec.allOnes width.bits).setWidth 64 := by
  cases width <;> rfl

theorem read_immediate (width : Width) (value : Word) (rest : List UInt8) :
    Decode.readLE (Decode.immediateBytes width) ((immediateBytes width value).data.toList ++ rest) =
      some (width.truncate value, rest) := by
  cases width <;>
    simp [immediateBytes, Decode.immediateBytes, littleEndian_list, List.range_succ,
      Decode.readLE, Width.truncate, -UInt64.toUInt64_toUInt8]
  all_goals
    apply UInt64.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro index bound
    simp only [UInt64.toBitVec_or, UInt64.toBitVec_and, UInt64.toBitVec_shiftLeft,
      UInt64.toBitVec_shiftRight, UInt64.toBitVec_toUInt8, UInt8.toBitVec_toUInt64,
      mask_bits, UInt64.toBitVec_ofNat, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
      BitVec.toNat_umod, BitVec.toNat_ofNat, BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_allOnes, Width.bits]
    have ranges : index < 8 ∨ (8 ≤ index ∧ index < 16) ∨ (16 ≤ index ∧ index < 24) ∨
        (24 ≤ index ∧ index < 32) ∨ (32 ≤ index ∧ index < 40) ∨
        (40 ≤ index ∧ index < 48) ∨ (48 ≤ index ∧ index < 56) ∨
        (56 ≤ index ∧ index < 64) := by omega
    rcases ranges with h | h | h | h | h | h | h | h <;>
      simp (discharger := omega) [decide_eq_true, decide_eq_false, Bool.and_comm] <;>
      congr 1 <;> omega

theorem truncate_bits (width : Width) (value : Word) :
    (width.truncate value).toBitVec = (value.toBitVec.setWidth width.bits).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  simp only [Width.truncate, UInt64.toBitVec_and, mask_bits, BitVec.getLsbD_and,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, decide_eq_true bound,
    Bool.true_and, Bool.and_comm]

@[simp] theorem truncate32 (value : Imm32) : Width.w32.truncate value.toUInt64 = value.toUInt64 := by
  apply UInt64.toBitVec_inj.mp
  simp [truncate_bits, UInt32.toBitVec_toUInt64, Width.bits]

@[simp] theorem truncate64 (value : Word) : Width.w64.truncate value = value := by
  apply UInt64.toBitVec_inj.mp
  simp [truncate_bits, Width.bits]

theorem read_imm32 (value : Imm32) (rest : List UInt8) :
    Decode.readLE 4 ((imm32Bytes value).data.toList ++ rest) = some (value.toUInt64, rest) := by
  simpa [imm32Bytes, immediateBytes, Decode.immediateBytes] using
    read_immediate .w32 value.toUInt64 rest

theorem imm32_zero_bytes : imm32Bytes 0 = bytes [0, 0, 0, 0] := by
  apply ByteArray.ext
  simp [imm32Bytes, littleEndian, bytes, List.range_succ]

@[simp] theorem sign32_decode (value : Imm32) : Decode.sign32 value.toUInt64 = signExtend32 value := by
  simp [Decode.sign32, signExtend32, UInt32.lt_iff_toNat_lt, UInt64.lt_iff_toNat_lt]

def normalizedImmediate (width : Width) (value : Imm32) : Word :=
  if width == .w64 then signExtend32 value else width.truncate value.toUInt64

theorem read_groupImmediate (width : Width) (value : Imm32) (rest : List UInt8) :
    Decode.groupImmediate width ((groupImmediateBytes width value).data.toList ++ rest) =
      some (normalizedImmediate width value, rest) := by
  have byte := read_immediate .w8 value.toUInt64 rest
  have short := read_immediate .w16 value.toUInt64 rest
  cases width <;>
    simp_all [Decode.groupImmediate, groupImmediateBytes, normalizedImmediate, read_imm32,
      Decode.immediateBytes, immediateBytes]

theorem truncate_nat (width : Width) (value : Word) :
    (width.truncate value).toNat = value.toNat % 2 ^ width.bits := by
  have bits := congrArg BitVec.toNat (truncate_bits width value)
  cases width <;>
    simp only [Width.bits, BitVec.toNat_setWidth, UInt64.toNat_toBitVec, Nat.reducePow] at bits ⊢ <;>
    omega

theorem truncate32_of_small (value : Word) (bound : value.toNat < 2 ^ 32) :
    Width.w32.truncate value = value := by
  apply UInt64.toNat_inj.mp
  rw [truncate_nat]
  exact Nat.mod_eq_of_lt bound

theorem read_word32 (value : Word) (bound : value.toNat < 2 ^ 32) (rest : List UInt8) :
    Decode.readLE 4 ((littleEndian 4 value).data.toList ++ rest) = some (value, rest) := by
  simpa [Decode.immediateBytes, immediateBytes, truncate32_of_small value bound] using
    read_immediate .w32 value rest

end Ix.Compiler.X86.Encode
