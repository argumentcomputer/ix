import Ix.Compiler.X86.EncodeControl

/-! Width and signed-word laws used by the byte execution bridge. -/

namespace Ix.Compiler.X86.Encode

theorem width_bound (width : Width) : width.bits ≤ 64 := by cases width <;> decide

@[simp] theorem truncate_truncate (width : Width) (value : Word) :
    width.truncate (width.truncate value) = width.truncate value := by
  simp [Width.truncate, UInt64.and_assoc]

theorem writeReg_truncate (core : Core) (width : Width) (register : GPR) (value : Word) :
    core.writeReg width register (width.truncate value) = core.writeReg width register value := by
  cases width <;> simp [Core.writeReg]

theorem writeReg_congr (core : Core) (width : Width) (register : GPR) (left right : Word)
    (equal : width.truncate left = width.truncate right) :
    core.writeReg width register left = core.writeReg width register right := by
  rw [← writeReg_truncate, equal, writeReg_truncate]

theorem truncate_alu (operation : AluOp) (width : Width) (left right : Word) :
    width.truncate (operation.eval left right) =
      width.truncate (operation.eval (width.truncate left) (width.truncate right)) := by
  apply UInt64.toBitVec_inj.mp
  cases operation <;>
    simp (discharger := exact width_bound width) [AluOp.eval, truncate_bits,
      UInt64.toBitVec_add, UInt64.toBitVec_sub, UInt64.toBitVec_and, UInt64.toBitVec_or,
      UInt64.toBitVec_xor, BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, BitVec.setWidth_add]

theorem alu_congr_right (operation : AluOp) (width : Width) (left first second : Word)
    (equal : width.truncate first = width.truncate second) :
    width.truncate (operation.eval left first) = width.truncate (operation.eval left second) := by
  rw [truncate_alu operation width left first, equal, ← truncate_alu]

theorem signExtend32_bits (value : Imm32) :
    (signExtend32 value).toBitVec = value.toBitVec.signExtend 64 := by
  have sign : value.toBitVec.msb = decide (2147483648 ≤ value.toNat) := by
    simp [BitVec.msb_eq_decide]
  by_cases low : value.toNat < 2147483648
  · have msb : value.toBitVec.msb = false := by simp [sign, Nat.not_le.mpr low]
    simp [signExtend32, UInt32.lt_iff_toNat_lt, low, UInt32.toBitVec_toUInt64,
      BitVec.signExtend_eq_setWidth_of_msb_false msb]
  · have msb : value.toBitVec.msb = true := by simp [sign, Nat.le_of_not_lt low]
    simp only [signExtend32, UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat,
      show (2147483648 : Nat) % 2 ^ 32 = 2147483648 from rfl, low, ↓reduceIte,
      UInt64.toBitVec_or, UInt32.toBitVec_toUInt64]
    change value.toBitVec.setWidth 64 ||| ((BitVec.allOnes 32).setWidth 64 <<< 32) = _
    apply BitVec.eq_of_getLsbD_eq
    intro index bound
    by_cases inner : index < 32 <;>
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
        BitVec.getLsbD_allOnes, BitVec.getLsbD_signExtend, msb] <;>
      simp (discharger := omega) [bound, inner] <;> omega

theorem normalizedImmediate_truncate (width : Width) (value : Imm32) :
    width.truncate (normalizedImmediate width value) = width.truncate (signExtend32 value) := by
  cases width with
  | w64 => rfl
  | w8 | w16 | w32 =>
    simp only [normalizedImmediate, beq_iff_eq, reduceCtorEq, ↓reduceIte, truncate_truncate]
    apply UInt64.toBitVec_inj.mp
    simp only [truncate_bits, signExtend32_bits, UInt32.toBitVec_toUInt64]
    apply congrArg (BitVec.setWidth 64)
    apply BitVec.eq_of_getLsbD_eq
    intro index bound
    simp only [Width.bits] at bound
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, Width.bits]
    simp [bound, show index < 32 by omega, show index < 64 by omega]

theorem spill_bound (slot : StackSlot) : 0 < slot.displacement.toNat ∧ slot.displacement.toNat < 2 ^ 31 := by
  have bound := slot.index.toNat_lt_size
  simp only [StackSlot.displacement, UInt64.toNat_mul, UInt64.toNat_add, UInt16.toNat_toUInt64]
  change 0 < (((slot.index.toNat + 1) % 18446744073709551616) * 8) % 18446744073709551616 ∧
    (((slot.index.toNat + 1) % 18446744073709551616) * 8) % 18446744073709551616 < 2147483648
  simp only [UInt16.size] at bound
  omega

theorem signExtend32_ofInt (value : Int) (fits : fitsSigned32 value = true) :
    (signExtend32 (Int32.ofInt value).toUInt32).toBitVec = BitVec.ofInt 64 value := by
  simp only [fitsSigned32, decide_eq_true_eq] at fits
  rw [signExtend32_bits]
  change (BitVec.ofInt 32 value).signExtend 64 = _
  unfold BitVec.signExtend
  rw [BitVec.toInt_ofInt_eq_self (by decide : 0 < 32) fits.1 fits.2]

theorem signExtend32_neg (value : Word) (bound : value.toNat < 2 ^ 31) :
    signExtend32 (0 - value).toUInt32 = 0 - value := by
  have fits : fitsSigned32 (-(value.toNat : Int)) = true := by
    simp only [fitsSigned32, decide_eq_true_eq]
    omega
  have raw : (Int32.ofInt (-(value.toNat : Int))).toUInt32 = (0 - value).toUInt32 := by
    apply UInt32.toBitVec_inj.mp
    simp [UInt64.toBitVec_toUInt32, BitVec.neg_eq_not_add]
    rfl
  apply UInt64.toBitVec_inj.mp
  rw [← raw, signExtend32_ofInt _ fits]
  simp [BitVec.ofInt_neg]

@[simp] theorem spillAddress_eval (slot : StackSlot) (core : Core) :
    (spillAddress slot).eval core = core.readReg .rbp - slot.displacement := by
  simp only [spillAddress, MemAddr.eval, UInt64.add_zero]
  rw [signExtend32_neg _ (spill_bound slot).2]
  simp [UInt64.sub_eq_add_neg]

end Ix.Compiler.X86.Encode
