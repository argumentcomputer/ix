import Compilatrix.X86.Basic

/-! Width, sign-extension and canonical-immediate laws. They are pure word
facts, independent of the encoder: the typed constructors' row choices, the
byte execution bridge and the stream proofs all use them. -/

namespace Compilatrix.X86.Encode

theorem mask_bits (width : Width) :
    width.mask.toBitVec = (BitVec.allOnes width.bits).setWidth 64 := by
  cases width <;> rfl

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

theorem truncate_congr {width : Width} {left right : Word}
    (equal : left.toNat % 2 ^ width.bits = right.toNat % 2 ^ width.bits) :
    width.truncate left = width.truncate right := by
  apply UInt64.toNat_inj.mp
  rw [truncate_nat, truncate_nat, equal]

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

theorem truncate_mul (width : Width) (left right : Word) :
    width.truncate (left * right) = width.truncate (width.truncate left * width.truncate right) := by
  apply UInt64.toBitVec_inj.mp
  simp (discharger := exact width_bound width) [truncate_bits, UInt64.toBitVec_mul, BitVec.setWidth_mul]

/-! ## Sign extension and canonical immediates -/

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

theorem signExtend8_low (value : UInt8) : (signExtend8 value).toNat % 2 ^ 8 = value.toNat := by
  unfold signExtend8
  have bound := value.toNat_lt_size
  split
  · simp only [UInt8.toNat_toUInt64]
    exact Nat.mod_eq_of_lt bound
  · rw [UInt64.toNat_or, Nat.or_mod_two_pow]
    simp only [UInt8.toNat_toUInt64]
    rw [Nat.mod_eq_of_lt bound]
    simp

theorem signExtend16_low (value : UInt16) : (signExtend16 value).toNat % 2 ^ 16 = value.toNat := by
  unfold signExtend16
  have bound := value.toNat_lt_size
  split
  · simp only [UInt16.toNat_toUInt64]
    exact Nat.mod_eq_of_lt bound
  · rw [UInt64.toNat_or, Nat.or_mod_two_pow]
    simp only [UInt16.toNat_toUInt64]
    rw [Nat.mod_eq_of_lt bound]
    simp

theorem signExtend32_low (value : UInt32) : (signExtend32 value).toNat % 2 ^ 32 = value.toNat := by
  unfold signExtend32
  have bound := value.toNat_lt_size
  split
  · simp only [UInt32.toNat_toUInt64]
    exact Nat.mod_eq_of_lt bound
  · rw [UInt64.toNat_or, Nat.or_mod_two_pow]
    simp only [UInt32.toNat_toUInt64]
    rw [Nat.mod_eq_of_lt bound]
    simp

/-- An immediate's canonical value keeps the bits its field carries. -/
theorem norm_low (kind : ImmKind) (value : Word) (present : kind ≠ .none) :
    (kind.norm value).toNat % 256 ^ kind.bytes = value.toNat % 256 ^ kind.bytes := by
  cases kind with
  | none => contradiction
  | imm8 =>
      simp only [ImmKind.norm, ImmKind.bytes]
      rw [show (256 : Nat) ^ 1 = 2 ^ 8 from rfl, signExtend8_low, UInt64.toNat_toUInt8]
  | imm16 =>
      simp only [ImmKind.norm, ImmKind.bytes]
      rw [show (256 : Nat) ^ 2 = 2 ^ 16 from rfl, signExtend16_low, UInt64.toNat_toUInt16]
  | imm32 =>
      simp only [ImmKind.norm, ImmKind.bytes]
      rw [show (256 : Nat) ^ 4 = 2 ^ 32 from rfl, signExtend32_low, UInt64.toNat_toUInt32]
  | imm64 => rfl

theorem norm_signExtend32 (value : Imm32) : ImmKind.imm32.norm (signExtend32 value) = signExtend32 value := by
  simp only [ImmKind.norm]
  congr 1
  apply UInt32.toNat_inj.mp
  rw [UInt64.toNat_toUInt32, signExtend32_low]

theorem norm_truncate (kind : ImmKind) (width : Width) (value : Word) (present : kind ≠ .none)
    (exact : 256 ^ kind.bytes = 2 ^ width.bits) : width.truncate (kind.norm value) = width.truncate value := by
  apply truncate_congr
  have low := norm_low kind value present
  rwa [exact] at low

theorem fullImm_truncate (width : Width) (value : Imm32) :
    width.truncate ((Table.fullImm width).norm (signExtend32 value)) = width.truncate (signExtend32 value) := by
  cases width with
  | w8 => exact norm_truncate .imm8 .w8 _ (by decide) rfl
  | w16 => exact norm_truncate .imm16 .w16 _ (by decide) rfl
  | w32 => exact norm_truncate .imm32 .w32 _ (by decide) rfl
  | w64 => simp only [Table.fullImm, norm_signExtend32]

theorem moveImm_truncate (width : Width) (value : Word) :
    width.truncate ((Table.moveImm width).norm value) = width.truncate value := by
  cases width with
  | w8 => exact norm_truncate .imm8 .w8 _ (by decide) rfl
  | w16 => exact norm_truncate .imm16 .w16 _ (by decide) rfl
  | w32 => exact norm_truncate .imm32 .w32 _ (by decide) rfl
  | w64 => rfl

/-! ## Signed displacements -/

theorem spill_bound (slot : StackSlot) : 0 < slot.displacement.toNat ∧ slot.displacement.toNat < 2 ^ 31 := by
  have bound := slot.index.toNat_lt_size
  simp only [StackSlot.displacement, UInt64.toNat_mul, UInt64.toNat_add, UInt16.toNat_toUInt64]
  change 0 < (((slot.index.toNat + 1) % 18446744073709551616) * 8) % 18446744073709551616 ∧
    (((slot.index.toNat + 1) % 18446744073709551616) * 8) % 18446744073709551616 < 2147483648
  simp only [UInt16.size] at bound
  omega


theorem signExtend32_ofInt_of_bounds (value : Int) (low : -(2 ^ 31 : Int) ≤ value) (high : value < 2 ^ 31) :
    (signExtend32 (Int32.ofInt value).toUInt32).toBitVec = BitVec.ofInt 64 value := by
  rw [signExtend32_bits]
  change (BitVec.ofInt 32 value).signExtend 64 = _
  unfold BitVec.signExtend
  rw [BitVec.toInt_ofInt_eq_self (by decide : 0 < 32) low high]

theorem signExtend32_neg (value : Word) (bound : value.toNat < 2 ^ 31) :
    signExtend32 (0 - value).toUInt32 = 0 - value := by
  have raw : (Int32.ofInt (-(value.toNat : Int))).toUInt32 = (0 - value).toUInt32 := by
    apply UInt32.toBitVec_inj.mp
    simp [UInt64.toBitVec_toUInt32, BitVec.neg_eq_not_add]
    rfl
  apply UInt64.toBitVec_inj.mp
  rw [← raw, signExtend32_ofInt_of_bounds _ (by omega) (by omega)]
  simp [BitVec.ofInt_neg]

@[simp] theorem spillAddress_eval (slot : StackSlot) (core : Core) :
    (spillAddress slot).eval core = core.readReg .rbp - slot.displacement := by
  simp only [spillAddress, MemAddr.eval, UInt64.add_zero]
  rw [signExtend32_neg _ (spill_bound slot).2]
  simp [UInt64.sub_eq_add_neg]

/-! ## Compact immediates -/

theorem fitsImm8_truncate {width : Width} {value : Word} (fits : fitsImm8 width value = true) :
    width.truncate (ImmKind.imm8.norm value) = width.truncate value := by
  simp only [fitsImm8, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at fits
  exact fits.2

theorem fitsImm8_narrow {width : Width} {value : Word} (fits : fitsImm8 width value = true) :
    width ≠ .w8 := by
  simp only [fitsImm8, Bool.and_eq_true, bne_iff_ne, ne_eq] at fits
  exact fits.1

end Compilatrix.X86.Encode
