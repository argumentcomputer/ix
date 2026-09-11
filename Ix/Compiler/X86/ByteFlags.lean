import Ix.Compiler.X86.ByteEval
import Ix.Compiler.X86.EncodeWord

/-! Comparison flags agree with all ten emitted typed conditions. -/

namespace Ix.Compiler.X86.ByteEval

theorem sub_zero (left right : BitVec bits) : (left - right == 0) = (left == right) := by
  simp [Bool.beq_eq_decide_eq, BitVec.sub_eq_iff_eq_add]

theorem sub_signed_less (left right : BitVec bits) :
    ((left - right).msb ^^ BitVec.ssubOverflow left right) = decide (left.toInt < right.toInt) := by
  by_cases under : left.toInt - right.toInt < -2 ^ (bits - 1)
  · have wrap := BitVec.toInt_sub_toInt_lt_twoPow_iff.mp under
    simp [BitVec.msb_eq_toInt, BitVec.toInt_sub, BitVec.ssubOverflow, under,
      show ¬(left.toInt - right.toInt).bmod (2 ^ bits) < 0 by omega,
      show left.toInt < right.toInt by omega]
  · by_cases over : 2 ^ (bits - 1) ≤ left.toInt - right.toInt
    · have wrap := BitVec.twoPow_le_toInt_sub_toInt_iff.mp over
      simp [BitVec.msb_eq_toInt, BitVec.toInt_sub, BitVec.ssubOverflow, under, over,
        wrap.2.2, show ¬left.toInt < right.toInt by omega]
    · have clean : ¬BitVec.ssubOverflow left right := by
        simp [BitVec.ssubOverflow, under, over]
      rw [BitVec.msb_eq_toInt, BitVec.toInt_sub_of_not_ssubOverflow clean]
      simp [BitVec.ssubOverflow, under, over]
      omega

def conditionBits (condition : Condition) (left right : BitVec bits) : Bool :=
  match condition with
  | .eq => left == right
  | .ne => left != right
  | .unsignedLt => decide (left.toNat < right.toNat)
  | .unsignedLe => decide (left.toNat ≤ right.toNat)
  | .unsignedGt => decide (right.toNat < left.toNat)
  | .unsignedGe => decide (right.toNat ≤ left.toNat)
  | .signedLt => decide (left.toInt < right.toInt)
  | .signedLe => decide (left.toInt ≤ right.toInt)
  | .signedGt => decide (right.toInt < left.toInt)
  | .signedGe => decide (right.toInt ≤ left.toInt)

theorem sub_test (condition : Condition) (left right : BitVec bits) :
    (subFlags left right).test condition = some (conditionBits condition left right) := by
  cases condition <;>
    simp only [Flags.test, subFlags, resultFlags, conditionBits, sub_zero, sub_signed_less,
      BitVec.usubOverflow, bind, Option.bind, pure, Option.map_some, Option.some.injEq]
  all_goals
    apply Bool.eq_iff_iff.mpr
    first
    | solve | simp [← BitVec.toNat_inj, bne] <;> omega
    | solve | simp [← BitVec.toInt_inj] <;> omega

theorem signedValue_bits (width : Width) (value : Word) :
    width.signedValue value = (value.toBitVec.setWidth width.bits).toInt := by
  cases width <;>
    simp [Width.signedValue, Encode.truncate_nat, BitVec.toInt_eq_toNat_cond,
      BitVec.toNat_setWidth, Width.bits] <;>
    split <;> split <;> omega

theorem condition_agrees (condition : Condition) (width : Width) (left right : Word) :
    conditionBits condition (left.toBitVec.setWidth width.bits) (right.toBitVec.setWidth width.bits) =
      condition.holds width left right := by
  cases condition <;>
    simp [conditionBits, Condition.holds, signedValue_bits, UInt64.lt_iff_toNat_lt,
      UInt64.le_iff_toNat_le, Encode.truncate_nat, BitVec.toNat_setWidth,
      Bool.beq_eq_decide_eq, ← UInt64.toNat_inj, ← BitVec.toNat_inj, bne]

theorem compare_flags (condition : Condition) (width : Width) (left right : Word) :
    (aluFlags .sub width left right).test condition = some (condition.holds width left right) := by
  rw [aluFlags, sub_test, condition_agrees]

end Ix.Compiler.X86.ByteEval
