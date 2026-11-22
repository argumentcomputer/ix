import IxCC.X86.ByteEval
import IxCC.X86.EncodeWord

/-! Comparison flags agree with all ten emitted typed conditions. -/

namespace IxCC.X86.ByteEval

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

theorem merge_allSet (before computed : Flags) : before.merge Table.allSet computed = computed := by
  cases computed
  rfl

theorem restrict_nil (flags : Flags) : flags.restrict [] = {} := by
  cases flags
  rfl

/-- A condition reads only the flags it names. -/
theorem test_congr {first second : Flags} (condition : Condition)
    (same : ∀ flag ∈ condition.reads, first.get flag = second.get flag) :
    first.test condition = second.test condition := by
  cases condition <;>
    simp only [Condition.reads, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
      Flags.get] at same <;>
    simp only [Flags.test, same]

theorem merge_get_set {effect : Flag → FlagEffect} {flag : Flag} (set : effect flag = .set)
    (before computed : Flags) : (before.merge effect computed).get flag = computed.get flag := by
  cases flag <;> simp [Flags.merge, Flags.get, set, FlagEffect.pick]

/-- The flags a row sets do not depend on the flags before it: a consumer
that reads only set flags sees the same values from any earlier flags. -/
theorem test_merge_set {condition : Condition} {effect : Flag → FlagEffect}
    (set : ∀ flag ∈ condition.reads, effect flag = .set) (before other computed : Flags) :
    (before.merge effect computed).test condition = (other.merge effect computed).test condition :=
  test_congr condition fun flag member => by
    rw [merge_get_set (set flag member), merge_get_set (set flag member)]

theorem restrict_merge_set {reads : List Flag} {effect : Flag → FlagEffect}
    (set : ∀ flag ∈ reads, effect flag = .set) (before other computed : Flags) :
    (before.merge effect computed).restrict reads = (other.merge effect computed).restrict reads := by
  have same : ∀ flag, reads.contains flag = true →
      (before.merge effect computed).get flag = (other.merge effect computed).get flag := fun flag found => by
    rw [merge_get_set (set flag (List.contains_iff_mem.mp found)),
      merge_get_set (set flag (List.contains_iff_mem.mp found))]
  have cf := same .cf
  have zf := same .zf
  have sf := same .sf
  have of := same .of
  simp only [Flags.get] at cf zf sf of
  simp only [Flags.restrict]
  congr 1 <;> split <;> simp_all

end IxCC.X86.ByteEval

namespace IxCC.X86

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

theorem condition_congr (condition : Condition) (width : Width) (left first second : Word)
    (equal : width.truncate first = width.truncate second) :
    condition.holds width left first = condition.holds width left second := by
  cases condition <;> simp [Condition.holds, Width.signedValue, equal]

/-- The value a comparison's row compares against: its register, or its
immediate at the row's canonical width (imm8 when the value fits). -/
def Compare.operand (comparison : Compare) (core : Core) : Word :=
  match comparison.right with
  | .reg register => core.readReg register
  | .imm value =>
      if fitsImm8 comparison.width (signExtend32 value) then ImmKind.imm8.norm (signExtend32 value)
      else (Table.fullImm comparison.width).norm (signExtend32 value)

theorem Compare.operand_low (comparison : Compare) (core : Core) :
    comparison.width.truncate (comparison.operand core) = comparison.width.truncate (comparison.right.eval core) := by
  cases comparison with
  | mk width left right =>
    cases right with
    | reg register => rfl
    | imm value =>
        simp only [Compare.operand]
        split
        · exact Encode.fitsImm8_truncate ‹_›
        · exact Encode.fullImm_truncate width value

/-- The `cmp` row reads its operands, leaves the core unchanged and sets
the four flags of the subtraction. -/
theorem Compare.exec_eq (comparison : Compare) (core : Core) (flags : ByteEval.Flags) :
    comparison.row.1.exec comparison.row.2 core flags =
      .ok (core, ByteEval.aluFlags .sub comparison.width (core.readReg comparison.left) (comparison.operand core)) := by
  cases comparison with
  | mk width left right =>
    cases right with
    | reg register =>
        simp [Compare.row, Compare.operand, Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.arithDesc, Table.cmpArith, Table.Arith.sem,
          Table.Arith.role, Table.rmSlot, Table.regSlot, Table.cmpSem, readSlots, writeSlots, Arg.load,
          ByteEval.merge_allSet, Except.mapError]
    | imm value =>
        simp only [Compare.row, aluImmRow, Compare.operand]
        split <;>
        simp [Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.arithDesc, Table.cmpArith,
          Table.Arith.sem, Table.Arith.role, Table.rmSlot, Table.immSlot, Table.cmpSem, readSlots, writeSlots,
          Arg.load, ByteEval.merge_allSet, Except.mapError]

theorem Compare.flags_eq (comparison : Compare) (core : Core) :
    comparison.flags core =
      ByteEval.aluFlags .sub comparison.width (core.readReg comparison.left) (comparison.operand core) := by
  simp [Compare.flags, Compare.exec_eq]

/-- The table semantics of compare-and-branch is the mathematical condition
on the operands' low `width` bits. -/
theorem Compare.holds_eq (comparison : Compare) (condition : Condition) (core : Core) :
    comparison.holds condition core =
      condition.holds comparison.width (core.readReg comparison.left) (comparison.right.eval core) := by
  rw [Compare.holds, Compare.flags_eq, ByteEval.compare_flags, Option.getD_some]
  exact condition_congr _ _ _ _ _ (Compare.operand_low comparison core)

theorem Compare.flags_test (comparison : Compare) (condition : Condition) (core : Core) :
    (comparison.flags core).test condition = some (comparison.holds condition core) := by
  rw [Compare.holds, Compare.flags_eq, ByteEval.compare_flags, Option.getD_some]

/-- A compare-and-branch goes where its comparison's condition says. -/
theorem executeTerminator_compare (checked : Checked) (comparison : Compare) (condition : Condition)
    (yes no : BlockId) (machine : Machine) :
    executeTerminator checked (.compare comparison condition yes no) machine =
      machine.goto checked (if comparison.holds condition machine.core then yes else no) := by
  have test := Compare.flags_test comparison condition machine.core
  rw [Compare.flags_eq] at test
  simp only [Terminator.compare, executeTerminator, Compare.exec_eq, test]

/-- `FusedOk` as a statement about flag effects. -/
theorem FusedOk.set {producer consumer : Op} (fused : FusedOk producer consumer = true) :
    ∀ flag ∈ (desc consumer).flagsIn, (desc producer).flagsOut flag = .set := by
  intro flag member
  simpa using List.all_eq_true.mp fused flag member

@[simp] theorem jcc_flagsIn (condition : Condition) : (desc (Op.jccRel32 condition)).flagsIn = condition.reads := rfl

end IxCC.X86
