import IxCC.Xv.Select.Basic
import IxCC.Xv.Select.Cond
import IxCC.Lir.Semantics
import IxCC.X86.ByteFlags

/-!
# Selection lemmas proved now

The per-rule facts that are cheap to state and prove on their own:
the flag producers the branch rules pick decide exactly the Lir condition.

- `condX86_holds`, `swapCond_holds`: the ten comparisons are x86
  conditions, and swapping operands swaps the condition (rule 1).
- `cmp_test`: the `cmp` row's flags, tested as the `jcc` row tests them,
  are the Lir comparison (rules 1 and 3).
- `and_test_tz`, `and_test_tnz`: the flags of `and`, which the `test` row
  computes too, give the Lir tag test through the zero flag (rule 2).
- `test_self_flags`, `test_self_test`: `test a, a` sets the flags of
  `cmp a, 0`, so it decides every comparison with zero (rule 1).
- `add_carry`, `sub_borrow`: `jb`/`jc` after the 64-bit `add` or `sub` row
  is Lir's `brOvf` carry or borrow (rule 4).
- `imm8?_low`, `immFull?_low`: a selected immediate has the Lir constant's
  low bits (rules 1, 4, 5 and 6).

`Fences.Xv` pins them to the standard axioms. -/

namespace IxCC.Xv.Select

open IxCC.X86

theorem condX86_holds {c : Lir.Cond} {cx : Condition} (h : condX86 c = some cx) (w : Width) (a b : Word) :
    cx.holds w a b = c.holds w a b := by
  cases c <;> simp only [condX86, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

private theorem word_beq_comm (x y : Word) : (x == y) = (y == x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact eq_comm

theorem swapCond_holds (c : Condition) (w : Width) (a b : Word) :
    (swapCond c).holds w b a = c.holds w a b := by
  cases c <;> simp only [swapCond, Condition.holds, bne] <;>
    first
    | rfl
    | rw [word_beq_comm]

theorem cmp_test {c : Lir.Cond} {cx : Condition} (h : condX86 c = some cx) (w : Width) (a b : Word) :
    (ByteEval.aluFlags .sub w a b).test cx = some (c.holds w a b) := by
  rw [ByteEval.compare_flags, condX86_holds h]

theorem sub_borrow (a b : Word) :
    (ByteEval.aluFlags .sub .w64 a b).test .unsignedLt = some (Lir.Ovf.eval .subB a b).2 := by
  rw [ByteEval.compare_flags]
  simp [Condition.holds, Lir.Ovf.eval]

theorem add_carry (a b : Word) :
    (ByteEval.aluFlags .add .w64 a b).test .unsignedLt = some (Lir.Ovf.eval .addC a b).2 := by
  simp only [ByteEval.aluFlags, ByteEval.addFlags, ByteEval.resultFlags, ByteEval.Flags.test,
    Lir.Ovf.eval, Option.some.injEq, Width.bits, BitVec.setWidth_eq, BitVec.uaddOverflow]
  have ha := a.toNat_lt_size
  have hb := b.toNat_lt_size
  simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_toBitVec, UInt64.size] at *
  by_cases hc : 2 ^ 64 ≤ a.toNat + b.toNat <;> simp [hc] <;> omega

private theorem and_zero (w : Width) (a b : Word) :
    ((a.toBitVec.setWidth w.bits &&& b.toBitVec.setWidth w.bits) == 0) = (w.truncate (a &&& b) == 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, ← BitVec.setWidth_and, ← UInt64.toBitVec_and, ← UInt64.toBitVec_inj,
    Encode.truncate_bits, UInt64.toBitVec_zero, BitVec.toNat_eq, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have := (a &&& b).toBitVec.isLt
  cases w <;> simp [Width.bits] <;> omega

theorem and_test_tz (w : Width) (a b : Word) :
    (ByteEval.aluFlags .and w a b).test .eq = some (Lir.Cond.holds .tz w a b) := by
  simp only [ByteEval.aluFlags, ByteEval.resultFlags, ByteEval.Flags.test, Lir.Cond.holds, and_zero]

theorem and_test_tnz (w : Width) (a b : Word) :
    (ByteEval.aluFlags .and w a b).test .ne = some (Lir.Cond.holds .tnz w a b) := by
  simp only [ByteEval.aluFlags, ByteEval.resultFlags, ByteEval.Flags.test, Lir.Cond.holds, and_zero,
    Option.map_some, bne]

/-- `test a, a` sets the flags `cmp a, 0` sets. -/
theorem test_self_flags (w : Width) (a : Word) :
    ByteEval.aluFlags .and w a a = ByteEval.aluFlags .sub w a 0 := by
  simp only [ByteEval.aluFlags, ByteEval.subFlags, ByteEval.resultFlags, BitVec.and_self]
  generalize a.toBitVec.setWidth w.bits = x
  have z : (0 : Word).toBitVec.setWidth w.bits = 0#w.bits := by simp
  rw [z, BitVec.sub_zero]
  have hu : BitVec.usubOverflow x 0#w.bits = false := by simp [BitVec.usubOverflow]
  have hs : BitVec.ssubOverflow x 0#w.bits = false := by
    have h1 := x.toInt_lt
    have h2 := x.le_toInt
    simp [BitVec.ssubOverflow]
    omega
  rw [hu, hs]

/-- Rule 1's zero test: `test a, a` decides every comparison with 0. -/
theorem test_self_test {c : Lir.Cond} {cx : Condition} (h : condX86 c = some cx) (w : Width) (a : Word) :
    (ByteEval.aluFlags .and w a a).test cx = some (c.holds w a 0) := by
  rw [test_self_flags, cmp_test h]

theorem imm8?_low {w : Width} {k c : Word} (h : imm8? w k = some c) : w.truncate c = w.truncate k := by
  unfold imm8? at h
  split at h
  · cases h
    exact Encode.fitsImm8_truncate ‹_›
  · cases h

theorem immFull?_low {w : Width} {k c : Word} (h : immFull? w k = some c) : w.truncate c = w.truncate k := by
  simp only [immFull?] at h
  split at h
  · rename_i fits
    cases h
    exact beq_iff_eq.mp fits
  · cases h

end IxCC.Xv.Select
