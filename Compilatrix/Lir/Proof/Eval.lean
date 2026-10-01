import Compilatrix.Lir.Proof.Steps
import Compilatrix.Lir.Proof.EvalAttr

/-!
# Lir expressions at width 64

Equations for `BinOp.eval`, `Cond.holds`, `Rhs.eval`, `Addr.eval` and
`Stmt.exec` at width 64 (where `Width.truncate` is the identity), tagged
`lir_eval`, so that a run of concrete statements over symbolic registers
evaluates by `simp only [lir_eval, env_insert_get, …]`.
-/

set_option autoImplicit false

namespace Compilatrix.Lir

attribute [lir_eval] execList Stmt.exec Rhs.eval Addr.eval Arg.eval_v Arg.eval_imm env_insert_get env_empty
  evalArgs_cons evalArgs_nil bindParams Option.bind_eq_bind Option.bind_some Option.map_eq_map Option.map_some
  Option.bind_none

@[lir_eval] theorem option_pure {α : Type} (a : α) : (pure a : Option α) = some a := rfl

@[lir_eval] theorem trunc64 (x : Word) : X86.Width.truncate .w64 x = x := by
  apply UInt64.toNat_inj.mp
  simp only [X86.Width.truncate, X86.Width.mask, UInt64.toNat_and]
  rw [show (UInt64.toNat 0xffffffffffffffff) = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt x.toNat_lt_size

variable (a b : Word)

@[lir_eval] theorem bin_add : BinOp.eval .add .w64 a b = some (a + b) := by simp [BinOp.eval, trunc64]
@[lir_eval] theorem bin_sub : BinOp.eval .sub .w64 a b = some (a - b) := by simp [BinOp.eval, trunc64]
@[lir_eval] theorem bin_and : BinOp.eval .and .w64 a b = some (a &&& b) := by simp [BinOp.eval, trunc64]
@[lir_eval] theorem bin_or : BinOp.eval .or .w64 a b = some (a ||| b) := by simp [BinOp.eval, trunc64]
@[lir_eval] theorem bin_xor : BinOp.eval .xor .w64 a b = some (a ^^^ b) := by simp [BinOp.eval, trunc64]
@[lir_eval] theorem bin_mul : BinOp.eval .mul .w64 a b = some (a * b) := by simp [BinOp.eval, trunc64]
@[lir_eval] theorem bin_shl : BinOp.eval .shl .w64 a b = some (a <<< (b &&& 63)) := by
  simp [BinOp.eval, trunc64, shiftMask]
@[lir_eval] theorem bin_shr : BinOp.eval .shr .w64 a b = some (a >>> (b &&& 63)) := by
  simp [BinOp.eval, trunc64, shiftMask]
@[lir_eval] theorem bin_udiv : BinOp.eval .udiv .w64 a b = if b = 0 then none else some (a / b) := by
  simp [BinOp.eval, trunc64]
@[lir_eval] theorem bin_urem : BinOp.eval .urem .w64 a b = if b = 0 then none else some (a % b) := by
  simp [BinOp.eval, trunc64]

@[lir_eval] theorem holds_eq : Cond.holds .eq .w64 a b = decide (a = b) := by
  simp only [Cond.holds, trunc64]; cases h : (a == b) <;> simp_all
@[lir_eval] theorem holds_ne : Cond.holds .ne .w64 a b = decide (a ≠ b) := by
  simp only [Cond.holds, trunc64]; cases h : (a == b) <;> simp_all [bne]
@[lir_eval] theorem holds_ult : Cond.holds .ult .w64 a b = decide (a < b) := by simp [Cond.holds, trunc64]
@[lir_eval] theorem holds_ule : Cond.holds .ule .w64 a b = decide (a ≤ b) := by simp [Cond.holds, trunc64]
@[lir_eval] theorem holds_ugt : Cond.holds .ugt .w64 a b = decide (b < a) := by simp [Cond.holds, trunc64]
@[lir_eval] theorem holds_uge : Cond.holds .uge .w64 a b = decide (b ≤ a) := by simp [Cond.holds, trunc64]
@[lir_eval] theorem holds_tz : Cond.holds .tz .w64 a b = decide (a &&& b = 0) := by
  simp only [Cond.holds, trunc64]; cases h : (a &&& b == 0) <;> simp_all
@[lir_eval] theorem holds_tnz : Cond.holds .tnz .w64 a b = decide (a &&& b ≠ 0) := by
  simp only [Cond.holds, trunc64]; cases h : (a &&& b == 0) <;> simp_all [bne]

/-- A signed test against zero is the top bit. -/
theorem holds_slt_zero : Cond.holds .slt .w64 a 0 = decide (2 ^ 63 ≤ a.toNat) := by
  simp only [Cond.holds, X86.Width.signedValue, trunc64, X86.Width.bits]
  have := a.toNat_lt_size
  simp only [UInt64.size] at this
  by_cases h : a.toNat < 2 ^ 63 <;> simp [h] <;> omega

@[lir_eval] theorem and63_one : (UInt64.ofNat 1 : Word) &&& 63 = 1 := by decide
@[lir_eval] theorem ofNat_one_word : (UInt64.ofNat 1 : Word) = 1 := rfl
@[lir_eval] theorem ofNat_zero_word : (UInt64.ofNat 0 : Word) = 0 := rfl
@[lir_eval] theorem one_and63 : (1 : Word) &&& 63 = 1 := by decide
@[lir_eval] theorem dispWord_one : dispWord 1 = 1 := by decide
@[lir_eval] theorem dispWord_zero : dispWord 0 = 0 := by decide
@[lir_eval] theorem scale_one : X86.Scale.one.word = 1 := rfl

/-- A small nonnegative displacement is that word. -/
theorem dispWord_ofNat (n : Nat) : dispWord (n : Int) = UInt64.ofNat n := by
  apply UInt64.toNat_inj.mp
  simp only [dispWord, UInt64.toNat_ofBitVec, BitVec.toNat_ofInt, UInt64.toNat_ofNat']
  omega

/-- A small negative displacement is the word's negation. -/
theorem dispWord_neg {n : Nat} (h : n ≤ 2 ^ 63) : dispWord (-(n : Int)) = 0 - UInt64.ofNat n := by
  apply UInt64.toNat_inj.mp
  simp only [dispWord, UInt64.toNat_ofBitVec, BitVec.toNat_ofInt, UInt64.toNat_sub, UInt64.toNat_ofNat']
  have h0 : (UInt64.toNat 0) = 0 := rfl
  rw [h0]
  omega

end Compilatrix.Lir
