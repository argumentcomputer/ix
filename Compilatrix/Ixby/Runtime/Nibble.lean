import Compilatrix.Ixby.Runtime.ConversionLaws

namespace Compilatrix.Ixby.Runtime.Conversion

open Ix.Ixby Execution ScalarFunction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem nibbleWord_returns {program : Program} {id : FunctionId}
    (checked : Checked program id (nibble true)) (limits : Limits)
    (room : 5 ≤ limits.locals) (capacity : 4 ≤ limits.natBits)
    (n : Nat) (small : n < 16) (continuation : Array Continuation) :
    Reaches limits program (frameState id 0 #[.scalar (.nat n)] continuation)
      (returned (.scalar (.word32 n.toUInt32)) continuation) := by
  have localRoom : ∀ k, k ≤ 5 → ¬limits.locals < k := by omega
  have nats (k : Nat) (small : k < 16) : (Scalar.nat k).validate limits = .ok () :=
    validate_nat_of_lt (Nat.lt_of_lt_of_le small
      (Nat.pow_le_pow_right (by decide : 0 < 2) capacity))
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply reaches_of_chunk (fuel := 9) (count := 0)
    iterate 9
      rw [runChunk]
      simp [step, stepEval, Frame.check, checked.code, nibble, frameState,
        returned, evalOp, Frame.readOperands, Frame.read, Frame.transfer,
        Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, N, W,
        localRoom, nats, bind, Except.bind, pure, Except.pure]
    rfl

private theorem nibbleNat_returns_nat {program : Program} {id : FunctionId}
    (checked : Checked program id (nibble false)) (limits : Limits)
    (room : 5 ≤ limits.locals)
    (n : Nat) (small : n < 16) (continuation : Array Continuation) :
    Reaches limits program (frameState id 0 #[.scalar (.word32 n.toUInt32)] continuation)
      (returned (.scalar (.nat n)) continuation) := by
  have localRoom : ∀ k, k ≤ 5 → ¬limits.locals < k := by omega
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply reaches_of_chunk (fuel := 9) (count := 0)
    iterate 9
      rw [runChunk]
      simp [step, stepEval, Frame.check, checked.code, nibble, frameState,
        returned, evalOp, Frame.readOperands, Frame.read, Frame.transfer,
        Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, N, W,
        localRoom, bind, Except.bind, pure, Except.pure]
    rfl


theorem nibbleNat_returns {program : Program} {id : FunctionId}
    (checked : Checked program id (nibble false)) (limits : Limits)
    (room : 5 ≤ limits.locals) (word : UInt32) (small : word.toNat < 16)
    (continuation : Array Continuation) :
    Reaches limits program (frameState id 0 #[.scalar (.word32 word)] continuation)
      (returned (.scalar (.nat word.toNat)) continuation) := by
  simpa only [Nat.toUInt32, UInt32.ofNat_toNat] using
    nibbleNat_returns_nat checked limits room word.toNat small continuation

end Compilatrix.Ixby.Runtime.Conversion
