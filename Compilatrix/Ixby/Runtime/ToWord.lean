import Compilatrix.Ixby.Runtime.Nibble

/-! Termination and exact low-word agreement for the emitted Nat conversion.
The recursive call is the actual tail-call instruction, and the nibble helper
executes with a saved caller continuation. -/

namespace Compilatrix.Ixby.Runtime.Conversion

open Ix.Ixby Execution Representation ScalarFunction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem toWord_returns {program : Program} {id digit : FunctionId}
    (checked : Checked program id (toWord id digit))
    (digits : Checked program digit (nibble true)) (limits : Limits)
    (room : 11 ≤ limits.locals) (capacity : 5 ≤ limits.natBits)
    (n : Nat) (weight accumulator : UInt32)
    (valid : (Scalar.nat n).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size < limits.continuations) :
    Reaches limits program
      (frameState id 0 #[.scalar (.nat n), .scalar (.word32 weight), .scalar (.word32 accumulator)]
        continuation)
      (returned (.scalar (.word32 (accumulator + n.toUInt32 * weight))) continuation) := by
  have localRoom : ∀ k, k ≤ 11 → ¬limits.locals < k := by omega
  have smallNat (k : Nat) (small : k ≤ 16) : (Scalar.nat k).validate limits = .ok () :=
    validate_nat_of_lt (Nat.lt_of_lt_of_le (by omega : k < 2 ^ 5)
      (Nat.pow_le_pow_right (by decide : 0 < 2) capacity))
  induction n using Nat.strongRecOn generalizing weight accumulator with
  | ind n ih =>
    by_cases zero : n = 0
    · subst n
      apply reaches_of_chunk (fuel := 3) (count := 0)
      iterate 3
        rw [runChunk]
        simp [step, stepEval, Frame.check, checked.code, toWord, frameState, returned,
          evalOp, Frame.readOperands, Frame.read, Frame.transfer, Primitive.eval,
          Primitive.arity, N, W, localRoom, smallNat, bind, Except.bind, pure, Except.pure]
      rfl
    · by_cases done : weight = 0
      · subst weight
        apply reaches_of_chunk (fuel := 5) (count := 0)
        iterate 5
          rw [runChunk]
          simp [step, stepEval, Frame.check, checked.code, toWord, frameState, returned,
            evalOp, Frame.readOperands, Frame.read, Frame.transfer, Primitive.eval,
            Primitive.arity, N, W, localRoom, smallNat, valid, zero,
            bind, Except.bind, pure, Except.pure]
        rfl
      · have notZero : (n == 0) = false := beq_eq_false_iff_ne.mpr zero
        have notDone : (weight == 0) = false := beq_eq_false_iff_ne.mpr done
        have modValid := validate_nat_mono (Nat.mod_le n 16) valid
        have divValid := validate_nat_mono (Nat.div_le_self n 16) valid
        let saved : Frame := { function := id, block := 8, locals :=
          #[.scalar (.nat n), .scalar (.word32 weight), .scalar (.word32 accumulator),
            .scalar (.bool false), .scalar (.bool false), .scalar (.nat (n % 16))] }
        let value : Value := .scalar (.word32 (n % 16).toUInt32)
        have beforeCall : Reaches limits program
            (frameState id 0 #[.scalar (.nat n), .scalar (.word32 weight),
              .scalar (.word32 accumulator)] continuation)
            (frameState digit 0 #[.scalar (.nat (n % 16))]
              (continuation.push (.resume saved))) := by
          apply reaches_of_chunk (fuel := 6) (count := 0)
          iterate 6
            rw [runChunk]
            simp [step, stepEval, Frame.check, checked.code, digits.code, toWord, nibble,
              frameState, saved, evalOp, Frame.readOperands, Frame.read, Frame.transfer,
              State.push, enter, Primitive.eval, Primitive.arity, N, W,
              localRoom, smallNat, valid, modValid, notZero, notDone, Nat.not_le.mpr stack,
              bind, Except.bind, pure, Except.pure]
          rfl
        have digitPath := nibbleWord_returns digits limits (by omega) (by omega)
          (n % 16) (Nat.mod_lt n (by decide)) (continuation.push (.resume saved))
        have resumed : Reaches limits program
            (returned value (continuation.push (.resume saved)))
            (frameState id 8 (saved.locals ++ #[value]) continuation) := by
          apply Execution.resume
          simp [Frame.transfer, Frame.check, checked.code, toWord, saved, value,
            localRoom, bind, Except.bind, pure, Except.pure]
        have suffix : Reaches limits program
            (frameState id 8 (saved.locals ++ #[value]) continuation)
            (frameState id 0 #[.scalar (.nat (n / 16)), .scalar (.word32 (weight * 16)),
              .scalar (.word32 (accumulator + (n % 16).toUInt32 * weight))] continuation) := by
          apply reaches_of_chunk (fuel := 5) (count := 0)
          iterate 5
            rw [runChunk]
            simp [step, stepEval, Frame.check, checked.code, toWord, frameState, saved, value,
              evalOp, Frame.readOperands, Frame.read, Frame.transfer, enter,
              Primitive.eval, Primitive.arity, N, W, localRoom, smallNat, valid, divValid,
              word_shl_four, bind, Except.bind, pure, Except.pure]
          rfl
        have recursive := ih (n / 16) (Nat.div_lt_self (by omega) (by decide))
          (weight * 16) (accumulator + (n % 16).toUInt32 * weight) divValid
        have complete := beforeCall.trans (digitPath.trans (resumed.trans (suffix.trans recursive)))
        simpa only [toWord_nibble] using complete

end Compilatrix.Ixby.Runtime.Conversion
