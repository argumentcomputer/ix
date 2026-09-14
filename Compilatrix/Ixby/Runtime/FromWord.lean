import Compilatrix.Ixby.Runtime.Nibble

/-! Exact Nat reconstruction through the emitted word loop. Capacity covers
both the mathematical result and the final weight, which is computed even on
the last nonzero iteration. -/

namespace Compilatrix.Ixby.Runtime.Conversion

open Ix.Ixby Execution Representation ScalarFunction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem fromWordLoop_zero {program : Program} {id digit : FunctionId}
    (checked : Checked program id (fromWordLoop id digit)) (limits : Limits)
    (room : 10 ≤ limits.locals) (weight accumulator : Nat)
    (continuation : Array Continuation) :
    Reaches limits program
      (frameState id 0 #[.scalar (.word32 0), .scalar (.nat weight), .scalar (.nat accumulator)]
        continuation)
      (returned (.scalar (.nat accumulator)) continuation) := by
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 3) (count := 0)
  iterate 3
    rw [runChunk]
    simp [step, stepEval, Frame.check, checked.code, fromWordLoop, frameState, returned,
      evalOp, Frame.readOperands, Frame.read, Frame.transfer, Primitive.eval,
      Primitive.arity, N, W, localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem fromWordLoop_returns {program : Program} {id digit : FunctionId}
    (checked : Checked program id (fromWordLoop id digit))
    (digits : Checked program digit (nibble false)) (limits : Limits)
    (room : 10 ≤ limits.locals) (capacity : 5 ≤ limits.natBits)
    (fuel : Nat) (word : UInt32) (weight accumulator : Nat)
    (remaining : word.toNat < 16 ^ fuel)
    (resultValid : (Scalar.nat (accumulator + word.toNat * weight)).validate limits = .ok ())
    (weightValid : (Scalar.nat (weight * 16 ^ fuel)).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size < limits.continuations) :
    Reaches limits program
      (frameState id 0 #[.scalar (.word32 word), .scalar (.nat weight), .scalar (.nat accumulator)]
        continuation)
      (returned (.scalar (.nat (accumulator + word.toNat * weight))) continuation) := by
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  have smallNat (k : Nat) (small : k ≤ 16) : (Scalar.nat k).validate limits = .ok () :=
    validate_nat_of_lt (Nat.lt_of_lt_of_le (by omega : k < 2 ^ 5)
      (Nat.pow_le_pow_right (by decide : 0 < 2) capacity))
  induction fuel generalizing word weight accumulator with
  | zero =>
    have zero : word = 0 := by
      apply UInt32.toNat.inj
      simp only [Nat.pow_zero] at remaining
      change word.toNat = 0
      omega
    subst word
    simpa using fromWordLoop_zero checked limits room weight accumulator continuation
  | succ fuel ih =>
    by_cases zero : word = 0
    · subst word
      simpa using fromWordLoop_zero checked limits room weight accumulator continuation
    · have notZero : (word == 0) = false := beq_eq_false_iff_ne.mpr zero
      let digitValue := (word &&& (15 : UInt32)).toNat
      have digitBound : digitValue ≤ word.toNat := by
        simpa only [digitValue, word_and_fifteen] using Nat.mod_le word.toNat 16
      have digitSmall : digitValue < 16 := by
        simpa only [digitValue, word_and_fifteen] using Nat.mod_lt word.toNat (by decide : 0 < 16)
      have digitValid := smallNat digitValue (by omega)
      have mulValid := validate_nat_mono
        (Nat.le_trans (Nat.mul_le_mul_right weight digitBound)
          (Nat.le_add_left (word.toNat * weight) accumulator)) resultValid
      have accValid := validate_nat_mono (Nat.le_add_right accumulator (word.toNat * weight)) resultValid
      have nextAccValid := validate_nat_mono
        (Nat.add_le_add_left (Nat.mul_le_mul_right weight digitBound) accumulator) resultValid
      have nextWeightBound : weight * 16 ≤ weight * 16 ^ (fuel + 1) := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_right (by decide : 0 < 16) (show 1 ≤ fuel + 1 by omega)
      have nextWeightValid := validate_nat_mono nextWeightBound weightValid
      have inputWeightValid := validate_nat_mono
        (Nat.le_trans (Nat.le_mul_of_pos_right weight (by decide : 0 < 16)) nextWeightBound) weightValid
      let saved : Frame := { function := id, block := 5, locals :=
        #[.scalar (.word32 word), .scalar (.nat weight), .scalar (.nat accumulator),
          .scalar (.bool false), .scalar (.word32 (word &&& 15))] }
      let value : Value := .scalar (.nat digitValue)
      have beforeCall : Reaches limits program
          (frameState id 0 #[.scalar (.word32 word), .scalar (.nat weight),
            .scalar (.nat accumulator)] continuation)
          (frameState digit 0 #[.scalar (.word32 (word &&& 15))]
            (continuation.push (.resume saved))) := by
        apply reaches_of_chunk (fuel := 4) (count := 0)
        iterate 4
          rw [runChunk]
          simp [step, stepEval, Frame.check, checked.code, digits.code, fromWordLoop, nibble,
            frameState, saved, evalOp, Frame.readOperands, Frame.read, Frame.transfer,
            State.push, enter, Primitive.eval, Primitive.arity, N, W,
            localRoom, notZero, Nat.not_le.mpr stack, bind, Except.bind, pure, Except.pure]
        rfl
      have digitPath := nibbleNat_returns digits limits (by omega) (word &&& 15)
        digitSmall (continuation.push (.resume saved))
      have resumed : Reaches limits program
          (returned value (continuation.push (.resume saved)))
          (frameState id 5 (saved.locals ++ #[value]) continuation) := by
        apply Execution.resume
        simp [Frame.transfer, Frame.check, checked.code, fromWordLoop, saved, value,
          localRoom, bind, Except.bind, pure, Except.pure]
      have suffix : Reaches limits program
          (frameState id 5 (saved.locals ++ #[value]) continuation)
          (frameState id 0 #[.scalar (.word32 (word >>> 4)), .scalar (.nat (weight * 16)),
            .scalar (.nat (accumulator + digitValue * weight))] continuation) := by
        apply reaches_of_chunk (fuel := 5) (count := 0)
        iterate 5
          rw [runChunk]
          simp [step, stepEval, Frame.check, checked.code, fromWordLoop, frameState, saved, value,
            evalOp, Frame.readOperands, Frame.read, Frame.transfer, enter,
            Primitive.eval, Primitive.arity, N, W, localRoom, smallNat, digitValid,
            inputWeightValid, mulValid, accValid, nextAccValid, nextWeightValid,
            bind, Except.bind, pure, Except.pure]
        rfl
      have nextRemaining : (word >>> (4 : UInt32)).toNat < 16 ^ fuel := by
        rw [word_shr_four, Nat.div_lt_iff_lt_mul (by decide)]
        simpa [Nat.pow_succ] using remaining
      have invariant : accumulator + digitValue * weight +
          (word >>> (4 : UInt32)).toNat * (weight * 16) = accumulator + word.toNat * weight := by
        simpa only [digitValue, word_and_fifteen, word_shr_four] using
          fromWord_nibble word weight accumulator
      have nextResultValid : (Scalar.nat (accumulator + digitValue * weight +
          (word >>> (4 : UInt32)).toNat * (weight * 16))).validate limits = .ok () := by
        rw [invariant]
        exact resultValid
      have nextWeight : (Scalar.nat ((weight * 16) * 16 ^ fuel)).validate limits = .ok () := by
        simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using weightValid
      have recursive := ih (word >>> 4) (weight * 16) (accumulator + digitValue * weight)
        nextRemaining nextResultValid nextWeight
      have complete := beforeCall.trans (digitPath.trans (resumed.trans (suffix.trans recursive)))
      simpa only [invariant] using complete

end Compilatrix.Ixby.Runtime.Conversion
