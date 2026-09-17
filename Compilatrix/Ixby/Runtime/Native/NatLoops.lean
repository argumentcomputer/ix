import Compilatrix.Ixby.Runtime.Native.Scalars
import Compilatrix.Ixby.Runtime.NatPowLaws

/-! The unboxed halving and repeated-squaring loops preserve an arbitrary
caller continuation. Every multiplication is exact and separately bounded. -/

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby Execution Representation ScalarFunction Conversion NatLoops

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

variable {program : Program} (certificate : Certificate program) (limits : Limits)

include certificate

theorem Certificate.shiftRightLoop_returns (room : 6 ≤ limits.locals) (capacity : 2 ≤ limits.natBits)
    (n shift : Nat) (nValid : NatValid limits n) (shiftValid : NatValid limits shift)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 9 0 #[natural n, natural shift] continuation)
      (returned (natural (n >>> shift)) continuation) := by
  have code := (certificate.function 9).code
  change program.getFunction 9 = .ok Code.Ixby_Runtime_shiftRightLoop at code
  have localRoom : ∀ k, k ≤ 6 → ¬limits.locals < k := by omega
  have smallNat (k : Nat) (small : k ≤ 2) : (Scalar.nat k).validate limits = .ok () :=
    validate_nat_of_bits (by omega : k < 2 ^ 2) capacity
  change (Scalar.nat n).validate limits = .ok () at nValid
  change (Scalar.nat shift).validate limits = .ok () at shiftValid
  induction shift generalizing n with
  | zero =>
    apply reaches_of_chunk (fuel := 3) (count := 0)
    iterate 3
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, Code.Ixby_Runtime_shiftRightLoop,
        frameState, returned, natural, Frame.read, Frame.readOperands, Frame.transfer,
        evalOp, Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity,
        smallNat, localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  | succ shift ih =>
    by_cases zero : n = 0
    · subst n
      apply reaches_of_chunk (fuel := 5) (count := 0)
      iterate 5
        rw [runChunk]
        simp [step, stepEval, Frame.check, code, Code.Ixby_Runtime_shiftRightLoop,
          frameState, returned, natural, Frame.read, Frame.readOperands, Frame.transfer,
          evalOp, Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity,
          shiftValid, smallNat, localRoom, bind, Except.bind, pure, Except.pure]
      rfl
    · have nextN := validate_nat_mono (Nat.div_le_self n 2) nValid
      have nextShift := validate_nat_mono (show shift ≤ shift + 1 by omega) shiftValid
      have beforeLoop : Reaches limits program
          (frameState 9 0 #[natural n, natural (shift + 1)] continuation)
          (frameState 9 0 #[natural (n / 2), natural shift] continuation) := by
        apply reaches_of_chunk (fuel := 7) (count := 0)
        iterate 7
          rw [runChunk]
          simp [step, stepEval, Frame.check, code, Code.Ixby_Runtime_shiftRightLoop,
            frameState, natural, Frame.read, Frame.readOperands, Frame.transfer, enter, evalOp,
            Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, nValid, shiftValid,
            nextN, nextShift, zero, smallNat, localRoom, bind, Except.bind, pure, Except.pure]
        rfl
      simpa only [Nat.shiftRight_succ_inside] using beforeLoop.trans (ih (n / 2) nextN nextShift)

theorem Certificate.log2Loop_returns (room : 5 ≤ limits.locals) (capacity : 2 ≤ limits.natBits)
    (n accumulator : Nat) (nValid : NatValid limits n)
    (resultValid : NatValid limits (accumulator + n.log2)) (continuation : Array Continuation) :
    Reaches limits program (frameState 10 0 #[natural n, natural accumulator] continuation)
      (returned (natural (accumulator + n.log2)) continuation) := by
  have code := (certificate.function 10).code
  change program.getFunction 10 = .ok Code.Ixby_Runtime_log2Loop at code
  have localRoom : ∀ k, k ≤ 5 → ¬limits.locals < k := by omega
  have smallNat (k : Nat) (small : k ≤ 2) : (Scalar.nat k).validate limits = .ok () :=
    validate_nat_of_bits (by omega : k < 2 ^ 2) capacity
  change (Scalar.nat n).validate limits = .ok () at nValid
  change (Scalar.nat (accumulator + n.log2)).validate limits = .ok () at resultValid
  induction n using Nat.strongRecOn generalizing accumulator with
  | ind n ih =>
    by_cases done : n < 2
    · have result : n.log2 = 0 := by rw [Nat.log2_def]; simp [show ¬2 ≤ n by omega]
      apply reaches_of_chunk (fuel := 3) (count := 0)
      iterate 3
        rw [runChunk]
        simp [step, stepEval, Frame.check, code, Code.Ixby_Runtime_log2Loop,
          frameState, returned, natural, Frame.read, Frame.readOperands, Frame.transfer,
          evalOp, Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity,
          nValid, done, result, smallNat, localRoom, bind, Except.bind, pure, Except.pure]
      rfl
    · have recursiveLaw : n.log2 = (n / 2).log2 + 1 := by
        conv => lhs; rw [Nat.log2_def]
        simp [show 2 ≤ n by omega]
      have accValid := validate_nat_mono (Nat.le_add_right accumulator n.log2) resultValid
      have nextN := validate_nat_mono (Nat.div_le_self n 2) nValid
      have nextAcc := validate_nat_mono
        (show accumulator + 1 ≤ accumulator + n.log2 by rw [recursiveLaw]; omega) resultValid
      have invariant : accumulator + 1 + (n / 2).log2 = accumulator + n.log2 := by
        rw [recursiveLaw]; omega
      have beforeLoop : Reaches limits program
          (frameState 10 0 #[natural n, natural accumulator] continuation)
          (frameState 10 0 #[natural (n / 2), natural (accumulator + 1)] continuation) := by
        apply reaches_of_chunk (fuel := 5) (count := 0)
        iterate 5
          rw [runChunk]
          simp [step, stepEval, Frame.check, code, Code.Ixby_Runtime_log2Loop,
            frameState, natural, Frame.read, Frame.readOperands, Frame.transfer, enter, evalOp,
            Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, nValid, accValid,
            nextN, nextAcc, done, smallNat, localRoom, bind, Except.bind, pure, Except.pure]
        rfl
      have recursive := ih (n / 2) (Nat.div_lt_self (by omega) (by decide)) (accumulator + 1)
        nextN (by simpa only [invariant] using resultValid)
      simpa only [invariant] using beforeLoop.trans recursive

theorem Certificate.powLoop_returns (room : 10 ≤ limits.locals) (capacity : 2 ≤ limits.natBits)
    (base exponent accumulator : Nat) (baseValid : NatValid limits base)
    (exponentValid : NatValid limits exponent) (accumulatorValid : NatValid limits accumulator)
    (powerValid : NatValid limits (base ^ exponent))
    (resultValid : NatValid limits (accumulator * base ^ exponent))
    (continuation : Array Continuation) :
    Reaches limits program (frameState 11 0 #[natural base, natural exponent, natural accumulator] continuation)
      (returned (natural (accumulator * base ^ exponent)) continuation) := by
  have code := (certificate.function 11).code
  change program.getFunction 11 = .ok Code.Ixby_Runtime_powLoop at code
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  have smallNat (k : Nat) (small : k ≤ 2) : (Scalar.nat k).validate limits = .ok () :=
    validate_nat_of_bits (by omega : k < 2 ^ 2) capacity
  simp only [NatValid] at baseValid exponentValid accumulatorValid powerValid resultValid
  induction exponent using Nat.strongRecOn generalizing base accumulator with
  | ind exponent ih =>
    by_cases zero : exponent = 0
    · subst exponent
      apply reaches_of_chunk (fuel := 3) (count := 0)
      iterate 3
        rw [runChunk]
        simp [step, stepEval, Frame.check, code, Code.Ixby_Runtime_powLoop,
          frameState, returned, natural, Frame.read, Frame.readOperands, Frame.transfer,
          evalOp, Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity,
          smallNat, localRoom, bind, Except.bind, pure, Except.pure]
      rfl
    · have nextValid := validate_nat_mono (Nat.div_le_self exponent 2) exponentValid
      have bitValid := validate_nat_mono (Nat.mod_le exponent 2) exponentValid
      have notZero : (exponent == 0) = false := beq_eq_false_iff_ne.mpr zero
      by_cases odd : exponent % 2 = 1
      · have productValid := validate_nat_mono (pow_accumulator_le base exponent accumulator (by omega)) resultValid
        by_cases last : exponent / 2 = 0
        · have one : exponent = 1 := by omega
          subst exponent
          apply reaches_of_chunk (fuel := 10) (count := 0)
          iterate 10
            rw [runChunk]
            simp [step, stepEval, Frame.check, code, Code.Ixby_Runtime_powLoop,
              frameState, returned, natural, Frame.read, Frame.readOperands, Frame.transfer,
              evalOp, Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity,
              baseValid, accumulatorValid, productValid, smallNat, localRoom,
              bind, Except.bind, pure, Except.pure]
          rfl
        · have remaining : 0 < exponent / 2 := by omega
          have notLast : (exponent / 2 == 0) = false := beq_eq_false_iff_ne.mpr last
          have squareValid := validate_nat_mono (pow_square_le base exponent remaining) powerValid
          have beforeLoop : Reaches limits program
              (frameState 11 0 #[natural base, natural exponent, natural accumulator] continuation)
              (frameState 11 0 #[natural (base * base), natural (exponent / 2), natural (accumulator * base)] continuation) := by
            apply reaches_of_chunk (fuel := 11) (count := 0)
            iterate 11
              rw [runChunk]
              simp [step, stepEval, Frame.check, code, Code.Ixby_Runtime_powLoop,
                frameState, natural, Frame.read, Frame.readOperands, Frame.transfer, enter, evalOp,
                Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, exponentValid,
                nextValid, notZero, odd, baseValid, accumulatorValid, productValid, notLast,
                squareValid, smallNat, localRoom, bind, Except.bind, pure, Except.pure]
            rfl
          have invariant := pow_odd base exponent accumulator odd
          have recursive := ih (exponent / 2) (Nat.div_lt_self (by omega) (by decide))
            (base * base) (accumulator * base) squareValid nextValid productValid
            (validate_nat_mono (pow_half_le base exponent remaining) powerValid)
            (by simpa only [invariant] using resultValid)
          simpa only [invariant] using beforeLoop.trans recursive
      · have even : exponent % 2 = 0 := by omega
        have remaining : 0 < exponent / 2 := by omega
        have notLast : (exponent / 2 == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
        have squareValid := validate_nat_mono (pow_square_le base exponent remaining) powerValid
        have beforeLoop : Reaches limits program
            (frameState 11 0 #[natural base, natural exponent, natural accumulator] continuation)
            (frameState 11 0 #[natural (base * base), natural (exponent / 2), natural accumulator] continuation) := by
          apply reaches_of_chunk (fuel := 10) (count := 0)
          iterate 10
            rw [runChunk]
            simp [step, stepEval, Frame.check, code, Code.Ixby_Runtime_powLoop,
              frameState, natural, Frame.read, Frame.readOperands, Frame.transfer, enter, evalOp,
              Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, exponentValid,
              nextValid, notZero, even, baseValid, notLast, squareValid,
              smallNat, localRoom, bind, Except.bind, pure, Except.pure]
          rfl
        have invariant := pow_even base exponent even
        have recursive := ih (exponent / 2) (Nat.div_lt_self (by omega) (by decide))
          (base * base) accumulator squareValid nextValid accumulatorValid
          (by simpa only [invariant] using powerValid) (by simpa only [invariant] using resultValid)
        simpa only [invariant] using beforeLoop.trans recursive

theorem Certificate.natShiftRight_returns (room : 6 ≤ limits.locals) (capacity : 2 ≤ limits.natBits)
    (n shift : Nat) (nValid : NatValid limits n) (shiftValid : NatValid limits shift)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 21 0 #[natural n, natural shift] continuation)
      (returned (natural (n >>> shift)) continuation) := by
  have code := (certificate.function 21).code
  have loop := (certificate.function 9).code
  change program.getFunction 21 = .ok Code.Nat_shiftRight at code
  change program.getFunction 9 = .ok Code.Ixby_Runtime_shiftRightLoop at loop
  apply Reaches.trans (b := frameState 9 0 #[natural n, natural shift] continuation)
  · apply Reaches.of_step
    simp [step, stepEval, Frame.check, code, loop, Code.Nat_shiftRight, Code.Ixby_Runtime_shiftRightLoop,
      frameState, Frame.read, Frame.readOperands, enter, show ¬limits.locals < 2 by omega,
      bind, Except.bind, pure, Except.pure]
  · exact certificate.shiftRightLoop_returns limits room capacity n shift nValid shiftValid continuation

theorem Certificate.natLog2_returns (room : 5 ≤ limits.locals) (capacity : 2 ≤ limits.natBits)
    (n : Nat) (valid : NatValid limits n) (continuation : Array Continuation) :
    Reaches limits program (frameState 22 0 #[natural n] continuation)
      (returned (natural n.log2) continuation) := by
  have code := (certificate.function 22).code
  have loop := (certificate.function 10).code
  change program.getFunction 22 = .ok Code.Nat_log2 at code
  change program.getFunction 10 = .ok Code.Ixby_Runtime_log2Loop at loop
  apply Reaches.trans (b := frameState 10 0 #[natural n, natural 0] continuation)
  · apply Reaches.of_step
    simp [step, stepEval, Frame.check, code, loop, Code.Nat_log2, Code.Ixby_Runtime_log2Loop,
      frameState, natural, Frame.read, Frame.readOperands, enter, show ¬limits.locals < 1 by omega,
      show ¬limits.locals < 2 by omega, bind, Except.bind, pure, Except.pure]
  · simpa using certificate.log2Loop_returns limits room capacity n 0 valid
      (by simpa [NatValid] using validate_nat_mono (Nat.log2_le_self n) valid) continuation

theorem Certificate.natPow_returns (room : 10 ≤ limits.locals) (capacity : 2 ≤ limits.natBits)
    (base exponent : Nat) (baseValid : NatValid limits base) (exponentValid : NatValid limits exponent)
    (resultValid : NatValid limits (base ^ exponent)) (continuation : Array Continuation) :
    Reaches limits program (frameState 20 0 #[natural base, natural exponent] continuation)
      (returned (natural (base ^ exponent)) continuation) := by
  have code := (certificate.function 20).code
  have loop := (certificate.function 11).code
  change program.getFunction 20 = .ok Code.Nat_pow at code
  change program.getFunction 11 = .ok Code.Ixby_Runtime_powLoop at loop
  apply Reaches.trans (b := frameState 11 0 #[natural base, natural exponent, natural 1] continuation)
  · apply Reaches.of_step
    simp [step, stepEval, Frame.check, code, loop, Code.Nat_pow, Code.Ixby_Runtime_powLoop,
      frameState, natural, Frame.read, Frame.readOperands, enter, show ¬limits.locals < 2 by omega,
      show ¬limits.locals < 3 by omega, bind, Except.bind, pure, Except.pure]
  · simpa using certificate.powLoop_returns limits room capacity base exponent 1 baseValid exponentValid
      (validate_nat_of_bits (by decide : 1 < 2 ^ 1) (by omega)) resultValid
      (by simpa using resultValid) continuation

end Compilatrix.Ixby.Runtime.Native
