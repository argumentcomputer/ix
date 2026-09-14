import Compilatrix.Ixby.Runtime.NatLoopCertificate
import Compilatrix.Ixby.Runtime.NatMulCall
import Compilatrix.Ixby.Runtime.NatPowLaws

/-! Exact repeated squaring through the generated loop and the certified Nat
multiplication calls. An arbitrary accumulator requires capacity for both the
unscaled power and the accumulated result. At the public entry the accumulator
is one, so these are exactly the same final-result bound. -/

namespace Compilatrix.Ixby.Runtime.NatLoops.Certificate

open Ix.Ixby Execution Representation ScalarFunction Conversion

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

variable {program : Program} {links : NatLoops.Links}
  (certificate : NatLoops.Certificate program links) (limits : Limits)

include certificate

theorem powLoop_returns (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (base exponent accumulator : Nat)
    (baseValue accumulatorValue : Value)
    (baseRep : Number links.arithmetic.conversions.layout base baseValue)
    (accumulatorRep : Number links.arithmetic.conversions.layout accumulator accumulatorValue)
    (baseValid : (Scalar.nat base).validate limits = .ok ())
    (exponentValid : (Scalar.nat exponent).validate limits = .ok ())
    (accumulatorValid : (Scalar.nat accumulator).validate limits = .ok ())
    (powerValid : (Scalar.nat (base ^ exponent)).validate limits = .ok ())
    (resultValid : (Scalar.nat (accumulator * base ^ exponent)).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 4 ≤ limits.continuations) :
    ∃ value, Reaches limits program
      (frameState links.powLoop 0 #[baseValue, .scalar (.nat exponent), accumulatorValue] continuation)
      (returned value continuation) ∧
      Number links.arithmetic.conversions.layout (accumulator * base ^ exponent) value := by
  have localRoom : ∀ k, k ≤ 11 → ¬limits.locals < k := by omega
  have smallNat (k : Nat) (small : k ≤ 2) : (Scalar.nat k).validate limits = .ok () :=
    validate_nat_of_bits (by omega : k < 2 ^ 2) (by omega)
  induction exponent using Nat.strongRecOn generalizing base accumulator baseValue accumulatorValue with
  | ind exponent ih =>
    by_cases zero : exponent = 0
    · subst exponent
      refine ⟨accumulatorValue, ?_, by simpa using accumulatorRep⟩
      apply reaches_of_chunk (fuel := 3) (count := 0)
      iterate 3
        rw [runChunk]
        simp [step, stepEval, Frame.check, certificate.powLoop.code, NatLoops.powLoop,
          frameState, returned, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
          Primitive.eval, Primitive.arity, N, smallNat, localRoom, bind, Except.bind, pure, Except.pure]
      rfl
    · have nextValid := validate_nat_mono (Nat.div_le_self exponent 2) exponentValid
      have bitValid := validate_nat_mono (Nat.mod_le exponent 2) exponentValid
      have notZero : (exponent == 0) = false := beq_eq_false_iff_ne.mpr zero
      by_cases odd : exponent % 2 = 1
      · let locals : Array Value := #[baseValue, .scalar (.nat exponent), accumulatorValue,
          .scalar (.bool false), .scalar (.nat (exponent / 2)), .scalar (.nat (exponent % 2)),
          .scalar (.bool true)]
        have beforeMultiply : Reaches limits program
            (frameState links.powLoop 0 #[baseValue, .scalar (.nat exponent), accumulatorValue] continuation)
            (frameState links.powLoop 7 locals continuation) := by
          apply reaches_of_chunk (fuel := 6) (count := 0)
          iterate 6
            rw [runChunk]
            simp [step, stepEval, Frame.check, certificate.powLoop.code, NatLoops.powLoop,
              frameState, locals, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
              Primitive.eval, Primitive.arity, N, exponentValid, nextValid,
              notZero, odd, smallNat, localRoom, bind, Except.bind, pure, Except.pure]
          rfl
        have productValid := validate_nat_mono (pow_accumulator_le base exponent accumulator (by omega)) resultValid
        obtain ⟨product, multiplied, productRep⟩ := certificate.arithmetic.call_mul limits room capacity bytesCapacity
          { function := links.powLoop, block := 7, locals } (.local 2) (.local 0) 9
          accumulator base accumulatorValue baseValue accumulatorRep baseRep
          accumulatorValid baseValid productValid
          (by simp [Frame.check, certificate.powLoop.code, NatLoops.powLoop, locals, localRoom,
            bind, Except.bind, pure, Except.pure]) (by rfl) (by rfl)
          (by intro value; simp [Frame.transfer, Frame.check, certificate.powLoop.code, NatLoops.powLoop,
            locals, localRoom, bind, Except.bind, pure, Except.pure]) continuation stack
        by_cases last : exponent / 2 = 0
        · have one : exponent = 1 := by omega
          refine ⟨product, beforeMultiply.trans (multiplied.trans ?_), by simpa only [one, Nat.pow_one] using productRep⟩
          apply reaches_of_chunk (fuel := 3) (count := 0)
          iterate 3
            rw [runChunk]
            simp [step, stepEval, Frame.check, certificate.powLoop.code, NatLoops.powLoop,
              frameState, returned, locals, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
              Primitive.eval, Primitive.arity, N, last, smallNat, localRoom,
              bind, Except.bind, pure, Except.pure]
          rfl
        · have remaining : 0 < exponent / 2 := by omega
          have notLast : (exponent / 2 == 0) = false := beq_eq_false_iff_ne.mpr last
          let squareLocals := locals ++ #[product, .scalar (.bool false)]
          have beforeSquare : Reaches limits program
              (frameState links.powLoop 9 (locals ++ #[product]) continuation)
              (frameState links.powLoop 12 squareLocals continuation) := by
            apply reaches_of_chunk (fuel := 2) (count := 0)
            iterate 2
              rw [runChunk]
              simp [step, stepEval, Frame.check, certificate.powLoop.code, NatLoops.powLoop,
                frameState, locals, squareLocals, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
                Primitive.eval, Primitive.arity, N, notLast, nextValid, smallNat, localRoom,
                bind, Except.bind, pure, Except.pure]
            rfl
          have squareValid := validate_nat_mono (pow_square_le base exponent remaining) powerValid
          obtain ⟨square, squared, squareRep⟩ := certificate.arithmetic.call_mul limits room capacity bytesCapacity
            { function := links.powLoop, block := 12, locals := squareLocals } (.local 0) (.local 0) 13
            base base baseValue baseValue baseRep baseRep baseValid baseValid squareValid
            (by simp [Frame.check, certificate.powLoop.code, NatLoops.powLoop, squareLocals, locals, localRoom,
              bind, Except.bind, pure, Except.pure]) (by rfl) (by rfl)
            (by intro value; simp [Frame.transfer, Frame.check, certificate.powLoop.code, NatLoops.powLoop,
              squareLocals, locals, localRoom, bind, Except.bind, pure, Except.pure]) continuation stack
          have nextLoop : Reaches limits program
              (frameState links.powLoop 13 (squareLocals ++ #[square]) continuation)
              (frameState links.powLoop 0 #[square, .scalar (.nat (exponent / 2)), product] continuation) := by
            apply Reaches.of_step
            simp [step, stepEval, Frame.check, certificate.powLoop.code, NatLoops.powLoop,
              frameState, locals, squareLocals, Frame.read, Frame.readOperands, enter, localRoom,
              bind, Except.bind, pure, Except.pure]
          have invariant := pow_odd base exponent accumulator odd
          obtain ⟨value, recursive, represented⟩ := ih (exponent / 2)
            (Nat.div_lt_self (by omega) (by decide)) (base * base) (accumulator * base) square product
            squareRep productRep squareValid nextValid productValid
            (validate_nat_mono (pow_half_le base exponent remaining) powerValid)
            (by simpa only [invariant] using resultValid)
          exact ⟨value, beforeMultiply.trans (multiplied.trans (beforeSquare.trans (squared.trans
            (nextLoop.trans recursive)))), by simpa only [invariant] using represented⟩
      · have even : exponent % 2 = 0 := by omega
        have remaining : 0 < exponent / 2 := by omega
        have notOdd : (exponent % 2 == 1) = false := beq_eq_false_iff_ne.mpr odd
        have notLast : (exponent / 2 == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
        let locals : Array Value := #[baseValue, .scalar (.nat exponent), accumulatorValue,
          .scalar (.bool false), .scalar (.nat (exponent / 2)), .scalar (.nat (exponent % 2)),
          .scalar (.bool false), .scalar (.bool false)]
        have beforeSquare : Reaches limits program
            (frameState links.powLoop 0 #[baseValue, .scalar (.nat exponent), accumulatorValue] continuation)
            (frameState links.powLoop 16 locals continuation) := by
          apply reaches_of_chunk (fuel := 8) (count := 0)
          iterate 8
            rw [runChunk]
            simp [step, stepEval, Frame.check, certificate.powLoop.code, NatLoops.powLoop,
              frameState, locals, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
              Primitive.eval, Primitive.arity, N, exponentValid, nextValid, bitValid,
              notZero, notOdd, notLast, smallNat, localRoom,
              bind, Except.bind, pure, Except.pure]
          rfl
        have squareValid := validate_nat_mono (pow_square_le base exponent remaining) powerValid
        obtain ⟨square, squared, squareRep⟩ := certificate.arithmetic.call_mul limits room capacity bytesCapacity
          { function := links.powLoop, block := 16, locals } (.local 0) (.local 0) 17
          base base baseValue baseValue baseRep baseRep baseValid baseValid squareValid
          (by simp [Frame.check, certificate.powLoop.code, NatLoops.powLoop, locals, localRoom,
            bind, Except.bind, pure, Except.pure]) (by rfl) (by rfl)
          (by intro value; simp [Frame.transfer, Frame.check, certificate.powLoop.code, NatLoops.powLoop,
            locals, localRoom, bind, Except.bind, pure, Except.pure]) continuation stack
        have nextLoop : Reaches limits program
            (frameState links.powLoop 17 (locals ++ #[square]) continuation)
            (frameState links.powLoop 0 #[square, .scalar (.nat (exponent / 2)), accumulatorValue] continuation) := by
          apply Reaches.of_step
          simp [step, stepEval, Frame.check, certificate.powLoop.code, NatLoops.powLoop,
            frameState, locals, Frame.read, Frame.readOperands, enter, localRoom,
            bind, Except.bind, pure, Except.pure]
        have invariant := pow_even base exponent even
        obtain ⟨value, recursive, represented⟩ := ih (exponent / 2)
          (Nat.div_lt_self (by omega) (by decide)) (base * base) accumulator square accumulatorValue
          squareRep accumulatorRep squareValid nextValid accumulatorValid
          (by simpa only [invariant] using powerValid) (by simpa only [invariant] using resultValid)
        exact ⟨value, beforeSquare.trans (squared.trans (nextLoop.trans recursive)),
          by simpa only [invariant] using represented⟩

theorem pow_returns (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (base exponent : Nat) (left right : Value)
    (baseRep : Number links.arithmetic.conversions.layout base left)
    (exponentRep : Number links.arithmetic.conversions.layout exponent right)
    (baseValid : (Scalar.nat base).validate limits = .ok ())
    (exponentValid : (Scalar.nat exponent).validate limits = .ok ())
    (resultValid : (Scalar.nat (base ^ exponent)).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 4 ≤ limits.continuations) :
    ∃ value, Reaches limits program (frameState links.pow 0 #[left, right] continuation)
      (returned value continuation) ∧ Number links.arithmetic.conversions.layout (base ^ exponent) value := by
  have localRoom : ∀ k, k ≤ 11 → ¬limits.locals < k := by omega
  have observed := certificate.arithmetic.conversions.call_natural limits (by omega) capacity bytesCapacity
    { function := links.pow, block := 0, locals := #[left, right] } (.local 1) 1 exponent right exponentRep
    { function := links.pow, block := 1, locals := #[left, right, .scalar (.nat exponent)] }
    (by simp [Frame.check, certificate.pow.code, NatLoops.pow, localRoom, bind, Except.bind, pure, Except.pure])
    (by rfl)
    (by simp [Frame.transfer, Frame.check, certificate.pow.code, NatLoops.pow, localRoom,
      bind, Except.bind, pure, Except.pure]) continuation (by omega)
  let one : Value := .ctor links.arithmetic.conversions.layout.cached #[.scalar (.nat 1), .scalar (.word32 1)]
  have entered : Reaches limits program
      (frameState links.pow 1 #[left, right, .scalar (.nat exponent)] continuation)
      (frameState links.powLoop 0 #[left, .scalar (.nat exponent), one] continuation) := by
    apply reaches_of_chunk (fuel := 2) (count := 0)
    iterate 2
      rw [runChunk]
      simp [step, stepEval, Frame.check, certificate.pow.code, NatLoops.pow,
        certificate.powLoop.code, NatLoops.powLoop, certificate.arithmetic.conversions.cached,
        frameState, one, Frame.read, Frame.readOperands, Frame.transfer, evalOp, enter, N, W,
        localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  obtain ⟨value, path, represented⟩ := certificate.powLoop_returns limits room capacity bytesCapacity
    base exponent 1 left one baseRep (Number.cached 1) baseValid exponentValid
    (validate_nat_of_bits (by decide : 1 < 2 ^ 1) (by omega)) resultValid (by simpa using resultValid)
    continuation stack
  exact ⟨value, observed.trans (entered.trans path), by simpa using represented⟩

end Compilatrix.Ixby.Runtime.NatLoops.Certificate
