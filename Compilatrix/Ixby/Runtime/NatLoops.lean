import Compilatrix.Ixby.Runtime.NatShiftLog
import Compilatrix.Ixby.Runtime.NatPow

/-! Whole-program corollaries for all six certified Nat loop functions.
Each uses ordinary program and input admission; the local return contracts
remain separately compositional over arbitrary caller continuations. -/

namespace Compilatrix.Ixby.Runtime.NatLoops.Certificate

open Ix.Ixby Execution Representation ScalarFunction

variable {program : Program} {links : NatLoops.Links}
  (certificate : NatLoops.Certificate program links) (limits : Limits)

include certificate

theorem shiftRightLoop_evaluates (room : 6 ≤ limits.locals) (capacity : 2 ≤ limits.natBits)
    (n shift : Nat) (nValid : (Scalar.nat n).validate limits = .ok ())
    (shiftValid : (Scalar.nat shift).validate limits = .ok ())
    (entry : program.entry = links.shiftRightLoop) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes
      [.scalar (.nat n), .scalar (.nat shift)] = .ok ()) :
    ∃ value, Evaluates limits program #[.scalar (.nat n), .scalar (.nat shift)] value ∧
      Number links.arithmetic.conversions.layout (n >>> shift) value := by
  obtain ⟨value, path, represented⟩ := certificate.shiftRightLoop_returns limits room capacity n shift
    nValid shiftValid #[]
  refine ⟨value, path.evaluates ?_, represented⟩
  simp [initialState, admitted, enter, entry, certificate.shiftRightLoop.code, NatLoops.shiftRightLoop,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem log2Loop_evaluates (room : 5 ≤ limits.locals) (capacity : 2 ≤ limits.natBits)
    (n accumulator : Nat) (nValid : (Scalar.nat n).validate limits = .ok ())
    (resultValid : (Scalar.nat (accumulator + n.log2)).validate limits = .ok ())
    (entry : program.entry = links.log2Loop) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes
      [.scalar (.nat n), .scalar (.nat accumulator)] = .ok ()) :
    Evaluates limits program #[.scalar (.nat n), .scalar (.nat accumulator)]
      (.ctor links.arithmetic.conversions.layout.raw #[.scalar (.nat (accumulator + n.log2))]) := by
  apply (certificate.log2Loop_returns limits room capacity n accumulator nValid resultValid #[]).evaluates
  simp [initialState, admitted, enter, entry, certificate.log2Loop.code, NatLoops.log2Loop,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem powLoop_evaluates (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (stack : 4 ≤ limits.continuations)
    (base exponent accumulator : Nat) (baseValue accumulatorValue : Value)
    (baseRep : Number links.arithmetic.conversions.layout base baseValue)
    (accumulatorRep : Number links.arithmetic.conversions.layout accumulator accumulatorValue)
    (baseValid : (Scalar.nat base).validate limits = .ok ())
    (exponentValid : (Scalar.nat exponent).validate limits = .ok ())
    (accumulatorValid : (Scalar.nat accumulator).validate limits = .ok ())
    (powerValid : (Scalar.nat (base ^ exponent)).validate limits = .ok ())
    (resultValid : (Scalar.nat (accumulator * base ^ exponent)).validate limits = .ok ())
    (entry : program.entry = links.powLoop) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes
      [baseValue, .scalar (.nat exponent), accumulatorValue] = .ok ()) :
    ∃ value, Evaluates limits program #[baseValue, .scalar (.nat exponent), accumulatorValue] value ∧
      Number links.arithmetic.conversions.layout (accumulator * base ^ exponent) value := by
  obtain ⟨value, path, represented⟩ := certificate.powLoop_returns limits room capacity bytesCapacity
    base exponent accumulator baseValue accumulatorValue baseRep accumulatorRep baseValid exponentValid
    accumulatorValid powerValid resultValid #[] (by simpa using stack)
  refine ⟨value, path.evaluates ?_, represented⟩
  simp [initialState, admitted, enter, entry, certificate.powLoop.code, NatLoops.powLoop,
    Frame.check, inputs, frameState, show ¬limits.locals < 3 by omega,
    bind, Except.bind, pure, Except.pure]

theorem shiftRight_evaluates (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (stack : 3 ≤ limits.continuations)
    (n shift : Nat) (left right : Value)
    (leftRep : Number links.arithmetic.conversions.layout n left)
    (rightRep : Number links.arithmetic.conversions.layout shift right)
    (nValid : (Scalar.nat n).validate limits = .ok ())
    (shiftValid : (Scalar.nat shift).validate limits = .ok ())
    (entry : program.entry = links.shiftRight) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    ∃ value, Evaluates limits program #[left, right] value ∧
      Number links.arithmetic.conversions.layout (n >>> shift) value := by
  obtain ⟨value, path, represented⟩ := certificate.shiftRight_returns limits room capacity bytesCapacity
    n shift left right leftRep rightRep nValid shiftValid #[] (by simpa using stack)
  refine ⟨value, path.evaluates ?_, represented⟩
  simp [initialState, admitted, enter, entry, certificate.shiftRight.code, NatLoops.shiftRight,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem log2_evaluates (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (stack : 3 ≤ limits.continuations)
    (n : Nat) (value : Value) (represented : Number links.arithmetic.conversions.layout n value)
    (valid : (Scalar.nat n).validate limits = .ok ())
    (entry : program.entry = links.log2) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [value] = .ok ()) :
    Evaluates limits program #[value]
      (.ctor links.arithmetic.conversions.layout.raw #[.scalar (.nat n.log2)]) := by
  apply (certificate.log2_returns limits room capacity bytesCapacity n value represented valid #[]
    (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.log2.code, NatLoops.log2,
    Frame.check, inputs, frameState, show ¬limits.locals < 1 by omega,
    bind, Except.bind, pure, Except.pure]

theorem pow_evaluates (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (stack : 4 ≤ limits.continuations)
    (base exponent : Nat) (left right : Value)
    (baseRep : Number links.arithmetic.conversions.layout base left)
    (exponentRep : Number links.arithmetic.conversions.layout exponent right)
    (baseValid : (Scalar.nat base).validate limits = .ok ())
    (exponentValid : (Scalar.nat exponent).validate limits = .ok ())
    (resultValid : (Scalar.nat (base ^ exponent)).validate limits = .ok ())
    (entry : program.entry = links.pow) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    ∃ value, Evaluates limits program #[left, right] value ∧
      Number links.arithmetic.conversions.layout (base ^ exponent) value := by
  obtain ⟨value, path, represented⟩ := certificate.pow_returns limits room capacity bytesCapacity
    base exponent left right baseRep exponentRep baseValid exponentValid resultValid #[] (by simpa using stack)
  refine ⟨value, path.evaluates ?_, represented⟩
  simp [initialState, admitted, enter, entry, certificate.pow.code, NatLoops.pow,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

end Compilatrix.Ixby.Runtime.NatLoops.Certificate
