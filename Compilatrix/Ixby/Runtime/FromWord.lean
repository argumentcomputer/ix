import Compilatrix.Ixby.Runtime.ConversionLaws

/-! Exact execution of the generated weighted Word32-to-Nat helper. Capacity
covers the converted word, input weight and final result. Even a zero weight
cannot suppress validation of the conversion's intermediate Nat. -/

namespace Compilatrix.Ixby.Runtime.Conversion

open Ix.Ixby Execution Representation ScalarFunction

theorem fromWordLoop_returns {program : Program} {id digit : FunctionId}
    (checked : Checked program id (fromWordLoop id digit)) (limits : Limits)
    (room : 6 ≤ limits.locals) (word : UInt32) (weight accumulator : Nat)
    (wordValid : (Scalar.nat word.toNat).validate limits = .ok ())
    (weightValid : (Scalar.nat weight).validate limits = .ok ())
    (resultValid : (Scalar.nat (accumulator + word.toNat * weight)).validate limits = .ok ())
    (continuation : Array Continuation) :
    Reaches limits program
      (frameState id 0 #[.scalar (.word32 word), .scalar (.nat weight), .scalar (.nat accumulator)]
        continuation)
      (returned (.scalar (.nat (accumulator + word.toNat * weight))) continuation) := by
  have localRoom : ∀ k, k ≤ 6 → ¬limits.locals < k := by omega
  have accumulatorValid := validate_nat_mono
    (Nat.le_add_right accumulator (word.toNat * weight)) resultValid
  have productValid := validate_nat_mono
    (Nat.le_add_left (word.toNat * weight) accumulator) resultValid
  apply reaches_of_chunk (fuel := 4) (count := 0)
  iterate 4
    rw [runChunk]
    simp [step, stepEval, Frame.check, checked.code, fromWordLoop, frameState, returned,
      evalOp, Frame.readOperands, Frame.read, Frame.transfer, Primitive.eval,
      Primitive.arity, localRoom, wordValid, weightValid, accumulatorValid,
      productValid, resultValid, bind, Except.bind, pure, Except.pure]
  rfl

end Compilatrix.Ixby.Runtime.Conversion
