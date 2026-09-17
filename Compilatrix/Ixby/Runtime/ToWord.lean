import Compilatrix.Ixby.Runtime.ConversionLaws

/-! Exact execution of the generated weighted Nat-to-Word32 helper. The source
Nat is validated before truncation; no helper call or extra continuation is used. -/

namespace Compilatrix.Ixby.Runtime.Conversion

open Ix.Ixby Execution Representation ScalarFunction

theorem toWord_returns {program : Program} {id digit : FunctionId}
    (checked : Checked program id (toWord id digit)) (limits : Limits)
    (room : 6 ≤ limits.locals) (n : Nat) (weight accumulator : UInt32)
    (valid : (Scalar.nat n).validate limits = .ok ())
    (continuation : Array Continuation) :
    Reaches limits program
      (frameState id 0 #[.scalar (.nat n), .scalar (.word32 weight), .scalar (.word32 accumulator)]
        continuation)
      (returned (.scalar (.word32 (accumulator + n.toUInt32 * weight))) continuation) := by
  have localRoom : ∀ k, k ≤ 6 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 4) (count := 0)
  iterate 4
    rw [runChunk]
    simp [step, stepEval, Frame.check, checked.code, toWord, frameState, returned,
      evalOp, Frame.readOperands, Frame.read, Frame.transfer, Primitive.eval, Primitive.evalScalarUnchecked,
      Primitive.arity, localRoom, valid, bind, Except.bind, pure, Except.pure]
  rfl

end Compilatrix.Ixby.Runtime.Conversion
