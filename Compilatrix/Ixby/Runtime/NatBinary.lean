import Compilatrix.Ixby.Runtime.NatArithmeticCertificate
import Compilatrix.Ixby.Runtime.NaturalCall

/-! Complete binary helper executions through both exact-Nat observations,
constructor dispatch, and the conditional word cache. -/

namespace Compilatrix.Ixby.Runtime.NatArithmetic

open Ix.Ixby Execution Representation ScalarFunction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem binary_returns {program : Program} {links : Conversion.Links}
    (conversions : Conversion.Certificate program links) {id : FunctionId} {natOp wordOp : Primitive}
    (checked : Checked program id (binary links.natural links.cachedCtor links.rawCtor links.fieldCtor natOp wordOp))
    (limits : Limits) (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b n : Nat) (left right : Value)
    (leftRep : Number links.layout a left) (rightRep : Number links.layout b right)
    (natResult : natOp.eval limits [.scalar (.nat a), .scalar (.nat b)] = .ok (.scalar (.nat n)))
    (wordResult : wordOp.eval limits [.scalar (.word32 a.toUInt32), .scalar (.word32 b.toUInt32)] =
      .ok (.scalar (.word32 n.toUInt32)))
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    ∃ value, Reaches limits program (frameState id 0 #[left, right] continuation)
      (returned value continuation) ∧ Number links.layout n value := by
  have localRoom : ∀ k, k ≤ 11 → ¬limits.locals < k := by omega
  have beforeOp := conversions.read_naturals checked rfl rfl _ rfl limits (by omega)
    capacity bytesCapacity a b left right leftRep rightRep continuation stack
  cases leftRep <;> cases rightRep
  case cached.cached =>
    refine ⟨_, beforeOp.trans ?_, Number.cached n⟩
    apply reaches_of_chunk (fuel := 6) (count := 0)
    iterate 6
      rw [runChunk]
      simp [step, stepEval, Frame.check, checked.code, binary,
        conversions.cached, frameState, returned, Frame.read, Frame.readOperands,
        Frame.transfer, selectCase, evalOp, natResult, wordResult,
        localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  all_goals
    refine ⟨_, beforeOp.trans ?_, Number.raw n⟩
    first
    | (apply reaches_of_chunk (fuel := 4) (count := 0)
       iterate 4
         rw [runChunk]
         simp [step, stepEval, Frame.check, checked.code, binary,
           conversions.cached, conversions.raw, conversions.field,
           conversions.cachedRaw, conversions.cachedField, conversions.rawField,
           frameState, returned, Frame.read, Frame.readOperands, Frame.transfer,
           selectCase, evalOp, natResult, localRoom, bind, Except.bind, pure, Except.pure]
       rfl)
    | (apply reaches_of_chunk (fuel := 5) (count := 0)
       iterate 5
         rw [runChunk]
         simp [step, stepEval, Frame.check, checked.code, binary,
           conversions.cached, conversions.raw, conversions.field,
           conversions.cachedRaw, conversions.cachedField, conversions.rawField,
           frameState, returned, Frame.read, Frame.readOperands, Frame.transfer,
           selectCase, evalOp, natResult, localRoom, bind, Except.bind, pure, Except.pure]
       rfl)

end Compilatrix.Ixby.Runtime.NatArithmetic
