import Compilatrix.Ixby.Runtime.NatBinary

/-! Truncated subtraction executes the underflow branch before using word
subtraction. The non-underflow path repeats both actual conversion calls,
exactly as emitted by the existing builder. -/

namespace Compilatrix.Ixby.Runtime.NatArithmetic.Certificate

open Ix.Ixby Execution Representation ScalarFunction Conversion

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem sub_returns {program : Program} {links : NatArithmetic.Links}
    (certificate : NatArithmetic.Certificate program links)
    (limits : Limits) (room : 14 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    ∃ value, Reaches limits program (frameState links.sub 0 #[left, right] continuation)
      (returned value continuation) ∧ Number links.conversions.layout (a - b) value := by
  have localRoom : ∀ k, k ≤ 14 → ¬limits.locals < k := by omega
  have beforeOp := certificate.conversions.read_naturals certificate.sub rfl rfl _ rfl
    limits (by omega) capacity bytesCapacity a b left right leftRep rightRep continuation stack
  by_cases underflow : a < b
  · have less : Primitive.natLt.eval limits [.scalar (.nat a), .scalar (.nat b)] =
        .ok (.scalar (.bool true)) := by
      simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, leftValid, rightValid, underflow] <;> rfl
    refine ⟨_, beforeOp.trans ?_, cached_sub_underflow links.conversions.layout a b underflow⟩
    apply reaches_of_chunk (fuel := 4) (count := 0)
    iterate 4
      rw [runChunk]
      simp [step, stepEval, Frame.check, certificate.sub.code, subtract,
        certificate.conversions.cached, frameState, returned, Frame.read, Frame.readOperands,
        Frame.transfer, evalOp, less, N, W, localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  · have ordered : b ≤ a := by omega
    have less : Primitive.natLt.eval limits [.scalar (.nat a), .scalar (.nat b)] =
        .ok (.scalar (.bool false)) := by
      simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, leftValid, rightValid, underflow] <;> rfl
    have branchPath : Reaches limits program
        (frameState links.sub 2 #[left, right, .scalar (.nat a), .scalar (.nat b)] continuation)
        (frameState links.sub 5
          #[left, right, .scalar (.nat a), .scalar (.nat b), .scalar (.bool false)] continuation) := by
      apply reaches_of_chunk (fuel := 2) (count := 0)
      iterate 2
        rw [runChunk]
        simp [step, stepEval, Frame.check, certificate.sub.code, subtract,
          frameState, Frame.read, Frame.readOperands, Frame.transfer, evalOp, less,
          localRoom, bind, Except.bind, pure, Except.pure]
      rfl
    have againLeft := certificate.conversions.call_natural limits (by omega) capacity bytesCapacity
      { function := links.sub, block := 5, locals :=
          #[left, right, .scalar (.nat a), .scalar (.nat b), .scalar (.bool false)] }
      (.local 0) 7 a left leftRep
      { function := links.sub, block := 7, locals :=
          #[left, right, .scalar (.nat a), .scalar (.nat b), .scalar (.bool false), .scalar (.nat a)] }
      (by simp [Frame.check, certificate.sub.code, subtract, localRoom, bind, Except.bind, pure, Except.pure])
      (by rfl)
      (by simp [Frame.transfer, Frame.check, certificate.sub.code, subtract, localRoom,
        bind, Except.bind, pure, Except.pure]) continuation stack
    have againRight := certificate.conversions.call_natural limits (by omega) capacity bytesCapacity
      { function := links.sub, block := 7, locals :=
          #[left, right, .scalar (.nat a), .scalar (.nat b), .scalar (.bool false), .scalar (.nat a)] }
      (.local 1) 8 b right rightRep
      { function := links.sub, block := 8, locals :=
          #[left, right, .scalar (.nat a), .scalar (.nat b), .scalar (.bool false),
            .scalar (.nat a), .scalar (.nat b)] }
      (by simp [Frame.check, certificate.sub.code, subtract, localRoom, bind, Except.bind, pure, Except.pure])
      (by rfl)
      (by simp [Frame.transfer, Frame.check, certificate.sub.code, subtract, localRoom,
        bind, Except.bind, pure, Except.pure]) continuation stack
    have beforeSubtract := beforeOp.trans (branchPath.trans (againLeft.trans againRight))
    have natResult := eval_natSub limits a b leftValid rightValid
      (validate_nat_mono (Nat.sub_le a b) leftValid)
    have wordResult : Primitive.word32Sub.eval limits
        [.scalar (.word32 a.toUInt32), .scalar (.word32 b.toUInt32)] =
        .ok (.scalar (.word32 (a - b).toUInt32)) := by
      simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, Nat.toUInt32, UInt32.ofNat_sub ordered] <;> rfl
    cases leftRep <;> cases rightRep
    case cached.cached =>
      refine ⟨_, beforeSubtract.trans ?_, Number.cached (a - b)⟩
      apply reaches_of_chunk (fuel := 6) (count := 0)
      iterate 6
        rw [runChunk]
        simp [step, stepEval, Frame.check, certificate.sub.code, subtract,
          certificate.conversions.cached, returned, Frame.read, Frame.readOperands,
          Frame.transfer, selectCase, evalOp, natResult, wordResult,
          localRoom, bind, Except.bind, pure, Except.pure]
      rfl
    all_goals
      refine ⟨_, beforeSubtract.trans ?_, Number.raw _⟩
      first
      | (apply reaches_of_chunk (fuel := 4) (count := 0)
         iterate 4
           rw [runChunk]
           simp [step, stepEval, Frame.check, certificate.sub.code, subtract,
             certificate.conversions.cached, certificate.conversions.raw, certificate.conversions.field,
             certificate.conversions.cachedRaw, certificate.conversions.cachedField, certificate.conversions.rawField,
             returned, Frame.read, Frame.readOperands, Frame.transfer,
             selectCase, evalOp, natResult, localRoom, bind, Except.bind, pure, Except.pure]
         rfl)
      | (apply reaches_of_chunk (fuel := 5) (count := 0)
         iterate 5
           rw [runChunk]
           simp [step, stepEval, Frame.check, certificate.sub.code, subtract,
             certificate.conversions.cached, certificate.conversions.raw, certificate.conversions.field,
             certificate.conversions.cachedRaw, certificate.conversions.cachedField, certificate.conversions.rawField,
             returned, Frame.read, Frame.readOperands, Frame.transfer,
             selectCase, evalOp, natResult, localRoom, bind, Except.bind, pure, Except.pure]
         rfl)

end Compilatrix.Ixby.Runtime.NatArithmetic.Certificate
