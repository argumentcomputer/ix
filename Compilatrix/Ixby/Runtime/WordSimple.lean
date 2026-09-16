import Compilatrix.Ixby.Runtime.WordCertificate
import Compilatrix.Ixby.Runtime.WordCall
import Compilatrix.Ixby.Runtime.WordLaws

/-! Complete executions of identity, comparison, logical, and shift helpers.
All paths preserve arbitrary surrounding continuations. -/

namespace Compilatrix.Ixby.Runtime.Words

open Ix.Ixby Execution Representation ScalarFunction Conversion

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem identity_returns {program : Program} {id : FunctionId}
    (checked : Checked program id identity) (limits : Limits) (room : 1 ≤ limits.locals)
    (value : Value) (continuation : Array Continuation) :
    Reaches limits program (frameState id 0 #[value] continuation) (returned value continuation) := by
  apply Reaches.of_step
  simp [step, stepEval, Frame.check, checked.code, identity, frameState, returned,
    Frame.read, show ¬limits.locals < 1 by omega, bind, Except.bind, pure, Except.pure]

theorem compare_returns {program : Program} {links : Conversion.Links}
    (conversions : Conversion.Certificate program links) {id : FunctionId} {operation : Primitive}
    (checked : Checked program id (compare links.natural operation))
    (limits : Limits) (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : Nat) (left right : Value)
    (leftRep : Number links.layout a left) (rightRep : Number links.layout b right) (result : Bool)
    (evaluated : operation.eval limits [.scalar (.nat a), .scalar (.nat b)] = .ok (.scalar (.bool result)))
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState id 0 #[left, right] continuation)
      (returned (.scalar (.bool result)) continuation) := by
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  have observed := conversions.read_naturals checked rfl rfl _ rfl limits room
    capacity bytesCapacity a b left right leftRep rightRep continuation stack
  apply observed.trans
  apply reaches_of_chunk (fuel := 2) (count := 0)
  iterate 2
    rw [runChunk]
    simp [step, stepEval, Frame.check, checked.code, compare, frameState, returned,
      Frame.read, Frame.readOperands, Frame.transfer, evalOp, evaluated,
      localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem logical_returns {program : Program} {links : Conversion.Links}
    (conversions : Conversion.Certificate program links) {id : FunctionId} {operation : Primitive}
    (checked : Checked program id (logical links.lowWord links.fromWord operation))
    (limits : Limits) (room : 11 ≤ limits.locals) (capacity : 32 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : Nat) (left right : Value)
    (leftRep : Number links.layout a left) (rightRep : Number links.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ()) (word : UInt32)
    (evaluated : operation.eval limits [.scalar (.word32 a.toUInt32), .scalar (.word32 b.toUInt32)] =
      .ok (.scalar (.word32 word)))
    (continuation : Array Continuation) (stack : continuation.size + 2 ≤ limits.continuations) :
    Reaches limits program (frameState id 0 #[left, right] continuation)
      (returned (cachedValue links.layout word.toNat) continuation) := by
  have localRoom : ∀ k, k ≤ 11 → ¬limits.locals < k := by omega
  have observed := conversions.read_lowWords checked rfl rfl _ rfl limits room (by omega)
    bytesCapacity a b left right leftRep rightRep leftValid rightValid continuation stack
  have beforeReturn : Reaches limits program
      (frameState id 2 #[left, right, .scalar (.word32 a.toUInt32), .scalar (.word32 b.toUInt32)] continuation)
      (frameState links.fromWord 0 #[.scalar (.word32 word)] continuation) := by
    apply reaches_of_chunk (fuel := 2) (count := 0)
    iterate 2
      rw [runChunk]
      simp [step, stepEval, Frame.check, checked.code, logical, conversions.fromWord.code,
        fromWord, frameState, Frame.read, Frame.readOperands, Frame.transfer, evalOp, enter,
        evaluated, localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  have finished := conversions.fromWord_returns limits (by omega) capacity word continuation stack
  simpa only [cachedValue, Nat.toUInt32, UInt32.ofNat_toNat] using
    observed.trans (beforeReturn.trans finished)

theorem shift_returns {program : Program} {links : Conversion.Links}
    (conversions : Conversion.Certificate program links) {id : FunctionId} {operation : Primitive}
    (bits : Nat) (width : bits = 8 ∨ bits = 32)
    (checked : Checked program id (shift links.lowWord links.fromWord operation bits))
    (limits : Limits) (room : 11 ≤ limits.locals) (capacity : 32 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : Nat) (left right : Value)
    (leftRep : Number links.layout a left) (rightRep : Number links.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ()) (word : UInt32)
    (evaluated : operation.eval limits
      [.scalar (.word32 a.toUInt32), .scalar (.word32 (b.toUInt32 &&& (bits - 1).toUInt32))] =
      .ok (.scalar (.word32 word)))
    (continuation : Array Continuation) (stack : continuation.size + 2 ≤ limits.continuations) :
    Reaches limits program (frameState id 0 #[left, right] continuation)
      (returned (cachedValue links.layout
        (if bits < 32 then word &&& (2 ^ bits - 1).toUInt32 else word).toNat) continuation) := by
  have localRoom : ∀ k, k ≤ 11 → ¬limits.locals < k := by omega
  have mask : Primitive.word32And.eval limits
      [.scalar (.word32 b.toUInt32), .scalar (.word32 (bits - 1).toUInt32)] =
      .ok (.scalar (.word32 (b.toUInt32 &&& (bits - 1).toUInt32))) := by
    simp [Primitive.eval, Primitive.arity] <;> rfl
  rcases width with rfl | rfl
  all_goals
    simp [Nat.toUInt32] at mask evaluated
    have observed := conversions.read_lowWords checked rfl rfl _ rfl limits room (by omega)
      bytesCapacity a b left right leftRep rightRep leftValid rightValid continuation stack
    have maskResult : Primitive.word32And.eval limits
        [.scalar (.word32 word), .scalar (.word32 255)] = .ok (.scalar (.word32 (word &&& 255))) := by
      simp [Primitive.eval, Primitive.arity] <;> rfl
  case inl =>
    have beforeReturn : Reaches limits program
        (frameState id 2 #[left, right, .scalar (.word32 a.toUInt32), .scalar (.word32 b.toUInt32)] continuation)
        (frameState links.fromWord 0 #[.scalar (.word32 (word &&& 255))] continuation) := by
      apply reaches_of_chunk (fuel := 4) (count := 0)
      iterate 4
        rw [runChunk]
        simp [step, stepEval, Frame.check, checked.code, shift, conversions.fromWord.code,
          fromWord, frameState, Frame.read, Frame.readOperands, Frame.transfer, evalOp, enter,
          W, mask, evaluated, maskResult, localRoom, bind, Except.bind, pure, Except.pure]
      rfl
    have finished := conversions.fromWord_returns limits (by omega) capacity (word &&& 255) continuation stack
    simpa [cachedValue, Nat.toUInt32] using observed.trans (beforeReturn.trans finished)
  case inr =>
    have beforeReturn : Reaches limits program
        (frameState id 2 #[left, right, .scalar (.word32 a.toUInt32), .scalar (.word32 b.toUInt32)] continuation)
        (frameState links.fromWord 0 #[.scalar (.word32 word)] continuation) := by
      apply reaches_of_chunk (fuel := 3) (count := 0)
      iterate 3
        rw [runChunk]
        simp [step, stepEval, Frame.check, checked.code, shift, conversions.fromWord.code,
          fromWord, frameState, Frame.read, Frame.readOperands, Frame.transfer, evalOp, enter,
          W, mask, evaluated, localRoom, bind, Except.bind, pure, Except.pure]
      rfl
    have finished := conversions.fromWord_returns limits (by omega) capacity word continuation stack
    simpa only [show ¬(32 : Nat) < 32 by decide, if_false, cachedValue, Nat.toUInt32,
      UInt32.ofNat_toNat] using observed.trans (beforeReturn.trans finished)

end Compilatrix.Ixby.Runtime.Words
