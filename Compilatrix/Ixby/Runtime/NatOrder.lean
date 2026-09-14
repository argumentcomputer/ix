import Compilatrix.Ixby.Runtime.NatArithmeticCertificate
import Compilatrix.Ixby.Runtime.NaturalCall

/-! Strict and non-strict comparison of exact Nat observations. Native field
inputs expose their canonical Nat; the other operand is never reduced. -/

namespace Compilatrix.Ixby.Runtime.NatArithmetic.Certificate

open Ix.Ixby Execution Representation ScalarFunction

variable {program : Program} {links : Links} (certificate : Certificate program links)
  (limits : Limits)

include certificate

theorem lt_returns (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.less 0 #[left, right] continuation)
      (returned (.scalar (.bool (decide (a < b)))) continuation) := by
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  have observed := certificate.conversions.read_naturals certificate.less rfl rfl _ rfl limits room
    capacity bytesCapacity a b left right leftRep rightRep continuation stack
  have result : Primitive.natLt.eval limits [.scalar (.nat a), .scalar (.nat b)] =
      .ok (.scalar (.bool (decide (a < b)))) := by
    simp [Primitive.eval, Primitive.arity, leftValid, rightValid] <;> rfl
  apply observed.trans
  apply reaches_of_chunk (fuel := 2) (count := 0)
  iterate 2
    rw [runChunk]
    simp [step, stepEval, Frame.check, certificate.less.code, NatArithmetic.less, frameState, returned,
      Frame.read, Frame.readOperands, Frame.transfer, evalOp, result,
      localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem le_returns (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.lessEqual 0 #[left, right] continuation)
      (returned (.scalar (.bool (decide (a ≤ b)))) continuation) := by
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  have observed := certificate.conversions.read_naturals certificate.lessEqual rfl rfl _ rfl limits room
    capacity bytesCapacity a b left right leftRep rightRep continuation stack
  have result : Primitive.natLt.eval limits [.scalar (.nat b), .scalar (.nat a)] =
      .ok (.scalar (.bool (decide (b < a)))) := by
    simp [Primitive.eval, Primitive.arity, leftValid, rightValid] <;> rfl
  apply observed.trans
  by_cases ordered : a ≤ b
  all_goals
    have reversed : (b < a) ↔ ¬a ≤ b := by omega
    apply reaches_of_chunk (fuel := 3) (count := 0)
    iterate 3
      rw [runChunk]
      simp [step, stepEval, Frame.check, certificate.lessEqual.code, NatArithmetic.lessEqual, frameState, returned,
        Frame.read, Frame.readOperands, Frame.transfer, evalOp, result, reversed, ordered,
        localRoom, bind, Except.bind, pure, Except.pure]
    rfl

end Compilatrix.Ixby.Runtime.NatArithmetic.Certificate
