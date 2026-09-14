import Compilatrix.Ixby.Runtime.NatArithmeticCertificate
import Compilatrix.Ixby.Runtime.NaturalCall

/-! Exact quotient and remainder through both generated Nat observations and
the actual tail call to the raw-number constructor. No nonzero-divisor premise
is imposed: the reference Nat division and remainder laws include zero. -/

namespace Compilatrix.Ixby.Runtime.NatArithmetic

open Ix.Ixby Execution Representation ScalarFunction Conversion

theorem quotientRemainder_returns {program : Program} {links : Conversion.Links}
    (conversions : Conversion.Certificate program links) {id : FunctionId} {operation : Primitive}
    (checked : Checked program id (quotientRemainder links.natural links.fromRaw operation))
    (limits : Limits) (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b n : Nat) (left right : Value)
    (leftRep : Number links.layout a left) (rightRep : Number links.layout b right)
    (result : operation.eval limits [.scalar (.nat a), .scalar (.nat b)] = .ok (.scalar (.nat n)))
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState id 0 #[left, right] continuation)
      (returned (.ctor links.layout.raw #[.scalar (.nat n)]) continuation) := by
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  have observed := conversions.read_naturals checked rfl rfl _ rfl limits room
    capacity bytesCapacity a b left right leftRep rightRep continuation stack
  have beforeReturn : Reaches limits program
      (frameState id 2 #[left, right, .scalar (.nat a), .scalar (.nat b)] continuation)
      (frameState links.fromRaw 0 #[.scalar (.nat n)] continuation) := by
    apply reaches_of_chunk (fuel := 2) (count := 0)
    iterate 2
      rw [runChunk]
      simp [step, stepEval, Frame.check, checked.code, quotientRemainder,
        conversions.fromRaw.code, fromRaw, frameState, Frame.read, Frame.readOperands,
        Frame.transfer, evalOp, enter, result, localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  exact observed.trans (beforeReturn.trans (conversions.fromRaw_returns limits (by omega) n continuation))

namespace Certificate

variable {program : Program} {links : NatArithmetic.Links}
  (certificate : NatArithmetic.Certificate program links) (limits : Limits)

include certificate

theorem div_returns (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.div 0 #[left, right] continuation)
      (returned (.ctor links.conversions.layout.raw #[.scalar (.nat (a / b))]) continuation) :=
  quotientRemainder_returns certificate.conversions certificate.div limits room capacity bytesCapacity
    a b (a / b) left right leftRep rightRep
    (eval_natDiv limits a b leftValid rightValid (validate_nat_mono (Nat.div_le_self a b) leftValid))
    continuation stack

theorem mod_returns (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.mod 0 #[left, right] continuation)
      (returned (.ctor links.conversions.layout.raw #[.scalar (.nat (a % b))]) continuation) :=
  quotientRemainder_returns certificate.conversions certificate.mod limits room capacity bytesCapacity
    a b (a % b) left right leftRep rightRep
    (eval_natMod limits a b leftValid rightValid (validate_nat_mono (Nat.mod_le a b) leftValid))
    continuation stack

end Certificate
end Compilatrix.Ixby.Runtime.NatArithmetic
