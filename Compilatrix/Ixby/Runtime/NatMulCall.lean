import Compilatrix.Ixby.Runtime.NatArithmetic

/-! An ordinary call to the certified multiplication helper, including the
reference scheduler's real call and return checks. -/

namespace Compilatrix.Ixby.Runtime.NatArithmetic.Certificate

open Ix.Ixby Execution Representation

theorem call_mul {program : Program} {links : Links} (certificate : Certificate program links)
    (limits : Limits) (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes)
    (frame : Frame) (first second : Operand) (target : BlockId) (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (resultValid : (Scalar.nat (a * b)).validate limits = .ok ())
    (code : frame.check limits program =
      .ok ⟨frame.locals.size, .letOp (.call links.mul [first, second]) target⟩)
    (readLeft : frame.read first = .ok left) (readRight : frame.read second = .ok right)
    (transfer : ∀ value, frame.transfer limits program target #[value] =
      .ok { function := frame.function, block := target, locals := frame.locals ++ #[value] })
    (continuation : Array Continuation) (stack : continuation.size + 4 ≤ limits.continuations) :
    ∃ value, Reaches limits program { control := .eval frame, continuation }
      (frameState frame.function target (frame.locals ++ #[value]) continuation) ∧
      Number links.conversions.layout (a * b) value := by
  let saved : Frame := { frame with block := target }
  have entered : enter limits program links.mul #[left, right] =
      .ok { function := links.mul, block := 0, locals := #[left, right] } := by
    simp [enter, Frame.check, certificate.mul.code, binary,
      show ¬limits.locals < 2 by omega, bind, Except.bind, pure, Except.pure]
  have beforeCall : Reaches limits program { control := .eval frame, continuation }
      (frameState links.mul 0 #[left, right] (continuation.push (.resume saved))) := by
    apply Reaches.of_step
    simp [step, stepEval, code, evalOp, Frame.readOperands, readLeft, readRight, State.push,
      entered, frameState, saved, show ¬continuation.size ≥ limits.continuations by omega,
      bind, Except.bind, pure, Except.pure]
  obtain ⟨value, callee, represented⟩ := certificate.mul_returns limits room capacity bytesCapacity
    a b left right leftRep rightRep leftValid rightValid resultValid
    (continuation.push (.resume saved)) (by simp; omega)
  have afterCall := Execution.resume value continuation saved
    { function := frame.function, block := target, locals := frame.locals ++ #[value] }
    (by simpa [saved, Frame.transfer] using transfer value)
  exact ⟨value, beforeCall.trans (callee.trans afterCall), represented⟩

end Compilatrix.Ixby.Runtime.NatArithmetic.Certificate
