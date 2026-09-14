import Compilatrix.Ixby.Runtime.NatSub

/-! Source Nat arithmetic for the actual certified helper functions. Result
values preserve the exact Nat and every retained cache. Local paths preserve
arbitrary callers; whole-program corollaries require ordinary admission. -/

namespace Compilatrix.Ixby.Runtime.NatArithmetic.Certificate

open Ix.Ixby Execution Representation ScalarFunction

variable {program : Program} {links : Links} (certificate : Certificate program links)
  (limits : Limits)

include certificate

theorem add_returns (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (resultValid : (Scalar.nat (a + b)).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    ∃ value, Reaches limits program (frameState links.add 0 #[left, right] continuation)
      (returned value continuation) ∧ Number links.conversions.layout (a + b) value := by
  apply binary_returns certificate.conversions certificate.add limits room capacity bytesCapacity
    a b (a + b) left right leftRep rightRep
    (eval_natAdd limits a b leftValid rightValid resultValid) ?_ continuation stack
  simp [Primitive.eval, Primitive.arity, Nat.toUInt32] <;> rfl

theorem mul_returns (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (resultValid : (Scalar.nat (a * b)).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    ∃ value, Reaches limits program (frameState links.mul 0 #[left, right] continuation)
      (returned value continuation) ∧ Number links.conversions.layout (a * b) value := by
  apply binary_returns certificate.conversions certificate.mul limits room capacity bytesCapacity
    a b (a * b) left right leftRep rightRep
    (eval_natMul limits a b leftValid rightValid resultValid) ?_ continuation stack
  simp [Primitive.eval, Primitive.arity, Nat.toUInt32] <;> rfl

theorem add_evaluates (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (stack : 3 ≤ limits.continuations)
    (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (resultValid : (Scalar.nat (a + b)).validate limits = .ok ())
    (entry : program.entry = links.add) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    ∃ value, Evaluates limits program #[left, right] value ∧
      Number links.conversions.layout (a + b) value := by
  obtain ⟨value, path, represented⟩ := certificate.add_returns limits room capacity bytesCapacity
    a b left right leftRep rightRep leftValid rightValid resultValid #[] (by simpa using stack)
  refine ⟨value, path.evaluates ?_, represented⟩
  simp [initialState, admitted, enter, entry, certificate.add.code, binary,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem mul_evaluates (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (stack : 3 ≤ limits.continuations)
    (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (resultValid : (Scalar.nat (a * b)).validate limits = .ok ())
    (entry : program.entry = links.mul) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    ∃ value, Evaluates limits program #[left, right] value ∧
      Number links.conversions.layout (a * b) value := by
  obtain ⟨value, path, represented⟩ := certificate.mul_returns limits room capacity bytesCapacity
    a b left right leftRep rightRep leftValid rightValid resultValid #[] (by simpa using stack)
  refine ⟨value, path.evaluates ?_, represented⟩
  simp [initialState, admitted, enter, entry, certificate.mul.code, binary,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem sub_evaluates (room : 14 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (stack : 3 ≤ limits.continuations)
    (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (entry : program.entry = links.sub) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    ∃ value, Evaluates limits program #[left, right] value ∧
      Number links.conversions.layout (a - b) value := by
  obtain ⟨value, path, represented⟩ := certificate.sub_returns limits room capacity bytesCapacity
    a b left right leftRep rightRep leftValid rightValid #[] (by simpa using stack)
  refine ⟨value, path.evaluates ?_, represented⟩
  simp [initialState, admitted, enter, entry, certificate.sub.code, subtract,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

end Compilatrix.Ixby.Runtime.NatArithmetic.Certificate
