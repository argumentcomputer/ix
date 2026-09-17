import Compilatrix.Ixby.Runtime.NatSub
import Compilatrix.Ixby.Runtime.NatDivision
import Compilatrix.Ixby.Runtime.NatOrder
import Compilatrix.Ixby.Runtime.NatEquality

/-! Source Nat arithmetic and comparisons for the actual certified helper
functions. Numeric results preserve the exact Nat and every retained cache;
comparisons return the exact source Boolean. Local paths preserve
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
  simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, Nat.toUInt32] <;> rfl

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
  simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, Nat.toUInt32] <;> rfl

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

theorem div_evaluates (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (stack : 3 ≤ limits.continuations)
    (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (entry : program.entry = links.div) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right]
      (.ctor links.conversions.layout.raw #[.scalar (.nat (a / b))]) := by
  apply (certificate.div_returns limits room capacity bytesCapacity a b left right leftRep rightRep
    leftValid rightValid #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.div.code, quotientRemainder,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem mod_evaluates (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (stack : 3 ≤ limits.continuations)
    (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (entry : program.entry = links.mod) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right]
      (.ctor links.conversions.layout.raw #[.scalar (.nat (a % b))]) := by
  apply (certificate.mod_returns limits room capacity bytesCapacity a b left right leftRep rightRep
    leftValid rightValid #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.mod.code, quotientRemainder,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem eq_evaluates (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (stack : 3 ≤ limits.continuations)
    (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (entry : program.entry = links.equal) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right] (.scalar (.bool (a == b))) := by
  apply (certificate.eq_returns limits room capacity bytesCapacity a b left right leftRep rightRep
    leftValid rightValid #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.equal.code, NatArithmetic.equal,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem lt_evaluates (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (stack : 3 ≤ limits.continuations)
    (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (entry : program.entry = links.less) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right] (.scalar (.bool (decide (a < b)))) := by
  apply (certificate.lt_returns limits room capacity bytesCapacity a b left right leftRep rightRep
    leftValid rightValid #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.less.code, NatArithmetic.less,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem le_evaluates (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (stack : 3 ≤ limits.continuations)
    (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (entry : program.entry = links.lessEqual) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right] (.scalar (.bool (decide (a ≤ b)))) := by
  apply (certificate.le_returns limits room capacity bytesCapacity a b left right leftRep rightRep
    leftValid rightValid #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.lessEqual.code, NatArithmetic.lessEqual,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

end Compilatrix.Ixby.Runtime.NatArithmetic.Certificate
