import Compilatrix.Ixby.Runtime.FieldArithmeticCertificate
import Compilatrix.Ixby.Runtime.FieldCall

/-! Complete execution paths for the six base-field wrappers and extension
packing. Exact Nat observations are reduced by the certified `asField` callee;
field results are boxed canonically and extension coefficients retain their
source order. Every path preserves an arbitrary caller continuation. -/

namespace Compilatrix.Ixby.Runtime.FieldArithmetic

open Ix.Ixby Execution Representation ScalarFunction

theorem binary_returns {program : Program} {links : Conversion.Links}
    (conversions : Conversion.Certificate program links) {id : FunctionId} {operation : Primitive}
    (checked : Checked program id (binary links.asField links.fieldCtor operation))
    (limits : Limits) (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (a b : Nat) (left right : Value)
    (leftRep : Number links.layout a left) (rightRep : Number links.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (result : Goldilocks)
    (evaluated : operation.eval limits [.scalar (.field (Goldilocks.reduce a)),
      .scalar (.field (Goldilocks.reduce b))] = .ok (.scalar (.field result)))
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState id 0 #[left, right] continuation)
      (returned (.ctor links.layout.field #[.scalar (.field result)]) continuation) := by
  have localRoom : ∀ k, k ≤ 11 → ¬limits.locals < k := by omega
  have observed := conversions.read_fields checked rfl rfl _ rfl limits room capacity
    a b left right leftRep rightRep leftValid rightValid continuation stack
  apply observed.trans
  apply reaches_of_chunk (fuel := 3) (count := 0)
  iterate 3
    rw [runChunk]
    simp [step, stepEval, Frame.check, checked.code, binary, conversions.field,
      frameState, returned, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
      evaluated, localRoom, bind, Except.bind, pure, Except.pure]
  rfl

namespace Certificate

variable {program : Program} {links : Links} (certificate : Certificate program links)
  (limits : Limits)

include certificate

theorem reduce_returns (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (n : Nat) (value : Value) (represented : Number links.conversions.layout n value)
    (valid : (Scalar.nat n).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.reduce 0 #[value] continuation)
      (returned (.ctor links.conversions.layout.field #[.scalar (.field (Goldilocks.reduce n))])
        continuation) := by
  have localRoom : ∀ k, k ≤ 11 → ¬limits.locals < k := by omega
  have observed := certificate.conversions.call_asField limits room capacity
    { function := links.reduce, block := 0, locals := #[value] } (.local 0) 1 n value represented valid
    { function := links.reduce, block := 1, locals := #[value, .scalar (.field (Goldilocks.reduce n))] }
    (by simp [Frame.check, certificate.reduce.code, FieldArithmetic.reduce, localRoom,
      bind, Except.bind, pure, Except.pure]) rfl
    (by simp [Frame.transfer, Frame.check, certificate.reduce.code, FieldArithmetic.reduce, localRoom,
      bind, Except.bind, pure, Except.pure]) continuation stack
  apply observed.trans
  apply reaches_of_chunk (fuel := 2) (count := 0)
  iterate 2
    rw [runChunk]
    simp [step, stepEval, Frame.check, certificate.reduce.code, FieldArithmetic.reduce,
      certificate.conversions.field, returned, Frame.read, Frame.readOperands, Frame.transfer,
      evalOp, localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem add_returns (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.add 0 #[left, right] continuation)
      (returned (.ctor links.conversions.layout.field
        #[.scalar (.field ((Goldilocks.reduce a).add (Goldilocks.reduce b)))]) continuation) :=
  binary_returns certificate.conversions certificate.add limits room capacity a b left right
    leftRep rightRep leftValid rightValid _ (eval_fieldAdd limits _ _) continuation stack

theorem sub_returns (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.sub 0 #[left, right] continuation)
      (returned (.ctor links.conversions.layout.field
        #[.scalar (.field ((Goldilocks.reduce a).sub (Goldilocks.reduce b)))]) continuation) :=
  binary_returns certificate.conversions certificate.sub limits room capacity a b left right
    leftRep rightRep leftValid rightValid _ (eval_fieldSub limits _ _) continuation stack

theorem mul_returns (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.mul 0 #[left, right] continuation)
      (returned (.ctor links.conversions.layout.field
        #[.scalar (.field ((Goldilocks.reduce a).mul (Goldilocks.reduce b)))]) continuation) :=
  binary_returns certificate.conversions certificate.mul limits room capacity a b left right
    leftRep rightRep leftValid rightValid _ (eval_fieldMul limits _ _) continuation stack

theorem neg_returns (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (n : Nat) (value : Value) (represented : Number links.conversions.layout n value)
    (valid : (Scalar.nat n).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.neg 0 #[value] continuation)
      (returned (.ctor links.conversions.layout.field #[.scalar (.field (Goldilocks.reduce n).neg)])
        continuation) := by
  have localRoom : ∀ k, k ≤ 11 → ¬limits.locals < k := by omega
  have observed := certificate.conversions.call_asField limits room capacity
    { function := links.neg, block := 0, locals := #[value] } (.local 0) 1 n value represented valid
    { function := links.neg, block := 1, locals := #[value, .scalar (.field (Goldilocks.reduce n))] }
    (by simp [Frame.check, certificate.neg.code, negate, localRoom,
      bind, Except.bind, pure, Except.pure]) rfl
    (by simp [Frame.transfer, Frame.check, certificate.neg.code, negate, localRoom,
      bind, Except.bind, pure, Except.pure]) continuation stack
  have evaluated := eval_fieldSub limits 0 (Goldilocks.reduce n)
  apply observed.trans
  apply reaches_of_chunk (fuel := 3) (count := 0)
  iterate 3
    rw [runChunk]
    simp [step, stepEval, Frame.check, certificate.neg.code, negate, certificate.conversions.field,
      returned, Frame.read, Frame.readOperands, Frame.transfer, evalOp, evaluated, Goldilocks.neg,
      localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem inverse_returns (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (n : Nat) (value : Value) (represented : Number links.conversions.layout n value)
    (valid : (Scalar.nat n).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.inverse 0 #[value] continuation)
      (returned (.ctor links.conversions.layout.field #[.scalar (.field (Goldilocks.reduce n).inverse)])
        continuation) := by
  have localRoom : ∀ k, k ≤ 11 → ¬limits.locals < k := by omega
  have observed := certificate.conversions.call_asField limits room capacity
    { function := links.inverse, block := 0, locals := #[value] } (.local 0) 1 n value represented valid
    { function := links.inverse, block := 1, locals := #[value, .scalar (.field (Goldilocks.reduce n))] }
    (by simp [Frame.check, certificate.inverse.code, invert, localRoom,
      bind, Except.bind, pure, Except.pure]) rfl
    (by simp [Frame.transfer, Frame.check, certificate.inverse.code, invert, localRoom,
      bind, Except.bind, pure, Except.pure]) continuation stack
  have evaluated := eval_fieldInverse limits (Goldilocks.reduce n)
  apply observed.trans
  apply reaches_of_chunk (fuel := 3) (count := 0)
  iterate 3
    rw [runChunk]
    simp [step, stepEval, Frame.check, certificate.inverse.code, invert, certificate.conversions.field,
      returned, Frame.read, Frame.readOperands, Frame.transfer, evalOp, evaluated,
      localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem pack_returns (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.pack 0 #[left, right] continuation)
      (returned (.scalar (.extField ⟨Goldilocks.reduce a, Goldilocks.reduce b⟩)) continuation) := by
  have localRoom : ∀ k, k ≤ 11 → ¬limits.locals < k := by omega
  have observed := certificate.conversions.read_fields certificate.pack rfl rfl _ rfl limits room capacity
    a b left right leftRep rightRep leftValid rightValid continuation stack
  have evaluated := eval_extPack limits (Goldilocks.reduce a) (Goldilocks.reduce b)
  apply observed.trans
  apply reaches_of_chunk (fuel := 2) (count := 0)
  iterate 2
    rw [runChunk]
    simp [step, stepEval, Frame.check, certificate.pack.code, FieldArithmetic.pack,
      frameState, returned, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
      evaluated, localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem reduce_evaluates (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (stack : 3 ≤ limits.continuations) (n : Nat) (value : Value)
    (represented : Number links.conversions.layout n value)
    (valid : (Scalar.nat n).validate limits = .ok ())
    (entry : program.entry = links.reduce) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [value] = .ok ()) :
    Evaluates limits program #[value]
      (.ctor links.conversions.layout.field #[.scalar (.field (Goldilocks.reduce n))]) := by
  apply (certificate.reduce_returns limits room capacity n value represented valid #[]
    (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.reduce.code, FieldArithmetic.reduce,
    Frame.check, inputs, frameState, show ¬limits.locals < 1 by omega,
    bind, Except.bind, pure, Except.pure]

theorem neg_evaluates (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (stack : 3 ≤ limits.continuations) (n : Nat) (value : Value)
    (represented : Number links.conversions.layout n value)
    (valid : (Scalar.nat n).validate limits = .ok ())
    (entry : program.entry = links.neg) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [value] = .ok ()) :
    Evaluates limits program #[value]
      (.ctor links.conversions.layout.field #[.scalar (.field (Goldilocks.reduce n).neg)]) := by
  apply (certificate.neg_returns limits room capacity n value represented valid #[]
    (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.neg.code, negate,
    Frame.check, inputs, frameState, show ¬limits.locals < 1 by omega,
    bind, Except.bind, pure, Except.pure]

theorem inverse_evaluates (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (stack : 3 ≤ limits.continuations) (n : Nat) (value : Value)
    (represented : Number links.conversions.layout n value)
    (valid : (Scalar.nat n).validate limits = .ok ())
    (entry : program.entry = links.inverse) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [value] = .ok ()) :
    Evaluates limits program #[value]
      (.ctor links.conversions.layout.field #[.scalar (.field (Goldilocks.reduce n).inverse)]) := by
  apply (certificate.inverse_returns limits room capacity n value represented valid #[]
    (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.inverse.code, invert,
    Frame.check, inputs, frameState, show ¬limits.locals < 1 by omega,
    bind, Except.bind, pure, Except.pure]

theorem add_evaluates (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (stack : 3 ≤ limits.continuations) (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (entry : program.entry = links.add) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right]
      (.ctor links.conversions.layout.field
        #[.scalar (.field ((Goldilocks.reduce a).add (Goldilocks.reduce b)))]) := by
  apply (certificate.add_returns limits room capacity a b left right leftRep rightRep
    leftValid rightValid #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.add.code, binary,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem sub_evaluates (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (stack : 3 ≤ limits.continuations) (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (entry : program.entry = links.sub) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right]
      (.ctor links.conversions.layout.field
        #[.scalar (.field ((Goldilocks.reduce a).sub (Goldilocks.reduce b)))]) := by
  apply (certificate.sub_returns limits room capacity a b left right leftRep rightRep
    leftValid rightValid #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.sub.code, binary,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem mul_evaluates (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (stack : 3 ≤ limits.continuations) (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (entry : program.entry = links.mul) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right]
      (.ctor links.conversions.layout.field
        #[.scalar (.field ((Goldilocks.reduce a).mul (Goldilocks.reduce b)))]) := by
  apply (certificate.mul_returns limits room capacity a b left right leftRep rightRep
    leftValid rightValid #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.mul.code, binary,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem pack_evaluates (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (stack : 3 ≤ limits.continuations) (a b : Nat) (left right : Value)
    (leftRep : Number links.conversions.layout a left) (rightRep : Number links.conversions.layout b right)
    (leftValid : (Scalar.nat a).validate limits = .ok ())
    (rightValid : (Scalar.nat b).validate limits = .ok ())
    (entry : program.entry = links.pack) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right]
      (.scalar (.extField ⟨Goldilocks.reduce a, Goldilocks.reduce b⟩)) := by
  apply (certificate.pack_returns limits room capacity a b left right leftRep rightRep
    leftValid rightValid #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.pack.code, FieldArithmetic.pack,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

end Certificate
end Compilatrix.Ixby.Runtime.FieldArithmetic
