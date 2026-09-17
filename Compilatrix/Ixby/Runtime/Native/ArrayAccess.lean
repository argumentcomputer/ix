import Compilatrix.Ixby.Runtime.Native.ArrayBasic

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby Execution Representation ScalarFunction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

variable {program : Program} (certificate : Certificate program) (limits : Limits)

include certificate

theorem Certificate.arrayUsize_returns (room : 4 ≤ limits.locals) (typeValue : Value)
    (values : Array Value) (bound : values.size < 2 ^ 32) (valid : NatValid limits values.size)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 59 0 #[typeValue, arrayValue values] continuation)
      (returned (natural values.size) continuation) := by
  have code := (certificate.function 59).code
  have sizeCode := (certificate.function 58).code
  change program.getFunction 59 = .ok Code.Array_usize at code
  change program.getFunction 58 = .ok Code.Array_size at sizeCode
  apply Reaches.trans (b := frameState 58 0 #[.erased, arrayValue values] continuation)
  · apply Reaches.of_step
    simp [step, stepEval, Frame.check, code, sizeCode, Code.Array_usize, Code.Array_size, frameState,
      Frame.read, Frame.readOperands, enter, show ¬limits.locals < 2 by omega,
      bind, Except.bind, pure, Except.pure]
  · exact certificate.arraySize_returns limits room .erased values bound valid continuation

theorem Certificate.arrayGetAlias_returns {id : FunctionId}
    (checked : Checked program id Code.Array_getInternalBorrowed)
    (room : 8 ≤ limits.locals) (typeValue proofValue : Value)
    (values : Array Value) (index : Nat) (value : Value) (bound : values.size < 2 ^ 32)
    (sizeValid : NatValid limits values.size) (indexValid : NatValid limits index)
    (inside : index < values.size) (found : values[index]? = some value)
    (result : ResultValid limits value) (continuation : Array Continuation)
    (stack : continuation.size < limits.continuations) :
    Reaches limits program (frameState id 0 #[typeValue, arrayValue values, natural index, proofValue] continuation)
      (returned value continuation) := by
  have getCode := (certificate.function 62).code
  change program.getFunction 62 = .ok Code.Array_getInternal at getCode
  apply Reaches.trans (b := frameState 62 0 #[.erased, arrayValue values, natural index, .erased] continuation)
  · apply Reaches.of_step
    simp [step, stepEval, Frame.check, checked.code, getCode, Code.Array_getInternalBorrowed,
      Code.Array_getInternal, frameState, Frame.read, Frame.readOperands, enter,
      show ¬limits.locals < 4 by omega, bind, Except.bind, pure, Except.pure]
  · exact certificate.arrayGet_returns limits room .erased .erased values index value bound
      sizeValid indexValid inside found result continuation stack

theorem Certificate.arrayGetBang_inside_returns {id : FunctionId}
    (checked : Checked program id Code.Array_getBangInternal)
    (room : 8 ≤ limits.locals) (typeValue fallback : Value)
    (values : Array Value) (index : Nat) (value : Value) (bound : values.size < 2 ^ 32)
    (sizeValid : NatValid limits values.size) (indexValid : NatValid limits index)
    (inside : index < values.size) (found : values[index]? = some value)
    (result : ResultValid limits value) (continuation : Array Continuation)
    (stack : continuation.size < limits.continuations) :
    Reaches limits program (frameState id 0 #[typeValue, fallback, arrayValue values, natural index] continuation)
      (returned value continuation) := by
  have getCode := (certificate.function 62).code
  have sizeCode := (certificate.function 58).code
  change program.getFunction 62 = .ok Code.Array_getInternal at getCode
  change program.getFunction 58 = .ok Code.Array_size at sizeCode
  have sizeEval := eval_arrayLength limits values bound sizeValid
  have compare := eval_natLt limits index values.size indexValid sizeValid
  have localRoom : ∀ k, k ≤ 8 → ¬limits.locals < k := by omega
  apply Reaches.trans (b := frameState 62 0 #[.erased, arrayValue values, natural index, .erased] continuation)
  · apply reaches_of_chunk (fuel := 8) (count := 0)
    iterate 8
      rw [runChunk]
      simp [step, stepEval, Frame.check, checked.code, getCode, sizeCode, Code.Array_getBangInternal,
        Code.Array_getInternal, Code.Array_size, frameState, certificate.bytesCtor, certificate.arrayCtor,
        selectCase, arrayValue, arrayId, State.push, enter, Frame.read, Frame.readOperands, Frame.transfer,
        evalOp, sizeEval, compare, natural, inside, localRoom, Nat.not_le.mpr stack,
        bind, Except.bind, pure, Except.pure]
    rfl
  · exact certificate.arrayGet_returns limits room .erased .erased values index value bound
      sizeValid indexValid inside found result continuation stack

theorem Certificate.arrayGetBang_outside_returns {id : FunctionId}
    (checked : Checked program id Code.Array_getBangInternal)
    (room : 6 ≤ limits.locals) (typeValue fallback : Value)
    (values : Array Value) (index : Nat) (bound : values.size < 2 ^ 32)
    (sizeValid : NatValid limits values.size) (indexValid : NatValid limits index)
    (outside : values.size ≤ index) (continuation : Array Continuation)
    (stack : continuation.size < limits.continuations) :
    Reaches limits program (frameState id 0 #[typeValue, fallback, arrayValue values, natural index] continuation)
      (returned fallback continuation) := by
  have sizeCode := (certificate.function 58).code
  change program.getFunction 58 = .ok Code.Array_size at sizeCode
  have sizeEval := eval_arrayLength limits values bound sizeValid
  have compare := eval_natLt limits index values.size indexValid sizeValid
  have localRoom : ∀ k, k ≤ 6 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 8) (count := 0)
  iterate 8
    rw [runChunk]
    simp [step, stepEval, Frame.check, checked.code, sizeCode, Code.Array_getBangInternal, Code.Array_size,
      frameState, returned, certificate.bytesCtor, certificate.arrayCtor, selectCase, arrayValue, arrayId,
      State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp, sizeEval, compare,
      natural, Nat.not_lt.mpr outside, localRoom, Nat.not_le.mpr stack,
      bind, Except.bind, pure, Except.pure]
  rfl

/-- An invalid set does not inspect or validate the replacement element. -/
theorem Certificate.arraySet_outside_returns (room : 6 ≤ limits.locals) (typeValue : Value)
    (values : Array Value) (index : Nat) (value : Value) (bound : values.size < 2 ^ 32)
    (sizeValid : NatValid limits values.size) (indexValid : NatValid limits index)
    (outside : values.size ≤ index) (continuation : Array Continuation)
    (stack : continuation.size < limits.continuations) :
    Reaches limits program (frameState 69 0 #[typeValue, arrayValue values, natural index, value] continuation)
      (returned (arrayValue values) continuation) := by
  have code := (certificate.function 69).code
  have sizeCode := (certificate.function 58).code
  change program.getFunction 69 = .ok Code.Array_setBang at code
  change program.getFunction 58 = .ok Code.Array_size at sizeCode
  have sizeEval := eval_arrayLength limits values bound sizeValid
  have compare := eval_natLt limits index values.size indexValid sizeValid
  have localRoom : ∀ k, k ≤ 6 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 8) (count := 0)
  iterate 8
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, sizeCode, Code.Array_setBang, Code.Array_size,
      frameState, returned, certificate.bytesCtor, certificate.arrayCtor, selectCase, arrayValue, arrayId,
      State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp, sizeEval, compare,
      natural, Nat.not_lt.mpr outside, localRoom, Nat.not_le.mpr stack,
      bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.arrayUset_returns (room : 9 ≤ limits.locals) (typeValue proofValue : Value)
    (values : Array Value) (index : Nat) (value : Value) (bound : values.size < 2 ^ 32)
    (sizeValid : NatValid limits values.size) (indexValid : NatValid limits index)
    (inside : index < values.size) (argument : ArgumentValid limits value)
    (continuation : Array Continuation) (stack : continuation.size < limits.continuations) :
    Reaches limits program (frameState 70 0 #[typeValue, arrayValue values, natural index, value, proofValue] continuation)
      (returned (arrayValue (values.set! index value)) continuation) := by
  have code := (certificate.function 70).code
  have setCode := (certificate.function 69).code
  have sizeCode := (certificate.function 58).code
  change program.getFunction 70 = .ok Code.Array_uset at code
  change program.getFunction 69 = .ok Code.Array_setBang at setCode
  change program.getFunction 58 = .ok Code.Array_size at sizeCode
  have sizeEval := eval_arrayLength limits values bound sizeValid
  have compare := eval_natLt limits index values.size indexValid sizeValid
  have localRoom : ∀ k, k ≤ 9 → ¬limits.locals < k := by omega
  apply Reaches.trans (b := frameState 69 0 #[.erased, arrayValue values, natural index, value] continuation)
  · apply reaches_of_chunk (fuel := 8) (count := 0)
    iterate 8
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, setCode, sizeCode, Code.Array_uset, Code.Array_setBang,
        Code.Array_size, frameState, certificate.bytesCtor, certificate.arrayCtor, selectCase,
        arrayValue, arrayId, State.push, enter, Frame.read, Frame.readOperands, Frame.transfer,
        evalOp, sizeEval, compare, natural, inside, localRoom, Nat.not_le.mpr stack,
        bind, Except.bind, pure, Except.pure]
    rfl
  · exact certificate.arraySet_returns limits room .erased values index value bound sizeValid indexValid
      argument continuation stack

end Compilatrix.Ixby.Runtime.Native
