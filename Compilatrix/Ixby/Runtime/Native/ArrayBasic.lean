import Compilatrix.Ixby.Runtime.Native.Machine
import Compilatrix.Ixby.Runtime.Native.CollectionLaws

/-! Public array helpers retain erased source slots and use native persistent
arrays. Index bounds are exact Nat bounds; invalid set preserves its input. -/

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby Execution Representation ScalarFunction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

variable {program : Program} (certificate : Certificate program) (limits : Limits)

include certificate

theorem Certificate.arraySize_returns (room : 4 ≤ limits.locals) (typeValue : Value)
    (values : Array Value) (bound : values.size < 2 ^ 32) (valid : NatValid limits values.size)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 58 0 #[typeValue, arrayValue values] continuation)
      (returned (natural values.size) continuation) := by
  have code := (certificate.function 58).code
  change program.getFunction 58 = .ok Code.Array_size at code
  have evaluated := eval_arrayLength limits values bound valid
  have localRoom : ∀ k, k ≤ 4 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 3) (count := 0)
  iterate 3
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.Array_size, frameState, returned,
      certificate.bytesCtor, certificate.arrayCtor, selectCase, arrayValue, arrayId,
      Frame.read, Frame.readOperands, Frame.transfer, evalOp, evaluated, localRoom,
      bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.arrayEmpty_returns {id : FunctionId}
    (checked : Checked program id Code.Array_mkEmpty) (room : 4 ≤ limits.locals)
    (typeValue capacity : Value) (continuation : Array Continuation) :
    Reaches limits program (frameState id 0 #[typeValue, capacity] continuation)
      (returned (arrayValue #[]) continuation) := by
  have localRoom : ∀ k, k ≤ 4 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 3) (count := 0)
  iterate 3
    rw [runChunk]
    simp [step, stepEval, Frame.check, checked.code, Code.Array_mkEmpty, frameState, returned,
      certificate.arrayCtor, arrayValue, arrayId, Frame.read, Frame.readOperands, Frame.transfer,
      evalOp, eval_arrayEmpty, localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.arrayPush_returns (room : 6 ≤ limits.locals) (typeValue : Value)
    (values : Array Value) (value : Value) (bound : values.size + 1 < 2 ^ 32)
    (argument : ArgumentValid limits value) (continuation : Array Continuation) :
    Reaches limits program (frameState 68 0 #[typeValue, arrayValue values, value] continuation)
      (returned (arrayValue (values.push value)) continuation) := by
  have code := (certificate.function 68).code
  change program.getFunction 68 = .ok Code.Array_push at code
  have evaluated := eval_arrayPush limits values value bound argument
  have localRoom : ∀ k, k ≤ 6 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 4) (count := 0)
  iterate 4
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.Array_push, frameState, returned,
      certificate.bytesCtor, certificate.arrayCtor, selectCase, arrayValue, arrayId,
      Frame.read, Frame.readOperands, Frame.transfer, evalOp, evaluated, localRoom,
      bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.arrayGet_returns (room : 8 ≤ limits.locals) (typeValue proofValue : Value)
    (values : Array Value) (index : Nat) (value : Value) (bound : values.size < 2 ^ 32)
    (sizeValid : NatValid limits values.size) (indexValid : NatValid limits index)
    (inside : index < values.size) (found : values[index]? = some value)
    (result : ResultValid limits value) (continuation : Array Continuation)
    (stack : continuation.size < limits.continuations) :
    Reaches limits program (frameState 62 0 #[typeValue, arrayValue values, natural index, proofValue] continuation)
      (returned value continuation) := by
  have code := (certificate.function 62).code
  have sizeCode := (certificate.function 58).code
  change program.getFunction 62 = .ok Code.Array_getInternal at code
  change program.getFunction 58 = .ok Code.Array_size at sizeCode
  have sizeEval := eval_arrayLength limits values bound sizeValid
  have compare := eval_natLt limits index values.size indexValid sizeValid
  have getEval := eval_arrayGet limits values index value bound indexValid found result
  simp only [natural] at getEval
  have localRoom : ∀ k, k ≤ 8 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 10) (count := 0)
  iterate 10
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, sizeCode, Code.Array_getInternal, Code.Array_size,
      frameState, returned, certificate.bytesCtor, certificate.arrayCtor, selectCase, arrayValue, arrayId,
      State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp, sizeEval, getEval,
      compare, natural, inside, localRoom, Nat.not_le.mpr stack, bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.arraySet_returns (room : 9 ≤ limits.locals) (typeValue : Value)
    (values : Array Value) (index : Nat) (value : Value) (bound : values.size < 2 ^ 32)
    (sizeValid : NatValid limits values.size) (indexValid : NatValid limits index)
    (argument : ArgumentValid limits value) (continuation : Array Continuation)
    (stack : continuation.size < limits.continuations) :
    Reaches limits program (frameState 69 0 #[typeValue, arrayValue values, natural index, value] continuation)
      (returned (arrayValue (values.set! index value)) continuation) := by
  have code := (certificate.function 69).code
  have sizeCode := (certificate.function 58).code
  change program.getFunction 69 = .ok Code.Array_setBang at code
  change program.getFunction 58 = .ok Code.Array_size at sizeCode
  have sizeEval := eval_arrayLength limits values bound sizeValid
  have compare := eval_natLt limits index values.size indexValid sizeValid
  have localRoom : ∀ k, k ≤ 9 → ¬limits.locals < k := by omega
  by_cases inside : index < values.size
  · have setEval := eval_arraySet limits values index value bound indexValid inside argument
    simp only [natural] at setEval
    apply reaches_of_chunk (fuel := 11) (count := 0)
    iterate 11
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, sizeCode, Code.Array_setBang, Code.Array_size,
        frameState, returned, certificate.bytesCtor, certificate.arrayCtor, selectCase, arrayValue, arrayId,
        State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp, sizeEval, setEval,
        compare, natural, inside, localRoom, Nat.not_le.mpr stack, bind, Except.bind, pure, Except.pure]
    rfl
  · have unchanged : values.set! index value = values :=
      Array.setIfInBounds_eq_of_size_le (by omega)
    rw [unchanged]
    apply reaches_of_chunk (fuel := 8) (count := 0)
    iterate 8
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, sizeCode, Code.Array_setBang, Code.Array_size,
        frameState, returned, certificate.bytesCtor, certificate.arrayCtor, selectCase, arrayValue, arrayId,
        State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp, sizeEval,
        compare, natural, inside, localRoom, Nat.not_le.mpr stack, bind, Except.bind, pure, Except.pure]
    rfl

omit certificate in
/-- The resulting version and the original alias both represent their own
source sequence, including when the source index is outside the array. -/
theorem Certificate.arraySet_preserves_alias {α : Type} (encode : α → Value)
    (source : Array α) (index : Nat) (value : α) :
    ArrayRep encode source (arrayValue (source.map encode)) ∧
    ArrayRep encode (source.set! index value)
      (arrayValue ((source.map encode).set! index (encode value))) :=
  arrayRep_alias encode source index value

end Compilatrix.Ixby.Runtime.Native
