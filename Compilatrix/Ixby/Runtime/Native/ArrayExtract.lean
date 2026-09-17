import Compilatrix.Ixby.Runtime.Native.ArrayLoops

/-! Extract clamps its upper bound to source length. Invalid and reversed
ranges produce the empty native array before any native index operation. -/

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby Execution Representation ScalarFunction Conversion

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

variable {program : Program} (certificate : Certificate program) (limits : Limits)

include certificate

theorem Certificate.arrayExtractRed_returns (room : 10 ≤ limits.locals) (capacity : 32 ≤ limits.natBits)
    (values : Array Value) (elements : ElementsValid limits values) (bound : values.size < 2 ^ 32)
    (start stop : Nat) (startValid : NatValid limits start) (stopValid : NatValid limits stop)
    (continuation : Array Continuation) (stack : continuation.size + 2 ≤ limits.continuations) :
    Reaches limits program (frameState 72 0 #[arrayValue values, natural start, natural stop] continuation)
      (returned (arrayValue (values.extract start stop)) continuation) := by
  have code := (certificate.function 72).code
  have sizeCode := (certificate.function 58).code
  have emptyCode := (certificate.function 61).code
  have loopCode := (certificate.function 56).code
  change program.getFunction 72 = .ok Code.Array_extract__redArg at code
  change program.getFunction 58 = .ok Code.Array_size at sizeCode
  change program.getFunction 61 = .ok Code.Array_mkEmpty at emptyCode
  change program.getFunction 56 = .ok Code.Ixby_Runtime_extract at loopCode
  have sizeValid := natValid_array_index limits capacity values.size bound
  have sizeEval := eval_arrayLength limits values bound sizeValid
  have sizeCompare := eval_natLt limits values.size stop sizeValid stopValid
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  have stackRoom : ¬limits.continuations ≤ continuation.size := by omega
  by_cases above : values.size < stop
  · have compare := eval_natLt limits start values.size startValid sizeValid
    have cropped : values.extract start stop = values.extract start values.size := Array.extract_of_size_lt above
    rw [cropped]
    by_cases inside : start < values.size
    · apply Reaches.trans (b := frameState 56 0 #[arrayValue values, natural start, natural values.size, arrayValue #[]] continuation)
      · apply reaches_of_chunk (fuel := 16) (count := 0)
        iterate 16
          rw [runChunk]
          simp [step, stepEval, Frame.check, code, sizeCode, emptyCode, loopCode, Code.Array_extract__redArg,
            Code.Array_size, Code.Array_mkEmpty, Code.Ixby_Runtime_extract, frameState,
            certificate.bytesCtor, certificate.arrayCtor, selectCase, arrayValue, arrayId,
            State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp, sizeEval,
            sizeCompare, compare, natural, above, inside, eval_arrayEmpty, localRoom, stackRoom,
            bind, Except.bind, pure, Except.pure]
        rfl
      · have stopEq : start + (values.size - start) = values.size := by omega
        have path := certificate.extractLoop_returns limits room capacity values elements bound
          start (values.size - start) #[] (by omega) (by simp; omega) continuation stack
        simpa only [stopEq, Array.empty_append] using path
    · have empty : values.extract start values.size = #[] := Array.extract_eq_empty_of_le (by omega)
      rw [empty]
      apply reaches_of_chunk (fuel := 12) (count := 0)
      iterate 12
        rw [runChunk]
        simp [step, stepEval, Frame.check, code, sizeCode, Code.Array_extract__redArg, Code.Array_size,
          frameState, returned, certificate.bytesCtor, certificate.arrayCtor, selectCase, arrayValue, arrayId,
          State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp, sizeEval,
          sizeCompare, compare, natural, above, inside, eval_arrayEmpty, localRoom, stackRoom,
          bind, Except.bind, pure, Except.pure]
      rfl
  · have compare := eval_natLt limits start stop startValid stopValid
    by_cases inside : start < stop
    · apply Reaches.trans (b := frameState 56 0 #[arrayValue values, natural start, natural stop, arrayValue #[]] continuation)
      · apply reaches_of_chunk (fuel := 16) (count := 0)
        iterate 16
          rw [runChunk]
          simp [step, stepEval, Frame.check, code, sizeCode, emptyCode, loopCode, Code.Array_extract__redArg,
            Code.Array_size, Code.Array_mkEmpty, Code.Ixby_Runtime_extract, frameState,
            certificate.bytesCtor, certificate.arrayCtor, selectCase, arrayValue, arrayId,
            State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp, sizeEval,
            sizeCompare, compare, natural, above, inside, eval_arrayEmpty, localRoom, stackRoom,
            bind, Except.bind, pure, Except.pure]
        rfl
      · have stopEq : start + (stop - start) = stop := by omega
        have path := certificate.extractLoop_returns limits room capacity values elements bound
          start (stop - start) #[] (by omega) (by simp; omega) continuation stack
        simpa only [stopEq, Array.empty_append] using path
    · have empty : values.extract start stop = #[] := Array.extract_eq_empty_of_le (by omega)
      rw [empty]
      apply reaches_of_chunk (fuel := 12) (count := 0)
      iterate 12
        rw [runChunk]
        simp [step, stepEval, Frame.check, code, sizeCode, Code.Array_extract__redArg, Code.Array_size,
          frameState, returned, certificate.bytesCtor, certificate.arrayCtor, selectCase, arrayValue, arrayId,
          State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp, sizeEval,
          sizeCompare, compare, natural, above, inside, eval_arrayEmpty, localRoom, stackRoom,
          bind, Except.bind, pure, Except.pure]
      rfl

theorem Certificate.arrayExtract_returns (room : 10 ≤ limits.locals) (capacity : 32 ≤ limits.natBits)
    (typeValue : Value) (values : Array Value) (elements : ElementsValid limits values)
    (bound : values.size < 2 ^ 32) (start stop : Nat) (startValid : NatValid limits start)
    (stopValid : NatValid limits stop) (continuation : Array Continuation)
    (stack : continuation.size + 2 ≤ limits.continuations) :
    Reaches limits program (frameState 71 0 #[typeValue, arrayValue values, natural start, natural stop] continuation)
      (returned (arrayValue (values.extract start stop)) continuation) := by
  have code := (certificate.function 71).code
  have body := (certificate.function 72).code
  change program.getFunction 71 = .ok Code.Array_extract at code
  change program.getFunction 72 = .ok Code.Array_extract__redArg at body
  apply Reaches.trans (b := frameState 72 0 #[arrayValue values, natural start, natural stop] continuation)
  · apply Reaches.of_step
    simp [step, stepEval, Frame.check, code, body, Code.Array_extract, Code.Array_extract__redArg,
      frameState, Frame.read, Frame.readOperands, enter, show ¬limits.locals < 3 by omega,
      show ¬limits.locals < 4 by omega, bind, Except.bind, pure, Except.pure]
  · exact certificate.arrayExtractRed_returns limits room capacity values elements bound start stop
      startValid stopValid continuation stack

end Compilatrix.Ixby.Runtime.Native
