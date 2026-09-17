import Compilatrix.Ixby.Runtime.Native.ArrayLoops

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby Execution Representation ScalarFunction Conversion

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

variable {program : Program} (certificate : Certificate program) (limits : Limits)

include certificate

theorem Certificate.arrayAppendRed_returns (room : 10 ≤ limits.locals) (capacity : 32 ≤ limits.natBits)
    (a b : Array Value) (elements : ElementsValid limits b) (bound : a.size + b.size < 2 ^ 32)
    (continuation : Array Continuation) (stack : continuation.size + 2 ≤ limits.continuations) :
    Reaches limits program (frameState 74 0 #[arrayValue a, arrayValue b] continuation)
      (returned (arrayValue (a ++ b)) continuation) := by
  have code := (certificate.function 74).code
  have sizeCode := (certificate.function 58).code
  have copyCode := (certificate.function 55).code
  have loopCode := (certificate.function 56).code
  change program.getFunction 74 = .ok Code.Array_append__redArg at code
  change program.getFunction 58 = .ok Code.Array_size at sizeCode
  change program.getFunction 55 = .ok Code.Ixby_Runtime_copyArray at copyCode
  change program.getFunction 56 = .ok Code.Ixby_Runtime_extract at loopCode
  have leftValid := natValid_array_index limits capacity a.size (by omega)
  have rightValid := natValid_array_index limits capacity b.size (by omega)
  have zeroValid := natValid_array_index limits capacity 0 (by decide)
  have leftSize := eval_arrayLength limits a (by omega) leftValid
  have rightSize := eval_arrayLength limits b (by omega) rightValid
  have leftTest := eval_natEq limits a.size 0 leftValid zeroValid
  have rightTest := eval_natEq limits b.size 0 rightValid zeroValid
  have zeroTest := eval_natEq limits 0 0 zeroValid zeroValid
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  have stackRoom : ¬limits.continuations ≤ continuation.size := by omega
  by_cases leftEmpty : a.size = 0
  · have empty : a = #[] := Array.size_eq_zero_iff.mp leftEmpty
    have result : a ++ b = b := by simp [empty]
    apply reaches_of_chunk (fuel := 13) (count := 0)
    iterate 13
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, sizeCode, Code.Array_append__redArg, Code.Array_size,
        frameState, returned, certificate.bytesCtor, certificate.arrayCtor, selectCase, arrayValue, arrayId,
        State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp, leftSize, rightSize,
        leftTest, zeroTest, natural, leftEmpty, result, localRoom, stackRoom, bind, Except.bind, pure, Except.pure]
    rfl
  · by_cases rightEmpty : b.size = 0
    · have empty : b = #[] := Array.size_eq_zero_iff.mp rightEmpty
      have result : a ++ b = a := by simp [empty]
      apply reaches_of_chunk (fuel := 15) (count := 0)
      iterate 15
        rw [runChunk]
        simp [step, stepEval, Frame.check, code, sizeCode, Code.Array_append__redArg, Code.Array_size,
          frameState, returned, certificate.bytesCtor, certificate.arrayCtor, selectCase, arrayValue, arrayId,
          State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp, leftSize, rightSize,
          leftTest, rightTest, zeroTest, natural, leftEmpty, rightEmpty, result, localRoom, stackRoom,
          bind, Except.bind, pure, Except.pure]
      rfl
    · apply Reaches.trans (b := frameState 56 0 #[arrayValue b, natural 0, natural b.size, arrayValue a] continuation)
      · apply reaches_of_chunk (fuel := 20) (count := 0)
        iterate 20
          rw [runChunk]
          simp [step, stepEval, Frame.check, code, sizeCode, copyCode, loopCode, Code.Array_append__redArg,
            Code.Array_size, Code.Ixby_Runtime_copyArray, Code.Ixby_Runtime_extract, frameState,
            certificate.bytesCtor, certificate.arrayCtor, selectCase, arrayValue, arrayId,
            State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp, leftSize, rightSize,
            leftTest, rightTest, natural, leftEmpty, rightEmpty, localRoom, stackRoom,
            bind, Except.bind, pure, Except.pure]
        rfl
      · simpa using certificate.extractLoop_returns limits room capacity b elements (by omega)
          0 b.size a (by omega) bound continuation stack

theorem Certificate.arrayAppend_returns (room : 10 ≤ limits.locals) (capacity : 32 ≤ limits.natBits)
    (typeValue : Value) (a b : Array Value) (elements : ElementsValid limits b)
    (bound : a.size + b.size < 2 ^ 32) (continuation : Array Continuation)
    (stack : continuation.size + 2 ≤ limits.continuations) :
    Reaches limits program (frameState 73 0 #[typeValue, arrayValue a, arrayValue b] continuation)
      (returned (arrayValue (a ++ b)) continuation) := by
  have code := (certificate.function 73).code
  have body := (certificate.function 74).code
  change program.getFunction 73 = .ok Code.Array_append at code
  change program.getFunction 74 = .ok Code.Array_append__redArg at body
  apply Reaches.trans (b := frameState 74 0 #[arrayValue a, arrayValue b] continuation)
  · apply Reaches.of_step
    simp [step, stepEval, Frame.check, code, body, Code.Array_append, Code.Array_append__redArg,
      frameState, Frame.read, Frame.readOperands, enter, show ¬limits.locals < 2 by omega,
      show ¬limits.locals < 3 by omega, bind, Except.bind, pure, Except.pure]
  · exact certificate.arrayAppendRed_returns limits room capacity a b elements bound continuation stack

end Compilatrix.Ixby.Runtime.Native
