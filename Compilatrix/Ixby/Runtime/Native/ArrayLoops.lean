import Compilatrix.Ixby.Runtime.Native.ArrayBasic
import Compilatrix.Ixby.Runtime.Native.Sequence

/-! The native copy loop preserves a source sequence with an arbitrary
accumulator. The two saved callers cover the loop's get and its size call. -/

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby Execution Representation ScalarFunction Conversion

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

variable {program : Program} (certificate : Certificate program) (limits : Limits)

include certificate

theorem Certificate.extractLoop_returns (room : 10 ≤ limits.locals) (capacity : 32 ≤ limits.natBits)
    (values : Array Value) (elements : ElementsValid limits values) (bound : values.size < 2 ^ 32)
    (start count : Nat) (accumulator : Array Value) (range : start + count ≤ values.size)
    (resultBound : accumulator.size + count < 2 ^ 32)
    (continuation : Array Continuation) (stack : continuation.size + 2 ≤ limits.continuations) :
    Reaches limits program
      (frameState 56 0 #[arrayValue values, natural start, natural (start + count), arrayValue accumulator] continuation)
      (returned (arrayValue (accumulator ++ values.extract start (start + count))) continuation) := by
  have code := (certificate.function 56).code
  have getCode := (certificate.function 62).code
  have pushCode := (certificate.function 68).code
  change program.getFunction 56 = .ok Code.Ixby_Runtime_extract at code
  change program.getFunction 62 = .ok Code.Array_getInternal at getCode
  change program.getFunction 68 = .ok Code.Array_push at pushCode
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  have sizeValid := natValid_array_index limits capacity values.size bound
  have oneValid := validate_nat_of_bits (by decide : 1 < 2 ^ 32) capacity
  induction count generalizing start accumulator with
  | zero =>
    have indexValid := natValid_array_index limits capacity start (by omega)
    have compare := eval_natLt limits start start indexValid indexValid
    have empty : values.extract start start = #[] := Array.extract_eq_empty_of_le (by omega)
    apply reaches_of_chunk (fuel := 3) (count := 0)
    iterate 3
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, Code.Ixby_Runtime_extract, frameState, returned,
        Frame.read, Frame.readOperands, Frame.transfer, evalOp, natural, compare, empty,
        localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  | succ count ih =>
    have inside : start < values.size := by omega
    have indexValid := natValid_array_index limits capacity start (by omega)
    have stopValid := natValid_array_index limits capacity (start + (count + 1)) (by omega)
    have nextValid := natValid_array_index limits capacity (start + 1) (by omega)
    have compare := eval_natLt limits start (start + (count + 1)) indexValid stopValid
    have increment := eval_natAdd limits start 1 indexValid oneValid nextValid
    have valid := elements values[start] (Array.getElem_mem inside)
    let initial := #[arrayValue values, natural start, natural (start + (count + 1)), arrayValue accumulator]
    let getLocals := initial.push (.scalar (.bool true))
    let pushLocals := getLocals.push values[start]
    let nextLocals := pushLocals.push (arrayValue (accumulator.push values[start]))
    have beforeGet : Reaches limits program (frameState 56 0 initial continuation)
        (frameState 56 2 getLocals continuation) := by
      apply reaches_of_chunk (fuel := 2) (count := 0)
      iterate 2
        rw [runChunk]
        simp [step, stepEval, Frame.check, code, Code.Ixby_Runtime_extract, frameState,
          initial, getLocals, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
          natural, compare, show start < start + (count + 1) by omega,
          localRoom, bind, Except.bind, pure, Except.pure]
      rfl
    have getPath := call_returns limits program
      { function := 56, block := 2, locals := getLocals } 62
      [.erased, .local 0, .local 1, .erased]
      #[.erased, arrayValue values, natural start, .erased] 4 values[start]
      { function := 56, block := 4, locals := pushLocals } continuation (by omega)
      (by simp [Frame.check, code, Code.Ixby_Runtime_extract, getLocals, initial, localRoom,
        bind, Except.bind, pure, Except.pure]) rfl
      (by simp [enter, Frame.check, getCode, Code.Array_getInternal, localRoom,
        bind, Except.bind, pure, Except.pure])
      (by simp [Frame.transfer, Frame.check, code, Code.Ixby_Runtime_extract,
        initial, getLocals, pushLocals, localRoom, bind, Except.bind, pure, Except.pure])
      (certificate.arrayGet_returns limits (by omega) .erased .erased values start values[start]
        bound sizeValid indexValid inside (by simp) valid.2 _ (by simp; omega))
    have pushPath := call_returns limits program
      { function := 56, block := 4, locals := pushLocals } 68
      [.erased, .local 3, .local 5]
      #[.erased, arrayValue accumulator, values[start]] 5 (arrayValue (accumulator.push values[start]))
      { function := 56, block := 5, locals := nextLocals } continuation (by omega)
      (by simp [Frame.check, code, Code.Ixby_Runtime_extract, pushLocals, getLocals, initial, localRoom,
        bind, Except.bind, pure, Except.pure]) rfl
      (by simp [enter, Frame.check, pushCode, Code.Array_push, localRoom,
        bind, Except.bind, pure, Except.pure])
      (by simp [Frame.transfer, Frame.check, code, Code.Ixby_Runtime_extract,
        initial, getLocals, pushLocals, nextLocals, localRoom, bind, Except.bind, pure, Except.pure])
      (certificate.arrayPush_returns limits (by omega) .erased accumulator values[start]
        (by omega) valid.1 _)
    have nextLoop : Reaches limits program (frameState 56 5 nextLocals continuation)
        (frameState 56 0 #[arrayValue values, natural (start + 1), natural (start + (count + 1)),
          arrayValue (accumulator.push values[start])] continuation) := by
      apply reaches_of_chunk (fuel := 2) (count := 0)
      iterate 2
        rw [runChunk]
        simp [step, stepEval, Frame.check, code, Code.Ixby_Runtime_extract, frameState,
          initial, getLocals, pushLocals, nextLocals, Frame.read, Frame.readOperands, Frame.transfer,
          enter, evalOp, natural, increment, localRoom, bind, Except.bind, pure, Except.pure]
      rfl
    have sameStop : start + 1 + count = start + (count + 1) := by omega
    have recursive := ih (start + 1) (accumulator.push values[start]) (by omega) (by simp; omega)
    rw [sameStop] at recursive
    have invariant := extract_accumulator values accumulator start (start + (count + 1)) (by omega) range
    rw [invariant] at recursive
    exact beforeGet.trans (getPath.trans (pushPath.trans (nextLoop.trans recursive)))

end Compilatrix.Ixby.Runtime.Native
