import Compilatrix.Ixby.Runtime.Native.ByteWords
import Compilatrix.Ixby.Runtime.Native.Sequence

/-! Serializing a native byte array accumulates an immutable builder and
freezes exactly once. The invariant includes an arbitrary existing prefix. -/

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby Execution Representation ScalarFunction Conversion

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

variable {program : Program} (certificate : Certificate program) (limits : Limits)

include certificate

theorem Certificate.arrayBytes_returns (room : 10 ≤ limits.locals) (capacity : 32 ≤ limits.natBits)
    (wordCapacity : 4 ≤ limits.byteArrayBytes) (bytes : Array UInt8) (bound : bytes.size < 2 ^ 32)
    (start count : Nat) (accumulator : Array UInt8) (range : start + count ≤ bytes.size)
    (resultCapacity : accumulator.size + count ≤ limits.byteArrayBytes)
    (continuation : Array Continuation) :
    Reaches limits program
      (frameState 50 0 #[.array (bytes.map byteWord), natural start, natural (start + count), .byteBuilder accumulator] continuation)
      (returned (.scalar (.bytes (accumulator ++ bytes.extract start (start + count)))) continuation) := by
  have code := (certificate.function 50).code
  change program.getFunction 50 = .ok Code.Ixby_Runtime_arrayBytes at code
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  have oneValid := natValid_array_index limits capacity 1 (by decide)
  induction count generalizing start accumulator with
  | zero =>
    have indexValid := natValid_array_index limits capacity start (by omega)
    have compare := eval_natLt limits start start indexValid indexValid
    have frozen := eval_builderFreeze limits accumulator (by omega)
    have empty : bytes.extract start start = #[] := Array.extract_eq_empty_of_le (by omega)
    apply reaches_of_chunk (fuel := 4) (count := 0)
    iterate 4
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, Code.Ixby_Runtime_arrayBytes, frameState, returned,
        Frame.read, Frame.readOperands, Frame.transfer, evalOp, natural, compare, frozen, empty,
        localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  | succ count ih =>
    have inside : start < bytes.size := by omega
    have indexValid := natValid_array_index limits capacity start (by omega)
    have stopValid := natValid_array_index limits capacity (start + (count + 1)) (by omega)
    have nextValid := natValid_array_index limits capacity (start + 1) (by omega)
    have compare := eval_natLt limits start (start + (count + 1)) indexValid stopValid
    have increment := eval_natAdd limits start 1 indexValid oneValid nextValid
    have getEval := eval_arrayGet limits (bytes.map byteWord) start (byteWord bytes[start])
      (by simpa using bound) indexValid (by simp [inside]) (by rfl)
    have encoded := eval_word32ToBytes limits bytes[start].toUInt32 wordCapacity
    have sliced := eval_byteSlice limits bytes[start] wordCapacity
    have appended := eval_builderAppend limits accumulator #[bytes[start]] (by simp; omega)
    simp only [natural, byteWord, word, UInt8.toNat_toUInt32, Array.append_singleton] at getEval encoded sliced appended
    have beforeLoop : Reaches limits program
        (frameState 50 0 #[.array (bytes.map byteWord), natural start, natural (start + (count + 1)), .byteBuilder accumulator] continuation)
        (frameState 50 0 #[.array (bytes.map byteWord), natural (start + 1), natural (start + (count + 1)),
          .byteBuilder (accumulator.push bytes[start])] continuation) := by
      apply reaches_of_chunk (fuel := 8) (count := 0)
      iterate 8
        rw [runChunk]
        simp [step, stepEval, Frame.check, code, Code.Ixby_Runtime_arrayBytes, frameState,
          Frame.read, Frame.readOperands, Frame.transfer, enter, evalOp, natural, word,
          compare, getEval, encoded, sliced, appended, increment,
          show start < start + (count + 1) by omega, localRoom,
          bind, Except.bind, pure, Except.pure]
      rfl
    have sameStop : start + 1 + count = start + (count + 1) := by omega
    have recursive := ih (start + 1) (accumulator.push bytes[start]) (by omega) (by simp; omega)
    rw [sameStop, extract_accumulator bytes accumulator start (start + (count + 1)) (by omega) range] at recursive
    exact beforeLoop.trans recursive

theorem Certificate.toBytes_array_returns (room : 10 ≤ limits.locals) (capacity : 32 ≤ limits.natBits)
    (wordCapacity : 4 ≤ limits.byteArrayBytes) (bytes : Array UInt8) (bound : bytes.size < 2 ^ 32)
    (bytesCapacity : bytes.size ≤ limits.byteArrayBytes) (continuation : Array Continuation) :
    Reaches limits program (frameState 51 0 #[arrayValue (bytes.map byteWord)] continuation)
      (returned (.scalar (.bytes bytes)) continuation) := by
  have code := (certificate.function 51).code
  have loopCode := (certificate.function 50).code
  change program.getFunction 51 = .ok Code.Ixby_Runtime_toBytes at code
  change program.getFunction 50 = .ok Code.Ixby_Runtime_arrayBytes at loopCode
  have sizeValid := natValid_array_index limits capacity bytes.size bound
  have sizeEval := eval_arrayLength limits (bytes.map byteWord) (by simpa using bound) (by simpa using sizeValid)
  simp only [Array.size_map] at sizeEval
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  apply Reaches.trans (b := frameState 50 0 #[.array (bytes.map byteWord), natural 0, natural bytes.size, .byteBuilder #[]] continuation)
  · apply reaches_of_chunk (fuel := 4) (count := 0)
    iterate 4
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, loopCode, Code.Ixby_Runtime_toBytes, Code.Ixby_Runtime_arrayBytes,
        frameState, certificate.bytesCtor, certificate.arrayCtor, selectCase, arrayValue, arrayId,
        enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp, sizeEval, eval_builderEmpty,
        natural, localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  · simpa using certificate.arrayBytes_returns limits room capacity wordCapacity bytes bound 0 bytes.size #[]
      (by omega) (by simpa using bytesCapacity) continuation

theorem Certificate.toBytes_represents (room : 10 ≤ limits.locals) (capacity : 32 ≤ limits.natBits)
    (wordCapacity : 4 ≤ limits.byteArrayBytes) (bytes : Array UInt8) (value : Value)
    (represented : BytesRep bytes value) (bound : bytes.size < 2 ^ 32)
    (bytesCapacity : bytes.size ≤ limits.byteArrayBytes) (continuation : Array Continuation) :
    Reaches limits program (frameState 51 0 #[value] continuation)
      (returned (.scalar (.bytes bytes)) continuation) := by
  cases represented with
  | packed => exact certificate.toBytes_packed_returns limits (by omega) bytes continuation
  | array => exact certificate.toBytes_array_returns limits room capacity wordCapacity bytes bound bytesCapacity continuation

end Compilatrix.Ixby.Runtime.Native
