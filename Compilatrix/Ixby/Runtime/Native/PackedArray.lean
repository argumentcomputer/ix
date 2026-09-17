import Compilatrix.Ixby.Runtime.Native.ByteWords
import Compilatrix.Ixby.Runtime.Native.Sequence

/-! Checked packed byte views preserve source indexing and half-open slices.
The Nat guard precedes every conversion to a Word32 byte address. -/

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby Execution Representation ScalarFunction Conversion

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem eval_bytesGet_nat (limits : Limits) (bytes : Array UInt8) (index : Nat)
    (capacity : bytes.size ≤ limits.byteArrayBytes) (bound : index < 2 ^ 32)
    (inside : index < bytes.size) :
    Primitive.bytesGet.eval limits [.scalar (.bytes bytes), word index.toUInt32] =
      .ok (byteWord bytes[index]) := by
  have exactIndex : index.toUInt32.toNat = index := Nat.mod_eq_of_lt bound
  simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, Scalar.validate,
    word, byteWord, exactIndex, inside, Nat.not_lt.mpr capacity,
    bind, Except.bind, pure, Except.pure]

variable {program : Program} (certificate : Certificate program) (limits : Limits)

include certificate

theorem Certificate.packedGet_returns (room : 10 ≤ limits.locals) (typeValue proofValue : Value)
    (bytes : Array UInt8) (bound : bytes.size < 2 ^ 32) (capacity : bytes.size ≤ limits.byteArrayBytes)
    (index : Nat) (inside : index < bytes.size) (sizeValid : NatValid limits bytes.size)
    (indexValid : NatValid limits index) (continuation : Array Continuation)
    (stack : continuation.size < limits.continuations) :
    Reaches limits program (frameState 62 0 #[typeValue, packedValue bytes, natural index, proofValue] continuation)
      (returned (byteWord bytes[index]) continuation) := by
  have code := (certificate.function 62).code
  have sizeCode := (certificate.function 58).code
  change program.getFunction 62 = .ok Code.Array_getInternal at code
  change program.getFunction 58 = .ok Code.Array_size at sizeCode
  have compare := eval_natLt limits index bytes.size indexValid sizeValid
  have converted := eval_natToWord32 limits index indexValid
  have getEval := eval_bytesGet_nat limits bytes index capacity (by omega) inside
  simp only [word, byteWord] at getEval
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 10) (count := 0)
  iterate 10
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, sizeCode, Code.Array_getInternal, Code.Array_size,
      frameState, returned, certificate.bytesCtor, selectCase, packedValue, bytesId,
      State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp, getEval,
      converted, compare, natural, inside, localRoom, Nat.not_le.mpr stack,
      bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.packedExtractRed_returns (room : 13 ≤ limits.locals) (natCapacity : 32 ≤ limits.natBits)
    (bytes : Array UInt8) (bound : bytes.size < 2 ^ 32) (capacity : bytes.size ≤ limits.byteArrayBytes)
    (start stop : Nat) (startValid : NatValid limits start) (stopValid : NatValid limits stop)
    (continuation : Array Continuation) (stack : continuation.size < limits.continuations) :
    Reaches limits program (frameState 72 0 #[packedValue bytes, natural start, natural stop] continuation)
      (returned (if start < min stop bytes.size then packedValue (bytes.extract start stop)
        else arrayValue #[]) continuation) := by
  have code := (certificate.function 72).code
  have sizeCode := (certificate.function 58).code
  change program.getFunction 72 = .ok Code.Array_extract__redArg at code
  change program.getFunction 58 = .ok Code.Array_size at sizeCode
  have sizeValid := natValid_array_index limits natCapacity bytes.size bound
  have sizeCompare := eval_natLt limits bytes.size stop sizeValid stopValid
  have localRoom : ∀ k, k ≤ 13 → ¬limits.locals < k := by omega
  have stackRoom := Nat.not_le.mpr stack
  by_cases above : bytes.size < stop
  · have compare := eval_natLt limits start bytes.size startValid sizeValid
    have cropped : bytes.extract start stop = bytes.extract start bytes.size := Array.extract_of_size_lt above
    have stopMin : min stop bytes.size = bytes.size := by omega
    rw [stopMin, cropped]
    by_cases inside : start < bytes.size
    · have lengthValid := natValid_array_index limits natCapacity (bytes.size - start) (by omega)
      have sub := eval_natSub limits bytes.size start sizeValid startValid lengthValid
      have first := eval_natToWord32 limits start startValid
      have length := eval_natToWord32 limits (bytes.size - start) lengthValid
      have sliced := eval_bytesSlice_nat limits bytes start (bytes.size - start) capacity
        (by omega) (by omega) (by omega)
      have endEq : start + (bytes.size - start) = bytes.size := by omega
      have lengthEq : (bytes.extract start bytes.size).size = bytes.size - start := by simp
      rw [endEq] at sliced
      simp only [word] at sliced
      apply reaches_of_chunk (fuel := 15) (count := 0)
      iterate 15
        rw [runChunk]
        simp [step, stepEval, Frame.check, code, sizeCode, Code.Array_extract__redArg, Code.Array_size,
          frameState, returned, certificate.bytesCtor, selectCase, packedValue, bytesId,
          State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp, sizeCompare,
          compare, sub, first, length, sliced, natural, above, inside, lengthEq, localRoom, stackRoom,
          bind, Except.bind, pure, Except.pure]
      rfl
    · apply reaches_of_chunk (fuel := 11) (count := 0)
      iterate 11
        rw [runChunk]
        simp [step, stepEval, Frame.check, code, sizeCode, Code.Array_extract__redArg, Code.Array_size,
          frameState, returned, certificate.bytesCtor, certificate.arrayCtor, selectCase, packedValue, bytesId,
          arrayValue, arrayId, State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
          sizeCompare, compare, natural, above, inside, eval_arrayEmpty, localRoom, stackRoom,
          bind, Except.bind, pure, Except.pure]
      rfl
  · have compare := eval_natLt limits start stop startValid stopValid
    have stopMin : min stop bytes.size = stop := by omega
    rw [stopMin]
    by_cases inside : start < stop
    · have lengthValid := natValid_array_index limits natCapacity (stop - start) (by omega)
      have sub := eval_natSub limits stop start stopValid startValid lengthValid
      have first := eval_natToWord32 limits start startValid
      have length := eval_natToWord32 limits (stop - start) lengthValid
      have sliced := eval_bytesSlice_nat limits bytes start (stop - start) capacity
        (by omega) (by omega) (by omega)
      have endEq : start + (stop - start) = stop := by omega
      have lengthEq : (bytes.extract start stop).size = stop - start := by simp [Nat.min_eq_left (by omega : stop ≤ bytes.size)]
      rw [endEq] at sliced
      simp only [word] at sliced
      apply reaches_of_chunk (fuel := 15) (count := 0)
      iterate 15
        rw [runChunk]
        simp [step, stepEval, Frame.check, code, sizeCode, Code.Array_extract__redArg, Code.Array_size,
          frameState, returned, certificate.bytesCtor, selectCase, packedValue, bytesId,
          State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp, sizeCompare,
          compare, sub, first, length, sliced, natural, above, inside, lengthEq, localRoom, stackRoom,
          bind, Except.bind, pure, Except.pure]
      rfl
    · apply reaches_of_chunk (fuel := 11) (count := 0)
      iterate 11
        rw [runChunk]
        simp [step, stepEval, Frame.check, code, sizeCode, Code.Array_extract__redArg, Code.Array_size,
          frameState, returned, certificate.bytesCtor, certificate.arrayCtor, selectCase, packedValue, bytesId,
          arrayValue, arrayId, State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
          sizeCompare, compare, natural, above, inside, eval_arrayEmpty, localRoom, stackRoom,
          bind, Except.bind, pure, Except.pure]
      rfl

theorem Certificate.packedAppendRed_returns (room : 13 ≤ limits.locals) (natCapacity : 32 ≤ limits.natBits)
    (a b : Array UInt8) (bound : a.size + b.size < 2 ^ 32)
    (capacity : a.size + b.size ≤ limits.byteArrayBytes)
    (continuation : Array Continuation) (stack : continuation.size < limits.continuations) :
    Reaches limits program (frameState 74 0 #[packedValue a, packedValue b] continuation)
      (returned (packedValue (a ++ b)) continuation) := by
  have code := (certificate.function 74).code
  have sizeCode := (certificate.function 58).code
  have appendCode := (certificate.function 82).code
  change program.getFunction 74 = .ok Code.Array_append__redArg at code
  change program.getFunction 58 = .ok Code.Array_size at sizeCode
  change program.getFunction 82 = .ok Code.Ixby_Runtime_appendBytes at appendCode
  have leftValid := natValid_array_index limits natCapacity a.size (by omega)
  have rightValid := natValid_array_index limits natCapacity b.size (by omega)
  have sumValid := natValid_array_index limits natCapacity (a.size + b.size) bound
  have zeroValid := natValid_array_index limits natCapacity 0 (by decide)
  have leftTest := eval_natEq limits a.size 0 leftValid zeroValid
  have rightTest := eval_natEq limits b.size 0 rightValid zeroValid
  have zeroTest := eval_natEq limits 0 0 zeroValid zeroValid
  have localRoom : ∀ k, k ≤ 13 → ¬limits.locals < k := by omega
  have stackRoom := Nat.not_le.mpr stack
  by_cases leftEmpty : a.size = 0
  · have empty : a = #[] := Array.size_eq_zero_iff.mp leftEmpty
    have result : a ++ b = b := by simp [empty]
    apply reaches_of_chunk (fuel := 11) (count := 0)
    iterate 11
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, sizeCode, Code.Array_append__redArg, Code.Array_size,
        frameState, returned, certificate.bytesCtor, selectCase, packedValue, bytesId,
        State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
        leftTest, zeroTest, natural, leftEmpty, result, localRoom, stackRoom,
        bind, Except.bind, pure, Except.pure]
    rfl
  · by_cases rightEmpty : b.size = 0
    · have empty : b = #[] := Array.size_eq_zero_iff.mp rightEmpty
      have result : a ++ b = a := by simp [empty]
      apply reaches_of_chunk (fuel := 13) (count := 0)
      iterate 13
        rw [runChunk]
        simp [step, stepEval, Frame.check, code, sizeCode, Code.Array_append__redArg, Code.Array_size,
          frameState, returned, certificate.bytesCtor, selectCase, packedValue, bytesId,
          State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
          leftTest, rightTest, zeroTest, natural, leftEmpty, rightEmpty, result, localRoom, stackRoom,
          bind, Except.bind, pure, Except.pure]
      rfl
    · have sum := eval_natAdd limits a.size b.size leftValid rightValid sumValid
      have first : Primitive.byteBuilderAppend.eval limits [.byteBuilder #[], .scalar (.bytes a)] =
          .ok (.byteBuilder a) := by simpa using eval_builderAppend limits #[] a (by simp; omega)
      have appended := eval_builderAppend limits a b capacity
      have frozen := eval_builderFreeze limits (a ++ b) (by simpa using capacity)
      apply reaches_of_chunk (fuel := 24) (count := 0)
      iterate 24
        rw [runChunk]
        simp [step, stepEval, Frame.check, code, sizeCode, appendCode, Code.Array_append__redArg,
          Code.Array_size, Code.Ixby_Runtime_appendBytes, frameState, returned, certificate.bytesCtor,
          selectCase, packedValue, bytesId, State.push, enter, Frame.read, Frame.readOperands,
          Frame.transfer, evalOp, leftTest, rightTest, natural, leftEmpty, rightEmpty, sum,
          eval_builderEmpty, first, appended, frozen, localRoom, stackRoom,
          bind, Except.bind, pure, Except.pure]
      rfl

end Compilatrix.Ixby.Runtime.Native
