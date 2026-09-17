import Compilatrix.Ixby.Runtime.Native.ByteLoops
import Compilatrix.Ixby.Runtime.Native.WireValues

/-! Byte writes keep an immutable builder in the writer state. Source limits
are checked before append, and the other state fields are preserved exactly. -/

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby Execution Representation ScalarFunction Conversion

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

variable {program : Program} (certificate : WireCertificate program) (limits : Limits)

include certificate

theorem WireCertificate.writeBytes_builder_returns (room : 18 ≤ limits.locals)
    (capacity : 32 ≤ limits.natBits) (wordCapacity : 4 ≤ limits.byteArrayBytes)
    (before chunk : Array UInt8) (chunkValue : Value) (represented : BytesRep chunk chunkValue)
    (byteLimit : Nat) (nodes depth : Value) (limitValid : NatValid limits byteLimit)
    (bound : before.size + chunk.size < 2 ^ 32)
    (bytesCapacity : before.size + chunk.size ≤ limits.byteArrayBytes)
    (allowed : before.size + chunk.size ≤ byteLimit)
    (continuation : Array Continuation) (stack : continuation.size < limits.continuations) :
    Reaches limits program
      (frameState 101 0 #[chunkValue, writeState (writerValue before) byteLimit nodes depth] continuation)
      (returned (okValue (pairValue unitValue
        (writeState (writerValue (before ++ chunk)) byteLimit nodes depth))) continuation) := by
  have code := (certificate.function 3).code
  have sizeCode := (certificate.runtime.function 58).code
  have bytesCode := (certificate.runtime.function 51).code
  change program.getFunction 101 = .ok Code.MultiStark_Verify_Codec_Wire_writeBytes at code
  change program.getFunction 58 = .ok Code.Array_size at sizeCode
  change program.getFunction 51 = .ok Code.Ixby_Runtime_toBytes at bytesCode
  have beforeValid := natValid_array_index limits capacity before.size (by omega)
  have chunkValid := natValid_array_index limits capacity chunk.size (by omega)
  have sumValid := natValid_array_index limits capacity (before.size + chunk.size) bound
  have lengthEval := eval_builderLength limits before (by omega) beforeValid
  have added := eval_natAdd limits before.size chunk.size beforeValid chunkValid sumValid
  have compare := eval_natLt limits byteLimit (before.size + chunk.size) limitValid sumValid
  have appendEval := eval_builderAppend limits before chunk bytesCapacity
  let initial := #[chunkValue, writeState (writerValue before) byteLimit nodes depth]
  let locals := initial ++ #[writerValue before, natural before.size, natural chunk.size,
    natural (before.size + chunk.size), natural byteLimit, .scalar (.bool false), .byteBuilder before]
  let nextLocals := locals.push (.scalar (.bytes chunk))
  have localRoom : ∀ k, k ≤ 18 → ¬limits.locals < k := by omega
  have beforeBytes : Reaches limits program (frameState 101 0 initial continuation)
      (frameState 101 13 locals continuation) := by
    cases represented with
    | packed =>
      apply reaches_of_chunk (fuel := 15) (count := 0)
      iterate 15
        rw [runChunk]
        simp [step, stepEval, Frame.check, code, sizeCode, Code.MultiStark_Verify_Codec_Wire_writeBytes,
          Code.Array_size, frameState, initial, locals, writeState, writerValue, writerId, packedValue, bytesId,
          certificate.runtime.bytesCtor, certificate.runtime.arrayCtor, certificate.runtime.writerCtor,
          selectCase, State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp, lengthEval,
          added, compare, natural, Nat.not_lt.mpr allowed, localRoom, Nat.not_le.mpr stack,
          bind, Except.bind, pure, Except.pure]
      rfl
    | array =>
      have sizeEval := eval_arrayLength limits (chunk.map byteWord) (by simp; omega) (by simpa using chunkValid)
      simp only [Array.size_map] at sizeEval
      apply reaches_of_chunk (fuel := 16) (count := 0)
      iterate 16
        rw [runChunk]
        simp [step, stepEval, Frame.check, code, sizeCode, Code.MultiStark_Verify_Codec_Wire_writeBytes,
          Code.Array_size, frameState, initial, locals, writeState, writerValue, writerId, arrayValue, arrayId,
          certificate.runtime.bytesCtor, certificate.runtime.arrayCtor, certificate.runtime.writerCtor,
          selectCase, State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp, lengthEval,
          sizeEval, added, compare, natural, Nat.not_lt.mpr allowed, localRoom, Nat.not_le.mpr stack,
          bind, Except.bind, pure, Except.pure]
      rfl
  have bytesPath := call_returns limits program { function := 101, block := 13, locals }
    51 [.local 0] #[chunkValue] 28 (.scalar (.bytes chunk))
    { function := 101, block := 28, locals := nextLocals } continuation stack
    (by simp [Frame.check, code, Code.MultiStark_Verify_Codec_Wire_writeBytes, locals, initial,
      localRoom, bind, Except.bind, pure, Except.pure]) rfl
    (by simp [enter, Frame.check, bytesCode, Code.Ixby_Runtime_toBytes, localRoom,
      bind, Except.bind, pure, Except.pure])
    (by simp [Frame.transfer, Frame.check, code, Code.MultiStark_Verify_Codec_Wire_writeBytes,
      locals, initial, nextLocals, localRoom, bind, Except.bind, pure, Except.pure])
    (certificate.runtime.toBytes_represents limits (by omega) capacity wordCapacity chunk chunkValue
      represented (by omega) (by omega) _)
  apply beforeBytes.trans (bytesPath.trans ?_)
  apply reaches_of_chunk (fuel := 9) (count := 0)
  iterate 9
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.MultiStark_Verify_Codec_Wire_writeBytes,
      frameState, returned, initial, locals, nextLocals, writeState, writerValue, writerId,
      okValue, pairValue, unitValue, certificate.runtime.writerCtor, certificate.stateCtor,
      certificate.okCtor, certificate.pairCtor, certificate.unitCtor, Frame.read, Frame.readOperands,
      Frame.transfer, evalOp, appendEval, localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem WireCertificate.writeBytes_builder_rejects_limit (room : 10 ≤ limits.locals)
    (capacity : 32 ≤ limits.natBits) (before chunk : Array UInt8) (chunkValue : Value)
    (represented : BytesRep chunk chunkValue) (byteLimit : Nat) (nodes depth : Value)
    (limitValid : NatValid limits byteLimit) (bound : before.size + chunk.size < 2 ^ 32)
    (bytesCapacity : before.size ≤ limits.byteArrayBytes) (exceeded : byteLimit < before.size + chunk.size)
    (continuation : Array Continuation) (stack : continuation.size < limits.continuations) :
    Reaches limits program
      (frameState 101 0 #[chunkValue, writeState (writerValue before) byteLimit nodes depth] continuation)
      (returned byteLimitError continuation) := by
  have code := (certificate.function 3).code
  have sizeCode := (certificate.runtime.function 58).code
  change program.getFunction 101 = .ok Code.MultiStark_Verify_Codec_Wire_writeBytes at code
  change program.getFunction 58 = .ok Code.Array_size at sizeCode
  have beforeValid := natValid_array_index limits capacity before.size (by omega)
  have chunkValid := natValid_array_index limits capacity chunk.size (by omega)
  have sumValid := natValid_array_index limits capacity (before.size + chunk.size) bound
  have lengthEval := eval_builderLength limits before bytesCapacity beforeValid
  have added := eval_natAdd limits before.size chunk.size beforeValid chunkValid sumValid
  have compare := eval_natLt limits byteLimit (before.size + chunk.size) limitValid sumValid
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  cases represented with
  | packed =>
    apply reaches_of_chunk (fuel := 17) (count := 0)
    iterate 17
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, sizeCode, Code.MultiStark_Verify_Codec_Wire_writeBytes,
        Code.Array_size, frameState, returned, writeState, writerValue, writerId, packedValue, bytesId,
        byteLimitError, errorValue, certificate.runtime.bytesCtor, certificate.runtime.arrayCtor,
        certificate.runtime.writerCtor, certificate.byteLimitCtor, certificate.errorCtor, selectCase,
        State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp, lengthEval,
        added, compare, natural, exceeded, localRoom, Nat.not_le.mpr stack,
        bind, Except.bind, pure, Except.pure]
    rfl
  | array =>
    have sizeEval := eval_arrayLength limits (chunk.map byteWord) (by simp; omega) (by simpa using chunkValid)
    simp only [Array.size_map] at sizeEval
    apply reaches_of_chunk (fuel := 18) (count := 0)
    iterate 18
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, sizeCode, Code.MultiStark_Verify_Codec_Wire_writeBytes,
        Code.Array_size, frameState, returned, writeState, writerValue, writerId, arrayValue, arrayId,
        byteLimitError, errorValue, certificate.runtime.bytesCtor, certificate.runtime.arrayCtor,
        certificate.runtime.writerCtor, certificate.byteLimitCtor, certificate.errorCtor, selectCase,
        State.push, enter, Frame.read, Frame.readOperands, Frame.transfer, evalOp, lengthEval,
        sizeEval, added, compare, natural, exceeded, localRoom, Nat.not_le.mpr stack,
        bind, Except.bind, pure, Except.pure]
    rfl

end Compilatrix.Ixby.Runtime.Native
