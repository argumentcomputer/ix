import Compilatrix.Ixby.Runtime.Native.ByteWords
import Compilatrix.Ixby.Runtime.Native.WireValues
import Compilatrix.Ixby.Runtime.Native.Sequence

/-! A compositional writer contract: encode starts an empty builder, invokes
the writer, and freezes its successful result before the public Bytes boundary.
The writer's own execution remains an explicit premise. -/

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby Execution Representation ScalarFunction Conversion

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

variable {program : Program} (certificate : WireCertificate program) (limits : Limits)

include certificate

theorem WireCertificate.encode_builder_returns (room : 17 ≤ limits.locals)
    (capacity : 32 ≤ limits.natBits) (configId : CtorId) (byteLimit : Nat) (nodes depth writer : Value)
    (bytes : Array UInt8) (result : Value) (finalLimit : Nat) (finalNodes finalDepth : Value)
    (bound : bytes.size < 2 ^ 32) (bytesCapacity : bytes.size ≤ limits.byteArrayBytes)
    (continuation : Array Continuation) (stack : continuation.size < limits.continuations)
    (writerPath : Reaches limits program
      { control := .apply writer #[writeState (writerValue #[]) byteLimit nodes depth],
        continuation := continuation.push (.resume (encodeSaved configId byteLimit nodes depth writer)) }
      (returned (okValue (pairValue result (writeState (writerValue bytes) finalLimit finalNodes finalDepth)))
        (continuation.push (.resume (encodeSaved configId byteLimit nodes depth writer))))) :
    Reaches limits program
      (frameState 100 0 #[.ctor configId #[natural byteLimit, nodes, depth], writer] continuation)
      (returned (okValue (packedValue bytes)) continuation) := by
  have code := (certificate.function 2).code
  have bytesCode := (certificate.runtime.function 51).code
  change program.getFunction 100 = .ok Code.MultiStark_Verify_Codec_Wire_encode at code
  change program.getFunction 51 = .ok Code.Ixby_Runtime_toBytes at bytesCode
  have sizeValid := natValid_array_index limits capacity bytes.size bound
  have lengthEval := eval_bytesLength limits bytes bytesCapacity bound
  have sizeExact : bytes.size.toUInt32.toNat = bytes.size := Nat.mod_eq_of_lt bound
  have fromWord := eval_word32ToNat limits bytes.size.toUInt32 (by simpa only [sizeExact, NatValid] using sizeValid)
  simp only [sizeExact] at fromWord
  let initial := encodeLocals configId byteLimit nodes depth writer
  let state := writeState (writerValue bytes) finalLimit finalNodes finalDepth
  let pair := pairValue result state
  let writerResult := okValue pair
  let resumedLocals := initial.push writerResult
  let bytesLocals := resumedLocals ++ #[pair, state, writerValue bytes]
  let finalLocals := bytesLocals.push (.scalar (.bytes bytes))
  have localRoom : ∀ k, k ≤ 17 → ¬limits.locals < k := by omega
  have beforeWriter : Reaches limits program
      (frameState 100 0 #[.ctor configId #[natural byteLimit, nodes, depth], writer] continuation)
      (frameState 100 6 initial continuation) := by
    apply reaches_of_chunk (fuel := 6) (count := 0)
    iterate 6
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, Code.MultiStark_Verify_Codec_Wire_encode, frameState,
        initial, encodeLocals, writeState, writerValue, writerId, certificate.runtime.writerCtor,
        certificate.stateCtor, Frame.read, Frame.readOperands, Frame.transfer, evalOp, eval_builderEmpty,
        localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  have applied := apply_returns limits program { function := 100, block := 6, locals := initial }
    (.local 1) [.local 7] writer #[writeState (writerValue #[]) byteLimit nodes depth] 7 writerResult
    { function := 100, block := 7, locals := resumedLocals } continuation stack
    (by simp [Frame.check, code, Code.MultiStark_Verify_Codec_Wire_encode, initial, encodeLocals,
      localRoom, bind, Except.bind, pure, Except.pure]) rfl rfl
    (by simp [Frame.transfer, Frame.check, code, Code.MultiStark_Verify_Codec_Wire_encode,
      initial, encodeLocals, resumedLocals, localRoom, bind, Except.bind, pure, Except.pure]) writerPath
  have beforeBytes : Reaches limits program (frameState 100 7 resumedLocals continuation)
      (frameState 100 11 bytesLocals continuation) := by
    apply reaches_of_chunk (fuel := 3) (count := 0)
    iterate 3
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, Code.MultiStark_Verify_Codec_Wire_encode, frameState,
        initial, encodeLocals, resumedLocals, writerResult, bytesLocals, pair, state,
        pairValue, okValue, writeState, certificate.errorCtor, certificate.okCtor,
        selectCase, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
        localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  have bytesPath := call_returns limits program { function := 100, block := 11, locals := bytesLocals }
    51 [.local 11] #[writerValue bytes] 12 (.scalar (.bytes bytes))
    { function := 100, block := 12, locals := finalLocals } continuation stack
    (by simp [Frame.check, code, Code.MultiStark_Verify_Codec_Wire_encode, bytesLocals, resumedLocals,
      initial, encodeLocals, localRoom, bind, Except.bind, pure, Except.pure]) rfl
    (by simp [enter, Frame.check, bytesCode, Code.Ixby_Runtime_toBytes, localRoom,
      bind, Except.bind, pure, Except.pure])
    (by simp [Frame.transfer, Frame.check, code, Code.MultiStark_Verify_Codec_Wire_encode,
      initial, encodeLocals, resumedLocals, bytesLocals, finalLocals, localRoom,
      bind, Except.bind, pure, Except.pure])
    (certificate.runtime.toBytes_writer_returns limits (by omega) bytes bytesCapacity sizeValid _)
  apply beforeWriter.trans (applied.trans (beforeBytes.trans (bytesPath.trans ?_)))
  apply reaches_of_chunk (fuel := 5) (count := 0)
  iterate 5
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.MultiStark_Verify_Codec_Wire_encode, frameState, returned,
      initial, encodeLocals, resumedLocals, bytesLocals, finalLocals, okValue, packedValue, bytesId,
      natural, word, certificate.runtime.bytesCtor, certificate.okCtor, Frame.read, Frame.readOperands,
      Frame.transfer, evalOp, lengthEval, fromWord, localRoom, bind, Except.bind, pure, Except.pure]
  rfl

end Compilatrix.Ixby.Runtime.Native
