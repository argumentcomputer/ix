import Compilatrix.Ixby.Runtime.Native.Machine
import Compilatrix.Ixby.Runtime.Native.CollectionLaws

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby Execution Representation ScalarFunction

theorem eval_bytesSlice (limits : Limits) (bytes : Array UInt8) (start length : UInt32)
    (capacity : bytes.size ≤ limits.byteArrayBytes)
    (range : start.toNat + length.toNat ≤ bytes.size) :
    Primitive.bytesSlice.eval limits [.scalar (.bytes bytes), word start, word length] =
      .ok (.scalar (.bytes (bytes.extract start.toNat (start.toNat + length.toNat)))) := by
  simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, word, Scalar.validate,
    Nat.not_lt.mpr capacity, show ¬limits.byteArrayBytes < length.toNat by omega,
    range, bind, Except.bind, pure, Except.pure]

theorem eval_bytesSlice_nat (limits : Limits) (bytes : Array UInt8) (start length : Nat)
    (capacity : bytes.size ≤ limits.byteArrayBytes) (startBound : start < 2 ^ 32)
    (lengthBound : length < 2 ^ 32) (range : start + length ≤ bytes.size) :
    Primitive.bytesSlice.eval limits [.scalar (.bytes bytes), word start.toUInt32, word length.toUInt32] =
      .ok (.scalar (.bytes (bytes.extract start (start + length)))) := by
  have startExact : start.toUInt32.toNat = start := Nat.mod_eq_of_lt startBound
  have lengthExact : length.toUInt32.toNat = length := Nat.mod_eq_of_lt lengthBound
  simpa only [startExact, lengthExact] using eval_bytesSlice limits bytes start.toUInt32 length.toUInt32
    capacity (by simpa only [startExact, lengthExact] using range)

variable {program : Program} (certificate : Certificate program) (limits : Limits)

include certificate

theorem Certificate.packedSize_returns (room : 4 ≤ limits.locals) (typeValue : Value)
    (bytes : Array UInt8) (continuation : Array Continuation) :
    Reaches limits program (frameState 58 0 #[typeValue, packedValue bytes] continuation)
      (returned (natural bytes.size) continuation) := by
  have code := (certificate.function 58).code
  change program.getFunction 58 = .ok Code.Array_size at code
  have localRoom : ∀ k, k ≤ 4 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 2) (count := 0)
  iterate 2
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.Array_size, frameState, returned,
      certificate.bytesCtor, selectCase, packedValue, bytesId, Frame.read, Frame.transfer,
      localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.writerSize_returns (room : 4 ≤ limits.locals) (typeValue : Value)
    (bytes : Array UInt8) (capacity : bytes.size ≤ limits.byteArrayBytes)
    (valid : NatValid limits bytes.size) (continuation : Array Continuation) :
    Reaches limits program (frameState 58 0 #[typeValue, writerValue bytes] continuation)
      (returned (natural bytes.size) continuation) := by
  have code := (certificate.function 58).code
  change program.getFunction 58 = .ok Code.Array_size at code
  have evaluated := eval_builderLength limits bytes capacity valid
  have localRoom : ∀ k, k ≤ 4 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 3) (count := 0)
  iterate 3
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.Array_size, frameState, returned,
      certificate.bytesCtor, certificate.arrayCtor, certificate.writerCtor, selectCase,
      writerValue, writerId, Frame.read, Frame.readOperands, Frame.transfer, evalOp, evaluated,
      localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.toBytes_packed_returns (room : 3 ≤ limits.locals) (bytes : Array UInt8)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 51 0 #[packedValue bytes] continuation)
      (returned (.scalar (.bytes bytes)) continuation) := by
  have code := (certificate.function 51).code
  change program.getFunction 51 = .ok Code.Ixby_Runtime_toBytes at code
  have localRoom : ∀ k, k ≤ 3 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 2) (count := 0)
  iterate 2
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.Ixby_Runtime_toBytes, frameState, returned,
      certificate.bytesCtor, selectCase, packedValue, bytesId, Frame.read, Frame.transfer,
      localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.toBytes_writer_returns (room : 4 ≤ limits.locals) (bytes : Array UInt8)
    (capacity : bytes.size ≤ limits.byteArrayBytes) (valid : NatValid limits bytes.size)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 51 0 #[writerValue bytes] continuation)
      (returned (.scalar (.bytes bytes)) continuation) := by
  have code := (certificate.function 51).code
  change program.getFunction 51 = .ok Code.Ixby_Runtime_toBytes at code
  have frozen := eval_builderFreeze limits bytes capacity
  have length := eval_builderLength limits bytes capacity valid
  have localRoom : ∀ k, k ≤ 4 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 4) (count := 0)
  iterate 4
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.Ixby_Runtime_toBytes, frameState, returned,
      certificate.bytesCtor, certificate.arrayCtor, certificate.writerCtor, selectCase,
      writerValue, writerId, Frame.read, Frame.readOperands, Frame.transfer, evalOp, frozen, length,
      localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.appendBytes_returns (room : 6 ≤ limits.locals) (a b : Array UInt8)
    (capacity : a.size + b.size ≤ limits.byteArrayBytes) (continuation : Array Continuation) :
    Reaches limits program (frameState 82 0 #[.scalar (.bytes a), .scalar (.bytes b)] continuation)
      (returned (.scalar (.bytes (a ++ b))) continuation) := by
  have code := (certificate.function 82).code
  change program.getFunction 82 = .ok Code.Ixby_Runtime_appendBytes at code
  have first : Primitive.byteBuilderAppend.eval limits [.byteBuilder #[], .scalar (.bytes a)] =
      .ok (.byteBuilder a) := by simpa using eval_builderAppend limits #[] a (by simp; omega)
  have appended := eval_builderAppend limits a b capacity
  have frozen := eval_builderFreeze limits (a ++ b) (by simpa using capacity)
  have localRoom : ∀ k, k ≤ 6 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 5) (count := 0)
  iterate 5
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.Ixby_Runtime_appendBytes, frameState, returned,
      Frame.read, Frame.readOperands, Frame.transfer, evalOp, eval_builderEmpty, first, appended, frozen,
      localRoom, bind, Except.bind, pure, Except.pure]
  rfl

end Compilatrix.Ixby.Runtime.Native
