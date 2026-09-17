import Compilatrix.Ixby.Runtime.Native.PackedArray

/-! Single-dispatch reads preserve exact Nat bounds and writer validation.
These contracts use the certified complete body and the reference machine;
they require no spare continuation slot. -/

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby Execution Representation ScalarFunction Conversion

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

variable {program : Program} (certificate : Certificate program) (limits : Limits)

include certificate

theorem Certificate.writerGet_returns (room : 10 ≤ limits.locals) (typeValue proofValue : Value)
    (bytes : Array UInt8) (bound : bytes.size < 2 ^ 32) (capacity : bytes.size ≤ limits.byteArrayBytes)
    (index : Nat) (inside : index < bytes.size) (sizeValid : NatValid limits bytes.size)
    (indexValid : NatValid limits index) (continuation : Array Continuation) :
    Reaches limits program (frameState 62 0 #[typeValue, writerValue bytes, natural index, proofValue] continuation)
      (returned (byteWord bytes[index]) continuation) := by
  have code := (certificate.function 62).code
  change program.getFunction 62 = .ok Code.Array_getInternal at code
  have length := eval_builderLength limits bytes capacity sizeValid
  have compare := eval_natLt limits index bytes.size indexValid sizeValid
  have frozen := eval_builderFreeze limits bytes capacity
  have converted := eval_natToWord32 limits index indexValid
  have getEval := eval_bytesGet_nat limits bytes index capacity (by omega) inside
  simp only [word, byteWord] at getEval
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 8) (count := 0)
  iterate 8
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.Array_getInternal, frameState, returned,
      certificate.bytesCtor, certificate.arrayCtor, certificate.writerCtor, selectCase,
      writerValue, writerId, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
      length, compare, frozen, converted, getEval, natural, inside, localRoom,
      bind, Except.bind, pure, Except.pure]
  rfl

/-- Even indices above Word32 range are rejected before conversion. -/
theorem Certificate.arrayGet_outside (room : 7 ≤ limits.locals) (typeValue proofValue : Value)
    (values : Array Value) (bound : values.size < 2 ^ 32) (sizeValid : NatValid limits values.size)
    (index : Nat) (outside : values.size ≤ index) (indexValid : NatValid limits index)
    (continuation : Array Continuation) (fuel : Nat) :
    Ix.Ixby.run limits program (fuel + 5)
      (frameState 62 0 #[typeValue, arrayValue values, natural index, proofValue] continuation) =
      .error .notConstructor := by
  have code := (certificate.function 62).code
  change program.getFunction 62 = .ok Code.Array_getInternal at code
  have length := eval_arrayLength limits values bound sizeValid
  have compare := eval_natLt limits index values.size indexValid sizeValid
  have localRoom : ∀ k, k ≤ 7 → ¬limits.locals < k := by omega
  iterate 5
    rw [Ix.Ixby.run]
    simp [step, stepEval, Frame.check, code, Code.Array_getInternal, frameState,
      certificate.bytesCtor, certificate.arrayCtor, selectCase, arrayValue, arrayId,
      Frame.read, Frame.readOperands, Frame.transfer, evalOp, length, compare, natural,
      Nat.not_lt.mpr outside, localRoom, bind, Except.bind, pure, Except.pure]
  rfl

/-- The stored bound is checked before the payload, even for a malformed view. -/
theorem Certificate.packedGet_outside (room : 7 ≤ limits.locals) (typeValue proofValue payload : Value)
    (size index : Nat) (outside : size ≤ index) (sizeValid : NatValid limits size)
    (indexValid : NatValid limits index) (continuation : Array Continuation) (fuel : Nat) :
    Ix.Ixby.run limits program (fuel + 4)
      (frameState 62 0 #[typeValue, .ctor bytesId #[payload, natural size], natural index, proofValue] continuation) =
      .error .notConstructor := by
  have code := (certificate.function 62).code
  change program.getFunction 62 = .ok Code.Array_getInternal at code
  have compare := eval_natLt limits index size indexValid sizeValid
  have localRoom : ∀ k, k ≤ 7 → ¬limits.locals < k := by omega
  iterate 4
    rw [Ix.Ixby.run]
    simp [step, stepEval, Frame.check, code, Code.Array_getInternal, frameState,
      certificate.bytesCtor, selectCase, bytesId, Frame.read, Frame.readOperands,
      Frame.transfer, evalOp, compare, natural, Nat.not_lt.mpr outside, localRoom,
      bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.writerGet_outside (room : 7 ≤ limits.locals) (typeValue proofValue : Value)
    (bytes : Array UInt8) (capacity : bytes.size ≤ limits.byteArrayBytes)
    (sizeValid : NatValid limits bytes.size) (index : Nat) (outside : bytes.size ≤ index)
    (indexValid : NatValid limits index) (continuation : Array Continuation) (fuel : Nat) :
    Ix.Ixby.run limits program (fuel + 5)
      (frameState 62 0 #[typeValue, writerValue bytes, natural index, proofValue] continuation) =
      .error .notConstructor := by
  have code := (certificate.function 62).code
  change program.getFunction 62 = .ok Code.Array_getInternal at code
  have length := eval_builderLength limits bytes capacity sizeValid
  have compare := eval_natLt limits index bytes.size indexValid sizeValid
  have localRoom : ∀ k, k ≤ 7 → ¬limits.locals < k := by omega
  iterate 5
    rw [Ix.Ixby.run]
    simp [step, stepEval, Frame.check, code, Code.Array_getInternal, frameState,
      certificate.bytesCtor, certificate.arrayCtor, certificate.writerCtor, selectCase,
      writerValue, writerId, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
      length, compare, natural, Nat.not_lt.mpr outside, localRoom,
      bind, Except.bind, pure, Except.pure]
  rfl

/-- Builder validation precedes index validation, including an invalid index type. -/
theorem Certificate.writerGet_rejects_length (room : 5 ≤ limits.locals)
    (typeValue proofValue builder index : Value) (error : Error)
    (rejected : Primitive.byteBuilderLength.eval limits [builder] = .error error)
    (continuation : Array Continuation) (fuel : Nat) :
    Ix.Ixby.run limits program (fuel + 2)
      (frameState 62 0 #[typeValue, .ctor writerId #[builder], index, proofValue] continuation) =
      .error error := by
  have code := (certificate.function 62).code
  change program.getFunction 62 = .ok Code.Array_getInternal at code
  have localRoom : ∀ k, k ≤ 5 → ¬limits.locals < k := by omega
  iterate 2
    rw [Ix.Ixby.run]
    simp [step, stepEval, Frame.check, code, Code.Array_getInternal, frameState,
      certificate.bytesCtor, certificate.arrayCtor, certificate.writerCtor, selectCase,
      writerId, Frame.read, Frame.readOperands, Frame.transfer, evalOp, rejected,
      localRoom, bind, Except.bind, pure, Except.pure]

end Compilatrix.Ixby.Runtime.Native
