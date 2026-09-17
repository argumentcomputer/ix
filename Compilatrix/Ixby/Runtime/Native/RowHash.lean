import Compilatrix.Ixby.Runtime.Native.ByteLoops
import Compilatrix.Ixby.Runtime.Native.WireValues
import Ix.MultiStark.Verify.Mmcs.Basic

/-! Row hashing writes each canonical field's eight little-endian bytes into
one immutable builder and freezes once per row. The hashed preimage is the
pinned source concatenation of untagged eight-byte words, by definition; only
its construction changes. Erased fields are Nat scalars in a native array, so
packed and writer byte views are ill-typed rows and trap at dispatch. -/

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby Execution Representation ScalarFunction Conversion

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Erased source fields are Nat scalars holding their canonical values. -/
def fieldNatural (value : Goldilocks) : Value := natural value.val

/-- The pinned row preimage: untagged eight-byte little-endian words. -/
def rowBytes (fields : Array Goldilocks) : Array UInt8 :=
  fields.flatMap fun value => bytesLE 8 value.val

/-- The source hash input is exactly this concatenation, by definition. -/
theorem hashRow_bytes (fields : Array Goldilocks) :
    (MultiStark.Verify.Mmcs.hashRow fields).bytes = Blake3.hash (rowBytes fields) := rfl

theorem rowBytes_append (a b : Array Goldilocks) :
    rowBytes (a ++ b) = rowBytes a ++ rowBytes b := by
  simp [rowBytes, Array.flatMap_append]

theorem rowBytes_singleton (value : Goldilocks) : rowBytes #[value] = bytesLE 8 value.val := by
  simp [rowBytes]

/-- Consuming the next field appends its word before the remaining suffix. -/
theorem rowBytes_extract_cons (fields : Array Goldilocks) (index stop : Nat)
    (inside : index < stop) (bound : stop ≤ fields.size) :
    rowBytes (fields.extract index stop) =
      bytesLE 8 (fields[index]'(by omega)).val ++ rowBytes (fields.extract (index + 1) stop) := by
  rw [← extract_cons fields index stop inside bound, rowBytes_append, rowBytes_singleton]

private theorem rowBytes_list_length (values : List Goldilocks) :
    (values.flatMap fun value => (bytesLE 8 value.val).toList).length = 8 * values.length := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.flatMap_cons, List.length_append, Array.length_toList, bytesLE_size, ih,
      List.length_cons]
    omega

theorem rowBytes_size (fields : Array Goldilocks) : (rowBytes fields).size = 8 * fields.size := by
  rw [rowBytes, ← Array.length_toList, Array.toList_flatMap, rowBytes_list_length, Array.length_toList]

theorem eval_blake3 (limits : Limits) (bytes : Array UInt8)
    (capacity : bytes.size ≤ limits.byteArrayBytes) (digestCapacity : 32 ≤ limits.byteArrayBytes) :
    Primitive.blake3.eval limits [.scalar (.bytes bytes)] =
      .ok (.scalar (.bytes (Blake3.hash bytes))) := by
  simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, Scalar.validate,
    Nat.not_lt.mpr capacity, Nat.not_lt.mpr digestCapacity, Blake3.hash_size,
    bind, Except.bind, pure, Except.pure]

variable {program : Program} (certificate : WireCertificate program) (limits : Limits)

include certificate

/-- Every suffix of a native field row is appended to an arbitrary existing
prefix in index order, with one freeze after the last field. -/
theorem WireCertificate.rowBytesLoop_returns (room : 10 ≤ limits.locals)
    (capacity : 64 ≤ limits.natBits) (wordCapacity : 8 ≤ limits.byteArrayBytes)
    (fields : Array Goldilocks) (bound : fields.size < 2 ^ 32)
    (start count : Nat) (accumulator : Array UInt8) (range : start + count ≤ fields.size)
    (resultCapacity : accumulator.size + 8 * count ≤ limits.byteArrayBytes)
    (continuation : Array Continuation) :
    Reaches limits program
      (frameState 108 0 #[.array (fields.map fieldNatural), natural start, natural (start + count),
        .byteBuilder accumulator] continuation)
      (returned (.scalar (.bytes (accumulator ++ rowBytes (fields.extract start (start + count)))))
        continuation) := by
  have code := (certificate.function 10).code
  change program.getFunction 108 = .ok Code.Ixby_Runtime_rowBytesLoop at code
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  have indexCapacity : 32 ≤ limits.natBits := by omega
  have oneValid := natValid_array_index limits indexCapacity 1 (by decide)
  induction count generalizing start accumulator with
  | zero =>
    have indexValid := natValid_array_index limits indexCapacity start (by omega)
    have compare := eval_natLt limits start start indexValid indexValid
    have frozen := eval_builderFreeze limits accumulator (by omega)
    have empty : fields.extract start start = #[] := Array.extract_eq_empty_of_le (by omega)
    apply reaches_of_chunk (fuel := 4) (count := 0)
    iterate 4
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, Code.Ixby_Runtime_rowBytesLoop, frameState, returned,
        Frame.read, Frame.readOperands, Frame.transfer, evalOp, natural, compare, frozen, empty,
        rowBytes, localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  | succ count ih =>
    have inside : start < fields.size := by omega
    have indexValid := natValid_array_index limits indexCapacity start (by omega)
    have stopValid := natValid_array_index limits indexCapacity (start + (count + 1)) (by omega)
    have nextValid := natValid_array_index limits indexCapacity (start + 1) (by omega)
    have compare := eval_natLt limits start (start + (count + 1)) indexValid stopValid
    have increment := eval_natAdd limits start 1 indexValid oneValid nextValid
    have valueBound : fields[start].val < 2 ^ 64 :=
      Nat.lt_of_lt_of_le fields[start].isLt (by decide)
    have valueValid : NatValid limits fields[start].val := validate_nat_of_bits valueBound capacity
    have getEval := eval_arrayGet limits (fields.map fieldNatural) start (fieldNatural fields[start])
      (by simpa using bound) indexValid (by simp [inside])
      (by simpa [fieldNatural, natural, ResultValid, NatValid] using valueValid)
    have cast := eval_natToField limits fields[start].val valueValid
    rw [Goldilocks.reduce_canonical] at cast
    have encoded := eval_fieldToBytes limits fields[start] wordCapacity
    have appended := eval_builderAppend limits accumulator (bytesLE 8 fields[start].val)
      (by simp only [bytesLE_size]; omega)
    simp only [natural, fieldNatural] at getEval
    have beforeLoop : Reaches limits program
        (frameState 108 0 #[.array (fields.map fieldNatural), natural start, natural (start + (count + 1)),
          .byteBuilder accumulator] continuation)
        (frameState 108 0 #[.array (fields.map fieldNatural), natural (start + 1), natural (start + (count + 1)),
          .byteBuilder (accumulator ++ bytesLE 8 fields[start].val)] continuation) := by
      apply reaches_of_chunk (fuel := 8) (count := 0)
      iterate 8
        rw [runChunk]
        simp [step, stepEval, Frame.check, code, Code.Ixby_Runtime_rowBytesLoop, frameState,
          Frame.read, Frame.readOperands, Frame.transfer, enter, evalOp, natural,
          compare, getEval, cast, encoded, appended, increment,
          show start < start + (count + 1) by omega, localRoom,
          bind, Except.bind, pure, Except.pure]
      rfl
    have sameStop : start + 1 + count = start + (count + 1) := by omega
    have recursive := ih (start + 1) (accumulator ++ bytesLE 8 fields[start].val) (by omega)
      (by simp only [Array.size_append, bytesLE_size]; omega)
    rw [sameStop, Array.append_assoc,
      ← rowBytes_extract_cons fields start (start + (count + 1)) (by omega) range] at recursive
    exact beforeLoop.trans recursive

/-- A native field row hashes exactly the pinned source preimage. -/
theorem WireCertificate.hashRow_returns (room : 10 ≤ limits.locals)
    (capacity : 64 ≤ limits.natBits) (digestCapacity : 32 ≤ limits.byteArrayBytes)
    (fields : Array Goldilocks) (bound : fields.size < 2 ^ 32)
    (rowCapacity : 8 * fields.size ≤ limits.byteArrayBytes)
    (continuation : Array Continuation) (stack : continuation.size < limits.continuations) :
    Reaches limits program (frameState 109 0 #[arrayValue (fields.map fieldNatural)] continuation)
      (returned (packedValue (MultiStark.Verify.Mmcs.hashRow fields).bytes) continuation) := by
  have code := (certificate.function 11).code
  have loopCode := (certificate.function 10).code
  change program.getFunction 109 = .ok Code.MultiStark_Verify_Mmcs_hashRow at code
  change program.getFunction 108 = .ok Code.Ixby_Runtime_rowBytesLoop at loopCode
  have indexCapacity : 32 ≤ limits.natBits := by omega
  have sizeValid := natValid_array_index limits indexCapacity fields.size bound
  have sizeEval := eval_arrayLength limits (fields.map fieldNatural) (by simpa using bound)
    (by simpa using sizeValid)
  simp only [Array.size_map] at sizeEval
  have hashed := eval_blake3 limits (rowBytes fields) (by rw [rowBytes_size]; exact rowCapacity)
    digestCapacity
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  let values := fields.map fieldNatural
  let entered := #[arrayValue values, .array values, natural fields.size, .byteBuilder #[]]
  let resumed := entered.push (.scalar (.bytes (rowBytes fields)))
  have beforeLoop : Reaches limits program (frameState 109 0 #[arrayValue values] continuation)
      (frameState 109 5 entered continuation) := by
    apply reaches_of_chunk (fuel := 3) (count := 0)
    iterate 3
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, Code.MultiStark_Verify_Mmcs_hashRow, frameState,
        entered, values, certificate.runtime.bytesCtor, certificate.runtime.arrayCtor, selectCase,
        arrayValue, arrayId, Frame.read, Frame.readOperands, Frame.transfer, evalOp, sizeEval,
        eval_builderEmpty, natural, localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  have loopReturns := certificate.rowBytesLoop_returns limits room capacity (by omega) fields bound
    0 fields.size #[] (by omega) (by simp; omega)
    (continuation.push (.resume { function := 109, block := 6, locals := entered }))
  simp only [Nat.zero_add, Array.extract_size, Array.empty_append] at loopReturns
  have loopPath := call_returns limits program { function := 109, block := 5, locals := entered }
    108 [.local 1, .literal (.nat 0), .local 2, .local 3]
    #[.array values, natural 0, natural fields.size, .byteBuilder #[]] 6
    (.scalar (.bytes (rowBytes fields))) { function := 109, block := 6, locals := resumed }
    continuation stack
    (by simp [Frame.check, code, Code.MultiStark_Verify_Mmcs_hashRow, entered, localRoom,
      bind, Except.bind, pure, Except.pure])
    rfl
    (by simp [enter, Frame.check, loopCode, Code.Ixby_Runtime_rowBytesLoop, localRoom,
      bind, Except.bind, pure, Except.pure])
    (by simp [Frame.transfer, Frame.check, code, Code.MultiStark_Verify_Mmcs_hashRow, entered,
      resumed, localRoom, bind, Except.bind, pure, Except.pure])
    loopReturns
  apply beforeLoop.trans (loopPath.trans ?_)
  rw [hashRow_bytes]
  apply reaches_of_chunk (fuel := 3) (count := 0)
  iterate 3
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.MultiStark_Verify_Mmcs_hashRow,
      returned, entered, resumed, values, packedValue, bytesId, natural,
      certificate.runtime.bytesCtor, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
      hashed, Blake3.hash_size, localRoom, bind, Except.bind, pure, Except.pure]
  rfl

/-- A packed byte view is not a field row; dispatch traps immediately. -/
theorem WireCertificate.hashRow_packed_traps (room : 3 ≤ limits.locals) (bytes : Array UInt8)
    (continuation : Array Continuation) (fuel : Nat) :
    run limits program (fuel + 1 + 1) (frameState 109 0 #[packedValue bytes] continuation) =
      .error .notConstructor := by
  have code := (certificate.function 11).code
  change program.getFunction 109 = .ok Code.MultiStark_Verify_Mmcs_hashRow at code
  have localRoom : ∀ k, k ≤ 3 → ¬limits.locals < k := by omega
  simp [run, step, stepEval, Frame.check, code, Code.MultiStark_Verify_Mmcs_hashRow, frameState,
    certificate.runtime.bytesCtor, selectCase, packedValue, bytesId, Frame.read, Frame.transfer,
    localRoom, bind, Except.bind, pure, Except.pure] <;> rfl

/-- A writer buffer is not a field row either. -/
theorem WireCertificate.hashRow_writer_traps (room : 2 ≤ limits.locals) (bytes : Array UInt8)
    (continuation : Array Continuation) (fuel : Nat) :
    run limits program (fuel + 1 + 1) (frameState 109 0 #[writerValue bytes] continuation) =
      .error .notConstructor := by
  have code := (certificate.function 11).code
  change program.getFunction 109 = .ok Code.MultiStark_Verify_Mmcs_hashRow at code
  have localRoom : ∀ k, k ≤ 2 → ¬limits.locals < k := by omega
  simp [run, step, stepEval, Frame.check, code, Code.MultiStark_Verify_Mmcs_hashRow, frameState,
    certificate.runtime.bytesCtor, certificate.runtime.arrayCtor, certificate.runtime.writerCtor,
    selectCase, writerValue, writerId, Frame.read, Frame.transfer, localRoom,
    bind, Except.bind, pure, Except.pure] <;> rfl

end Compilatrix.Ixby.Runtime.Native
