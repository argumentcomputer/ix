import Compilatrix.Ixby.Runtime.ArrayTreeIndex
import Compilatrix.Ixby.Runtime.ArrayTreeGet

/-! Public checked lookup for tree-backed arrays, including the real size,
comparison, number-observation, constructor dispatch, and tail-call paths. -/

namespace Compilatrix.Ixby.Runtime.ArrayTrees.Certificate

open Ix.Ixby Execution Representation ScalarFunction Conversion

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

variable {program : Program} {links : Links} (certificate : Certificate program links)
  (limits : Limits)

include certificate

theorem get_returns (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue proofValue : Value)
    (height : Nat) (tree : Tree height) (n : Nat) (size : Value) (index : Nat) (indexValue value : Value)
    (sizeRep : Number links.arithmetic.conversions.layout n size)
    (indexRep : Number links.arithmetic.conversions.layout index indexValue)
    (within : n ≤ 2 ^ height) (bounded : index < n) (found : tree.get index = some value)
    (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 4 ≤ limits.continuations) :
    Reaches limits program
      (frameState links.get 0
        #[typeValue, arrayValue links.layout height tree size, indexValue, proofValue] continuation)
      (returned value continuation) := by
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  have sizeValid := validate_nat_mono within valid
  have indexValid := validate_nat_mono (by omega : index ≤ 2 ^ height) valid
  let array := arrayValue links.layout height tree size
  let args := #[typeValue, array, indexValue, proofValue]
  have checkedIndex : Reaches limits program (frameState links.get 0 args continuation)
      (frameState links.get 2 (args ++ #[size, .scalar (.bool true)]) continuation) := by
    simpa [bounded] using certificate.check_index limits certificate.get args (.local 1) (.local 2)
      rfl rfl _ rfl room (by simp [args]; omega) capacity bytesCapacity height tree size n index indexValue
      sizeRep indexRep sizeValid indexValid rfl rfl continuation stack
  let locals := args ++ #[size, .scalar (.bool true), size, .scalar (.nat (2 ^ height)), tree.encode links.layout]
  have dispatched : Reaches limits program
      (frameState links.get 2 (args ++ #[size, .scalar (.bool true)]) continuation)
      (frameState links.get 6 locals continuation) := by
    apply reaches_of_chunk (fuel := 2) (count := 0)
    iterate 2
      rw [runChunk]
      simp [args, array, locals, step, stepEval, Frame.check, certificate.get.code, ArrayTrees.get,
        certificate.bytesCtor, certificate.arrayCtor, certificate.bytesArray,
        frameState, arrayValue, Frame.read, Frame.transfer, selectCase,
        localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  have observed := certificate.arithmetic.conversions.call_natural limits room capacity bytesCapacity
    { function := links.get, block := 6, locals } (.local 2) 10 index indexValue indexRep
    { function := links.get, block := 10, locals := locals ++ #[.scalar (.nat index)] }
    (by simp [args, locals, Frame.check, certificate.get.code, ArrayTrees.get,
      localRoom, bind, Except.bind, pure, Except.pure]) rfl
    (by simp [args, locals, Frame.transfer, Frame.check, certificate.get.code, ArrayTrees.get,
      localRoom, bind, Except.bind, pure, Except.pure]) continuation (by omega)
  have entered : Reaches limits program
      (frameState links.get 10 (locals ++ #[.scalar (.nat index)]) continuation)
      (frameState links.treeGet 0
        #[tree.encode links.layout, .scalar (.nat (2 ^ height)), .scalar (.nat index)] continuation) := by
    apply Reaches.of_step
    simp [args, locals, step, stepEval, Frame.check, certificate.get.code, ArrayTrees.get,
      certificate.treeGet.code, ArrayTrees.treeGet, frameState, Frame.read, Frame.readOperands,
      enter, localRoom, bind, Except.bind, pure, Except.pure]
  exact checkedIndex.trans (dispatched.trans (observed.trans (entered.trans
    (certificate.treeGet_returns limits (by omega) (by omega) height tree index value
      (by omega) found valid continuation))))

theorem getAlias_returns {id : FunctionId} (checked : Checked program id (getAlias links))
    (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue proofValue : Value)
    (height : Nat) (tree : Tree height) (n : Nat) (size : Value) (index : Nat) (indexValue value : Value)
    (sizeRep : Number links.arithmetic.conversions.layout n size)
    (indexRep : Number links.arithmetic.conversions.layout index indexValue)
    (within : n ≤ 2 ^ height) (bounded : index < n) (found : tree.get index = some value)
    (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 4 ≤ limits.continuations) :
    Reaches limits program
      (frameState id 0 #[typeValue, arrayValue links.layout height tree size, indexValue, proofValue] continuation)
      (returned value continuation) := by
  have entered : Reaches limits program
      (frameState id 0 #[typeValue, arrayValue links.layout height tree size, indexValue, proofValue] continuation)
      (frameState links.get 0 #[.erased, arrayValue links.layout height tree size, indexValue, .erased] continuation) := by
    apply Reaches.of_step
    simp [step, stepEval, Frame.check, checked.code, getAlias, certificate.get.code, ArrayTrees.get,
      frameState, Frame.read, Frame.readOperands, enter, show ¬limits.locals < 4 by omega,
      bind, Except.bind, pure, Except.pure]
  exact entered.trans (certificate.get_returns limits room capacity bytesCapacity .erased .erased
    height tree n size index indexValue value sizeRep indexRep within bounded found valid continuation stack)

theorem getBang_of_lt_returns {id : FunctionId} (checked : Checked program id (ArrayTrees.getBang links))
    (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue defaultValue : Value)
    (height : Nat) (tree : Tree height) (n : Nat) (size : Value) (index : Nat) (indexValue value : Value)
    (sizeRep : Number links.arithmetic.conversions.layout n size)
    (indexRep : Number links.arithmetic.conversions.layout index indexValue)
    (within : n ≤ 2 ^ height) (bounded : index < n) (found : tree.get index = some value)
    (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 4 ≤ limits.continuations) :
    Reaches limits program
      (frameState id 0 #[typeValue, defaultValue, arrayValue links.layout height tree size, indexValue] continuation)
      (returned value continuation) := by
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  let args := #[typeValue, defaultValue, arrayValue links.layout height tree size, indexValue]
  have checkedIndex : Reaches limits program (frameState id 0 args continuation)
      (frameState id 2 (args ++ #[size, .scalar (.bool true)]) continuation) := by
    simpa [bounded] using certificate.check_index limits checked args (.local 2) (.local 3)
      rfl rfl _ rfl room (by simp [args]; omega) capacity bytesCapacity height tree size n index indexValue
      sizeRep indexRep (validate_nat_mono within valid) (validate_nat_mono (by omega : index ≤ 2 ^ height) valid)
      rfl rfl continuation stack
  have entered : Reaches limits program
      (frameState id 2 (args ++ #[size, .scalar (.bool true)]) continuation)
      (frameState links.get 0 #[.erased, arrayValue links.layout height tree size, indexValue, .erased] continuation) := by
    apply reaches_of_chunk (fuel := 2) (count := 0)
    iterate 2
      rw [runChunk]
      simp [args, step, stepEval, Frame.check, checked.code, ArrayTrees.getBang, certificate.get.code, ArrayTrees.get,
        frameState, Frame.read, Frame.readOperands, Frame.transfer, enter,
        localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  exact checkedIndex.trans (entered.trans (certificate.get_returns limits room capacity bytesCapacity
    .erased .erased height tree n size index indexValue value sizeRep indexRep within bounded found valid continuation stack))

theorem getBang_of_ge_returns {id : FunctionId} (checked : Checked program id (ArrayTrees.getBang links))
    (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue defaultValue : Value)
    (height : Nat) (tree : Tree height) (n : Nat) (size : Value) (index : Nat) (indexValue : Value)
    (sizeRep : Number links.arithmetic.conversions.layout n size)
    (indexRep : Number links.arithmetic.conversions.layout index indexValue)
    (outside : n ≤ index) (sizeValid : (Scalar.nat n).validate limits = .ok ())
    (indexValid : (Scalar.nat index).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 4 ≤ limits.continuations) :
    Reaches limits program
      (frameState id 0 #[typeValue, defaultValue, arrayValue links.layout height tree size, indexValue] continuation)
      (returned defaultValue continuation) := by
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  let args := #[typeValue, defaultValue, arrayValue links.layout height tree size, indexValue]
  have checkedIndex : Reaches limits program (frameState id 0 args continuation)
      (frameState id 2 (args ++ #[size, .scalar (.bool false)]) continuation) := by
    simpa [show ¬index < n by omega] using certificate.check_index limits checked args (.local 2) (.local 3)
      rfl rfl _ rfl room (by simp [args]; omega) capacity bytesCapacity height tree size n index indexValue
      sizeRep indexRep sizeValid indexValid rfl rfl continuation stack
  apply checkedIndex.trans
  apply reaches_of_chunk (fuel := 2) (count := 0)
  iterate 2
    rw [runChunk]
    simp [args, step, stepEval, Frame.check, checked.code, ArrayTrees.getBang, frameState, returned,
      Frame.read, Frame.transfer, localRoom, bind, Except.bind, pure, Except.pure]
  rfl

end Compilatrix.Ixby.Runtime.ArrayTrees.Certificate
