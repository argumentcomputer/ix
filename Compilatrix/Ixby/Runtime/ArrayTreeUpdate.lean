import Compilatrix.Ixby.Runtime.ArrayTreeIndex
import Compilatrix.Ixby.Runtime.ArrayTreeSet

/-! Tree-backed updates preserve the original size representation and all
other elements. Out-of-bounds set! returns the original physical array. -/

namespace Compilatrix.Ixby.Runtime.ArrayTrees.Certificate

open Ix.Ixby Execution Representation ScalarFunction Conversion

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

variable {program : Program} {links : Links} (certificate : Certificate program links)
  (limits : Limits)

include certificate

theorem set_of_lt_returns (room : 12 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue : Value)
    (height : Nat) (tree : Tree height) (n : Nat) (size : Value) (index : Nat) (indexValue value : Value)
    (sizeRep : Number links.arithmetic.conversions.layout n size)
    (indexRep : Number links.arithmetic.conversions.layout index indexValue)
    (within : n ≤ 2 ^ height) (bounded : index < n)
    (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + max 4 (height + 1) ≤ limits.continuations) :
    Reaches limits program
      (frameState links.set 0
        #[typeValue, arrayValue links.layout height tree size, indexValue, value] continuation)
      (returned (arrayValue links.layout height (tree.set height index value) size) continuation) := by
  have localRoom : ∀ k, k ≤ 12 → ¬limits.locals < k := by omega
  let array := arrayValue links.layout height tree size
  let args := #[typeValue, array, indexValue, value]
  have checkedIndex : Reaches limits program (frameState links.set 0 args continuation)
      (frameState links.set 2 (args ++ #[size, .scalar (.bool true)]) continuation) := by
    simpa [bounded] using certificate.check_index limits certificate.set args (.local 1) (.local 2)
      rfl rfl _ rfl (by omega) (by simp [args]; omega) capacity bytesCapacity height tree size n index indexValue
      sizeRep indexRep (validate_nat_mono within valid) (validate_nat_mono (by omega : index ≤ 2 ^ height) valid)
      rfl rfl continuation (by omega)
  let locals := args ++ #[size, .scalar (.bool true), size, .scalar (.nat (2 ^ height)), tree.encode links.layout]
  have dispatched : Reaches limits program
      (frameState links.set 2 (args ++ #[size, .scalar (.bool true)]) continuation)
      (frameState links.set 6 locals continuation) := by
    apply reaches_of_chunk (fuel := 2) (count := 0)
    iterate 2
      rw [runChunk]
      simp [args, array, locals, step, stepEval, Frame.check, certificate.set.code, ArrayTrees.set,
        certificate.bytesCtor, certificate.arrayCtor, certificate.bytesArray,
        frameState, arrayValue, Frame.read, Frame.transfer, selectCase,
        localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  have observed := certificate.arithmetic.conversions.call_natural limits (by omega) capacity bytesCapacity
    { function := links.set, block := 6, locals } (.local 2) 9 index indexValue indexRep
    { function := links.set, block := 9, locals := locals ++ #[.scalar (.nat index)] }
    (by simp [args, locals, Frame.check, certificate.set.code, ArrayTrees.set,
      localRoom, bind, Except.bind, pure, Except.pure]) rfl
    (by simp [args, locals, Frame.transfer, Frame.check, certificate.set.code, ArrayTrees.set,
      localRoom, bind, Except.bind, pure, Except.pure]) continuation (by omega)
  let before := locals ++ #[.scalar (.nat index)]
  let updated := (tree.set height index value).encode links.layout
  have written := certificate.treeSet_returns limits room (by omega) height tree index value (by omega) valid
    (continuation.push (.resume { function := links.set, block := 10, locals := before })) (by simp; omega)
  have called := ArrayTrees.call_returns limits program { function := links.set, block := 9, locals := before }
    links.treeSet [.local 8, .local 7, .local 9, .local 3]
    #[tree.encode links.layout, .scalar (.nat (2 ^ height)), .scalar (.nat index), value] 10 updated
    { function := links.set, block := 10, locals := before ++ #[updated] } continuation (by omega)
    (by simp [args, locals, before, Frame.check, certificate.set.code, ArrayTrees.set,
      localRoom, bind, Except.bind, pure, Except.pure]) rfl
    (by simp [enter, Frame.check, certificate.treeSet.code, ArrayTrees.treeSet,
      localRoom, bind, Except.bind, pure, Except.pure])
    (by simp [args, locals, before, Frame.transfer, Frame.check, certificate.set.code, ArrayTrees.set,
      localRoom, bind, Except.bind, pure, Except.pure]) written
  have finished : Reaches limits program
      (frameState links.set 10 (before ++ #[updated]) continuation)
      (returned (arrayValue links.layout height (tree.set height index value) size) continuation) := by
    apply reaches_of_chunk (fuel := 2) (count := 0)
    iterate 2
      rw [runChunk]
      simp [args, locals, before, updated, step, stepEval, Frame.check, certificate.set.code, ArrayTrees.set,
        certificate.arrayCtor, frameState, returned, arrayValue, Frame.read, Frame.readOperands,
        Frame.transfer, evalOp, localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  exact checkedIndex.trans (dispatched.trans (observed.trans (called.trans finished)))

theorem set_of_ge_returns (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue : Value)
    (height : Nat) (tree : Tree height) (n : Nat) (size : Value) (index : Nat) (indexValue value : Value)
    (sizeRep : Number links.arithmetic.conversions.layout n size)
    (indexRep : Number links.arithmetic.conversions.layout index indexValue)
    (outside : n ≤ index) (sizeValid : (Scalar.nat n).validate limits = .ok ())
    (indexValid : (Scalar.nat index).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 4 ≤ limits.continuations) :
    Reaches limits program
      (frameState links.set 0 #[typeValue, arrayValue links.layout height tree size, indexValue, value] continuation)
      (returned (arrayValue links.layout height tree size) continuation) := by
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  let args := #[typeValue, arrayValue links.layout height tree size, indexValue, value]
  have checkedIndex : Reaches limits program (frameState links.set 0 args continuation)
      (frameState links.set 2 (args ++ #[size, .scalar (.bool false)]) continuation) := by
    simpa [show ¬index < n by omega] using certificate.check_index limits certificate.set args (.local 1) (.local 2)
      rfl rfl _ rfl room (by simp [args]; omega) capacity bytesCapacity height tree size n index indexValue
      sizeRep indexRep sizeValid indexValid rfl rfl continuation stack
  apply checkedIndex.trans
  apply reaches_of_chunk (fuel := 2) (count := 0)
  iterate 2
    rw [runChunk]
    simp [args, step, stepEval, Frame.check, certificate.set.code, ArrayTrees.set, frameState, returned,
      Frame.read, Frame.transfer, localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem uset_returns (room : 12 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue proofValue : Value)
    (height : Nat) (tree : Tree height) (n : Nat) (size : Value) (index : Nat) (indexValue value : Value)
    (sizeRep : Number links.arithmetic.conversions.layout n size)
    (indexRep : Number links.arithmetic.conversions.layout index indexValue)
    (within : n ≤ 2 ^ height) (bounded : index < n)
    (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + max 4 (height + 1) ≤ limits.continuations) :
    Reaches limits program
      (frameState links.uset 0
        #[typeValue, arrayValue links.layout height tree size, indexValue, value, proofValue] continuation)
      (returned (arrayValue links.layout height (tree.set height index value) size) continuation) := by
  have localRoom : ∀ k, k ≤ 12 → ¬limits.locals < k := by omega
  let args := #[typeValue, arrayValue links.layout height tree size, indexValue, value, proofValue]
  have checkedIndex : Reaches limits program (frameState links.uset 0 args continuation)
      (frameState links.uset 2 (args ++ #[size, .scalar (.bool true)]) continuation) := by
    simpa [bounded] using certificate.check_index limits certificate.uset args (.local 1) (.local 2)
      rfl rfl _ rfl (by omega) (by simp [args]; omega) capacity bytesCapacity height tree size n index indexValue
      sizeRep indexRep (validate_nat_mono within valid) (validate_nat_mono (by omega : index ≤ 2 ^ height) valid)
      rfl rfl continuation (by omega)
  have entered : Reaches limits program
      (frameState links.uset 2 (args ++ #[size, .scalar (.bool true)]) continuation)
      (frameState links.set 0 #[.erased, arrayValue links.layout height tree size, indexValue, value] continuation) := by
    apply reaches_of_chunk (fuel := 2) (count := 0)
    iterate 2
      rw [runChunk]
      simp [args, step, stepEval, Frame.check, certificate.uset.code, ArrayTrees.uset, certificate.set.code, ArrayTrees.set,
        frameState, Frame.read, Frame.readOperands, Frame.transfer, enter,
        localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  exact checkedIndex.trans (entered.trans (certificate.set_of_lt_returns limits room capacity bytesCapacity
    .erased height tree n size index indexValue value sizeRep indexRep within bounded valid continuation stack))

end Compilatrix.Ixby.Runtime.ArrayTrees.Certificate
