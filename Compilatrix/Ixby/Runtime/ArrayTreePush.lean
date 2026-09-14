import Compilatrix.Ixby.Runtime.ArrayTreeBasic
import Compilatrix.Ixby.Runtime.ArrayTreeSet

/-! Push composes exact size arithmetic with a sparse-tree write. Full trees
grow by doubling capacity and attaching an empty right subtree. -/

namespace Compilatrix.Ixby.Runtime.ArrayTrees.Certificate

open Ix.Ixby Execution Representation ScalarFunction Conversion
open Words (cachedValue)

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

variable {program : Program} {links : Links} (certificate : Certificate program links)
  (limits : Limits)

include certificate

theorem push_prepare (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue : Value)
    (height : Nat) (tree : Tree height) (n : Nat) (size value : Value)
    (sizeRep : Number links.arithmetic.conversions.layout n size)
    (sizeValid : (Scalar.nat n).validate limits = .ok ())
    (nextValid : (Scalar.nat (n + 1)).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 4 ≤ limits.continuations) :
    ∃ nextSize, Reaches limits program
      (frameState links.push 0 #[typeValue, arrayValue links.layout height tree size, value] continuation)
      (frameState links.push 8
        #[typeValue, arrayValue links.layout height tree size, value, size,
          cachedValue links.arithmetic.conversions.layout 1, nextSize,
          size, .scalar (.nat (2 ^ height)), tree.encode links.layout, .scalar (.nat n)] continuation) ∧
      Number links.arithmetic.conversions.layout (n + 1) nextSize := by
  have localRoom : ∀ k, k ≤ 11 → ¬limits.locals < k := by omega
  let array := arrayValue links.layout height tree size
  let args := #[typeValue, array, value]
  let one := cachedValue links.arithmetic.conversions.layout 1
  have oneRep : Number links.arithmetic.conversions.layout 1 one := .cached 1
  have oneValid : (Scalar.nat 1).validate limits = .ok () :=
    validate_nat_of_bits (bits := 64) (by decide) capacity
  have sizePath := certificate.call_size limits (by omega)
    { function := links.push, block := 0, locals := args } (.local 1) 1 height tree size
    { function := links.push, block := 1, locals := args ++ #[size] }
    (by simp [args, Frame.check, certificate.push.code, ArrayTrees.push,
      localRoom, bind, Except.bind, pure, Except.pure]) rfl
    (by simp [args, Frame.transfer, Frame.check, certificate.push.code, ArrayTrees.push,
      localRoom, bind, Except.bind, pure, Except.pure]) continuation (by omega)
  have constant : Reaches limits program (frameState links.push 1 (args ++ #[size]) continuation)
      (frameState links.push 2 (args ++ #[size, one]) continuation) := by
    apply Reaches.of_step
    simp [args, one, step, stepEval, Frame.check, certificate.push.code, ArrayTrees.push,
      certificate.arithmetic.conversions.cached, frameState, cachedValue, Frame.readOperands, Frame.read,
      Frame.transfer, evalOp, N, W, localRoom, bind, Except.bind, pure, Except.pure]
  obtain ⟨nextSize, added, nextRep⟩ := certificate.arithmetic.add_returns limits room capacity bytesCapacity
    n 1 size one sizeRep oneRep sizeValid oneValid nextValid
    (continuation.push (.resume { function := links.push, block := 3, locals := args ++ #[size, one] }))
    (by simp; omega)
  have addition := ArrayTrees.call_returns limits program
    { function := links.push, block := 2, locals := args ++ #[size, one] } links.arithmetic.add
    [.local 3, .local 4] #[size, one] 3 nextSize
    { function := links.push, block := 3, locals := args ++ #[size, one, nextSize] }
    continuation (by omega)
    (by simp [args, Frame.check, certificate.push.code, ArrayTrees.push,
      localRoom, bind, Except.bind, pure, Except.pure]) rfl
    (by simp [enter, Frame.check, certificate.arithmetic.add.code, NatArithmetic.binary,
      localRoom, bind, Except.bind, pure, Except.pure])
    (by simp [args, Frame.transfer, Frame.check, certificate.push.code, ArrayTrees.push,
      localRoom, bind, Except.bind, pure, Except.pure]) added
  let locals := args ++ #[size, one, nextSize, size, .scalar (.nat (2 ^ height)), tree.encode links.layout]
  have dispatched : Reaches limits program
      (frameState links.push 3 (args ++ #[size, one, nextSize]) continuation)
      (frameState links.push 5 locals continuation) := by
    apply Reaches.of_step
    simp [args, array, locals, step, stepEval, Frame.check, certificate.push.code, ArrayTrees.push,
      certificate.bytesCtor, certificate.arrayCtor, certificate.bytesArray,
      frameState, arrayValue, Frame.read, Frame.transfer, selectCase,
      localRoom, bind, Except.bind, pure, Except.pure]
  have observed := certificate.arithmetic.conversions.call_natural limits (by omega) capacity bytesCapacity
    { function := links.push, block := 5, locals } (.local 3) 8 n size sizeRep
    { function := links.push, block := 8, locals := locals ++ #[.scalar (.nat n)] }
    (by simp [args, locals, Frame.check, certificate.push.code, ArrayTrees.push,
      localRoom, bind, Except.bind, pure, Except.pure]) rfl
    (by simp [args, locals, Frame.transfer, Frame.check, certificate.push.code, ArrayTrees.push,
      localRoom, bind, Except.bind, pure, Except.pure]) continuation (by omega)
  exact ⟨nextSize, sizePath.trans (constant.trans (addition.trans (dispatched.trans observed))), nextRep⟩

theorem push_with_space_returns (room : 13 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue : Value)
    (height : Nat) (tree : Tree height) (n : Nat) (size value : Value)
    (sizeRep : Number links.arithmetic.conversions.layout n size) (space : n < 2 ^ height)
    (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + max 4 (height + 1) ≤ limits.continuations) :
    ∃ nextSize, Reaches limits program
      (frameState links.push 0 #[typeValue, arrayValue links.layout height tree size, value] continuation)
      (returned (arrayValue links.layout height (tree.set height n value) nextSize) continuation) ∧
      Number links.arithmetic.conversions.layout (n + 1) nextSize := by
  have localRoom : ∀ k, k ≤ 13 → ¬limits.locals < k := by omega
  have sizeValid := validate_nat_mono (by omega : n ≤ 2 ^ height) valid
  obtain ⟨nextSize, prepared, nextRep⟩ := certificate.push_prepare limits (by omega) capacity bytesCapacity
    typeValue height tree n size value sizeRep sizeValid (validate_nat_mono (by omega : n + 1 ≤ 2 ^ height) valid)
    continuation (by omega)
  let locals := #[typeValue, arrayValue links.layout height tree size, value, size,
    cachedValue links.arithmetic.conversions.layout 1, nextSize, size, .scalar (.nat (2 ^ height)),
    tree.encode links.layout, .scalar (.nat n)]
  let before := locals ++ #[.scalar (.bool true)]
  have selected : Reaches limits program (frameState links.push 8 locals continuation)
      (frameState links.push 10 before continuation) := by
    apply reaches_of_chunk (fuel := 2) (count := 0)
    iterate 2
      rw [runChunk]
      simp [locals, before, step, stepEval, Frame.check, certificate.push.code, ArrayTrees.push,
        frameState, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
        Primitive.eval, Primitive.arity, sizeValid, valid, space,
        localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  let updated := (tree.set height n value).encode links.layout
  have written := certificate.treeSet_returns limits (by omega) (by omega) height tree n value space valid
    (continuation.push (.resume { function := links.push, block := 12, locals := before })) (by simp; omega)
  have called := ArrayTrees.call_returns limits program { function := links.push, block := 10, locals := before }
    links.treeSet [.local 8, .local 7, .local 9, .local 2]
    #[tree.encode links.layout, .scalar (.nat (2 ^ height)), .scalar (.nat n), value] 12 updated
    { function := links.push, block := 12, locals := before ++ #[updated] } continuation (by omega)
    (by simp [locals, before, Frame.check, certificate.push.code, ArrayTrees.push,
      localRoom, bind, Except.bind, pure, Except.pure]) rfl
    (by simp [enter, Frame.check, certificate.treeSet.code, ArrayTrees.treeSet,
      localRoom, bind, Except.bind, pure, Except.pure])
    (by simp [locals, before, Frame.transfer, Frame.check, certificate.push.code, ArrayTrees.push,
      localRoom, bind, Except.bind, pure, Except.pure]) written
  have finished : Reaches limits program (frameState links.push 12 (before ++ #[updated]) continuation)
      (returned (arrayValue links.layout height (tree.set height n value) nextSize) continuation) := by
    apply reaches_of_chunk (fuel := 2) (count := 0)
    iterate 2
      rw [runChunk]
      simp [locals, before, updated, step, stepEval, Frame.check, certificate.push.code, ArrayTrees.push,
        certificate.arrayCtor, frameState, returned, arrayValue, Frame.read, Frame.readOperands,
        Frame.transfer, evalOp, localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  exact ⟨nextSize, prepared.trans (selected.trans (called.trans finished)), nextRep⟩

theorem push_full_returns (room : 16 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (typeValue : Value)
    (height : Nat) (tree : Tree height) (size value : Value)
    (sizeRep : Number links.arithmetic.conversions.layout (2 ^ height) size)
    (valid : (Scalar.nat (2 ^ (height + 1))).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + max 4 (height + 2) ≤ limits.continuations) :
    ∃ nextSize, Reaches limits program
      (frameState links.push 0 #[typeValue, arrayValue links.layout height tree size, value] continuation)
      (returned (arrayValue links.layout (height + 1)
        ((Tree.node tree (.empty height)).set (height + 1) (2 ^ height) value) nextSize) continuation) ∧
      Number links.arithmetic.conversions.layout (2 ^ height + 1) nextSize := by
  have localRoom : ∀ k, k ≤ 16 → ¬limits.locals < k := by omega
  have positive := pow_positive height
  have doubled : 2 ^ height + 2 ^ height = 2 ^ (height + 1) := by rw [Nat.pow_succ]; omega
  have sizeValid := validate_nat_mono (by omega : 2 ^ height ≤ 2 ^ (height + 1)) valid
  obtain ⟨nextSize, prepared, nextRep⟩ := certificate.push_prepare limits (by omega) capacity bytesCapacity
    typeValue height tree (2 ^ height) size value sizeRep sizeValid
    (validate_nat_mono (by omega : 2 ^ height + 1 ≤ 2 ^ (height + 1)) valid) continuation (by omega)
  let locals := #[typeValue, arrayValue links.layout height tree size, value, size,
    cachedValue links.arithmetic.conversions.layout 1, nextSize, size, .scalar (.nat (2 ^ height)),
    tree.encode links.layout, .scalar (.nat (2 ^ height))]
  let grown := Tree.node tree (Tree.empty height)
  let before := locals ++ #[.scalar (.bool false), .scalar (.nat (2 ^ (height + 1))),
    (Tree.empty height).encode links.layout, grown.encode links.layout]
  have selected : Reaches limits program (frameState links.push 8 locals continuation)
      (frameState links.push 16 before continuation) := by
    apply reaches_of_chunk (fuel := 5) (count := 0)
    iterate 5
      rw [runChunk]
      simp [locals, before, grown, step, stepEval, Frame.check, certificate.push.code, ArrayTrees.push,
        certificate.emptyCtor, certificate.nodeCtor, frameState, Tree.encode,
        Frame.read, Frame.readOperands, Frame.transfer, evalOp,
        Primitive.eval, Primitive.arity, sizeValid, valid, doubled,
        localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  let updated := (grown.set (height + 1) (2 ^ height) value).encode links.layout
  have written := certificate.treeSet_returns limits (by omega) (by omega) (height + 1) grown (2 ^ height) value
    (by omega) valid (continuation.push (.resume { function := links.push, block := 17, locals := before }))
    (by simp; omega)
  have called := ArrayTrees.call_returns limits program { function := links.push, block := 16, locals := before }
    links.treeSet [.local 13, .local 11, .local 9, .local 2]
    #[grown.encode links.layout, .scalar (.nat (2 ^ (height + 1))), .scalar (.nat (2 ^ height)), value] 17 updated
    { function := links.push, block := 17, locals := before ++ #[updated] } continuation (by omega)
    (by simp [locals, before, Frame.check, certificate.push.code, ArrayTrees.push,
      localRoom, bind, Except.bind, pure, Except.pure]) rfl
    (by simp [enter, Frame.check, certificate.treeSet.code, ArrayTrees.treeSet,
      localRoom, bind, Except.bind, pure, Except.pure])
    (by simp [locals, before, Frame.transfer, Frame.check, certificate.push.code, ArrayTrees.push,
      localRoom, bind, Except.bind, pure, Except.pure]) written
  have finished : Reaches limits program (frameState links.push 17 (before ++ #[updated]) continuation)
      (returned (arrayValue links.layout (height + 1)
        (grown.set (height + 1) (2 ^ height) value) nextSize) continuation) := by
    apply reaches_of_chunk (fuel := 2) (count := 0)
    iterate 2
      rw [runChunk]
      simp [locals, before, updated, step, stepEval, Frame.check, certificate.push.code, ArrayTrees.push,
        certificate.arrayCtor, frameState, returned, arrayValue, Frame.read, Frame.readOperands,
        Frame.transfer, evalOp, localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  exact ⟨nextSize, prepared.trans (selected.trans (called.trans finished)), nextRep⟩

end Compilatrix.Ixby.Runtime.ArrayTrees.Certificate
