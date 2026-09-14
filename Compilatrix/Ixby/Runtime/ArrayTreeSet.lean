import Compilatrix.Ixby.Runtime.ArrayTreeCall

/-! Sparse-tree writes execute the emitted recursive helper. Each descent
adds one real resume frame and reconstructs the untouched sibling exactly. -/

namespace Compilatrix.Ixby.Runtime.ArrayTrees.Certificate

open Ix.Ixby Execution Representation ScalarFunction Conversion

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

variable {program : Program} {links : Links} (certificate : Certificate program links)
  (limits : Limits)

include certificate

theorem treeSet_returns (room : 12 ≤ limits.locals) (capacity : 2 ≤ limits.natBits)
    (height : Nat) (tree : Tree height) (index : Nat) (value : Value)
    (bounded : index < 2 ^ height)
    (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + height ≤ limits.continuations) :
    Reaches limits program
      (frameState links.treeSet 0
        #[tree.encode links.layout, .scalar (.nat (2 ^ height)), .scalar (.nat index), value] continuation)
      (returned ((tree.set height index value).encode links.layout) continuation) := by
  have localRoom : ∀ k, k ≤ 12 → ¬limits.locals < k := by omega
  have smallNat (k : Nat) (small : k ≤ 2) : (Scalar.nat k).validate limits = .ok () :=
    validate_nat_of_bits (by omega : k < 2 ^ 2) capacity
  induction height generalizing index continuation with
  | zero =>
    apply reaches_of_chunk (fuel := 4) (count := 0)
    iterate 4
      rw [runChunk]
      simp [step, stepEval, Frame.check, certificate.treeSet.code, ArrayTrees.treeSet, certificate.leafCtor,
        frameState, returned, Tree.set, Tree.encode, Frame.read, Frame.readOperands, Frame.transfer,
        evalOp, Primitive.eval, Primitive.arity, N, smallNat, localRoom, bind, Except.bind, pure,
        Except.pure]
    rfl
  | succ height ih =>
    have positive := pow_positive height
    have doubled : 2 ^ (height + 1) = 2 ^ height + 2 ^ height := by rw [Nat.pow_succ]; omega
    have notLeaf : ¬2 ^ (height + 1) = 1 := by omega
    have notLeafB : (2 ^ (height + 1) == 1) = false := beq_eq_false_iff_ne.mpr notLeaf
    have nextValid := validate_nat_mono (show 2 ^ height ≤ 2 ^ (height + 1) by omega) valid
    have indexValid := validate_nat_mono (by omega : index ≤ 2 ^ (height + 1)) valid
    have restValid := validate_nat_mono (Nat.sub_le index (2 ^ height)) indexValid
    cases tree with
    | empty =>
      by_cases goLeft : index < 2 ^ height
      · have nextBound : index < 2 ^ height := goLeft
        let locals : Array Value := #[(Tree.empty (height + 1)).encode links.layout, .scalar (.nat (2 ^ (height + 1))), .scalar (.nat index), value, .scalar (.bool false), .scalar (.nat (2 ^ height)), (Tree.empty height).encode links.layout, .scalar (.bool true)]
        have beforeCall : Reaches limits program
            (frameState links.treeSet 0
              #[(Tree.empty (height + 1)).encode links.layout, .scalar (.nat (2 ^ (height + 1))),
                .scalar (.nat index), value] continuation)
            (frameState links.treeSet 10 locals continuation) := by
          apply reaches_of_chunk (fuel := 7) (count := 0)
          iterate 7
            rw [runChunk]
            simp [locals, step, stepEval, Frame.check, certificate.treeSet.code, ArrayTrees.treeSet,
              certificate.emptyCtor, frameState, Tree.encode, Frame.read, Frame.readOperands,
              Frame.transfer, evalOp, selectCase, Primitive.eval, Primitive.arity, N, valid, nextValid,
              indexValid, notLeafB, goLeft, pow_half, smallNat, localRoom, bind, Except.bind, pure,
              Except.pure]
          rfl
        have recursive := ih (Tree.empty height) index nextBound nextValid
          (continuation.push (.resume { function := links.treeSet, block := 12, locals }))
          (by simp; omega)
        have called := ArrayTrees.call_returns limits program
          { function := links.treeSet, block := 10, locals } links.treeSet
          [.local 6, .local 5, .local 2, .local 3] #[(Tree.empty height).encode links.layout, .scalar (.nat (2 ^ height)), .scalar (.nat index), value] 12 (((Tree.empty height).set height index value).encode links.layout)
          { function := links.treeSet, block := 12, locals := locals ++ #[((Tree.empty height).set height index value).encode links.layout] }
          continuation (by omega)
          (by simp [locals, Frame.check, certificate.treeSet.code, ArrayTrees.treeSet, Tree.encode, N, localRoom,
            bind, Except.bind, pure, Except.pure])
          (by rfl)
          (by simp [Frame.check, certificate.treeSet.code, ArrayTrees.treeSet, Tree.encode, enter, N, localRoom, bind,
            Except.bind, pure, Except.pure])
          (by simp [locals, Frame.check, certificate.treeSet.code, ArrayTrees.treeSet, Tree.encode, Frame.transfer, N,
            localRoom, bind, Except.bind, pure, Except.pure]) recursive
        have finished : Reaches limits program
            (frameState links.treeSet 12 (locals ++ #[((Tree.empty height).set height index value).encode links.layout]) continuation)
            (returned (((Tree.empty (height + 1)).set (height + 1) index value).encode links.layout) continuation) := by
          apply reaches_of_chunk (fuel := 2) (count := 0)
          iterate 2
            rw [runChunk]
            simp [locals, step, stepEval, Frame.check, certificate.treeSet.code, ArrayTrees.treeSet,
              certificate.nodeCtor, frameState, returned, Tree.encode, Tree.set, Tree.left, Tree.right,
              Frame.read, Frame.readOperands, Frame.transfer, evalOp, N, goLeft, localRoom, bind,
              Except.bind, pure, Except.pure]
          rfl
        exact beforeCall.trans (called.trans finished)
      · have nextBound : index - 2 ^ height < 2 ^ height := by omega
        let locals : Array Value := #[(Tree.empty (height + 1)).encode links.layout, .scalar (.nat (2 ^ (height + 1))), .scalar (.nat index), value, .scalar (.bool false), .scalar (.nat (2 ^ height)), (Tree.empty height).encode links.layout, .scalar (.bool false), .scalar (.nat (index - 2 ^ height))]
        have beforeCall : Reaches limits program
            (frameState links.treeSet 0
              #[(Tree.empty (height + 1)).encode links.layout, .scalar (.nat (2 ^ (height + 1))),
                .scalar (.nat index), value] continuation)
            (frameState links.treeSet 14 locals continuation) := by
          apply reaches_of_chunk (fuel := 8) (count := 0)
          iterate 8
            rw [runChunk]
            simp [locals, step, stepEval, Frame.check, certificate.treeSet.code, ArrayTrees.treeSet,
              certificate.emptyCtor, frameState, Tree.encode, Frame.read, Frame.readOperands,
              Frame.transfer, evalOp, selectCase, Primitive.eval, Primitive.arity, N, valid, nextValid,
              indexValid, restValid, notLeafB, goLeft, pow_half, smallNat, localRoom, bind, Except.bind,
              pure, Except.pure]
          rfl
        have recursive := ih (Tree.empty height) (index - 2 ^ height) nextBound nextValid
          (continuation.push (.resume { function := links.treeSet, block := 15, locals }))
          (by simp; omega)
        have called := ArrayTrees.call_returns limits program
          { function := links.treeSet, block := 14, locals } links.treeSet
          [.local 6, .local 5, .local 8, .local 3] #[(Tree.empty height).encode links.layout, .scalar (.nat (2 ^ height)), .scalar (.nat (index - 2 ^ height)), value] 15 (((Tree.empty height).set height (index - 2 ^ height) value).encode links.layout)
          { function := links.treeSet, block := 15, locals := locals ++ #[((Tree.empty height).set height (index - 2 ^ height) value).encode links.layout] }
          continuation (by omega)
          (by simp [locals, Frame.check, certificate.treeSet.code, ArrayTrees.treeSet, Tree.encode, N, localRoom,
            bind, Except.bind, pure, Except.pure])
          (by rfl)
          (by simp [Frame.check, certificate.treeSet.code, ArrayTrees.treeSet, Tree.encode, enter, N, localRoom, bind,
            Except.bind, pure, Except.pure])
          (by simp [locals, Frame.check, certificate.treeSet.code, ArrayTrees.treeSet, Tree.encode, Frame.transfer, N,
            localRoom, bind, Except.bind, pure, Except.pure]) recursive
        have finished : Reaches limits program
            (frameState links.treeSet 15 (locals ++ #[((Tree.empty height).set height (index - 2 ^ height) value).encode links.layout]) continuation)
            (returned (((Tree.empty (height + 1)).set (height + 1) index value).encode links.layout) continuation) := by
          apply reaches_of_chunk (fuel := 2) (count := 0)
          iterate 2
            rw [runChunk]
            simp [locals, step, stepEval, Frame.check, certificate.treeSet.code, ArrayTrees.treeSet,
              certificate.nodeCtor, frameState, returned, Tree.encode, Tree.set, Tree.left, Tree.right,
              Frame.read, Frame.readOperands, Frame.transfer, evalOp, N, goLeft, localRoom, bind,
              Except.bind, pure, Except.pure]
          rfl
        exact beforeCall.trans (called.trans finished)
    | node left right =>
      by_cases goLeft : index < 2 ^ height
      · have nextBound : index < 2 ^ height := goLeft
        let locals : Array Value := #[(Tree.node left right).encode links.layout, .scalar (.nat (2 ^ (height + 1))), .scalar (.nat index), value, .scalar (.bool false), .scalar (.nat (2 ^ height)), left.encode links.layout, right.encode links.layout, .scalar (.bool true)]
        have beforeCall : Reaches limits program
            (frameState links.treeSet 0
              #[(Tree.node left right).encode links.layout, .scalar (.nat (2 ^ (height + 1))),
                .scalar (.nat index), value] continuation)
            (frameState links.treeSet 18 locals continuation) := by
          apply reaches_of_chunk (fuel := 6) (count := 0)
          iterate 6
            rw [runChunk]
            simp [locals, step, stepEval, Frame.check, certificate.treeSet.code, ArrayTrees.treeSet,
              certificate.emptyCtor, certificate.nodeCtor, certificate.emptyNode, frameState,
              Tree.encode, Frame.read, Frame.readOperands, Frame.transfer, evalOp, selectCase,
              Primitive.eval, Primitive.arity, N, valid, nextValid, indexValid, notLeafB, goLeft,
              pow_half, smallNat, localRoom, bind, Except.bind, pure, Except.pure]
          rfl
        have recursive := ih left index nextBound nextValid
          (continuation.push (.resume { function := links.treeSet, block := 20, locals }))
          (by simp; omega)
        have called := ArrayTrees.call_returns limits program
          { function := links.treeSet, block := 18, locals } links.treeSet
          [.local 6, .local 5, .local 2, .local 3] #[left.encode links.layout, .scalar (.nat (2 ^ height)), .scalar (.nat index), value] 20 ((left.set height index value).encode links.layout)
          { function := links.treeSet, block := 20, locals := locals ++ #[(left.set height index value).encode links.layout] }
          continuation (by omega)
          (by simp [locals, Frame.check, certificate.treeSet.code, ArrayTrees.treeSet, Tree.encode, N, localRoom,
            bind, Except.bind, pure, Except.pure])
          (by rfl)
          (by simp [Frame.check, certificate.treeSet.code, ArrayTrees.treeSet, enter, N, localRoom, bind, Except.bind,
            pure, Except.pure])
          (by simp [locals, Frame.check, certificate.treeSet.code, ArrayTrees.treeSet, Tree.encode, Frame.transfer, N,
            localRoom, bind, Except.bind, pure, Except.pure]) recursive
        have finished : Reaches limits program
            (frameState links.treeSet 20 (locals ++ #[(left.set height index value).encode links.layout]) continuation)
            (returned (((Tree.node left right).set (height + 1) index value).encode links.layout) continuation) := by
          apply reaches_of_chunk (fuel := 2) (count := 0)
          iterate 2
            rw [runChunk]
            simp [locals, step, stepEval, Frame.check, certificate.treeSet.code, ArrayTrees.treeSet,
              certificate.nodeCtor, frameState, returned, Tree.encode, Tree.set, Tree.left, Tree.right,
              Frame.read, Frame.readOperands, Frame.transfer, evalOp, N, goLeft, localRoom, bind,
              Except.bind, pure, Except.pure]
          rfl
        exact beforeCall.trans (called.trans finished)
      · have nextBound : index - 2 ^ height < 2 ^ height := by omega
        let locals : Array Value := #[(Tree.node left right).encode links.layout, .scalar (.nat (2 ^ (height + 1))), .scalar (.nat index), value, .scalar (.bool false), .scalar (.nat (2 ^ height)), left.encode links.layout, right.encode links.layout, .scalar (.bool false), .scalar (.nat (index - 2 ^ height))]
        have beforeCall : Reaches limits program
            (frameState links.treeSet 0
              #[(Tree.node left right).encode links.layout, .scalar (.nat (2 ^ (height + 1))),
                .scalar (.nat index), value] continuation)
            (frameState links.treeSet 22 locals continuation) := by
          apply reaches_of_chunk (fuel := 7) (count := 0)
          iterate 7
            rw [runChunk]
            simp [locals, step, stepEval, Frame.check, certificate.treeSet.code, ArrayTrees.treeSet,
              certificate.emptyCtor, certificate.nodeCtor, certificate.emptyNode, frameState,
              Tree.encode, Frame.read, Frame.readOperands, Frame.transfer, evalOp, selectCase,
              Primitive.eval, Primitive.arity, N, valid, nextValid, indexValid, restValid, notLeafB,
              goLeft, pow_half, smallNat, localRoom, bind, Except.bind, pure, Except.pure]
          rfl
        have recursive := ih right (index - 2 ^ height) nextBound nextValid
          (continuation.push (.resume { function := links.treeSet, block := 23, locals }))
          (by simp; omega)
        have called := ArrayTrees.call_returns limits program
          { function := links.treeSet, block := 22, locals } links.treeSet
          [.local 7, .local 5, .local 9, .local 3] #[right.encode links.layout, .scalar (.nat (2 ^ height)), .scalar (.nat (index - 2 ^ height)), value] 23 ((right.set height (index - 2 ^ height) value).encode links.layout)
          { function := links.treeSet, block := 23, locals := locals ++ #[(right.set height (index - 2 ^ height) value).encode links.layout] }
          continuation (by omega)
          (by simp [locals, Frame.check, certificate.treeSet.code, ArrayTrees.treeSet, Tree.encode, N, localRoom,
            bind, Except.bind, pure, Except.pure])
          (by rfl)
          (by simp [Frame.check, certificate.treeSet.code, ArrayTrees.treeSet, enter, N, localRoom, bind, Except.bind,
            pure, Except.pure])
          (by simp [locals, Frame.check, certificate.treeSet.code, ArrayTrees.treeSet, Tree.encode, Frame.transfer, N,
            localRoom, bind, Except.bind, pure, Except.pure]) recursive
        have finished : Reaches limits program
            (frameState links.treeSet 23 (locals ++ #[(right.set height (index - 2 ^ height) value).encode links.layout]) continuation)
            (returned (((Tree.node left right).set (height + 1) index value).encode links.layout) continuation) := by
          apply reaches_of_chunk (fuel := 2) (count := 0)
          iterate 2
            rw [runChunk]
            simp [locals, step, stepEval, Frame.check, certificate.treeSet.code, ArrayTrees.treeSet,
              certificate.nodeCtor, frameState, returned, Tree.encode, Tree.set, Tree.left, Tree.right,
              Frame.read, Frame.readOperands, Frame.transfer, evalOp, N, goLeft, localRoom, bind,
              Except.bind, pure, Except.pure]
          rfl
        exact beforeCall.trans (called.trans finished)

end Compilatrix.Ixby.Runtime.ArrayTrees.Certificate
