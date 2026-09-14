import Compilatrix.Ixby.Runtime.ArrayTreeCall

/-! Lookup follows a live slot through the actual emitted tree helper. All
recursive edges are tail calls and preserve every surrounding continuation. -/

namespace Compilatrix.Ixby.Runtime.ArrayTrees.Certificate

open Ix.Ixby Execution Representation ScalarFunction Conversion

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

variable {program : Program} {links : Links} (certificate : Certificate program links)
  (limits : Limits)

include certificate

theorem treeGet_returns (room : 8 ≤ limits.locals) (capacity : 2 ≤ limits.natBits)
    (height : Nat) (tree : Tree height) (index : Nat) (value : Value)
    (bounded : index < 2 ^ height) (found : tree.get index = some value)
    (valid : (Scalar.nat (2 ^ height)).validate limits = .ok ())
    (continuation : Array Continuation) :
    Reaches limits program
      (frameState links.treeGet 0
        #[tree.encode links.layout, .scalar (.nat (2 ^ height)), .scalar (.nat index)] continuation)
      (returned value continuation) := by
  have localRoom : ∀ k, k ≤ 8 → ¬limits.locals < k := by omega
  have smallNat (k : Nat) (small : k ≤ 2) : (Scalar.nat k).validate limits = .ok () :=
    validate_nat_of_bits (by omega : k < 2 ^ 2) capacity
  induction height generalizing index with
  | zero =>
    cases tree with
    | empty => simp [Tree.get] at found
    | leaf leaf =>
      have same : leaf = value := by simpa [Tree.get] using found
      subst leaf
      apply reaches_of_chunk (fuel := 4) (count := 0)
      iterate 4
        rw [runChunk]
        simp [step, stepEval, Frame.check, certificate.treeGet.code, ArrayTrees.treeGet,
          frameState, returned, Tree.encode, Frame.read, Frame.readOperands, Frame.transfer,
          evalOp, Primitive.eval, Primitive.arity, N, smallNat, localRoom,
          bind, Except.bind, pure, Except.pure]
      rfl
  | succ height ih =>
    have positive := pow_positive height
    have doubled : 2 ^ (height + 1) = 2 ^ height + 2 ^ height := by rw [Nat.pow_succ]; omega
    have notLeaf : ¬2 ^ (height + 1) = 1 := by omega
    have nextValid := validate_nat_mono (show 2 ^ height ≤ 2 ^ (height + 1) by omega) valid
    have indexValid := validate_nat_mono (by omega : index ≤ 2 ^ (height + 1)) valid
    have restValid := validate_nat_mono (Nat.sub_le index (2 ^ height)) indexValid
    cases tree with
    | empty => simp [Tree.get] at found
    | node left right =>
      by_cases goLeft : index < 2 ^ height
      · have recursive := ih left index goLeft (by simpa [Tree.get, goLeft] using found) nextValid
        apply Reaches.trans (b := frameState links.treeGet 0
          #[left.encode links.layout, .scalar (.nat (2 ^ height)), .scalar (.nat index)] continuation) ?_ recursive
        apply reaches_of_chunk (fuel := 7) (count := 0)
        iterate 7
          rw [runChunk]
          simp [step, stepEval, Frame.check, certificate.treeGet.code, ArrayTrees.treeGet,
            frameState, Tree.encode, Frame.read, Frame.readOperands, Frame.transfer, enter,
            evalOp, Primitive.eval, Primitive.arity, N, valid, nextValid, indexValid, notLeaf,
            goLeft, pow_half, smallNat, localRoom, bind, Except.bind, pure, Except.pure]
        rfl
      · have restBound : index - 2 ^ height < 2 ^ height := by omega
        have recursive := ih right (index - 2 ^ height) restBound
          (by simpa [Tree.get, goLeft] using found) nextValid
        apply Reaches.trans (b := frameState links.treeGet 0
          #[right.encode links.layout, .scalar (.nat (2 ^ height)), .scalar (.nat (index - 2 ^ height))]
            continuation) ?_ recursive
        apply reaches_of_chunk (fuel := 8) (count := 0)
        iterate 8
          rw [runChunk]
          simp [step, stepEval, Frame.check, certificate.treeGet.code, ArrayTrees.treeGet,
            frameState, Tree.encode, Frame.read, Frame.readOperands, Frame.transfer, enter,
            evalOp, Primitive.eval, Primitive.arity, N, valid, nextValid, indexValid, restValid,
            notLeaf, goLeft, pow_half, smallNat, localRoom, bind, Except.bind, pure, Except.pure]
        rfl

end Compilatrix.Ixby.Runtime.ArrayTrees.Certificate
