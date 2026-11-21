/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

module
public import Blake3.Pure

@[expose] public section

/-! The canonical tree, built level by level.

`Blake3.Pure.subtree` splits an input at the largest power of two strictly below its length.
Streaming implementations build the same tree bottom-up: they compute the outputs of the
1024-byte chunks from left to right (`chunkOutputs`), then pair adjacent chaining values level by
level, carrying an odd last one up unchanged (`pairOutputs`), until one output remains
(`mergeLevels`). This module proves that the two agree (`mergeLevels_chunkOutputs`,
`digest_eq_mergeLevels`), and states the level step on chaining values alone
(`pairChainingValues`), the form an implementation that keeps only chaining values uses.

The proof splits a list of `2^k + r` outputs (`0 < r ≤ 2^k`) at `2^k`: pairing a list whose left
part has even length pairs the two parts separately (`pairOutputs_append`), so the level-wise
merge of the whole is the parent of the merges of the parts (`mergeLevels_append`). The chunks of
an input split the same way at the canonical split, a multiple of 1024 (`chunkOutputs_append`).
-/

namespace Blake3.Pure

/-! ### Unfolding `Blake3.Pure`

`Blake3/Pure/Proofs.lean` states these too (`subtree_small`, `subtree_step`, `leftLen_chunks`,
`leftLen_bounds`, `chunkLoop_small`, `chunkLoop_step`). They are restated here, with the same
proofs, because that module uses `dif_pos` and `dif_neg`, deprecated in Lean v4.34.1, so it does not
build where warnings are errors. -/

theorem subtree_of_le (counter : Nat) (input : List UInt8) (small : input.length ≤ 1024) :
    subtree counter input = chunkOutput counter.toUInt64 input := by
  rw [subtree, dite_eq_left small]

theorem subtree_of_gt (counter : Nat) (input : List UInt8) (large : 1024 < input.length) :
    subtree counter input = parentOutput
      (subtree counter (input.take (leftLen input.length))).chainingValue
      (subtree (counter + leftLen input.length / 1024)
        (input.drop (leftLen input.length))).chainingValue := by
  rw [subtree, dite_eq_right (by omega)]

theorem leftLen_eq_pow {size : Nat} (large : 1024 < size) :
    ∃ exponent, leftLen size = 1024 * 2 ^ exponent := by
  have exponent : 10 ≤ (size - 1).log2 := (Nat.le_log2 (by omega)).mpr (by omega)
  refine ⟨(size - 1).log2 - 10, ?_⟩
  unfold leftLen
  conv => lhs; rw [show (size - 1).log2 = 10 + ((size - 1).log2 - 10) by omega]
  rw [Nat.pow_add]

theorem leftLen_half {size : Nat} (large : 1024 < size) :
    leftLen size < size ∧ size ≤ 2 * leftLen size := by
  have upper := Nat.lt_log2_self (n := size - 1)
  rw [Nat.pow_succ] at upper
  exact ⟨leftLen_lt large, by unfold leftLen; omega⟩

theorem chunkLoop_of_le (counter : UInt64) (cv : CV) (start : Bool) (input : List UInt8)
    (small : input.length ≤ 64) :
    chunkLoop counter cv start input =
      ⟨cv, blockWords input, input.length.toUInt32, counter, (if start then 1 else 0) ||| 2⟩ := by
  rw [chunkLoop, dite_eq_left small]

theorem chunkLoop_of_gt (counter : UInt64) (cv : CV) (start : Bool) (input : List UInt8)
    (large : 64 < input.length) :
    chunkLoop counter cv start input =
      chunkLoop counter (compress cv (blockWords (input.take 64)) counter 64 (if start then 1 else 0))
        false (input.drop 64) := by
  rw [chunkLoop, dite_eq_right (by omega)]

/-! ### Chunks -/

/-- The outputs of an input's chunks, numbered from `counter`: 1024 bytes each, the last one 1 to
1024 bytes (the empty input has one empty chunk). -/
def chunkOutputs (counter : Nat) (input : List UInt8) : List Output :=
  if _h : input.length ≤ 1024 then [chunkOutput counter.toUInt64 input]
  else
    chunkOutput counter.toUInt64 (input.take 1024) :: chunkOutputs (counter + 1) (input.drop 1024)
termination_by input.length
decreasing_by simp only [List.length_drop]; omega

theorem chunkOutputs_small (counter : Nat) (input : List UInt8) (small : input.length ≤ 1024) :
    chunkOutputs counter input = [chunkOutput counter.toUInt64 input] := by
  rw [chunkOutputs, dite_eq_left small]

theorem chunkOutputs_large (counter : Nat) (input : List UInt8) (large : 1024 < input.length) :
    chunkOutputs counter input =
      chunkOutput counter.toUInt64 (input.take 1024) ::
        chunkOutputs (counter + 1) (input.drop 1024) := by
  rw [chunkOutputs, dite_eq_right (by omega)]

/-- An input has one chunk per started 1024 bytes, and at least one. -/
theorem chunkOutputs_length (counter : Nat) (input : List UInt8) :
    (chunkOutputs counter input).length =
      if input.length ≤ 1024 then 1 else (input.length + 1023) / 1024 := by
  by_cases small : input.length ≤ 1024
  · rw [chunkOutputs_small counter input small, ite_eq_left small, List.length_singleton]
  · rw [chunkOutputs_large counter input (by omega), ite_eq_right small, List.length_cons,
      chunkOutputs_length (counter + 1) (input.drop 1024), List.length_drop]
    split <;> omega
termination_by input.length
decreasing_by simp only [List.length_drop]; omega

/-- Chunks after a whole number of full chunks continue the numbering. -/
theorem chunkOutputs_append (counter count : Nat) (left right : List UInt8)
    (full : left.length = 1024 * count) (positive : 0 < count) (nonempty : 0 < right.length) :
    chunkOutputs counter (left ++ right) =
      chunkOutputs counter left ++ chunkOutputs (counter + count) right := by
  have long : 1024 < (left ++ right).length := by rw [List.length_append]; omega
  rw [chunkOutputs_large counter (left ++ right) long]
  by_cases one : count = 1
  · subst one
    rw [chunkOutputs_small counter left (by omega), List.take_left' (by omega),
      List.drop_left' (by omega), List.singleton_append]
  · rw [chunkOutputs_large counter left (by omega), List.take_append_of_le_length (by omega),
      List.drop_append_of_le_length (by omega),
      chunkOutputs_append (counter + 1) (count - 1) (left.drop 1024) right
        (by rw [List.length_drop]; omega) (by omega) nonempty,
      List.cons_append, show counter + 1 + (count - 1) = counter + count by omega]
termination_by left.length
decreasing_by rw [List.length_drop]; omega

/-! ### Levels -/

/-- One level of the tree: adjacent outputs are paired into parents, from the left; an odd last
output is carried up unchanged. -/
def pairOutputs : List Output → List Output
  | [] => []
  | [output] => [output]
  | left :: right :: rest => parentOutput left.chainingValue right.chainingValue :: pairOutputs rest

theorem pairOutputs_length : (outputs : List Output) →
    (pairOutputs outputs).length = (outputs.length + 1) / 2
  | [] => by simp [pairOutputs]
  | [_] => by simp [pairOutputs]
  | _ :: _ :: rest => by
    simp only [pairOutputs, List.length_cons, pairOutputs_length rest]
    omega

theorem pairOutputs_length_lt {outputs : List Output} (two : 2 ≤ outputs.length) :
    (pairOutputs outputs).length < outputs.length := by
  rw [pairOutputs_length]; omega

/-- Pairing a list whose left part has even length pairs the two parts separately. -/
theorem pairOutputs_append : (left right : List Output) → left.length % 2 = 0 →
    pairOutputs (left ++ right) = pairOutputs left ++ pairOutputs right
  | [], _, _ => rfl
  | [_], _, even => by simp at even
  | _ :: _ :: rest, right, even => by
    have restEven : rest.length % 2 = 0 := by simp only [List.length_cons] at even; omega
    simp only [List.cons_append, pairOutputs, pairOutputs_append rest right restEven]

/-- The tree over a list of outputs, built level by level (`pairOutputs`) until one output remains.
The empty list, which no input produces, gives the empty input's output. -/
def mergeLevels (outputs : List Output) : Output :=
  match outputs with
  | [] => chunkOutput 0 []
  | [output] => output
  | left :: right :: rest => mergeLevels (pairOutputs (left :: right :: rest))
termination_by outputs.length
decreasing_by exact pairOutputs_length_lt (by rw [List.length_cons, List.length_cons]; omega)

theorem mergeLevels_singleton (output : Output) : mergeLevels [output] = output := by
  rw [mergeLevels]

theorem mergeLevels_step (left right : Output) (rest : List Output) :
    mergeLevels (left :: right :: rest) = mergeLevels (pairOutputs (left :: right :: rest)) := by
  conv => lhs; rw [mergeLevels]

theorem mergeLevels_pairOutputs : (outputs : List Output) →
    mergeLevels (pairOutputs outputs) = mergeLevels outputs
  | [] => rfl
  | [_] => rfl
  | left :: right :: rest => (mergeLevels_step left right rest).symm

/-- Merging `2^exponent` outputs followed by at least one and at most `2^exponent` more gives the
parent of the two parts' merges: level by level, the split stays at a power of two. -/
theorem mergeLevels_append (exponent : Nat) : (left right : List Output) →
    left.length = 2 ^ exponent → 0 < right.length → right.length ≤ 2 ^ exponent →
    mergeLevels (left ++ right) =
      parentOutput (mergeLevels left).chainingValue (mergeLevels right).chainingValue := by
  induction exponent with
  | zero =>
    intro left right leftLength rightPositive rightLength
    rw [Nat.pow_zero] at leftLength rightLength
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp leftLength
    obtain ⟨y, rfl⟩ := List.length_eq_one_iff.mp (by omega : right.length = 1)
    rw [List.singleton_append, mergeLevels_step,
      show pairOutputs [x, y] = [parentOutput x.chainingValue y.chainingValue] from rfl,
      mergeLevels_singleton, mergeLevels_singleton, mergeLevels_singleton]
  | succ exponent ih =>
    intro left right leftLength rightPositive rightLength
    have double : 2 ^ (exponent + 1) = 2 * 2 ^ exponent := by rw [Nat.pow_succ, Nat.mul_comm]
    have leftPairs := pairOutputs_length left
    have rightPairs := pairOutputs_length right
    rw [← mergeLevels_pairOutputs (left ++ right),
      pairOutputs_append left right (by omega),
      ih (pairOutputs left) (pairOutputs right) (by omega) (by omega) (by omega),
      mergeLevels_pairOutputs, mergeLevels_pairOutputs]

/-! ### The tree -/

/-- The canonical tree (`subtree`) is the level-by-level merge of the chunk outputs. -/
theorem mergeLevels_chunkOutputs (counter : Nat) (input : List UInt8) :
    mergeLevels (chunkOutputs counter input) = subtree counter input := by
  by_cases small : input.length ≤ 1024
  · rw [chunkOutputs_small counter input small, mergeLevels_singleton,
      subtree_of_le counter input small]
  · have large : 1024 < input.length := by omega
    obtain ⟨exponent, full⟩ := leftLen_eq_pow large
    obtain ⟨below, atMost⟩ := leftLen_half large
    have positive := Nat.two_pow_pos exponent
    have takeLength : (input.take (leftLen input.length)).length = leftLen input.length := by
      rw [List.length_take]; omega
    have dropLength : (input.drop (leftLen input.length)).length =
        input.length - leftLen input.length := List.length_drop
    have halves := chunkOutputs_append counter (2 ^ exponent) (input.take (leftLen input.length))
      (input.drop (leftLen input.length)) (takeLength.trans full) positive
      (by rw [dropLength]; omega)
    rw [List.take_append_drop] at halves
    rw [subtree_of_gt counter input large,
      show leftLen input.length / 1024 = 2 ^ exponent by omega, halves,
      mergeLevels_append exponent _ _
        (by rw [chunkOutputs_length, takeLength]; split <;> omega)
        (by rw [chunkOutputs_length]; split <;> omega)
        (by rw [chunkOutputs_length, dropLength]; split <;> omega),
      mergeLevels_chunkOutputs counter (input.take (leftLen input.length)),
      mergeLevels_chunkOutputs (counter + 2 ^ exponent) (input.drop (leftLen input.length))]
termination_by input.length
decreasing_by
  · have := leftLen_lt (size := input.length) (by omega)
    simp only [List.length_take]; omega
  · have := leftLen_positive input.length
    simp only [List.length_drop]; omega

/-- BLAKE3 is the root of the level-by-level merge of the chunk outputs. -/
theorem digest_eq_mergeLevels (input : List UInt8) :
    digest input = (mergeLevels (chunkOutputs 0 input)).rootHash := by
  show (subtree 0 input).rootHash = _
  rw [mergeLevels_chunkOutputs]

/-! ### Chaining values -/

/-- `pairOutputs` on chaining values alone: what an implementation that keeps only the chaining
values of a level computes. -/
def pairChainingValues : List CV → List CV
  | [] => []
  | [cv] => [cv]
  | left :: right :: rest => (parentOutput left right).chainingValue :: pairChainingValues rest

theorem pairOutputs_chainingValues : (outputs : List Output) →
    (pairOutputs outputs).map Output.chainingValue =
      pairChainingValues (outputs.map Output.chainingValue)
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: rest => by
    simp only [pairOutputs, List.map_cons, pairChainingValues, pairOutputs_chainingValues rest]

end Blake3.Pure
