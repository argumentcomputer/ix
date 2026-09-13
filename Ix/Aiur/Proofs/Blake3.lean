/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Blake3
import Ix.Aiur.Proofs.Challenger
import Ix.Aiur.Proofs.Transcript

namespace Aiur.NativeAIR.Blake3

theorem schedules_permute : ∀ index : Fin 7,
    schedules[index].toList.Perm (List.finRange 16) := by decide

theorem schedules_next : ∀ index : Fin 6,
    schedules[index.val + 1] = Vector.ofFn (fun position : Fin 16 =>
      schedules[index.val][schedules[1][position]]) := by decide

theorem rotateRight_bits (word : UInt32) (count : UInt32)
    (positive : 0 < count.toNat) (bounded : count.toNat < 32) :
    (rotateRight word count).toBitVec = word.toBitVec.rotateRight count.toNat := by
  simp [rotateRight, UInt32.toBitVec_shiftRight, UInt32.toBitVec_shiftLeft,
    BitVec.rotateRight_def, Nat.mod_eq_of_lt bounded]
  congr 2
  omega

theorem bytesWord_value (bytes : Vector UInt8 4) :
    (bytesWord bytes).toNat = Challenger.littleEndian bytes.toList := by
  have bound := Challenger.littleEndian_bound bytes.toList
  simp only [Vector.length_toList] at bound
  exact Nat.mod_eq_of_lt (by simpa using bound)

theorem wordBytes_encoding (word : UInt32) : (wordBytes word).toList = KeyCodec.encodeNat 4 word.toNat := by
  simp [wordBytes, Vector.toList_ofFn, List.ofFn_succ, KeyCodec.encodeNat, Nat.div_div_eq_div_mul]

theorem bytesWord_wordBytes (word : UInt32) : bytesWord (wordBytes word) = word := by
  apply UInt32.toNat_inj.mp
  rw [bytesWord_value, wordBytes_encoding]
  exact Challenger.littleEndian_encode 4 word.toNat (by exact word.toNat_lt)

theorem bytesWord_pack (a b c d : UInt8) : (bytesWord #v[a, b, c, d]).toNat =
    a.toNat + 256 * (b.toNat + 256 * (c.toNat + 256 * d.toNat)) := by
  rw [bytesWord_value]
  simp [Challenger.littleEndian]

theorem wordBytes_pack (a b c d : UInt8) : wordBytes (bytesWord #v[a, b, c, d]) = #v[a, b, c, d] := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  apply Vector.ext
  intro index bounded
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;>
    apply UInt8.toNat_inj.mp <;> simp [wordBytes, bytesWord_pack] <;> omega

theorem wordBytes_bytesWord (bytes : Vector UInt8 4) : wordBytes (bytesWord bytes) = bytes := by
  have value : bytes = #v[bytes[0], bytes[1], bytes[2], bytes[3]] := by
    apply Vector.ext
    intro index bounded
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  conv => lhs; rw [value]
  rw [wordBytes_pack, ← value]

theorem bytesWord_injective {first second : Vector UInt8 4} (equal : bytesWord first = bytesWord second) :
    first = second := by rw [← wordBytes_bytesWord first, equal, wordBytes_bytesWord]

theorem blockWords_byte (input : List UInt8) (word : Fin 16) (byte : Fin 4) :
    ((Vector.ofFn fun byte : Fin 4 => input.toArray[word.val * 4 + byte.val]?.getD 0) : Vector UInt8 4)[byte]
      = input[word.val * 4 + byte.val]?.getD 0 := by simp

theorem blockWords_value (input : List UInt8) (word : Fin 16) :
    (blockWords input)[word].toNat =
      Challenger.littleEndian (List.ofFn fun byte : Fin 4 => input[word.val * 4 + byte.val]?.getD 0) := by
  simpa [blockWords, Vector.toList_ofFn] using bytesWord_value
    (Vector.ofFn fun byte : Fin 4 => input.toArray[word.val * 4 + byte.val]?.getD 0)

theorem cvBytes_value (cv : CV) (index : Fin 32) :
    (cvBytes cv)[index] = (cv[index.val / 4].toNat / 256^(index.val % 4)).toUInt8 := by
  simp [cvBytes, wordBytes]

theorem g_unchanged (state : Block) (a b c d index : Fin 16) (x y : UInt32)
    (ha : a ≠ index) (hb : b ≠ index) (hc : c ≠ index) (hd : d ≠ index) :
    (g state a b c d x y)[index] = state[index] := by
  simp [g, Fin.getElem_fin, Fin.val_inj, ha, hb, hc, hd]

theorem g_values (state : Block) (a b c d : Fin 16) (x y : UInt32)
    (ab : a ≠ b) (ac : a ≠ c) (ad : a ≠ d) (bc : b ≠ c) (bd : b ≠ d) (cd : c ≠ d) :
    let words := mix state[a] state[b] state[c] state[d] x y
    (g state a b c d x y)[a] = words[0] ∧ (g state a b c d x y)[b] = words[1] ∧
    (g state a b c d x y)[c] = words[2] ∧ (g state a b c d x y)[d] = words[3] := by
  simp [g, Fin.getElem_fin, Fin.val_inj,
    Ne.symm ab, Ne.symm ac, Ne.symm ad, Ne.symm bc, Ne.symm bd, Ne.symm cd]

theorem initialWords_counter (cv : CV) (counter : UInt64) (blockLen flags : UInt32) :
    (initialWords cv counter blockLen flags)[12].toNat +
      2^32 * (initialWords cv counter blockLen flags)[13].toNat = counter.toNat := by
  have bounded := counter.toNat_lt
  simp [initialWords, Nat.shiftRight_eq_div_pow]
  omega

theorem parentOutput_values (left right : CV) :
    (parentOutput left right).cv = iv ∧ (parentOutput left right).block = left ++ right ∧
    (parentOutput left right).blockLen = 64 ∧ (parentOutput left right).counter = 0 ∧
    (parentOutput left right).flags = 4 := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem leftLen_bounds {size : Nat} (large : 1024 < size) :
    leftLen size < size ∧ size ≤ 2 * leftLen size := by
  have upper := Nat.lt_log2_self (n := size - 1)
  rw [Nat.pow_succ] at upper
  exact ⟨leftLen_lt large, by unfold leftLen; omega⟩

theorem leftLen_chunks {size : Nat} (large : 1024 < size) :
    ∃ exponent, leftLen size = 1024 * 2^exponent := by
  have exponent : 10 ≤ (size - 1).log2 := (Nat.le_log2 (by omega)).mpr (by omega)
  refine ⟨(size - 1).log2 - 10, ?_⟩
  unfold leftLen
  conv => lhs; rw [show (size - 1).log2 = 10 + ((size - 1).log2 - 10) by omega]
  rw [Nat.pow_add]

theorem leftLen_chunk_multiple {size : Nat} (large : 1024 < size) :
    leftLen size / 1024 * 1024 = leftLen size := by
  obtain ⟨exponent, value⟩ := leftLen_chunks large
  rw [value]
  omega

theorem leftLen_unique {left right exponent : Nat}
    (power : left = 1024 * 2^exponent) (positive : 0 < right) (bounded : right ≤ left) :
    leftLen (left + right) = left := by
  have pow : left = 2^(10 + exponent) := by rw [Nat.pow_add]; exact power
  have nonzero : left + right - 1 ≠ 0 := by
    have := Nat.two_pow_pos (10 + exponent)
    omega
  have log : (left + right - 1).log2 = 10 + exponent :=
    (Nat.log2_eq_iff nonzero).mpr ⟨by omega, by rw [Nat.pow_succ, ← pow]; omega⟩
  rw [leftLen, log, ← pow]

theorem chunkLoop_small (counter : UInt64) (cv : CV) (start : Bool) (input : List UInt8)
    (small : input.length ≤ 64) :
    chunkLoop counter cv start input =
      ⟨cv, blockWords input, input.length.toUInt32, counter, (if start then 1 else 0) ||| 2⟩ := by
  rw [chunkLoop, dif_pos small]

theorem chunkLoop_step (counter : UInt64) (cv : CV) (start : Bool) (input : List UInt8)
    (large : 64 < input.length) :
    chunkLoop counter cv start input =
      chunkLoop counter (compress cv (blockWords (input.take 64)) counter 64 (if start then 1 else 0))
        false (input.drop 64) := by
  rw [chunkLoop, dif_neg (by omega)]

theorem chunkLoop_counter (counter : UInt64) (cv : CV) (start : Bool) (input : List UInt8) :
    (chunkLoop counter cv start input).counter = counter := by
  rw [chunkLoop]
  split
  · rfl
  · exact chunkLoop_counter _ _ _ _
termination_by input.length
decreasing_by simp only [List.length_drop]; omega

theorem chunkOutput_counter (counter : UInt64) (input : List UInt8) :
    (chunkOutput counter input).counter = counter := chunkLoop_counter _ _ _ _

/-- Every non-final block has exactly 64 bytes. The final block may be full;
only the empty input has an empty final block. -/
inductive ChunkReads (counter : UInt64) : CV → Bool → List UInt8 → Output → Prop where
  | last (cv : CV) (start : Bool) (input : List UInt8) (small : input.length ≤ 64) :
      ChunkReads counter cv start input
        ⟨cv, blockWords input, input.length.toUInt32, counter, (if start then 1 else 0) ||| 2⟩
  | step (cv : CV) (start : Bool) (input : List UInt8) (output : Output)
      (large : 64 < input.length)
      (rest : ChunkReads counter
        (compress cv (blockWords (input.take 64)) counter 64 (if start then 1 else 0))
        false (input.drop 64) output) : ChunkReads counter cv start input output

theorem chunkLoop_reads (counter : UInt64) (cv : CV) (start : Bool) (input : List UInt8) :
    ChunkReads counter cv start input (chunkLoop counter cv start input) := by
  by_cases small : input.length ≤ 64
  · rw [chunkLoop_small _ _ _ _ small]
    exact .last _ _ _ small
  · rw [chunkLoop_step _ _ _ _ (by omega)]
    exact .step _ _ _ _ (by omega) (chunkLoop_reads _ _ _ _)
termination_by input.length
decreasing_by simp only [List.length_drop]; omega

theorem ChunkReads.complete {counter : UInt64} {cv : CV} {start : Bool} {input : List UInt8} {output : Output}
    (reads : ChunkReads counter cv start input output) : chunkLoop counter cv start input = output := by
  induction reads with
  | last cv start input small => exact chunkLoop_small _ _ _ _ small
  | step cv start input output large rest ih => rw [chunkLoop_step _ _ _ _ large, ih]

theorem chunkLoop_iff (counter : UInt64) (cv : CV) (start : Bool) (input : List UInt8) (output : Output) :
    chunkLoop counter cv start input = output ↔ ChunkReads counter cv start input output :=
  ⟨fun equal => equal ▸ chunkLoop_reads _ _ _ _, ChunkReads.complete⟩

theorem ChunkReads.framing {counter : UInt64} {cv : CV} {start : Bool} {input : List UInt8} {output : Output}
    (reads : ChunkReads counter cv start input output) :
    ∃ count, let remaining := input.drop (64 * count)
      remaining.length ≤ 64 ∧ (input ≠ [] → 0 < remaining.length) ∧
      output.block = blockWords remaining ∧ output.blockLen.toNat = remaining.length ∧
      output.counter = counter ∧ output.flags = (if start && count == 0 then 1 else 0) ||| 2 := by
  induction reads with
  | last cv start input small =>
    refine ⟨0, ?_⟩
    simp only [Nat.mul_zero, List.drop_zero, Nat.reduceBEq, Bool.and_true]
    refine ⟨small, ?_, by trivial, ?_, by trivial, by trivial⟩
    · intro nonempty; exact List.length_pos_iff.mpr nonempty
    · exact Nat.mod_eq_of_lt (by omega)
  | step cv start input output large rest ih =>
    obtain ⟨count, bound, positive, block, length, counterEq, flags⟩ := ih
    refine ⟨count + 1, ?_⟩
    simp only [List.drop_drop] at bound positive block length
    have advance : 64 * (count + 1) = 64 + 64 * count := by omega
    rw [advance]
    refine ⟨bound, fun _ => positive (by simp only [← List.length_pos_iff, List.length_drop]; omega),
      block, length, counterEq, ?_⟩
    simpa using flags

theorem chunkOutput_framing (counter : UInt64) (input : List UInt8) (bounded : input.length ≤ 1024) :
    ∃ count, count < 16 ∧
      let remaining := input.drop (64 * count)
      remaining.length ≤ 64 ∧ (input ≠ [] → 0 < remaining.length) ∧
      (chunkOutput counter input).block = blockWords remaining ∧
      (chunkOutput counter input).blockLen.toNat = remaining.length ∧
      (chunkOutput counter input).counter = counter ∧
      (chunkOutput counter input).flags = (if count = 0 then 3 else 2) := by
  obtain ⟨count, bound, positive, block, length, counterEq, flags⟩ := (chunkLoop_reads counter iv true input).framing
  have countBound : count < 16 := by
    by_cases nonempty : input = []
    · subst input
      have : count = 0 := by
        have flagEmpty : (chunkLoop counter iv true []).flags = 3 := by rw [chunkLoop_small _ _ _ _ (by decide)]; rfl
        rw [flagEmpty] at flags
        by_cases zero : count = 0
        · exact zero
        · simp [zero] at flags
      omega
    · have := positive nonempty
      simp only [List.length_drop] at this
      omega
  refine ⟨count, countBound, bound, positive, block, length, counterEq, ?_⟩
  change (chunkLoop counter iv true input).flags = _
  rw [flags]
  by_cases zero : count = 0 <;> simp [zero] <;> decide

theorem subtree_small (counter : Nat) (input : List UInt8) (small : input.length ≤ 1024) :
    subtree counter input = chunkOutput counter.toUInt64 input := by
  rw [subtree, dif_pos small]

theorem subtree_step (counter : Nat) (input : List UInt8) (large : 1024 < input.length) :
    subtree counter input = parentOutput
      (subtree counter (input.take (leftLen input.length))).chainingValue
      (subtree (counter + leftLen input.length / 1024) (input.drop (leftLen input.length))).chainingValue := by
  rw [subtree, dif_neg (by omega)]

theorem subtree_root_counter (input : List UInt8) : (subtree 0 input).counter = 0 := by
  by_cases small : input.length ≤ 1024
  · rw [subtree_small _ _ small, chunkOutput_counter]; rfl
  · rw [subtree_step _ _ (by omega)]; rfl

/-- Canonical BLAKE3 trees, specified by full power-of-two left subtrees
and nonempty right subtrees no larger than their siblings. -/
inductive TreeHash : Nat → List UInt8 → Output → Prop where
  | chunk (counter : Nat) (input : List UInt8) (output : Output) (small : input.length ≤ 1024)
      (blocks : ChunkReads counter.toUInt64 iv true input output) : TreeHash counter input output
  | parent (counter exponent : Nat) (left right : List UInt8) (leftOutput rightOutput : Output)
      (full : left.length = 1024 * 2^exponent) (nonempty : 0 < right.length) (bounded : right.length ≤ left.length)
      (leftHash : TreeHash counter left leftOutput)
      (rightHash : TreeHash (counter + left.length / 1024) right rightOutput) :
      TreeHash counter (left ++ right) (parentOutput leftOutput.chainingValue rightOutput.chainingValue)

theorem subtree_tree (counter : Nat) (input : List UInt8) : TreeHash counter input (subtree counter input) := by
  by_cases small : input.length ≤ 1024
  · rw [subtree_small _ _ small]
    exact .chunk _ _ _ small (chunkLoop_reads _ _ _ _)
  · have large : 1024 < input.length := by omega
    have splitBound := leftLen_bounds large
    obtain ⟨exponent, full⟩ := leftLen_chunks large
    have takeLength : (input.take (leftLen input.length)).length = leftLen input.length := by
      simp only [List.length_take]; omega
    have result := TreeHash.parent counter exponent (input.take (leftLen input.length))
      (input.drop (leftLen input.length)) _ _ (by rw [takeLength]; exact full)
      (by simp only [List.length_drop]; omega)
      (by simp only [List.length_drop, takeLength]; omega)
      (subtree_tree _ _) (subtree_tree _ _)
    rw [List.take_append_drop, takeLength] at result
    rw [subtree_step _ _ large]
    exact result
termination_by input.length
decreasing_by
  · have := leftLen_lt (size := input.length) (by omega)
    simp only [List.length_take]; omega
  · have := leftLen_positive input.length
    simp only [List.length_drop]; omega

theorem TreeHash.complete {counter : Nat} {input : List UInt8} {output : Output}
    (tree : TreeHash counter input output) : subtree counter input = output := by
  induction tree with
  | chunk counter input output small blocks => rw [subtree_small _ _ small]; exact blocks.complete
  | parent counter exponent left right leftOutput rightOutput full nonempty bounded leftHash rightHash ihLeft ihRight =>
    have positive := Nat.two_pow_pos exponent
    have large : 1024 < (left ++ right).length := by simp only [List.length_append]; omega
    have split := leftLen_unique full nonempty bounded
    rw [subtree_step _ _ large, List.length_append, split,
      List.take_left, List.drop_left, ihLeft, ihRight]

theorem subtree_iff (counter : Nat) (input : List UInt8) (output : Output) :
    subtree counter input = output ↔ TreeHash counter input output :=
  ⟨fun equal => equal ▸ subtree_tree _ _, TreeHash.complete⟩

theorem TreeHash.unique {counter : Nat} {input : List UInt8} {first second : Output}
    (one : TreeHash counter input first) (two : TreeHash counter input second) : first = second :=
  one.complete.symm.trans two.complete

theorem native_counter {counter : Nat} {input : List UInt8}
    (span : counter * 1024 + input.length < 2^64) :
    counter < 2^54 ∧ counter.toUInt64.toNat = counter := by
  constructor
  · omega
  · exact Nat.mod_eq_of_lt (by omega)

theorem native_child_spans {counter : Nat} {input : List UInt8}
    (span : counter * 1024 + input.length < 2^64) (large : 1024 < input.length) :
    counter * 1024 + (input.take (leftLen input.length)).length < 2^64 ∧
    (counter + leftLen input.length / 1024) * 1024 + (input.drop (leftLen input.length)).length < 2^64 := by
  have splitBound := leftLen_lt large
  have multiple := leftLen_chunk_multiple large
  simp only [List.length_take, List.length_drop, Nat.add_mul]
  omega

/-- A particular leaf reached by the actual canonical subtree recursion. -/
inductive ChunkAt : Nat → List UInt8 → Nat → List UInt8 → Prop where
  | leaf (counter : Nat) (input : List UInt8) (small : input.length ≤ 1024) :
      ChunkAt counter input counter input
  | left {counter leaf : Nat} {input bytes : List UInt8} (large : 1024 < input.length)
      (path : ChunkAt counter (input.take (leftLen input.length)) leaf bytes) :
      ChunkAt counter input leaf bytes
  | right {counter leaf : Nat} {input bytes : List UInt8} (large : 1024 < input.length)
      (path : ChunkAt (counter + leftLen input.length / 1024) (input.drop (leftLen input.length)) leaf bytes) :
      ChunkAt counter input leaf bytes

theorem ChunkAt.native {counter leaf : Nat} {input bytes : List UInt8}
    (path : ChunkAt counter input leaf bytes) (span : counter * 1024 + input.length < 2^64) :
    bytes.length ≤ 1024 ∧ leaf < 2^54 ∧ leaf.toUInt64.toNat = leaf := by
  induction path with
  | leaf counter input small => exact ⟨small, native_counter span⟩
  | left large path ih => exact ih (native_child_spans span large).1
  | right large path ih => exact ih (native_child_spans span large).2

theorem digest_native_counters {input bytes : List UInt8} (native : NativeInput input) {leaf : Nat}
    (path : ChunkAt 0 input leaf bytes) : bytes.length ≤ 1024 ∧ leaf < 2^54 ∧ leaf.toUInt64.toNat = leaf :=
  path.native (by simpa only [NativeInput, Nat.zero_mul, Nat.zero_add] using native)

theorem digest_tree (input : List UInt8) :
    ∃ output, TreeHash 0 input output ∧ output.counter = 0 ∧ digest input = output.rootHash :=
  ⟨subtree 0 input, subtree_tree _ _, subtree_root_counter _, rfl⟩

theorem replay_iff (fuel : Nat) (key : KeyCodec.Key) (proof : ProofCodec.Data)
    (claims : List (List G)) (result : Transcript.Replay) :
    replay fuel key proof claims = some result ↔ result.Reads hash fuel key proof claims :=
  Transcript.replay_iff _ _ _ _ _ _

theorem replay_unique {fuel more : Nat} {key : KeyCodec.Key} {proof : ProofCodec.Data}
    {claims : List (List G)} {first second : Transcript.Replay}
    (one : replay fuel key proof claims = some first) (two : replay more key proof claims = some second) :
    first = second := Transcript.replay_unique one two

theorem verifyArithmetic_iff (fuel : Nat) (key : KeyCodec.Key) (proof : ProofCodec.Data)
    (claims : List (List G)) (rows : List ProofShape.Row) (result : Transcript.Replay) :
    verifyArithmetic fuel key proof claims rows = some result ↔
      replay fuel key proof claims = some result ∧
        VerifierArithmetic.verify result.challenges claims rows = some true :=
  Transcript.verifyArithmetic_iff _ _ _ _ _ _ _

theorem hash_bytes (input : List UInt8) : List.ofFn (hash input) = (digest input).toList := by
  change List.ofFn (fun index : Fin 32 => (digest input)[index]) = _
  exact Vector.toList_ofFn.symm.trans
    (congrArg Vector.toList (Vector.ofFn_getElem (xs := digest input)))

end Aiur.NativeAIR.Blake3

namespace Aiur.BoundVerifier
open NativeAIR

/-- Concrete Blake3 supplies all transcript challenges and the continuing
PCS state. Authentication and cryptographic soundness remain separate. -/
theorem CompiledBackend.blake3_transcript_row {selection : Selection} (backend : CompiledBackend selection)
    {bytes : ByteArray} (checked : CheckedProof backend.keyData bytes)
    {fuel : Nat} {claims : List (List G)} {result : Transcript.Replay}
    (accepted : Blake3.verifyArithmetic fuel backend.keyData checked.data claims checked.rows = some result)
    {position : Nat} {row : ProofShape.Row} (present : checked.rows[position]? = some row) :
    result.Reads Blake3.hash fuel backend.keyData checked.data claims ∧
      row.Sourced backend.keyData checked.data row.circuitIndex position ∧ row.Fits backend.keyData.parameters ∧
      ∃ initial before evaluation,
        VerifierArithmetic.initialAccumulator result.challenges claims = some initial ∧
        (initial :: checked.rows.map (·.accumulator))[position]? = some before ∧
        VerifierArithmetic.evaluate result.challenges row before = some evaluation ∧
        Quotient.composition result.challenges.alpha evaluation.constraints =
          Domain.vanishing evaluation.domain result.challenges.zeta * evaluation.quotientValue :=
  backend.transcript_row checked accepted present

end Aiur.BoundVerifier
