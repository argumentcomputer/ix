import Aiur.Library.Blake3.Correctness
import Aiur.Library.Blake3.PureTree

/-! The model of `Blake3::hash` (`Aiur.Library.Blake3`), proved against `Blake3.Pure.digest`.

`Blake3::hash` reads its input a block at a time while 64 bytes are left (`take_block`,
`hash_blocks`), hands the last 0 to 63 bytes to the byte loop (`compress_chunks`, `finish`) in the
same chunk state, and merges the chunk chaining values level by level (`compress_layer`). This
module models those functions in Lean (`hashBlocks`, `compressChunks`, `finish`; `compressLayer` and
`nextLayer` are in `Correctness`) and proves that the model of `hash` computes BLAKE3
(`hash_model_spec`):
* within a chunk, the model's blocks are `Blake3.Pure.chunkLoop`'s (`hashBlocks_last`,
  `hashBlocks_chunk`), so the layer it builds holds the chunk chaining values
  (`hashBlocks_chunks`);
* `compressLayer` of those is the root of `Blake3.Pure.mergeLevels` (`compress_layer_spec`), which
  is `Blake3.Pure.digest` (`Blake3.Pure.digest_eq_mergeLevels`, in `PureTree`).

As in `Correctness`, the models are written by hand after the Aiur source; no theorem here
evaluates that source. A layer (`Blake3::Layer`, a stack) is modeled as a list whose head is the
bottom of the stack: `LayerNode::Push(layer, cv)` is `layer ++ [cv]`. A `Field` that holds a block
or byte count is modeled as a `Nat`; the flags `start + 2 * end + 8 * root` as `blockFlags`.
-/

open Blake3.Pure

namespace Aiur.Library.Blake3

/-! ### The model -/

/-- The flags `CHUNK_START * start + CHUNK_END * end + ROOT * root` (1, 2, 8) that `hash_blocks`,
`compress_block` and `finish` pass to `compress_init`. -/
def blockFlags (start finish root : Bool) : UInt32 :=
  (if start then 1 else 0) + (if finish then 2 else 0) + (if root then 8 else 0)

theorem blockFlags_step (start : Bool) : blockFlags start false false = if start then 1 else 0 := by
  cases start <;> decide

theorem blockFlags_end (start : Bool) :
    blockFlags start true false = (if start then 1 else 0) ||| 2 := by
  cases start <;> decide

theorem blockFlags_root (start : Bool) :
    blockFlags start true true = ((if start then 1 else 0) ||| 2) ||| 8 := by
  cases start <;> decide

/-- The empty block `[UInt32::ZERO; 16]` that `finish` compresses for the empty input. -/
theorem blockWords_nil : blockWords [] = Vector.replicate 16 0 := by
  decide

/-- Lean model of `Blake3::finish(byte_acc, block_index, chunk_index, chunk_count, block_digest,
layer)`, the end of the byte loop: `byte_acc` holds the last block's `block_index` bytes, reversed
(`bytes_to_block(pad_block(byte_acc, 64 - block_index))` is `blockWords` of them in order:
`pad_block_spec`, `bytes_to_block_spec`), and `chunk_index` counts the chunk's bytes. -/
def finish (byteAcc : List UInt8) (blockIndex chunkIndex : Nat) (chunkCount : UInt64)
    (blockDigest : CV) (layer : List CV) : List CV :=
  if blockIndex = 0 then
    if chunkIndex = 0 then
      if chunkCount = 0 then
        layer ++ [compress blockDigest (blockWords []) chunkCount 0 (blockFlags true true true)]
      else layer
    else layer ++ [blockDigest]
  else
    layer ++ [compress blockDigest (blockWords byteAcc.reverse) chunkCount blockIndex.toUInt32
      (blockFlags (decide (chunkIndex - blockIndex = 0)) true (decide (chunkCount = 0)))]

/-- Lean model of `Blake3::compress_chunks(input, byte_acc, block_index, chunk_index, chunk_count,
block_digest, layer)`, the byte loop, with `Blake3::compress_block` (called at a block's 64th byte)
inlined. `hash` only calls it on fewer than 64 bytes (`compressChunks_tail`). -/
def compressChunks : (input byteAcc : List UInt8) → (blockIndex chunkIndex : Nat) →
    (chunkCount : UInt64) → (blockDigest : CV) → (layer : List CV) → List CV
  | [], byteAcc, blockIndex, chunkIndex, chunkCount, blockDigest, layer =>
    finish byteAcc blockIndex chunkIndex chunkCount blockDigest layer
  | head :: input, byteAcc, blockIndex, chunkIndex, chunkCount, blockDigest, layer =>
    if blockIndex = 63 then
      if chunkIndex = 1023 then
        compressChunks input [] 0 0 (chunkCount + 1) iv
          (layer ++ [compress blockDigest (blockWords (head :: byteAcc).reverse) chunkCount 64
            (blockFlags false true (input.isEmpty && decide (chunkCount = 0)))])
      else
        compressChunks input [] 0 (chunkIndex + 1) chunkCount
          (compress blockDigest (blockWords (head :: byteAcc).reverse) chunkCount 64
            (blockFlags (decide (chunkIndex = 63)) input.isEmpty
              (input.isEmpty && decide (chunkCount = 0))))
          layer
    else
      compressChunks input (head :: byteAcc) (blockIndex + 1) (chunkIndex + 1) chunkCount
        blockDigest layer

/-- Lean model of `Blake3::hash_blocks(input, block_no, chunk_count, cv, layer)`. When 64 bytes are
left, `take_block` returns `Full` with the words of the first 64 (`blockWords (input.take 64)`) and
the rest (`input.drop 64`); otherwise `Short`, and the byte loop finishes. -/
def hashBlocks (input : List UInt8) (blockNo : Nat) (chunkCount : UInt64) (cv : CV)
    (layer : List CV) : List CV :=
  if _full : 64 ≤ input.length then
    let empty := (input.drop 64).isEmpty
    let digest := compress cv (blockWords (input.take 64)) chunkCount 64
      (blockFlags (decide (blockNo = 0)) (empty || decide (blockNo = 15))
        (empty && decide (chunkCount = 0)))
    if empty then layer ++ [digest]
    else if blockNo = 15 then hashBlocks (input.drop 64) 0 (chunkCount + 1) iv (layer ++ [digest])
    else hashBlocks (input.drop 64) (blockNo + 1) chunkCount digest layer
  else compressChunks input [] 0 (64 * blockNo) chunkCount cv layer
termination_by input.length
decreasing_by all_goals (simp only [List.length_drop]; omega)

/-- Lean model of `Blake3::hash(input)`. -/
def hashModel (input : List UInt8) : CV :=
  compressLayer (hashBlocks input 0 0 iv [])

/-! ### Steps of the model -/

/-- The chaining value an output adds to the tree: its root form (counter 0, `ROOT`) when `root`. -/
def outputCV (root : Bool) (output : Output) : CV :=
  if root then compress output.cv output.block 0 output.blockLen (output.flags ||| 8)
  else output.chainingValue

theorem cvBytes_outputCV_root (output : Output) :
    cvBytes (outputCV true output) = output.rootHash := rfl

theorem outputCV_of_ne {count : UInt64} (nonzero : count ≠ 0) (output : Output) :
    outputCV (decide (count = 0)) output = output.chainingValue := by
  rw [decide_eq_false nonzero]
  rfl

/-- A chunk's last block, as `chunkLoop` leaves it, gives the model's chaining value. -/
theorem outputCV_last (count : UInt64) (cv : CV) (block : Block) (len : UInt32) (start : Bool) :
    outputCV (decide (count = 0)) ⟨cv, block, len, count, (if start then 1 else 0) ||| 2⟩ =
      compress cv block count len (blockFlags start true (decide (count = 0))) := by
  by_cases zero : count = 0
  · subst zero
    rw [decide_eq_true (rfl : (0 : UInt64) = 0), blockFlags_root]
    rfl
  · rw [decide_eq_false zero, blockFlags_end]
    rfl

theorem chunkLoop_full_last (count : UInt64) (cv : CV) (start : Bool) (bytes : List UInt8)
    (full : bytes.length = 64) :
    (chunkLoop count cv start bytes).chainingValue =
      compress cv (blockWords bytes) count 64 (blockFlags start true false) := by
  rw [chunkLoop_of_le count cv start bytes (by omega), ← blockFlags_end]
  show compress cv (blockWords bytes) count bytes.length.toUInt32 (blockFlags start true false) = _
  rw [show bytes.length.toUInt32 = 64 from (congrArg Nat.toUInt32 full).trans rfl]

theorem hashBlocks_short (input : List UInt8) (blockNo : Nat) (count : UInt64) (cv : CV)
    (layer : List CV) (short : input.length < 64) :
    hashBlocks input blockNo count cv layer =
      compressChunks input [] 0 (64 * blockNo) count cv layer := by
  rw [hashBlocks, dite_eq_right (by omega)]

theorem hashBlocks_last_block (input : List UInt8) (blockNo : Nat) (count : UInt64) (cv : CV)
    (layer : List CV) (sixtyFour : input.length = 64) :
    hashBlocks input blockNo count cv layer =
      layer ++ [compress cv (blockWords input) count 64
        (blockFlags (decide (blockNo = 0)) true (decide (count = 0)))] := by
  have empty : (input.drop 64).isEmpty = true := by
    rw [List.isEmpty_iff, List.drop_eq_nil_iff]; omega
  have whole : input.take 64 = input := List.take_of_length_le (by omega)
  rw [hashBlocks, dite_eq_left (by omega)]
  simp [empty, whole, sixtyFour]

theorem hashBlocks_chunk_end (input : List UInt8) (count : UInt64) (cv : CV) (layer : List CV)
    (long : 64 < input.length) :
    hashBlocks input 15 count cv layer =
      hashBlocks (input.drop 64) 0 (count + 1) iv
        (layer ++ [compress cv (blockWords (input.take 64)) count 64
          (blockFlags false true false)]) := by
  have more : (input.drop 64).isEmpty = false := by
    rw [List.isEmpty_eq_false_iff, ne_eq, List.drop_eq_nil_iff]; omega
  have notShort : ¬ input.length ≤ 64 := by omega
  rw [hashBlocks, dite_eq_left (by omega)]
  simp [more, notShort]

theorem hashBlocks_step (input : List UInt8) (blockNo : Nat) (count : UInt64) (cv : CV)
    (layer : List CV) (long : 64 < input.length) (notLast : blockNo ≠ 15) :
    hashBlocks input blockNo count cv layer =
      hashBlocks (input.drop 64) (blockNo + 1) count
        (compress cv (blockWords (input.take 64)) count 64
          (blockFlags (decide (blockNo = 0)) false false)) layer := by
  have more : (input.drop 64).isEmpty = false := by
    rw [List.isEmpty_eq_false_iff, ne_eq, List.drop_eq_nil_iff]; omega
  have notShort : ¬ input.length ≤ 64 := by omega
  rw [hashBlocks, dite_eq_left (by omega)]
  simp [more, notShort, notLast]

/-- The byte loop on the last bytes of a block, from the block's start: they accumulate. -/
theorem compressChunks_tail (count : UInt64) (cv : CV) (layer : List CV) :
    (input acc : List UInt8) → (blockIndex chunkIndex : Nat) → blockIndex + input.length ≤ 63 →
    compressChunks input acc blockIndex chunkIndex count cv layer =
      finish (input.reverse ++ acc) (blockIndex + input.length) (chunkIndex + input.length) count
        cv layer
  | [], acc, blockIndex, chunkIndex, _ => by
    simp only [compressChunks, List.reverse_nil, List.nil_append, List.length_nil, Nat.add_zero]
  | head :: input, acc, blockIndex, chunkIndex, room => by
    have notFull : blockIndex ≠ 63 := by rw [List.length_cons] at room; omega
    have e1 : blockIndex + 1 + input.length = blockIndex + (input.length + 1) := by omega
    have e2 : chunkIndex + 1 + input.length = chunkIndex + (input.length + 1) := by omega
    rw [compressChunks, ite_eq_right notFull,
      compressChunks_tail count cv layer input (head :: acc) (blockIndex + 1) (chunkIndex + 1)
        (by rw [List.length_cons] at room; omega),
      e1, e2, List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons]

theorem finish_tail (tail : List UInt8) (blockNo : Nat) (count : UInt64) (cv : CV)
    (layer : List CV) (positive : 0 < tail.length) :
    finish tail.reverse tail.length (64 * blockNo + tail.length) count cv layer =
      layer ++ [compress cv (blockWords tail) count tail.length.toUInt32
        (blockFlags (decide (blockNo = 0)) true (decide (count = 0)))] := by
  have start : (64 * blockNo + tail.length - tail.length = 0) ↔ (blockNo = 0) := by omega
  rw [finish, ite_eq_right (by omega), List.reverse_reverse]
  simp only [start]

/-- The empty input: one empty block, the root. -/
theorem hashBlocks_nil (cv : CV) (layer : List CV) :
    hashBlocks [] 0 0 cv layer = layer ++ [outputCV true (chunkLoop 0 cv true [])] := by
  rw [hashBlocks_short [] 0 0 cv layer (by decide), chunkLoop_of_le 0 cv true [] (by decide)]
  show finish [] 0 0 0 cv layer = _
  rw [finish, ite_eq_left (rfl : (0 : Nat) = 0), ite_eq_left (rfl : (0 : Nat) = 0),
    ite_eq_left (rfl : (0 : UInt64) = 0), blockFlags_root]
  rfl

/-! ### Chunks -/

/-- A chunk's last bytes (`0 < input.length ≤` what is left of the chunk after `blockNo` blocks):
the model adds the chaining value of `chunkLoop`'s output, as the root if the chunk is the first. -/
theorem hashBlocks_last (input : List UInt8) (blockNo : Nat) (count : UInt64) (cv : CV)
    (layer : List CV) (positive : 0 < input.length) (within : input.length ≤ 64 * (16 - blockNo)) :
    hashBlocks input blockNo count cv layer =
      layer ++
        [outputCV (decide (count = 0)) (chunkLoop count cv (decide (blockNo = 0)) input)] := by
  by_cases short : input.length < 64
  · rw [hashBlocks_short input blockNo count cv layer short,
      compressChunks_tail count cv layer input [] 0 (64 * blockNo) (by omega),
      List.append_nil, Nat.zero_add, finish_tail input blockNo count cv layer positive,
      chunkLoop_of_le count cv _ input (by omega), outputCV_last]
  · by_cases sixtyFour : input.length = 64
    · rw [hashBlocks_last_block input blockNo count cv layer sixtyFour,
        chunkLoop_of_le count cv _ input (by omega), outputCV_last,
        show input.length.toUInt32 = 64 from (congrArg Nat.toUInt32 sixtyFour).trans rfl]
    · have long : 64 < input.length := by omega
      rw [hashBlocks_step input blockNo count cv layer long (by omega),
        hashBlocks_last (input.drop 64) (blockNo + 1) count _ layer
          (by rw [List.length_drop]; omega) (by rw [List.length_drop]; omega),
        chunkLoop_of_gt count cv _ input long, blockFlags_step,
        show decide (blockNo + 1 = 0) = false from decide_eq_false (by omega)]
termination_by input.length
decreasing_by rw [List.length_drop]; omega

/-- A chunk followed by more input: after its last block the model adds the chaining value of
`chunkLoop`'s output and starts the next chunk. -/
theorem hashBlocks_chunk (input : List UInt8) (blockNo : Nat) (count : UInt64) (cv : CV)
    (layer : List CV) (inChunk : blockNo ≤ 15) (more : 64 * (16 - blockNo) < input.length) :
    hashBlocks input blockNo count cv layer =
      hashBlocks (input.drop (64 * (16 - blockNo))) 0 (count + 1) iv
        (layer ++ [(chunkLoop count cv (decide (blockNo = 0))
          (input.take (64 * (16 - blockNo)))).chainingValue]) := by
  have long : 64 < input.length := by omega
  by_cases last : blockNo = 15
  · subst last
    rw [hashBlocks_chunk_end input count cv layer long, show 64 * (16 - 15) = 64 from rfl,
      chunkLoop_full_last count cv _ (input.take 64) (by rw [List.length_take]; omega),
      show decide (15 = 0) = false from rfl]
  · rw [hashBlocks_step input blockNo count cv layer long last,
      hashBlocks_chunk (input.drop 64) (blockNo + 1) count _ layer (by omega)
        (by rw [List.length_drop]; omega),
      chunkLoop_of_gt count cv _ (input.take (64 * (16 - blockNo)))
        (by rw [List.length_take]; omega),
      List.take_take, List.drop_take, List.drop_drop, blockFlags_step,
      show min 64 (64 * (16 - blockNo)) = 64 by omega,
      show 64 * (16 - blockNo) - 64 = 64 * (16 - (blockNo + 1)) by omega,
      show 64 + 64 * (16 - (blockNo + 1)) = 64 * (16 - blockNo) by omega,
      show decide (blockNo + 1 = 0) = false from decide_eq_false (by omega)]
termination_by input.length
decreasing_by rw [List.length_drop]; omega

theorem toUInt64_succ (c : Nat) : c.toUInt64 + 1 = (c + 1).toUInt64 :=
  (UInt64.ofNat_add c 1).symm

theorem toUInt64_ne_zero {c : Nat} (positive : 0 < c) (bounded : c < 2 ^ 64) : c.toUInt64 ≠ 0 := by
  intro zero
  have value := congrArg UInt64.toNat zero
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', UInt64.toNat_zero] at value
  omega

/-- From a chunk's start, the model adds the chaining values of the input's chunks, numbered from
`c`, provided the last one's counter is not 0 (so none is the root). -/
theorem hashBlocks_chunks (input : List UInt8) (c : Nat) (layer : List CV)
    (positive : 0 < input.length) (nonzero : 0 < c + (input.length - 1) / 1024)
    (bounded : c + (input.length - 1) / 1024 < 2 ^ 64) :
    hashBlocks input 0 c.toUInt64 iv layer =
      layer ++ (chunkOutputs c input).map Output.chainingValue := by
  by_cases small : input.length ≤ 1024
  · have single : (input.length - 1) / 1024 = 0 := by omega
    rw [hashBlocks_last input 0 c.toUInt64 iv layer positive (by omega),
      outputCV_of_ne (toUInt64_ne_zero (by omega) (by omega)), chunkOutputs_small c input small]
    rfl
  · rw [hashBlocks_chunk input 0 c.toUInt64 iv layer (by omega) (by omega),
      show 64 * (16 - 0) = 1024 from rfl, toUInt64_succ,
      hashBlocks_chunks (input.drop 1024) (c + 1) _ (by rw [List.length_drop]; omega)
        (by rw [List.length_drop]; omega) (by rw [List.length_drop]; omega),
      chunkOutputs_large c input (by omega), List.map_cons, List.append_assoc,
      List.singleton_append]
    rfl
termination_by input.length
decreasing_by rw [List.length_drop]; omega

/-! ### The tree and `hash` -/

theorem compress_layer_singleton (cv : CV) : compressLayer [cv] = cv := by
  rw [compressLayer]

theorem nextLayer_eq_pairChainingValues : (cvs : List CV) → nextLayer cvs = pairChainingValues cvs
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: rest => by
    simp only [nextLayer, pairChainingValues, nextLayer_eq_pairChainingValues rest]

theorem compress_layer_pair (left right : Output) :
    cvBytes (compressLayer ([left, right].map Output.chainingValue)) =
      (mergeLevels [left, right]).rootHash := by
  rw [mergeLevels_step,
    show pairOutputs [left, right] = [parentOutput left.chainingValue right.chainingValue] from rfl,
    mergeLevels_singleton]
  exact compress_layer_two_spec left.chainingValue right.chainingValue

theorem compress_layer_map_step (left right third : Output) (rest : List Output) :
    compressLayer ((left :: right :: third :: rest).map Output.chainingValue) =
      compressLayer ((pairOutputs (left :: right :: third :: rest)).map Output.chainingValue) := by
  rw [pairOutputs_chainingValues, ← nextLayer_eq_pairChainingValues]
  exact compress_layer_step_spec left.chainingValue right.chainingValue third.chainingValue
    (rest.map Output.chainingValue)

theorem compress_layer_spec_le (limit : Nat) : (outputs : List Output) → outputs.length ≤ limit →
    2 ≤ outputs.length →
    cvBytes (compressLayer (outputs.map Output.chainingValue)) =
      (mergeLevels outputs).rootHash := by
  induction limit with
  | zero => intro outputs below two; omega
  | succ limit ih =>
    intro outputs below two
    match outputs, below, two with
    | [], _, two => exact absurd two (by simp)
    | [_], _, two => exact absurd two (by simp)
    | [left, right], _, _ => exact compress_layer_pair left right
    | left :: right :: third :: rest, below, _ =>
      have pairs := pairOutputs_length (left :: right :: third :: rest)
      simp only [List.length_cons] at pairs below
      rw [compress_layer_map_step, ← mergeLevels_pairOutputs (left :: right :: third :: rest),
        ih _ (by omega) (by omega)]

/-- `compress_layer` of two or more chaining values is the root of their level-by-level merge. -/
theorem compress_layer_spec (outputs : List Output) (two : 2 ≤ outputs.length) :
    cvBytes (compressLayer (outputs.map Output.chainingValue)) = (mergeLevels outputs).rootHash :=
  compress_layer_spec_le outputs.length outputs (Nat.le_refl _) two

/-- **The model of `Blake3::hash` computes BLAKE3** (`Blake3.Pure.digest`), for every input of fewer
than `2^64` bytes. -/
theorem hash_model_spec (input : List UInt8) (native : NativeInput input) :
    cvBytes (hashModel input) = digest input := by
  have bounded : input.length < 2 ^ 64 := native
  by_cases small : input.length ≤ 1024
  · have single : hashBlocks input 0 0 iv [] = [outputCV true (chunkLoop 0 iv true input)] := by
      by_cases empty : input = []
      · subst empty
        exact hashBlocks_nil iv []
      · rw [hashBlocks_last input 0 0 iv [] (List.length_pos_iff.mpr empty) (by omega)]
        rfl
    show cvBytes (compressLayer (hashBlocks input 0 0 iv [])) = digest input
    rw [single, compress_layer_singleton, ← chunk_single_root_spec input small]
    rfl
  · have chunks := hashBlocks_chunks input 0 [] (by omega) (by omega) (by omega)
    show cvBytes (compressLayer (hashBlocks input 0 (0 : Nat).toUInt64 iv [])) = digest input
    rw [chunks, List.nil_append,
      compress_layer_spec _ (by rw [chunkOutputs_length, ite_eq_right small]; omega),
      ← digest_eq_mergeLevels]

/-- In the Lean model, `Blake3::verify_bytes_against(bytes, expected)` checks BLAKE3: under
`U32.Compatible F`, its field-wise check of `digest_bytes(hash(bytes))` against `expected` holds iff
the BLAKE3 digest of `bytes` is `expected`. -/
theorem verify_bytes_against_model_iff {F : Type} [Field F] (large : U32.Compatible F)
    (bytes : List UInt8) (native : NativeInput bytes) (expected : Digest) :
    addressToFields F (cvBytes (hashModel bytes)) = addressToFields F expected ↔
      digest bytes = expected := by
  rw [hash_model_spec bytes native]
  exact verify_bytes_against_iff large bytes expected

end Aiur.Library.Blake3
