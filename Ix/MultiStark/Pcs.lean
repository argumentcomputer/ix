module
public import Ix.Aiur.Meta
public import Ix.MultiStark.Deserialize
public import Ix.MultiStark.Keccak

/-!
# PCS (FRI) verification

Ports `multi-stark/src/verifier.rs`'s `pcs.verify(...)` — a `TwoAdicFriPcs` FRI
verification: Merkle `verify_batch` (binary tree, multi-height injection), the
challenger continuation, the FRI fold chain (`open_input` / `verify_query`), and
the final-polynomial check.

## Merkle (MMCS) hash primitives

The input/commit-phase commitments are a `MerkleTreeMmcs` over Blake3
(`multi-stark/src/types.rs`):

* leaf hash  : `SerializingHasher<Blake3>` — serialize each `Goldilocks` element
  to its canonical 8 LE bytes, then `blake3` the row.
* compression: `CompressionFunctionFromHasher<Blake3, 2, 32>` — `blake3(a || b)`
  of two 32-byte child digests.

`Digest` is `[U64; 4]` = the 32 Blake3 output bytes (8-byte LE groups), so the
deserialized caps round-trip unchanged. The Blake3 gadget is `Ix/IxVM/Blake3.lean`.
-/

public section

namespace MultiStark

def pcs := ⟦
  -- ==========================================================================
  -- Blake3 MMCS hash primitives.
  --
  -- The input/commit-phase commitments are a `MerkleTreeMmcs` over Blake3:
  --   leaf   = `blake3(serialized row bytes)`  (`SerializingHasher<Blake3>`)
  --   2-to-1 = `blake3(a || b)`                (`CompressionFunctionFromHasher<Blake3, 2, 32>`)
  -- A row's `Val`s are serialized as 8 LE bytes each (canonical `u64`). `Digest`
  -- is `[U64; 4]` = the 32 blake3 output bytes (8-byte LE groups), so the
  -- deserialized caps round-trip with zero change to the deserializer.
  -- ==========================================================================

  -- 8 LE bytes of a `U64` lane (`SerializingHasher`: a `Val` is 8 LE bytes).
  fn b3_u64_onto(v: U64, tail: ByteStream) -> ByteStream {
    store(ListNode.Cons(v[0], store(ListNode.Cons(v[1], store(ListNode.Cons(v[2],
    store(ListNode.Cons(v[3], store(ListNode.Cons(v[4], store(ListNode.Cons(v[5],
    store(ListNode.Cons(v[6], store(ListNode.Cons(v[7], tail))))))))))))))))
  }
  -- All lanes of a row, in order.
  fn b3_row_onto(row: List‹U64›, tail: ByteStream) -> ByteStream {
    match load(row) {
      ListNode.Nil => tail,
      ListNode.Cons(v, rest) => b3_u64_onto(v, b3_row_onto(rest, tail)),
    }
  }
  -- A 4-byte blake3 output word.
  fn b3_w4_onto(w: [U8; 4], tail: ByteStream) -> ByteStream {
    store(ListNode.Cons(w[0], store(ListNode.Cons(w[1], store(ListNode.Cons(w[2],
    store(ListNode.Cons(w[3], tail))))))))
  }
  -- The 32 bytes of a blake3 digest (`[[U8;4];8]`, word order = output order).
  fn b3_flatten_onto(h: [[U8; 4]; 8], tail: ByteStream) -> ByteStream {
    b3_w4_onto(h[0], b3_w4_onto(h[1], b3_w4_onto(h[2], b3_w4_onto(h[3],
    b3_w4_onto(h[4], b3_w4_onto(h[5], b3_w4_onto(h[6], b3_w4_onto(h[7], tail))))))))
  }
  -- blake3 output `[[U8;4];8]` -> `Digest` `[U64;4]` (two words per LE lane).
  fn b3_to_digest(h: [[U8; 4]; 8]) -> Digest {
    [[h[0][0], h[0][1], h[0][2], h[0][3], h[1][0], h[1][1], h[1][2], h[1][3]],
     [h[2][0], h[2][1], h[2][2], h[2][3], h[3][0], h[3][1], h[3][2], h[3][3]],
     [h[4][0], h[4][1], h[4][2], h[4][3], h[5][0], h[5][1], h[5][2], h[5][3]],
     [h[6][0], h[6][1], h[6][2], h[6][3], h[7][0], h[7][1], h[7][2], h[7][3]]]
  }
  -- ==========================================================================
  -- Lane-granular blake3 for MMCS leaf rows. A leaf's input is a `List‹U64›`
  -- of 8-byte lanes, so blocks (64 bytes = 8 lanes) can be assembled straight
  -- from the lane values — one list `load` per lane — instead of serializing
  -- to a byte list that `blake3` then walks, re-accumulates, and re-loads
  -- (~4 memory ops per byte). Mirrors `blake3_compress_chunks`/`_block`/
  -- `_finish` at block granularity with the identical flag schedule
  -- (CHUNK_START = 1, CHUNK_END = 2, ROOT = 8; chunk = 16 blocks), reusing
  -- `blake3_compress` and the `Layer` chunk-tree fold unchanged.
  -- ==========================================================================

  -- Pop up to 8 lanes (one block), zero-padding the tail. Returns the block's
  -- lanes, its real byte length (8·k, so 64 for a full block), and the rest.
  fn b3_lane_block(lanes: List‹U64›) -> ([U64; 8], G, List‹U64›) {
    let z = [0u8; 8];
    match load(lanes) {
      ListNode.Nil => ([z; 8], 0, lanes),
      ListNode.Cons(v0, r0) => match load(r0) {
        ListNode.Nil => ([v0, z, z, z, z, z, z, z], 8, r0),
        ListNode.Cons(v1, r1) => match load(r1) {
          ListNode.Nil => ([v0, v1, z, z, z, z, z, z], 16, r1),
          ListNode.Cons(v2, r2) => match load(r2) {
            ListNode.Nil => ([v0, v1, v2, z, z, z, z, z], 24, r2),
            ListNode.Cons(v3, r3) => match load(r3) {
              ListNode.Nil => ([v0, v1, v2, v3, z, z, z, z], 32, r3),
              ListNode.Cons(v4, r4) => match load(r4) {
                ListNode.Nil => ([v0, v1, v2, v3, v4, z, z, z], 40, r4),
                ListNode.Cons(v5, r5) => match load(r5) {
                  ListNode.Nil => ([v0, v1, v2, v3, v4, v5, z, z], 48, r5),
                  ListNode.Cons(v6, r6) => match load(r6) {
                    ListNode.Nil => ([v0, v1, v2, v3, v4, v5, v6, z], 56, r6),
                    ListNode.Cons(v7, r7) =>
                      ([v0, v1, v2, v3, v4, v5, v6, v7], 64, r7),
                  },
                },
              },
            },
          },
        },
      },
    }
  }

  -- Block-granular chunk walk. `block_no` is the block index within the
  -- current chunk (0..15); `cv` is the chaining value (IV at each chunk start);
  -- chunk digests are pushed onto `layer` in order, exactly like the byte
  -- driver, and folded by `blake3_compress_layer` at the end.
  fn b3_lane_chunks(lanes: List‹U64›, block_no: G, chunk_count: &U64, cv: &[[U8; 4]; 8], layer: &Layer) -> &Layer {
    match load(lanes) {
      -- Exhausted with no block to compress: only reachable for an empty
      -- input (every other path detects exhaustion after compressing).
      -- Mirror of `blake3_finish`'s (0, 0) arm.
      ListNode.Nil =>
        match load(chunk_count) {
          [0, 0, 0, 0, 0, 0, 0, 0] =>
            store(Layer.Push(layer, blake3_compress(load(cv), [[0u8; 4]; 16], load(chunk_count), 0, 11))),
          _ => layer,
        },
      _ =>
        let (v, nbytes, rest) = b3_lane_block(lanes);
        let block = [
          [v[0][0], v[0][1], v[0][2], v[0][3]], [v[0][4], v[0][5], v[0][6], v[0][7]],
          [v[1][0], v[1][1], v[1][2], v[1][3]], [v[1][4], v[1][5], v[1][6], v[1][7]],
          [v[2][0], v[2][1], v[2][2], v[2][3]], [v[2][4], v[2][5], v[2][6], v[2][7]],
          [v[3][0], v[3][1], v[3][2], v[3][3]], [v[3][4], v[3][5], v[3][6], v[3][7]],
          [v[4][0], v[4][1], v[4][2], v[4][3]], [v[4][4], v[4][5], v[4][6], v[4][7]],
          [v[5][0], v[5][1], v[5][2], v[5][3]], [v[5][4], v[5][5], v[5][6], v[5][7]],
          [v[6][0], v[6][1], v[6][2], v[6][3]], [v[6][4], v[6][5], v[6][6], v[6][7]],
          [v[7][0], v[7][1], v[7][2], v[7][3]], [v[7][4], v[7][5], v[7][6], v[7][7]]];
        let empty = match load(rest) { ListNode.Nil => 1, _ => 0, };
        let at15 = eq_zero(block_no - 15);
        -- CHUNK_START on the chunk's first block; CHUNK_END iff this is the
        -- chunk's 16th block OR the input ends here; ROOT only for the last
        -- block of a single-chunk input (multi-chunk roots come from the
        -- layer fold's PARENT+ROOT, as in the byte driver).
        let start_flag = eq_zero(block_no);
        let end_flag = empty + at15 - (empty * at15);
        let root_flag = empty * u64_is_zero(load(chunk_count));
        let flags = start_flag + 2 * end_flag + 8 * root_flag;
        let digest = blake3_compress(load(cv), block, load(chunk_count), nbytes, flags);
        match (empty, at15) {
          (1, _) => store(Layer.Push(layer, digest)),
          (_, 1) =>
            let IV = [[103u8, 230u8, 9u8, 106u8], [133u8, 174u8, 103u8, 187u8], [114u8, 243u8, 110u8, 60u8], [58u8, 245u8, 79u8, 165u8], [127u8, 82u8, 14u8, 81u8], [140u8, 104u8, 5u8, 155u8], [171u8, 217u8, 131u8, 31u8], [25u8, 205u8, 224u8, 91u8]];
            b3_lane_chunks(rest, 0, store(relaxed_u64_succ(load(chunk_count))), store(IV), store(Layer.Push(layer, digest))),
          (_, _) => b3_lane_chunks(rest, block_no + 1, chunk_count, store(digest), layer),
        },
    }
  }

  -- ==========================================================================
  -- blake3 straight from an IO channel arena: 64-byte `io_read` blocks fed
  -- directly to `blake3_compress` — no byte list is materialized, walked,
  -- accumulated, or re-loaded. Same flag schedule as the byte driver; the
  -- (cold, once-per-hash) ≤63-byte tail reuses `pad_block`/`bytes_to_block`.
  -- Used for digest-binding large advice streams (the verifying key).
  -- ==========================================================================

  -- Reverse-ordered tail accumulator (head = last byte), the shape
  -- `pad_block`/`bytes_to_block` expect. Reads one byte per step (io_read's
  -- length is static); at most 63 steps, once per hash.
  fn b3_io_tail_acc(ch: G, i: G, n: G, acc: ByteStream) -> ByteStream {
    match n {
      0 => acc,
      _ =>
        let [b] = io_read(ch, i, 1);
        b3_io_tail_acc(ch, i + 1, n - 1,
          store(ListNode.Cons(u8_from_field_unsafe(b), acc))),
    }
  }

  fn b3_io_chunks(ch: G, i: G, remaining: G, block_no: G, chunk_count: &U64, cv: &[[U8; 4]; 8], layer: &Layer) -> &Layer {
    match u32_less_than(remaining, 64) {
      0 =>
        -- A full 64-byte block is available.
        let [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
             b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31,
             b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
             b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63] =
          io_read(ch, i, 64);
        let block = [
          [u8_from_field_unsafe(b0), u8_from_field_unsafe(b1), u8_from_field_unsafe(b2), u8_from_field_unsafe(b3)],
          [u8_from_field_unsafe(b4), u8_from_field_unsafe(b5), u8_from_field_unsafe(b6), u8_from_field_unsafe(b7)],
          [u8_from_field_unsafe(b8), u8_from_field_unsafe(b9), u8_from_field_unsafe(b10), u8_from_field_unsafe(b11)],
          [u8_from_field_unsafe(b12), u8_from_field_unsafe(b13), u8_from_field_unsafe(b14), u8_from_field_unsafe(b15)],
          [u8_from_field_unsafe(b16), u8_from_field_unsafe(b17), u8_from_field_unsafe(b18), u8_from_field_unsafe(b19)],
          [u8_from_field_unsafe(b20), u8_from_field_unsafe(b21), u8_from_field_unsafe(b22), u8_from_field_unsafe(b23)],
          [u8_from_field_unsafe(b24), u8_from_field_unsafe(b25), u8_from_field_unsafe(b26), u8_from_field_unsafe(b27)],
          [u8_from_field_unsafe(b28), u8_from_field_unsafe(b29), u8_from_field_unsafe(b30), u8_from_field_unsafe(b31)],
          [u8_from_field_unsafe(b32), u8_from_field_unsafe(b33), u8_from_field_unsafe(b34), u8_from_field_unsafe(b35)],
          [u8_from_field_unsafe(b36), u8_from_field_unsafe(b37), u8_from_field_unsafe(b38), u8_from_field_unsafe(b39)],
          [u8_from_field_unsafe(b40), u8_from_field_unsafe(b41), u8_from_field_unsafe(b42), u8_from_field_unsafe(b43)],
          [u8_from_field_unsafe(b44), u8_from_field_unsafe(b45), u8_from_field_unsafe(b46), u8_from_field_unsafe(b47)],
          [u8_from_field_unsafe(b48), u8_from_field_unsafe(b49), u8_from_field_unsafe(b50), u8_from_field_unsafe(b51)],
          [u8_from_field_unsafe(b52), u8_from_field_unsafe(b53), u8_from_field_unsafe(b54), u8_from_field_unsafe(b55)],
          [u8_from_field_unsafe(b56), u8_from_field_unsafe(b57), u8_from_field_unsafe(b58), u8_from_field_unsafe(b59)],
          [u8_from_field_unsafe(b60), u8_from_field_unsafe(b61), u8_from_field_unsafe(b62), u8_from_field_unsafe(b63)]];
        let is_last = eq_zero(remaining - 64);
        let at15 = eq_zero(block_no - 15);
        let start_flag = eq_zero(block_no);
        let end_flag = is_last + at15 - (is_last * at15);
        let root_flag = is_last * u64_is_zero(load(chunk_count));
        let flags = start_flag + 2 * end_flag + 8 * root_flag;
        let digest = blake3_compress(load(cv), block, load(chunk_count), 64, flags);
        match (is_last, at15) {
          (1, _) => store(Layer.Push(layer, digest)),
          (_, 1) =>
            let IV = [[103u8, 230u8, 9u8, 106u8], [133u8, 174u8, 103u8, 187u8], [114u8, 243u8, 110u8, 60u8], [58u8, 245u8, 79u8, 165u8], [127u8, 82u8, 14u8, 81u8], [140u8, 104u8, 5u8, 155u8], [171u8, 217u8, 131u8, 31u8], [25u8, 205u8, 224u8, 91u8]];
            b3_io_chunks(ch, i + 64, remaining - 64, 0, store(relaxed_u64_succ(load(chunk_count))), store(IV), store(Layer.Push(layer, digest))),
          (_, _) => b3_io_chunks(ch, i + 64, remaining - 64, block_no + 1, chunk_count, store(digest), layer),
        },
      _ =>
        -- Partial tail (< 64 bytes): always the input's last block.
        match remaining {
          0 =>
            -- Empty input from the very start. Mirror of `blake3_finish`'s
            -- (0, 0) arm (any other path compresses before exhausting).
            match load(chunk_count) {
              [0, 0, 0, 0, 0, 0, 0, 0] =>
                store(Layer.Push(layer, blake3_compress(load(cv), [[0u8; 4]; 16], load(chunk_count), 0, 11))),
              _ => layer,
            },
          _ =>
            let block = bytes_to_block(pad_block(
              b3_io_tail_acc(ch, i, remaining, store(ListNode.Nil)), 64 - remaining));
            let start_flag = eq_zero(block_no);
            let flags = start_flag + 2 + 8 * u64_is_zero(load(chunk_count));
            store(Layer.Push(layer, blake3_compress(load(cv), block, load(chunk_count), remaining, flags))),
        },
    }
  }

  -- blake3 of `len` bytes at offset `idx` on IO channel `ch` (identical
  -- output to `blake3` over those bytes — pinned by `io_hash_test`).
  fn b3_io(ch: G, idx: G, len: G) -> [[U8; 4]; 8] {
    let IV = [[103u8, 230u8, 9u8, 106u8], [133u8, 174u8, 103u8, 187u8], [114u8, 243u8, 110u8, 60u8], [58u8, 245u8, 79u8, 165u8], [127u8, 82u8, 14u8, 81u8], [140u8, 104u8, 5u8, 155u8], [171u8, 217u8, 131u8, 31u8], [25u8, 205u8, 224u8, 91u8]];
    blake3_compress_layer(load(b3_io_chunks(ch, idx, len, 0, store([0u8; 8]), store(IV), store(Layer.Nil))))
  }

  -- blake3 of a lane list (identical output to `blake3` over the lanes' LE
  -- bytes — pinned by the `lane_hash_test` differential self-test).
  fn b3_lanes(lanes: List‹U64›) -> [[U8; 4]; 8] {
    let IV = [[103u8, 230u8, 9u8, 106u8], [133u8, 174u8, 103u8, 187u8], [114u8, 243u8, 110u8, 60u8], [58u8, 245u8, 79u8, 165u8], [127u8, 82u8, 14u8, 81u8], [140u8, 104u8, 5u8, 155u8], [171u8, 217u8, 131u8, 31u8], [25u8, 205u8, 224u8, 91u8]];
    blake3_compress_layer(load(b3_lane_chunks(lanes, 0, store([0u8; 8]), store(IV), store(Layer.Nil))))
  }

  -- The MMCS leaf hash of a row (`SerializingHasher<Blake3>`).
  fn mmcs_hash_row(row: List‹U64›) -> Digest {
    b3_to_digest(b3_lanes(row))
  }
  -- The MMCS 2-to-1 compression (`CompressionFunctionFromHasher<Blake3, 2, 32>`).
  -- `a || b` is exactly 64 bytes = one blake3 block of a single chunk, so this
  -- is one direct `blake3_compress` with the same parameters that input takes
  -- through `blake3_compress_chunks`: cv = IV, counter = 0, block_len = 64,
  -- flags = CHUNK_START + CHUNK_END + ROOT (1 + 2 + 8). The block words are
  -- assembled straight from the digest lanes (each `U64` lane = two LE 4-byte
  -- words) — no byte list is built, walked, re-accumulated, or re-loaded.
  fn mmcs_compress(a: Digest, b: Digest) -> Digest {
    let IV = [[103u8, 230u8, 9u8, 106u8], [133u8, 174u8, 103u8, 187u8], [114u8, 243u8, 110u8, 60u8], [58u8, 245u8, 79u8, 165u8], [127u8, 82u8, 14u8, 81u8], [140u8, 104u8, 5u8, 155u8], [171u8, 217u8, 131u8, 31u8], [25u8, 205u8, 224u8, 91u8]];
    let block = [
      [a[0][0], a[0][1], a[0][2], a[0][3]], [a[0][4], a[0][5], a[0][6], a[0][7]],
      [a[1][0], a[1][1], a[1][2], a[1][3]], [a[1][4], a[1][5], a[1][6], a[1][7]],
      [a[2][0], a[2][1], a[2][2], a[2][3]], [a[2][4], a[2][5], a[2][6], a[2][7]],
      [a[3][0], a[3][1], a[3][2], a[3][3]], [a[3][4], a[3][5], a[3][6], a[3][7]],
      [b[0][0], b[0][1], b[0][2], b[0][3]], [b[0][4], b[0][5], b[0][6], b[0][7]],
      [b[1][0], b[1][1], b[1][2], b[1][3]], [b[1][4], b[1][5], b[1][6], b[1][7]],
      [b[2][0], b[2][1], b[2][2], b[2][3]], [b[2][4], b[2][5], b[2][6], b[2][7]],
      [b[3][0], b[3][1], b[3][2], b[3][3]], [b[3][4], b[3][5], b[3][6], b[3][7]]];
    b3_to_digest(blake3_compress(IV, block, [0u8; 8], 64, 11))
  }

  -- ==========================================================================
  -- Merkle MMCS `verify_batch` (binary tree, DIGEST_ELEMS = 4).
  --
  -- Ports `multi-stark/Plonky3/merkle-tree/src/mmcs.rs::verify_batch` for the
  -- binary (N = 2) case. All committed matrices have power-of-two heights, so a
  -- matrix's height is `2^log_height`. The opened rows arrive in matrix order;
  -- `lhs` is the matching list of per-matrix log-heights. The query `index` is
  -- threaded as a bit list (LSB first = leaf→root path) to avoid field division.
  --
  -- The leaf hash joins all matrices at the maximum log-height. Walking down,
  -- each level folds with one proof sibling (ordered by the path bit), then —
  -- if any matrix lives at the new log-height — injects that matrix group's leaf
  -- hash via a second compression (this consumes no proof sibling), exactly as
  -- the Rust loop's `next_height_openings_digest` injection.
  -- ==========================================================================

  -- 1 iff two digests are equal (compared as field elements; hash outputs are
  -- canonical so this is exact).
  fn digest_eq(a: Digest, b: Digest) -> G {
    eq_zero(limb_to_field(a[0]) - limb_to_field(b[0])) *
    eq_zero(limb_to_field(a[1]) - limb_to_field(b[1])) *
    eq_zero(limb_to_field(a[2]) - limb_to_field(b[2])) *
    eq_zero(limb_to_field(a[3]) - limb_to_field(b[3]))
  }

  -- Compress (current, sibling) in path order: path bit 0 ⇒ current is the left
  -- child, bit 1 ⇒ current is the right child.
  fn compress_ordered(bit: G, d: Digest, s: Digest) -> Digest {
    match bit {
      0 => mmcs_compress(d, s),
      _ => mmcs_compress(s, d),
    }
  }

  -- 1 iff some matrix has log-height `target`.
  fn has_height(lhs: List‹G›, target: G) -> G {
    match load(lhs) {
      ListNode.Nil => 0,
      ListNode.Cons(h, rest) =>
        match eq_zero(h - target) {
          1 => 1,
          _ => has_height(rest, target),
        },
    }
  }

  -- Concatenate the opened rows of every matrix whose log-height is `target`
  -- (in matrix order — the stable height-sort preserves it), for the joint leaf
  -- hash `hash_iter_slices`.
  fn concat_at(rows: List‹List‹U64››, lhs: List‹G›, target: G) -> List‹U64› {
    match load(rows) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(r, rrest) =>
        let &ListNode.Cons(lh, lrest) = lhs;
        concat_at_step(eq_zero(lh - target), r, rrest, lrest, target),
    }
  }
  fn concat_at_step(hit: G, r: List‹U64›, rrest: List‹List‹U64››,
      lrest: List‹G›, target: G) -> List‹U64› {
    match hit {
      0 => concat_at(rrest, lrest, target),
      _ => list_concat(r, concat_at(rrest, lrest, target)),
    }
  }

  -- Canonicalize each lane: the MMCS leaf hash serializes `as_canonical_u64`,
  -- but opened base values are on the wire in the (possibly non-canonical)
  -- internal Goldilocks repr — e.g. field zero ships as `p`. `gl_reduce` maps
  -- them to `< p` before hashing (idempotent on already-canonical lanes).
  fn canon_lanes(l: List‹U64›) -> List‹U64› {
    match load(l) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(x, rest) => store(ListNode.Cons(gl_to_bytes(gl_val(x)), canon_lanes(rest))),
    }
  }
  -- ==========================================================================
  -- Rows-walking leaf hash: hash the selected rows' lanes directly, with
  -- on-the-fly canonicalization — no concatenated lane list is ever
  -- materialized (`concat_at` rebuilt every selected lane per query, and
  -- `canon_lanes` copied the result again). Differentially pinned against
  -- the concat + canon reference by `rows_hash_test`.
  -- ==========================================================================

  -- The rows at log-height `target`, dropped if empty (an empty row
  -- contributes no bytes, and dropping it lets exhaustion be detected by
  -- plain Nil checks in the block walker).
  fn select_rows(rows: List‹List‹U64››, lhs: List‹G›, target: G) -> List‹List‹U64›› {
    match load(rows) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(r, rrest) =>
        let &ListNode.Cons(lh, lrest) = lhs;
        match eq_zero(lh - target) {
          0 => select_rows(rrest, lrest, target),
          _ => match load(r) {
            ListNode.Nil => select_rows(rrest, lrest, target),
            _ => store(ListNode.Cons(r, select_rows(rrest, lrest, target))),
          },
        },
    }
  }

  -- Pop one canonicalized lane across row boundaries. `got = 0` iff both the
  -- current row and the remaining rows are exhausted (selected rows are
  -- non-empty, so advancing to the next row always yields a lane).
  fn rows_pop(cur: List‹U64›, rows: List‹List‹U64››) -> (U64, List‹U64›, List‹List‹U64››, G) {
    match load(cur) {
      ListNode.Cons(x, rest) => (gl_to_bytes(gl_val(x)), rest, rows, 1),
      ListNode.Nil => match load(rows) {
        ListNode.Nil => ([0u8; 8], cur, rows, 0),
        ListNode.Cons(r, rrest) => rows_pop(r, rrest),
      },
    }
  }

  -- Block-granular chunk walk over rows-of-lanes; mirrors `b3_lane_chunks`
  -- (same flag schedule, same `Layer` fold), gathering each 64-byte block
  -- with eight cross-row pops.
  fn b3_rows_chunks(cur: List‹U64›, rows: List‹List‹U64››, block_no: G, chunk_count: &U64, cv: &[[U8; 4]; 8], layer: &Layer) -> &Layer {
    let (l0, c1, r1, g0) = rows_pop(cur, rows);
    match g0 {
      -- Exhausted with no block to compress: only reachable for an empty
      -- input (every other path detects exhaustion after compressing).
      0 =>
        match load(chunk_count) {
          [0, 0, 0, 0, 0, 0, 0, 0] =>
            store(Layer.Push(layer, blake3_compress(load(cv), [[0u8; 4]; 16], load(chunk_count), 0, 11))),
          _ => layer,
        },
      _ =>
        let (l1, c2, r2, g1) = rows_pop(c1, r1);
        let (l2, c3, r3, g2) = rows_pop(c2, r2);
        let (l3, c4, r4, g3) = rows_pop(c3, r3);
        let (l4, c5, r5, g4) = rows_pop(c4, r4);
        let (l5, c6, r6, g5) = rows_pop(c5, r5);
        let (l6, c7, r7, g6) = rows_pop(c6, r6);
        let (l7, c8, r8, g7) = rows_pop(c7, r7);
        let nbytes = 8 * (g0 + g1 + g2 + g3 + g4 + g5 + g6 + g7);
        let block = [
          [l0[0], l0[1], l0[2], l0[3]], [l0[4], l0[5], l0[6], l0[7]],
          [l1[0], l1[1], l1[2], l1[3]], [l1[4], l1[5], l1[6], l1[7]],
          [l2[0], l2[1], l2[2], l2[3]], [l2[4], l2[5], l2[6], l2[7]],
          [l3[0], l3[1], l3[2], l3[3]], [l3[4], l3[5], l3[6], l3[7]],
          [l4[0], l4[1], l4[2], l4[3]], [l4[4], l4[5], l4[6], l4[7]],
          [l5[0], l5[1], l5[2], l5[3]], [l5[4], l5[5], l5[6], l5[7]],
          [l6[0], l6[1], l6[2], l6[3]], [l6[4], l6[5], l6[6], l6[7]],
          [l7[0], l7[1], l7[2], l7[3]], [l7[4], l7[5], l7[6], l7[7]]];
        let empty = match load(c8) {
          ListNode.Nil => match load(r8) { ListNode.Nil => 1, _ => 0, },
          _ => 0,
        };
        let at15 = eq_zero(block_no - 15);
        let start_flag = eq_zero(block_no);
        let end_flag = empty + at15 - (empty * at15);
        let root_flag = empty * u64_is_zero(load(chunk_count));
        let flags = start_flag + 2 * end_flag + 8 * root_flag;
        let digest = blake3_compress(load(cv), block, load(chunk_count), nbytes, flags);
        match (empty, at15) {
          (1, _) => store(Layer.Push(layer, digest)),
          (_, 1) =>
            let IV = [[103u8, 230u8, 9u8, 106u8], [133u8, 174u8, 103u8, 187u8], [114u8, 243u8, 110u8, 60u8], [58u8, 245u8, 79u8, 165u8], [127u8, 82u8, 14u8, 81u8], [140u8, 104u8, 5u8, 155u8], [171u8, 217u8, 131u8, 31u8], [25u8, 205u8, 224u8, 91u8]];
            b3_rows_chunks(c8, r8, 0, store(relaxed_u64_succ(load(chunk_count))), store(IV), store(Layer.Push(layer, digest))),
          (_, _) => b3_rows_chunks(c8, r8, block_no + 1, chunk_count, store(digest), layer),
        },
    }
  }

  fn b3_rows(rows: List‹List‹U64››) -> [[U8; 4]; 8] {
    let IV = [[103u8, 230u8, 9u8, 106u8], [133u8, 174u8, 103u8, 187u8], [114u8, 243u8, 110u8, 60u8], [58u8, 245u8, 79u8, 165u8], [127u8, 82u8, 14u8, 81u8], [140u8, 104u8, 5u8, 155u8], [171u8, 217u8, 131u8, 31u8], [25u8, 205u8, 224u8, 91u8]];
    blake3_compress_layer(load(b3_rows_chunks(store(ListNode.Nil), rows, 0, store([0u8; 8]), store(IV), store(Layer.Nil))))
  }

  -- The joint Blake3 leaf hash of all matrices at log-height `target`.
  fn leaf_hash_at(rows: List‹List‹U64››, lhs: List‹G›, target: G) -> Digest {
    b3_to_digest(b3_rows(select_rows(rows, lhs, target)))
  }

  -- Inject the leaf hash of any matrices at log-height `lh` (if present) via a
  -- second compression onto `d`.
  fn inject_maybe(rows: List‹List‹U64››, lhs: List‹G›, lh: G, d: Digest) -> Digest {
    match has_height(lhs, lh) {
      0 => d,
      _ => mmcs_compress(d, leaf_hash_at(rows, lhs, lh)),
    }
  }

  -- Recompose remaining path bits (LSB first) into the cap index.
  fn bits_to_num(bits: List‹G›) -> G {
    match load(bits) {
      ListNode.Nil => 0,
      ListNode.Cons(b, rest) => b + 2 * bits_to_num(rest),
    }
  }

  -- Walk the authentication path: one proof sibling per level (fold), with a
  -- possible leaf injection at the new log-height `lh`. Returns the recomputed
  -- root and the leftover cap index.
  fn mmcs_fold(d: Digest, rows: List‹List‹U64››, lhs: List‹G›,
      proof: List‹Digest›, ibits: List‹G›, lh: G) -> (Digest, G) {
    match load(proof) {
      ListNode.Nil => (d, bits_to_num(ibits)),
      ListNode.Cons(s, prest) =>
        let &ListNode.Cons(bit, brest) = ibits;
        let d1 = compress_ordered(bit, d, s);
        let d2 = inject_maybe(rows, lhs, lh, d1);
        mmcs_fold(d2, rows, lhs, prest, brest, lh - 1),
    }
  }

  -- Recompute the Merkle root from the opened rows + authentication path.
  fn mmcs_root(rows: List‹List‹U64››, lhs: List‹G›, ibits: List‹G›,
      proof: List‹Digest›, log_max: G) -> (Digest, G) {
    let leaf = leaf_hash_at(rows, lhs, log_max);
    mmcs_fold(leaf, rows, lhs, proof, ibits, log_max - 1)
  }

  -- 1 iff the recomputed root matches the commitment cap at the cap index.
  fn mmcs_verify(cap: MerkleCap, rows: List‹List‹U64››, lhs: List‹G›,
      ibits: List‹G›, proof: List‹Digest›, log_max: G) -> G {
    let (root, capidx) = mmcs_root(rows, lhs, ibits, proof, log_max);
    digest_eq(list_lookup(cap, capidx), root)
  }

  -- ==========================================================================
  -- FRI fold step (`TwoAdicFriFolding::fold_row`, arity-2 case).
  --
  -- `innerFri` uses `maxLogArity = 1`, so every FRI fold is binary. Ports
  -- `fold_row` for `log_arity = 1`: given the sibling pair (e0, e1) of a node
  -- and the round challenge β,
  --   folded = (e0 + e1)/2 + β·(e0 − e1)/(2s),
  --   s = g_{log_height+1}^{reverse_bits_len(index, log_height)}     (base field)
  -- where `g_k = two_adic_gen(k)`. The index is threaded as its low-`log_height`
  -- bit list (LSB first), matching `ch_sample_bits`; `reverse_bits_len` is then
  -- just reversing that list.
  -- ==========================================================================

  -- Reverse a `G` (bit) list onto `acc`.
  fn glist_rev(l: List‹G›, acc: List‹G›) -> List‹G› {
    match load(l) {
      ListNode.Nil => acc,
      ListNode.Cons(b, rest) => glist_rev(rest, store(ListNode.Cons(b, acc))),
    }
  }

  -- base^(Σ bits_i · 2^i), bits LSB-first (square-and-multiply over the bits).
  -- `base` is a native Goldilocks element; `bits` is a native bit list.
  fn exp_by_bits(base: Goldilocks, bits: List‹G›) -> Goldilocks {
    match load(bits) {
      ListNode.Nil => gl_one(),
      ListNode.Cons(b, rest) =>
        let half = exp_by_bits(gl_sq(base), rest);
        match b {
          0 => half,
          _ => gl_mul(base, half),
        },
    }
  }

  -- The arity-2 FRI fold. `index_bits` = the low `log_height` index bits, LSB
  -- first (so `reverse_bits_len` = reversing the list).
  fn fri_fold2(index_bits: List‹G›, log_height: G, beta: Ext, e0: Ext, e1: Ext) -> Ext {
    let g = two_adic_gen(log_height + 1);
    let s = exp_by_bits(g, glist_rev(index_bits, store(ListNode.Nil)));
    let two_s = gl_add(s, s);
    let t1 = eg_div(eg_add(e0, e1), [gl_two(), gl_zero()]);
    let t2 = eg_mul(beta, eg_div(eg_sub(e0, e1), [two_s, gl_zero()]));
    eg_add(t1, t2)
  }

  -- ==========================================================================
  -- `open_input` reduced openings (`fri/verifier.rs::open_input` inner loop).
  --
  -- For a matrix opened at a point z with verifier domain point x, accumulate
  -- over the matrix columns:
  --   ro += alpha_pow · (p_z − p_x) · q ;  alpha_pow *= alpha,   q = 1/(z − x)
  -- where p_x are the INPUT opened base values (from the query's batch opening,
  -- authenticated by the input MMCS) and p_z the OOD opened ext values. The
  -- query domain point is
  --   x = GENERATOR(7) · two_adic_gen(log_height)^{reverse_bits_len(idx, log_height)}.
  -- All extension arithmetic — no Merkle hashing here.
  -- ==========================================================================

  -- The base-field query domain point x. `index_bits` = low-`log_height` index
  -- bits, LSB first (so reverse_bits_len = reversing the list).
  fn ro_x(index_bits: List‹G›, log_height: G) -> Goldilocks {
    gl_mul(gl_seven(), exp_by_bits(two_adic_gen(log_height), glist_rev(index_bits, store(ListNode.Nil))))
  }

  -- Raw wire rows (`U64` lanes, possibly non-canonical) to native Goldilocks
  -- values for the reduced-opening arithmetic (`limb_to_field` reduces mod p).
  fn lanes_to_gl(l: List‹U64›) -> List‹Goldilocks› {
    match load(l) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(x, rest) => store(ListNode.Cons(limb_to_field(x), lanes_to_gl(rest))),
    }
  }

  -- Accumulate one matrix-point's column contributions. `q = 1/(z − x)`.
  fn ro_fold(p_x: List‹Goldilocks›, p_z: List‹Ext›, q: Ext, alpha: Ext, ro: Ext, ap: Ext)
      -> (Ext, Ext) {
    match load(p_x) {
      ListNode.Nil => (ro, ap),
      ListNode.Cons(px, pxr) =>
        let &ListNode.Cons(pz, pzr) = p_z;
        let term = eg_mul(eg_mul(ap, eg_sub(pz, [px, gl_zero()])), q);
        ro_fold(pxr, pzr, q, alpha, eg_add(ro, term), eg_mul(ap, alpha)),
    }
  }

  -- ==========================================================================
  -- PCS (FRI) verification — `two_adic_pcs::verify` + `fri::verify_fri`.
  --
  -- Specialised to `innerFri`: arity 2 (log_arity = 1 every round),
  -- log_blowup = 1, log_final_poly_len = 0 (final_poly is ONE constant
  -- coefficient ⇒ the final Horner eval is just `final_poly[0]`, no `x` needed),
  -- num_queries = 1, commit/query PoW bits = 0 (a challenger no-op). Field
  -- arithmetic is the non-native byte Goldilocks (`gl_*`/`eg_*`).
  --
  -- A reduced-opening accumulator, one per distinct log-height. `alpha_pow`
  -- threads across every (batch, matrix, point, column) at that height, in the
  -- prover's observation order (stage_1, stage_2, quotient, preprocessed).
  -- ==========================================================================
  enum Bucket { Mk(G, Ext, Ext) }   -- log_height, alpha_pow, reduced_opening

  -- ── challenger: observe the opened values (observe_algebra_slice) ──────────
  -- Built with the PREPEND helpers (`b8_onto` composition, O(1) per element),
  -- front-to-back, so the whole observation batch costs one `list_concat` at
  -- the end. Appending item-by-item onto the accumulated input (`snoc_b8`)
  -- re-walks and rebuilds the entire buffer per observation — quadratic in
  -- transcript size; at kernel scale the opened-values batch alone made that
  -- billions of memory records.
  -- One ext element = its two base coordinates, each 8 LE bytes.
  fn ext_row_onto(row: List‹Ext›, tail: ByteStream) -> ByteStream {
    match load(row) {
      ListNode.Nil => tail,
      ListNode.Cons(e, rest) => b8_onto(gl_to_bytes(e[0]), b8_onto(gl_to_bytes(e[1]), ext_row_onto(rest, tail))),
    }
  }
  fn points_onto(pts: List‹List‹Ext››, tail: ByteStream) -> ByteStream {
    match load(pts) {
      ListNode.Nil => tail,
      ListNode.Cons(row, rest) => ext_row_onto(row, points_onto(rest, tail)),
    }
  }
  fn round_onto(round: OpenedRound, tail: ByteStream) -> ByteStream {
    match load(round) {
      ListNode.Nil => tail,
      ListNode.Cons(mat, rest) => points_onto(mat, round_onto(rest, tail)),
    }
  }
  fn prep_onto(prep_opt: PreprocessedOpt, tail: ByteStream) -> ByteStream {
    match prep_opt {
      PreprocessedOpt.NoPreprocessed => tail,
      PreprocessedOpt.SomePreprocessed(round) => round_onto(round, tail),
    }
  }
  -- Observe one Val (= 1) per FRI round, the variable-arity schedule.
  fn obs_log_arities(input: ByteStream, comms: List‹MerkleCap›) -> ByteStream {
    match load(comms) {
      ListNode.Nil => input,
      ListNode.Cons(_c, rest) =>
        obs_log_arities(snoc_b8(input, [1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]), rest),
    }
  }
  -- Per round: observe the commitment, then sample β (PoW bits = 0 ⇒ no-op).
  -- `GrindingChallenger::check_witness` for one commit round: when `bits > 0`,
  -- observe the PoW witness then sample `bits` bits and assert they are all zero
  -- (else InvalidPowWitness). Returns the post-PoW `(input, output)` so the
  -- immediately-following β sample continues the SAME hash stream (no observe in
  -- between). `bits == 0` is the short-circuit: no observe, no sample.
  fn pcs_commit_pow(input: ByteStream, witness: U64, bits: G) -> (ByteStream, ByteStream) {
    match bits {
      0 => (input, store(ListNode.Nil)),
      _ =>
        let (pbits, i1, o1) = ch_sample_bits(snoc_b8(input, witness), store(ListNode.Nil), bits);
        assert_eq!(bits_to_num(pbits), 0);
        (i1, o1),
    }
  }
  -- Per round: observe the commitment, run the commit-phase PoW check, then
  -- sample the folding challenge β (continuing the challenger past the PoW).
  fn pcs_betas(input: ByteStream, comms: List‹MerkleCap›, witnesses: List‹U64›, bits: G)
      -> (List‹Ext›, ByteStream) {
    match load(comms) {
      ListNode.Nil => (store(ListNode.Nil), input),
      ListNode.Cons(c, rest) =>
        let &ListNode.Cons(w, wrest) = witnesses;
        let (i1, o1) = pcs_commit_pow(snoc_cap(input, c), w, bits);
        let (b0, b1, i2, _o) = ch_sample_ext(i1, o1);
        let (bs, i3) = pcs_betas(i2, rest, wrest, bits);
        (store(ListNode.Cons([gl_val(b0), gl_val(b1)], bs)), i3),
    }
  }

  -- ── reduced-opening buckets ───────────────────────────────────────────────
  fn repeat_g(v: G, n: G) -> List‹G› {
    match n {
      0 => store(ListNode.Nil),
      _ => store(ListNode.Cons(v, repeat_g(v, n - 1))),
    }
  }
  -- 1 iff some circuit `i < rem` has log-height `log_degrees[i] + log_blowup == h`.
  fn circ_has_height(log_degrees: List‹U8›, log_blowup: G, rem: G, i: G, h: G) -> G {
    match rem {
      0 => 0,
      _ => match eq_zero(to_field(list_lookup(log_degrees, i)) + log_blowup - h) {
        1 => 1,
        _ => circ_has_height(log_degrees, log_blowup, rem - 1, i + 1, h),
      },
    }
  }
  -- One bucket per distinct log-height, built DESCENDING by counting `h` down
  -- from `log_global_max`. Each starts (alpha_pow = 1, reduced_opening = 0).
  fn build_buckets(log_degrees: List‹U8›, log_blowup: G, num_circuits: G, h: G) -> List‹Bucket› {
    match h {
      0 => store(ListNode.Nil),
      _ => match circ_has_height(log_degrees, log_blowup, num_circuits, 0, h) {
        0 => build_buckets(log_degrees, log_blowup, num_circuits, h - 1),
        _ => store(ListNode.Cons(
               Bucket.Mk(h, [gl_one(), gl_zero()], [gl_zero(), gl_zero()]),
               build_buckets(log_degrees, log_blowup, num_circuits, h - 1))),
      },
    }
  }
  -- Find the bucket at log-height `lh`, fold one matrix-point's columns into it
  -- (`ro_fold` threads its `alpha_pow`), and write it back.
  fn bucket_update(buckets: List‹Bucket›, lh: G, p_x: List‹Goldilocks›, p_z: List‹Ext›,
      q: Ext, alpha: Ext) -> List‹Bucket› {
    match load(buckets) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(b, rest) =>
        let Bucket.Mk(h, ap, ro) = b;
        match eq_zero(h - lh) {
          1 =>
            let (ro2, ap2) = ro_fold(p_x, p_z, q, alpha, ro, ap);
            store(ListNode.Cons(Bucket.Mk(h, ap2, ro2), rest)),
          _ => store(ListNode.Cons(b, bucket_update(rest, lh, p_x, p_z, q, alpha))),
        },
    }
  }
  -- A bucket at log-height `log_blowup` would come from a trace matrix of height
  -- 1 (a constant polynomial); then `(f(ζ) − f(x))/(ζ − x)` must be 0. Assert it
  -- (`open_input`'s `FinalPolyMismatch` guard). No-op if no such bucket exists.
  fn assert_blowup_zero(buckets: List‹Bucket›, log_blowup: G) -> G {
    match load(buckets) {
      ListNode.Nil => 1,
      ListNode.Cons(b, rest) =>
        let Bucket.Mk(h, _ap, ro) = b;
        match eq_zero(h - log_blowup) {
          1 => assert_eq!(eg_eq(ro, [gl_zero(), gl_zero()]), 1); 1,
          _ => assert_blowup_zero(rest, log_blowup),
        },
    }
  }
  -- 1 iff the proof carries a preprocessed opened round (used for the input-proof
  -- batch-count check).
  fn prep_count(prep_opt: PreprocessedOpt) -> G {
    match prep_opt {
      PreprocessedOpt.NoPreprocessed => 0,
      PreprocessedOpt.SomePreprocessed(_r) => 1,
    }
  }
  -- Compute x = GENERATOR·g^{revbits} for this height and fold the contribution.
  fn ri_apply(buckets: List‹Bucket›, lh: G, idxbits: List‹G›, log_gmax: G,
      z: Ext, p_x: List‹Goldilocks›, p_z: List‹Ext›, alpha: Ext) -> List‹Bucket› {
    -- the base opening and the ext opening at this point must have equal width
    -- (PointEvaluationCountMismatch); `ro_fold` walks them in lockstep.
    assert_eq!(eq_zero(list_length(p_x) - list_length(p_z)), 1);
    let x = ro_x(list_drop(idxbits, log_gmax - lh), lh);
    let q = eg_inverse(eg_sub(z, [x, gl_zero()]));
    bucket_update(buckets, lh, p_x, p_z, q, alpha)
  }

  -- A stage_1/stage_2/preprocessed-style matrix: two opening points
  -- (ζ, ζ·g) with the same base row `p_x`. `g` = trace subgroup generator.
  fn open_2pt_mat(buckets: List‹Bucket›, idxbits: List‹G›, log_gmax: G, lh: G,
      ldeg: G, zeta: Ext, p_x: List‹Goldilocks›, mat: List‹List‹Ext››, alpha: Ext)
      -> List‹Bucket› {
    let pz0 = list_lookup(mat, 0);
    let pz1 = list_lookup(mat, 1);
    let zn = eg_mul(zeta, [two_adic_gen(ldeg), gl_zero()]);
    let b1 = ri_apply(buckets, lh, idxbits, log_gmax, zeta, p_x, pz0, alpha);
    ri_apply(b1, lh, idxbits, log_gmax, zn, p_x, pz1, alpha)
  }
  fn open_batch_2pt(buckets: List‹Bucket›, idxbits: List‹G›, log_gmax: G, log_blowup: G, ci: G,
      rem: G, log_degrees: List‹U8›, zeta: Ext, base_rows: List‹List‹U64››,
      opened: OpenedRound, alpha: Ext) -> List‹Bucket› {
    match rem {
      0 => buckets,
      _ =>
        let ldeg = to_field(list_lookup(log_degrees, ci));
        let b = open_2pt_mat(buckets, idxbits, log_gmax, ldeg + log_blowup, ldeg, zeta,
                  lanes_to_gl(list_lookup(base_rows, ci)), list_lookup(opened, ci), alpha);
        open_batch_2pt(b, idxbits, log_gmax, log_blowup, ci + 1, rem - 1, log_degrees, zeta,
                       base_rows, opened, alpha),
    }
  }

  -- The quotient batch: `qd` chunks per circuit, one opening point (ζ) each.
  fn open_q_chunks(buckets: List‹Bucket›, idxbits: List‹G›, log_gmax: G, lh: G,
      chunk: G, qrem: G, zeta: Ext, base_rows: List‹List‹U64››,
      q_opened: OpenedRound, alpha: Ext) -> (List‹Bucket›, G) {
    match qrem {
      0 => (buckets, chunk),
      _ =>
        let b = ri_apply(buckets, lh, idxbits, log_gmax, zeta,
                  lanes_to_gl(list_lookup(base_rows, chunk)), list_lookup(list_lookup(q_opened, chunk), 0), alpha);
        open_q_chunks(b, idxbits, log_gmax, lh, chunk + 1, qrem - 1, zeta, base_rows, q_opened, alpha),
    }
  }
  fn open_quotient(buckets: List‹Bucket›, idxbits: List‹G›, log_gmax: G, log_blowup: G, ci: G,
      rem: G, chunk: G, circuits: List‹SysCircuit›, log_degrees: List‹U8›, zeta: Ext,
      base_rows: List‹List‹U64››, q_opened: OpenedRound, alpha: Ext) -> List‹Bucket› {
    match rem {
      0 => buckets,
      _ =>
        let SysCircuit.Mk(_a, _cc, md, _ph, _pw, _w1, _w2) = list_lookup(circuits, ci);
        let qd = quotient_degree_of(md);
        let lh = to_field(list_lookup(log_degrees, ci)) + log_blowup;
        let (b, chunk2) = open_q_chunks(buckets, idxbits, log_gmax, lh, chunk, qd, zeta, base_rows, q_opened, alpha);
        open_quotient(b, idxbits, log_gmax, log_blowup, ci + 1, rem - 1, chunk2, circuits, log_degrees, zeta, base_rows, q_opened, alpha),
    }
  }

  -- The preprocessed batch: only circuits with `prep_indices[i] = Some(j)`;
  -- `k` tracks the position in the preprocessed commitment (= base-row index).
  fn open_prep(buckets: List‹Bucket›, idxbits: List‹G›, log_gmax: G, log_blowup: G, ci: G, rem: G,
      k: G, log_degrees: List‹U8›, prep_indices: List‹OptIdx›, zeta: Ext,
      base_rows: List‹List‹U64››, prep_round: OpenedRound, alpha: Ext) -> List‹Bucket› {
    match rem {
      0 => buckets,
      _ => match list_lookup(prep_indices, ci) {
        OptIdx.NoIdx =>
          open_prep(buckets, idxbits, log_gmax, log_blowup, ci + 1, rem - 1, k, log_degrees,
                    prep_indices, zeta, base_rows, prep_round, alpha),
        OptIdx.SomeIdx(_j) =>
          let ldeg = to_field(list_lookup(log_degrees, ci));
          let b = open_2pt_mat(buckets, idxbits, log_gmax, ldeg + log_blowup, ldeg, zeta,
                    lanes_to_gl(list_lookup(base_rows, k)), list_lookup(prep_round, k), alpha);
          open_prep(b, idxbits, log_gmax, log_blowup, ci + 1, rem - 1, k + 1, log_degrees,
                    prep_indices, zeta, base_rows, prep_round, alpha),
      },
    }
  }
  fn open_prep_batch(buckets: List‹Bucket›, input_proof: List‹BatchOpening›,
      prep_commit: MerkleCap, prep_opt: PreprocessedOpt, prep_indices: List‹OptIdx›,
      log_degrees: List‹U8›, num_circuits: G, idxbits: List‹G›, log_gmax: G, log_blowup: G,
      zeta: Ext, alpha: Ext) -> List‹Bucket› {
    match prep_opt {
      PreprocessedOpt.NoPreprocessed => buckets,
      PreprocessedOpt.SomePreprocessed(prep_round) =>
        let BatchOpening.Mk(rows_p, proof_p) = list_lookup(input_proof, 3);
        -- one opened base row per preprocessed matrix (BatchOpenedValuesCountMismatch)
        assert_eq!(eq_zero(list_length(rows_p) - list_length(prep_round)), 1);
        assert_eq!(mmcs_verify(prep_commit, rows_p,
          heights_prep(log_degrees, log_blowup, prep_indices, num_circuits, 0), idxbits, proof_p, log_gmax), 1);
        open_prep(buckets, idxbits, log_gmax, log_blowup, 0, num_circuits, 0, log_degrees,
                  prep_indices, zeta, rows_p, prep_round, alpha),
    }
  }

  -- ── per-batch input-MMCS matrix log-heights (`log_degree + log_blowup`) ────
  fn heights_all(log_degrees: List‹U8›, log_blowup: G, rem: G, i: G) -> List‹G› {
    match rem {
      0 => store(ListNode.Nil),
      _ => store(ListNode.Cons(to_field(list_lookup(log_degrees, i)) + log_blowup,
                               heights_all(log_degrees, log_blowup, rem - 1, i + 1))),
    }
  }
  fn heights_quotient(circuits: List‹SysCircuit›, log_degrees: List‹U8›, log_blowup: G, rem: G, i: G) -> List‹G› {
    match rem {
      0 => store(ListNode.Nil),
      _ =>
        let SysCircuit.Mk(_a, _cc, md, _ph, _pw, _w1, _w2) = list_lookup(circuits, i);
        list_concat(repeat_g(to_field(list_lookup(log_degrees, i)) + log_blowup, quotient_degree_of(md)),
                    heights_quotient(circuits, log_degrees, log_blowup, rem - 1, i + 1)),
    }
  }
  fn heights_prep(log_degrees: List‹U8›, log_blowup: G, prep_indices: List‹OptIdx›, rem: G, i: G) -> List‹G› {
    match rem {
      0 => store(ListNode.Nil),
      _ => match list_lookup(prep_indices, i) {
        OptIdx.NoIdx => heights_prep(log_degrees, log_blowup, prep_indices, rem - 1, i + 1),
        OptIdx.SomeIdx(_j) =>
          store(ListNode.Cons(to_field(list_lookup(log_degrees, i)) + log_blowup,
                              heights_prep(log_degrees, log_blowup, prep_indices, rem - 1, i + 1))),
      },
    }
  }

  -- ── FRI fold chain (`verify_query`, arity 2) ──────────────────────────────
  -- Reconstruct the sibling pair: evals[index_in_group] = folded, other = sib.
  fn recon_evals(bit: G, folded: Ext, sib: Ext) -> (Ext, Ext) {
    match bit {
      0 => (folded, sib),
      _ => (sib, folded),
    }
  }
  -- Flatten two ext evals to the 4 base coords of the ExtensionMmcs leaf row.
  fn flatten2(e0: Ext, e1: Ext) -> List‹U64› {
    store(ListNode.Cons(gl_to_bytes(e0[0]), store(ListNode.Cons(gl_to_bytes(e0[1]),
      store(ListNode.Cons(gl_to_bytes(e1[0]), store(ListNode.Cons(gl_to_bytes(e1[1]), store(ListNode.Nil)))))))))
  }
  -- Roll the next reduced opening into the folded eval when its height matches
  -- the new folded height: `folded += beta^(2^log_arity) · ro`  (log_arity = 1).
  fn rollin(folded: Ext, log_folded: G, beta: Ext, ro_rest: List‹Bucket›) -> (Ext, List‹Bucket›) {
    match load(ro_rest) {
      ListNode.Nil => (folded, ro_rest),
      ListNode.Cons(b, rest) =>
        let Bucket.Mk(h, _ap, ro) = b;
        match eq_zero(h - log_folded) {
          1 => (eg_add(folded, eg_mul(ext_exp_pow2(beta, 1), ro)), rest),
          _ => (folded, ro_rest),
        },
    }
  }
  fn verify_query(folded: Ext, betas: List‹Ext›, comms: List‹MerkleCap›,
      openings: List‹CommitPhaseProofStep›, domidx: List‹G›, log_cur: G,
      ro_rest: List‹Bucket›, log_final: G) -> Ext {
    match load(openings) {
      ListNode.Nil =>
        -- must have folded down to exactly the final domain size, and every
        -- reduced opening must have been rolled in (FinalFoldHeightMismatch /
        -- UnconsumedReducedOpenings).
        assert_eq!(eq_zero(log_cur - log_final), 1);
        assert_eq!(list_length(ro_rest), 0);
        folded,
      ListNode.Cons(op, op_rest) =>
        let &ListNode.Cons(beta, beta_rest) = betas;
        let &ListNode.Cons(comm, comm_rest) = comms;
        let CommitPhaseProofStep.Mk(_la, sibs, oproof) = op;
        -- arity 2 ⇒ exactly arity-1 = 1 sibling (SiblingValuesLengthMismatch).
        assert_eq!(list_length(sibs), 1);
        let &ListNode.Cons(ibit, idrest) = domidx;     -- index_in_group = LSB
        let log_folded = log_cur - 1;
        let (e0, e1) = recon_evals(ibit, folded, list_lookup(sibs, 0));
        -- authenticate the sibling pair against this round's commitment
        assert_eq!(mmcs_verify(comm, store(ListNode.Cons(flatten2(e0, e1), store(ListNode.Nil))),
          store(ListNode.Cons(log_folded, store(ListNode.Nil))), idrest, oproof, log_folded), 1);
        let folded1 = fri_fold2(idrest, log_folded, beta, e0, e1);
        let (folded2, ro_rest2) = rollin(folded1, log_folded, beta, ro_rest);
        verify_query(folded2, beta_rest, comm_rest, op_rest, idrest, log_folded, ro_rest2, log_final),
    }
  }

  -- ── one FRI query ─────────────────────────────────────────────────────────
  -- For the query index `idxbits`: build the reduced-opening accumulators,
  -- authenticate each input batch (input MMCS), run the fold chain, and check
  -- the final polynomial. `log_final = log_blowup` (log_final_poly_len = 0).
  fn verify_one_query(idxbits: List‹G›, qp: QueryProof, alpha: Ext,
      stage1: OpenedRound, stage2: OpenedRound, q_opened: OpenedRound,
      prep_opt: PreprocessedOpt, s1c: MerkleCap, s2c: MerkleCap, qc: MerkleCap,
      prep_commit: MerkleCap, circuits: List‹SysCircuit›, prep_indices: List‹OptIdx›,
      log_degrees: List‹U8›, zeta: Ext, num_circuits: G, log_blowup: G, log_gmax: G,
      betas: List‹Ext›, commit_phase_commits: List‹MerkleCap›, final_poly: List‹Ext›,
      num_rounds: G) -> G {
    let QueryProof.Mk(input_proof, commit_phase_openings) = qp;
    -- one commit-phase opening per round (QueryCommitPhaseOpeningsCountMismatch),
    -- one input batch per commitment (InputProofBatchCountMismatch).
    assert_eq!(eq_zero(list_length(commit_phase_openings) - num_rounds), 1);
    assert_eq!(eq_zero(list_length(input_proof) - (3 + prep_count(prep_opt))), 1);
    let buckets = build_buckets(log_degrees, log_blowup, num_circuits, log_gmax);
    let BatchOpening.Mk(rows_s1, proof_s1) = list_lookup(input_proof, 0);
    assert_eq!(eq_zero(list_length(rows_s1) - num_circuits), 1);
    assert_eq!(mmcs_verify(s1c, rows_s1, heights_all(log_degrees, log_blowup, num_circuits, 0), idxbits, proof_s1, log_gmax), 1);
    let buckets = open_batch_2pt(buckets, idxbits, log_gmax, log_blowup, 0, num_circuits, log_degrees, zeta, rows_s1, stage1, alpha);
    let BatchOpening.Mk(rows_s2, proof_s2) = list_lookup(input_proof, 1);
    assert_eq!(eq_zero(list_length(rows_s2) - num_circuits), 1);
    assert_eq!(mmcs_verify(s2c, rows_s2, heights_all(log_degrees, log_blowup, num_circuits, 0), idxbits, proof_s2, log_gmax), 1);
    let buckets = open_batch_2pt(buckets, idxbits, log_gmax, log_blowup, 0, num_circuits, log_degrees, zeta, rows_s2, stage2, alpha);
    let BatchOpening.Mk(rows_q, proof_q) = list_lookup(input_proof, 2);
    assert_eq!(eq_zero(list_length(rows_q) - list_length(q_opened)), 1);
    assert_eq!(mmcs_verify(qc, rows_q, heights_quotient(circuits, log_degrees, log_blowup, num_circuits, 0), idxbits, proof_q, log_gmax), 1);
    let buckets = open_quotient(buckets, idxbits, log_gmax, log_blowup, 0, num_circuits, 0, circuits, log_degrees, zeta, rows_q, q_opened, alpha);
    let buckets = open_prep_batch(buckets, input_proof, prep_commit, prep_opt, prep_indices, log_degrees, num_circuits, idxbits, log_gmax, log_blowup, zeta, alpha);
    -- a height-`log_blowup` (constant-poly) reduced opening must be zero
    let _cz = assert_blowup_zero(buckets, log_blowup);
    -- the first reduced opening must sit at log_global_max_height
    -- (InitialReducedOpeningHeightMismatch).
    let &ListNode.Cons(b0, ro_rest) = buckets;
    let Bucket.Mk(h0, _ap0, folded_start) = b0;
    assert_eq!(eq_zero(h0 - log_gmax), 1);
    let folded = verify_query(folded_start, betas, commit_phase_commits, commit_phase_openings, idxbits, log_gmax, ro_rest, log_blowup);
    -- final check: with log_final_poly_len = 0, eval = final_poly[0]
    assert_eq!(eg_eq(list_lookup(final_poly, 0), folded), 1);
    1
  }

  -- Loop over all `num_queries` query proofs, sampling one index per query
  -- (consecutive `sample_bits` continue the same challenger stream).
  fn query_loop(input: ByteStream, output: ByteStream, query_proofs: List‹QueryProof›,
      alpha: Ext, stage1: OpenedRound, stage2: OpenedRound, q_opened: OpenedRound,
      prep_opt: PreprocessedOpt, s1c: MerkleCap, s2c: MerkleCap, qc: MerkleCap,
      prep_commit: MerkleCap, circuits: List‹SysCircuit›, prep_indices: List‹OptIdx›,
      log_degrees: List‹U8›, zeta: Ext, num_circuits: G, log_blowup: G, log_gmax: G,
      betas: List‹Ext›, commit_phase_commits: List‹MerkleCap›, final_poly: List‹Ext›,
      num_rounds: G) -> G {
    match load(query_proofs) {
      ListNode.Nil => 1,
      ListNode.Cons(qp, rest) =>
        let (idxbits, input2, output2) = ch_sample_bits(input, output, log_gmax);
        let _q = verify_one_query(idxbits, qp, alpha, stage1, stage2, q_opened, prep_opt,
          s1c, s2c, qc, prep_commit, circuits, prep_indices, log_degrees, zeta, num_circuits,
          log_blowup, log_gmax, betas, commit_phase_commits, final_poly, num_rounds);
        query_loop(input2, output2, rest, alpha, stage1, stage2, q_opened, prep_opt,
          s1c, s2c, qc, prep_commit, circuits, prep_indices, log_degrees, zeta, num_circuits,
          log_blowup, log_gmax, betas, commit_phase_commits, final_poly, num_rounds),
    }
  }

  -- ── top-level FRI verification ────────────────────────────────────────────
  -- `log_blowup` comes from the verifying key; `num_queries` / `commit_pow_bits`
  -- are the protocol's FRI parameters (public). `query_pow_bits` is taken to be 0
  -- (our system), so the query-phase grinding check is a no-op.
  fn pcs_fri_verify(post_zeta_input: ByteStream, stage1: OpenedRound, stage2: OpenedRound,
      q_opened: OpenedRound, prep_opt: PreprocessedOpt, opening: FriProof,
      s1c: MerkleCap, s2c: MerkleCap, qc: MerkleCap, prep_commit: MerkleCap,
      circuits: List‹SysCircuit›, prep_indices: List‹OptIdx›, log_degrees: List‹U8›,
      zeta: Ext, num_circuits: G, log_blowup: G, num_queries: G, commit_pow_bits: G) -> G {
    let FriProof.Mk(commit_phase_commits, pw, query_proofs, final_poly, _qpw) = opening;
    let num_rounds = list_length(commit_phase_commits);
    -- FRI shape: one PoW witness per round, num_queries query proofs, and (since
    -- log_final_poly_len = 0) a single final-poly coefficient.
    assert_eq!(eq_zero(list_length(pw) - num_rounds), 1);
    assert_eq!(eq_zero(list_length(query_proofs) - num_queries), 1);
    assert_eq!(list_length(final_poly), 1);
    -- challenger continuation: observe all opened values (coms_to_verify
    -- order), built as one front-to-back suffix + a single concat (the input
    -- is only ~32 bytes here — it collapses to the digest on every flush).
    let obs = round_onto(stage1, round_onto(stage2, round_onto(q_opened,
      prep_onto(prep_opt, store(ListNode.Nil)))));
    let input = list_concat(post_zeta_input, obs);
    -- PCS batch-combination challenge α
    let (a0, a1, input, _oa) = ch_sample_ext(input, store(ListNode.Nil));
    let alpha = [gl_val(a0), gl_val(a1)];
    -- per-round FRI fold challenges β (with commit-phase PoW), then observe
    -- final_poly + the log-arity schedule.
    let (betas, input) = pcs_betas(input, commit_phase_commits, pw, commit_pow_bits);
    let input = list_concat(input, ext_row_onto(final_poly, store(ListNode.Nil)));
    let input = obs_log_arities(input, commit_phase_commits);
    -- query indices + per-query verification (log_global_max_height = #rounds + log_blowup)
    let log_gmax = num_rounds + log_blowup;
    query_loop(input, store(ListNode.Nil), query_proofs, alpha, stage1, stage2, q_opened,
      prep_opt, s1c, s2c, qc, prep_commit, circuits, prep_indices, log_degrees, zeta,
      num_circuits, log_blowup, log_gmax, betas, commit_phase_commits, final_poly, num_rounds)
  }

⟧

end MultiStark

end
