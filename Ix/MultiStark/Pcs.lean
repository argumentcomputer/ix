module
public import Ix.Aiur.Meta
public import Ix.MultiStark.Deserialize
public import Ix.MultiStark.Keccak

/-!
# PCS (FRI) verification

`multi-stark/src/verifier.rs` calls `pcs.verify(coms_to_verify, opening_proof,
&mut challenger)` — a `TwoAdicFriPcs` FRI verification: query openings, Merkle
authentication paths, FRI folding consistency. This is the heaviest part of the
verifier and is being ported here in stages.

## Stage 1 — Merkle (MMCS) hash primitives (this file, done + validated)

The input/commit-phase commitments are `MerkleTreeMmcs` over the keccak hasher
configured in `multi-stark/src/types.rs`:

* leaf hash  : `SerializingHasher<PaddingFreeSponge<KeccakF, 25, 17, 4>>`
  — serialize each `Goldilocks` element to its canonical `u64`, then run a
  padding-free **overwrite-mode** sponge (rate 17 lanes, capacity 8, output 4)
  built on the keccak-f[1600] permutation (reused from `Keccak.lean`).
* compression: `CompressionFunctionFromHasher<PaddingFreeSponge<…>, 2, 4>`
  — hash the 8 lanes of two concatenated digests into a 4-lane digest.

`PaddingFreeSponge` differs from keccak-256 (`Keccak.lean`): no `10*1` padding,
rate 17 *lanes* (not 136 bytes), and each input block **overwrites** the rate
region (keccak-256 XORs). A full block triggers a permute; a final partial block
permutes once iff it absorbed ≥1 element; an empty trailing block does not
permute.

Validated against `multi-stark`'s own hasher (see `pcs_hash_test`, reference
values from the `pcs_ref_values` test in `multi-stark/src/types.rs`).

## Stage 2+ — TODO

Merkle `verify_batch` (binary tree, multi-height injection), challenger
threading, the FRI fold chain (`open_input` / `verify_query`), and the final
polynomial check. Until those land, `pcs_verify` remains an accept-stub.
-/

public section

namespace MultiStark

def pcs := ⟦
  -- ==========================================================================
  -- PaddingFreeSponge<KeccakF, 25, 17, 4> in overwrite mode.
  --
  -- Lanes are the keccak `Lane` type (`&[U8; 8]`, LE). A `U64` opened value is
  -- (for an honest, canonical proof) exactly the 8 LE bytes of a lane, so a lane
  -- is just `store(u64)`. The 25-lane keccak `State` and `keccak_f_fold` are
  -- reused from `Keccak.lean`.
  -- ==========================================================================

  -- Take one input element as the next rate lane, or keep the existing state
  -- lane `dflt` when the input is exhausted. The flag is 1 iff an input element
  -- was consumed (input is consumed front-to-back, so the per-block flags are a
  -- run of 1s followed by 0s).
  fn u64_pick(vals: List‹U64›, dflt: Lane) -> (Lane, List‹U64›, G) {
    match load(vals) {
      ListNode.Nil => (dflt, vals, 0),
      ListNode.Cons(x, rest) => (store(x), rest, 1),
    }
  }

  -- Absorb the input lanes into the state, 17 (= RATE) at a time, overwriting
  -- the rate region. After a FULL block of 17, permute and continue. A final
  -- partial block (1..16 elements) permutes once; an exactly-empty trailing
  -- block does not permute (matches `PaddingFreeSponge::hash_iter`).
  fn pf_absorb(sp: State, vals: List‹U64›) -> State {
    let old = load(sp);
    let (l0,  v1,  f0)  = u64_pick(vals, old[0]);
    let (l1,  v2,  _f1) = u64_pick(v1,  old[1]);
    let (l2,  v3,  _f2) = u64_pick(v2,  old[2]);
    let (l3,  v4,  _f3) = u64_pick(v3,  old[3]);
    let (l4,  v5,  _f4) = u64_pick(v4,  old[4]);
    let (l5,  v6,  _f5) = u64_pick(v5,  old[5]);
    let (l6,  v7,  _f6) = u64_pick(v6,  old[6]);
    let (l7,  v8,  _f7) = u64_pick(v7,  old[7]);
    let (l8,  v9,  _f8) = u64_pick(v8,  old[8]);
    let (l9,  v10, _f9) = u64_pick(v9,  old[9]);
    let (l10, v11, _fa) = u64_pick(v10, old[10]);
    let (l11, v12, _fb) = u64_pick(v11, old[11]);
    let (l12, v13, _fc) = u64_pick(v12, old[12]);
    let (l13, v14, _fd) = u64_pick(v13, old[13]);
    let (l14, v15, _fe) = u64_pick(v14, old[14]);
    let (l15, v16, _ff) = u64_pick(v15, old[15]);
    let (l16, v17, f16) = u64_pick(v16, old[16]);
    let sp2 = store([l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13,
                     l14, l15, l16, old[17], old[18], old[19], old[20], old[21],
                     old[22], old[23], old[24]]);
    match f16 {
      1 => pf_absorb(keccak_f_fold(sp2, 24), v17),
      _ => match f0 {
        0 => sp2,
        _ => keccak_f_fold(sp2, 24),
      },
    }
  }

  -- Hash a list of `u64` lanes (a serialized field-element row, or two
  -- concatenated digests) into a 4-lane `Digest`.
  fn pf_sponge_u64(vals: List‹U64›) -> Digest {
    let z = store([0u8; 8]);
    let init = store([z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z,
                      z, z, z, z, z]);
    let sp = pf_absorb(init, vals);
    let s = load(sp);
    [load(s[0]), load(s[1]), load(s[2]), load(s[3])]
  }

  -- The MMCS leaf hash of a single matrix row (`SerializingHasher` over the row
  -- of canonical `u64`s). For a leaf joining several same-height matrices, the
  -- rows are concatenated first (see `verify_batch`, future work).
  fn mmcs_hash_row(row: List‹U64›) -> Digest {
    pf_sponge_u64(row)
  }

  -- The MMCS 2-to-1 compression: hash the 8 lanes of two concatenated digests.
  fn mmcs_compress(a: Digest, b: Digest) -> Digest {
    let t0 = store(ListNode.Nil);
    let t1 = store(ListNode.Cons(b[3], t0));
    let t2 = store(ListNode.Cons(b[2], t1));
    let t3 = store(ListNode.Cons(b[1], t2));
    let t4 = store(ListNode.Cons(b[0], t3));
    let t5 = store(ListNode.Cons(a[3], t4));
    let t6 = store(ListNode.Cons(a[2], t5));
    let t7 = store(ListNode.Cons(a[1], t6));
    let t8 = store(ListNode.Cons(a[0], t7));
    pf_sponge_u64(t8)
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

  -- The joint leaf hash of all matrices at log-height `target`.
  fn leaf_hash_at(rows: List‹List‹U64››, lhs: List‹G›, target: G) -> Digest {
    pf_sponge_u64(concat_at(rows, lhs, target))
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
  -- PCS verification entry (STILL A STUB).
  -- Accepts any FRI opening proof. A real implementation will check query
  -- openings, Merkle paths (via `mmcs_*` above) and the FRI folding against the
  -- committed roots and the (threaded) Fiat-Shamir challenger.
  -- ==========================================================================
  fn pcs_verify(opening: FriProof) -> G {
    1
  }

  -- ==========================================================================
  -- Self-test (validation): the keccak MMCS sponge/compression against
  -- reference values from `multi-stark`'s own hasher (`pcs_ref_values`).
  -- Compares each output lane mod p via `limb_to_field` (all reference lanes are
  -- canonical, so this is exact).
  -- ==========================================================================

  -- A small single-byte value as a `U64` (8 LE bytes).
  fn u64_of(b: U8) -> U64 {
    [b, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]
  }
  -- `[i+1, i+2, …, n]` as a `List‹U64›`.
  fn build_range(i: G, n: G) -> List‹U64› {
    match n - i {
      0 => store(ListNode.Nil),
      _ => store(ListNode.Cons(u64_of(u8_from_field_unsafe(i + 1)), build_range(i + 1, n))),
    }
  }
  fn assert_digest(d: Digest, e0: G, e1: G, e2: G, e3: G) -> G {
    assert_eq!(limb_to_field(d[0]), e0);
    assert_eq!(limb_to_field(d[1]), e1);
    assert_eq!(limb_to_field(d[2]), e2);
    assert_eq!(limb_to_field(d[3]), e3);
    1
  }
  pub fn pcs_hash_test() -> G {
    -- LEAF3: hash([1,2,3])
    let d3 = mmcs_hash_row(build_range(0, 3));
    assert_eq!(assert_digest(d3, 0xc55a6a1beaea9fec, 0xc8f0dbc4c59ec440,
                                 0xacb1295de9bfe032, 0x445d569d3dfc9543), 1);
    -- LEAF17: exactly one full block, no extra permute.
    let d17 = mmcs_hash_row(build_range(0, 17));
    assert_eq!(assert_digest(d17, 0x388da73622e8fdd5, 0xec687be9c50d2218,
                                  0x528d145dfe6571af, 0xd2eb808dfba4703c), 1);
    -- LEAF20: full block + 3-element partial (two permutes).
    let d20 = mmcs_hash_row(build_range(0, 20));
    assert_eq!(assert_digest(d20, 0xec696847be88d358, 0x202861c67ff4cec8,
                                  0x88e006a48aaa0661, 0xabaddb9d32ecd024), 1);
    -- COMPRESS([1,2,3,4],[5,6,7,8])
    let c = mmcs_compress([u64_of(1u8), u64_of(2u8), u64_of(3u8), u64_of(4u8)],
                          [u64_of(5u8), u64_of(6u8), u64_of(7u8), u64_of(8u8)]);
    assert_eq!(assert_digest(c, 0xda1ef0642722b22e, 0x4851efdbdb2a2fd8,
                                0x37e8ff900ea95d47, 0xa153eee7805376fb), 1);
    1
  }

  -- Merkle `verify_batch` self-test against the `pcs_merkle_ref` reference: a
  -- cap-height-0 tree over 3 matrices of heights 8/4/2 (log-heights 3/2/1),
  -- opened at index 5 (path bits 1,0,1). Checks the recomputed root matches the
  -- committed root and that the cap index is 0, then that a tampered opened row
  -- yields a different (rejected) root.
  pub fn pcs_merkle_test() -> G {
    -- opened rows (matrix order): m0 row5, m1 row2, m2 row1.
    let row0 = store(ListNode.Cons(u64_of(11u8), store(ListNode.Cons(u64_of(12u8), store(ListNode.Nil)))));
    let row1 = store(ListNode.Cons(u64_of(107u8), store(ListNode.Cons(u64_of(108u8),
                 store(ListNode.Cons(u64_of(109u8), store(ListNode.Nil)))))));
    let row2 = store(ListNode.Cons(u64_of(202u8), store(ListNode.Nil)));
    let rows = store(ListNode.Cons(row0, store(ListNode.Cons(row1,
                 store(ListNode.Cons(row2, store(ListNode.Nil)))))));
    -- log-heights and path bits (index 5 = 0b101, LSB first).
    let lhs = store(ListNode.Cons(3, store(ListNode.Cons(2, store(ListNode.Cons(1, store(ListNode.Nil)))))));
    let ibits = store(ListNode.Cons(1, store(ListNode.Cons(0, store(ListNode.Cons(1, store(ListNode.Nil)))))));
    -- authentication path SIB0, SIB1, SIB2 (each a Digest = [U64; 4]).
    let sib0 = [[9u8, 36u8, 179u8, 127u8, 205u8, 83u8, 105u8, 203u8],
                [95u8, 229u8, 105u8, 223u8, 113u8, 55u8, 97u8, 122u8],
                [135u8, 8u8, 65u8, 248u8, 163u8, 163u8, 68u8, 81u8],
                [9u8, 11u8, 20u8, 209u8, 10u8, 168u8, 151u8, 125u8]];
    let sib1 = [[227u8, 58u8, 255u8, 213u8, 77u8, 152u8, 42u8, 77u8],
                [113u8, 86u8, 2u8, 151u8, 97u8, 63u8, 58u8, 45u8],
                [228u8, 139u8, 228u8, 194u8, 182u8, 115u8, 107u8, 221u8],
                [248u8, 16u8, 30u8, 93u8, 176u8, 36u8, 205u8, 88u8]];
    let sib2 = [[236u8, 144u8, 115u8, 218u8, 140u8, 5u8, 86u8, 229u8],
                [95u8, 186u8, 252u8, 175u8, 21u8, 247u8, 153u8, 25u8],
                [113u8, 78u8, 92u8, 200u8, 212u8, 175u8, 247u8, 47u8],
                [78u8, 145u8, 206u8, 54u8, 175u8, 155u8, 165u8, 206u8]];
    let proof = store(ListNode.Cons(sib0, store(ListNode.Cons(sib1,
                  store(ListNode.Cons(sib2, store(ListNode.Nil)))))));
    let (root, capidx) = mmcs_root(rows, lhs, ibits, proof, 3);
    assert_eq!(capidx, 0);
    assert_eq!(assert_digest(root, 0x6211b9a1a116a006, 0x435ee98e1504880f,
                                   0x900c7274b9a215f, 0xf6e3aaac5dcd90bd), 1);
    -- tamper: perturb m0's first opened value → root must change.
    let bad0 = store(ListNode.Cons(u64_of(99u8), store(ListNode.Cons(u64_of(12u8), store(ListNode.Nil)))));
    let bad_rows = store(ListNode.Cons(bad0, store(ListNode.Cons(row1,
                     store(ListNode.Cons(row2, store(ListNode.Nil)))))));
    let cap = store(ListNode.Cons([[6u8, 160u8, 22u8, 161u8, 161u8, 185u8, 17u8, 98u8],
                                   [15u8, 136u8, 4u8, 21u8, 142u8, 233u8, 94u8, 67u8],
                                   [95u8, 33u8, 154u8, 75u8, 39u8, 199u8, 0u8, 9u8],
                                   [189u8, 144u8, 205u8, 93u8, 172u8, 170u8, 227u8, 246u8]],
                    store(ListNode.Nil)));
    assert_eq!(mmcs_verify(cap, rows, lhs, ibits, proof, 3), 1);
    assert_eq!(mmcs_verify(cap, bad_rows, lhs, ibits, proof, 3), 0);
    1
  }
⟧

end MultiStark

end
