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
⟧

end MultiStark

end
