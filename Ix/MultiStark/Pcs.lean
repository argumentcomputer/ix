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

  -- Canonicalize each lane: the MMCS leaf hash serializes `as_canonical_u64`,
  -- but opened base values are on the wire in the (possibly non-canonical)
  -- internal Goldilocks repr — e.g. field zero ships as `p`. `gl_reduce` maps
  -- them to `< p` before hashing (idempotent on already-canonical lanes).
  fn canon_lanes(l: List‹U64›) -> List‹U64› {
    match load(l) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(x, rest) => store(ListNode.Cons(gl_reduce(x), canon_lanes(rest))),
    }
  }
  -- The joint leaf hash of all matrices at log-height `target`.
  fn leaf_hash_at(rows: List‹List‹U64››, lhs: List‹G›, target: G) -> Digest {
    pf_sponge_u64(canon_lanes(concat_at(rows, lhs, target)))
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
  -- `base` is a non-native Goldilocks element; `bits` is a native bit list.
  fn exp_by_bits(base: [U8; 8], bits: List‹G›) -> [U8; 8] {
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

  -- Self-test: arity-2 fold at index 5, log_height 3 vs the `fri_fold_ref`
  -- reference (computed by the real `TwoAdicFriFolding::fold_row`).
  pub fn fri_fold_test() -> G {
    let index_bits = store(ListNode.Cons(1, store(ListNode.Cons(0,
                       store(ListNode.Cons(1, store(ListNode.Nil)))))));
    let e0 = [[17u8, 17u8, 17u8, 17u8, 17u8, 17u8, 17u8, 17u8],
              [34u8, 34u8, 34u8, 34u8, 34u8, 34u8, 34u8, 34u8]];
    let e1 = [[51u8, 51u8, 51u8, 51u8, 51u8, 51u8, 51u8, 51u8],
              [68u8, 68u8, 68u8, 68u8, 68u8, 68u8, 68u8, 68u8]];
    let beta = [[85u8, 85u8, 85u8, 85u8, 85u8, 85u8, 85u8, 85u8],
                [102u8, 102u8, 102u8, 102u8, 102u8, 102u8, 102u8, 102u8]];
    let folded = fri_fold2(index_bits, 3, beta, e0, e1);
    assert_eq!(limb_to_field(folded[0]), 9349172584842537206);
    assert_eq!(limb_to_field(folded[1]), 984486879173118962);
    1
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
  fn ro_x(index_bits: List‹G›, log_height: G) -> [U8; 8] {
    gl_mul(gl_seven(), exp_by_bits(two_adic_gen(log_height), glist_rev(index_bits, store(ListNode.Nil))))
  }

  -- Accumulate one matrix-point's column contributions. `q = 1/(z − x)`.
  fn ro_fold(p_x: List‹[U8; 8]›, p_z: List‹Ext›, q: Ext, alpha: Ext, ro: Ext, ap: Ext)
      -> (Ext, Ext) {
    match load(p_x) {
      ListNode.Nil => (ro, ap),
      ListNode.Cons(px, pxr) =>
        let &ListNode.Cons(pz, pzr) = p_z;
        let term = eg_mul(eg_mul(ap, eg_sub(pz, [px, gl_zero()])), q);
        ro_fold(pxr, pzr, q, alpha, eg_add(ro, term), eg_mul(ap, alpha)),
    }
  }

  -- Self-test vs `ro_fold_ref`: x at index 5 / log_height 3, then accumulate
  -- (p_z − p_x)/(z − x) over 3 columns with alpha powers.
  pub fn ro_fold_test() -> G {
    let index_bits = store(ListNode.Cons(1, store(ListNode.Cons(0,
                       store(ListNode.Cons(1, store(ListNode.Nil)))))));
    let x = ro_x(index_bits, 3);
    assert_eq!(limb_to_field(x), 117440512);
    let z = [[154u8, 120u8, 86u8, 52u8, 18u8, 0u8, 0u8, 0u8],
             [1u8, 239u8, 205u8, 171u8, 0u8, 0u8, 0u8, 0u8]];
    let alpha = [[17u8, 17u8, 17u8, 17u8, 17u8, 17u8, 17u8, 17u8],
                 [2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]];
    let px0 = [11u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
    let px1 = [22u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
    let px2 = [33u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
    let p_x = store(ListNode.Cons(px0, store(ListNode.Cons(px1,
                store(ListNode.Cons(px2, store(ListNode.Nil)))))));
    let pz0 = [[100u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], [1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]];
    let pz1 = [[200u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], [2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]];
    let pz2 = [[44u8, 1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], [3u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]];
    let p_z = store(ListNode.Cons(pz0, store(ListNode.Cons(pz1,
                store(ListNode.Cons(pz2, store(ListNode.Nil)))))));
    let q = eg_inverse(eg_sub(z, [x, gl_zero()]));
    let (ro, _ap) = ro_fold(p_x, p_z, q, alpha, [gl_zero(), gl_zero()], [gl_one(), gl_zero()]);
    assert_eq!(limb_to_field(ro[0]), 7130765474285082575);
    assert_eq!(limb_to_field(ro[1]), 12254464995725315436);
    1
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
  -- One ext element = its two base coordinates, each 8 LE bytes.
  fn obs_ext_row(input: ByteStream, row: List‹Ext›) -> ByteStream {
    match load(row) {
      ListNode.Nil => input,
      ListNode.Cons(e, rest) => obs_ext_row(snoc_b8(snoc_b8(input, e[0]), e[1]), rest),
    }
  }
  fn obs_points(input: ByteStream, pts: List‹List‹Ext››) -> ByteStream {
    match load(pts) {
      ListNode.Nil => input,
      ListNode.Cons(row, rest) => obs_points(obs_ext_row(input, row), rest),
    }
  }
  fn obs_round(input: ByteStream, round: OpenedRound) -> ByteStream {
    match load(round) {
      ListNode.Nil => input,
      ListNode.Cons(mat, rest) => obs_round(obs_points(input, mat), rest),
    }
  }
  fn obs_prep(input: ByteStream, prep_opt: PreprocessedOpt) -> ByteStream {
    match prep_opt {
      PreprocessedOpt.NoPreprocessed => input,
      PreprocessedOpt.SomePreprocessed(round) => obs_round(input, round),
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
        (store(ListNode.Cons([gl_reduce(b0), gl_reduce(b1)], bs)), i3),
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
  fn bucket_update(buckets: List‹Bucket›, lh: G, p_x: List‹[U8; 8]›, p_z: List‹Ext›,
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
      z: Ext, p_x: List‹[U8; 8]›, p_z: List‹Ext›, alpha: Ext) -> List‹Bucket› {
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
      ldeg: G, zeta: Ext, p_x: List‹[U8; 8]›, mat: List‹List‹Ext››, alpha: Ext)
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
                  list_lookup(base_rows, ci), list_lookup(opened, ci), alpha);
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
                  list_lookup(base_rows, chunk), list_lookup(list_lookup(q_opened, chunk), 0), alpha);
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
                    list_lookup(base_rows, k), list_lookup(prep_round, k), alpha);
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
    store(ListNode.Cons(e0[0], store(ListNode.Cons(e0[1],
      store(ListNode.Cons(e1[0], store(ListNode.Cons(e1[1], store(ListNode.Nil)))))))))
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
    -- challenger continuation: observe all opened values (coms_to_verify order)
    let input = obs_round(post_zeta_input, stage1);
    let input = obs_round(input, stage2);
    let input = obs_round(input, q_opened);
    let input = obs_prep(input, prep_opt);
    -- PCS batch-combination challenge α
    let (a0, a1, input, _oa) = ch_sample_ext(input, store(ListNode.Nil));
    let alpha = [gl_reduce(a0), gl_reduce(a1)];
    -- per-round FRI fold challenges β (with commit-phase PoW), then observe
    -- final_poly + the log-arity schedule.
    let (betas, input) = pcs_betas(input, commit_phase_commits, pw, commit_pow_bits);
    let input = obs_ext_row(input, final_poly);
    let input = obs_log_arities(input, commit_phase_commits);
    -- query indices + per-query verification (log_global_max_height = #rounds + log_blowup)
    let log_gmax = num_rounds + log_blowup;
    query_loop(input, store(ListNode.Nil), query_proofs, alpha, stage1, stage2, q_opened,
      prep_opt, s1c, s2c, qc, prep_commit, circuits, prep_indices, log_degrees, zeta,
      num_circuits, log_blowup, log_gmax, betas, commit_phase_commits, final_poly, num_rounds)
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
    -- LEAF22: full block + 5-element partial (two permutes), >20 lanes.
    let d22 = mmcs_hash_row(build_range(0, 22));
    assert_eq!(assert_digest(d22, 520358013996801752, 12301199992631688477,
      8732686820159480415, 10883226686987971725), 1);
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
