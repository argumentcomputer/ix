module
public import Ix.Aiur.Meta
public import Ix.IxVM.Core
public import Ix.IxVM.ByteStream

/-!
# Multi-STARK proof deserializer (Aiur)

Aiur deserializer for `multi_stark::prover::Proof`, mirroring the hand-written
bincode reader in `multi-stark/src/manual_codec.rs` (`fn deserialize`). Only
the deserializer is ported (no serializer).

The wire format is bincode `standard().with_little_endian().with_fixed_int_encoding()`:

* every `Vec` / length prefix : `u64`, 8 bytes little-endian
* `Option`                    : 1 tag byte (`0` = None, `1` = Some), then value
* `u8`                        : 1 byte
* struct                      : fields in declaration order, no framing
* `[T; N]` / tuple            : N elements back-to-back, no length prefix
* `Val` (Goldilocks)          : raw `u64`, 8 bytes LE (NOT reduced mod p)
* `ExtVal` (deg-2 ext)        : `[u64; 2]`, 16 bytes LE
* Merkle digest               : `[u64; 4]`, 32 bytes LE

`read_proof` builds a `Proof` object; `Ix/MultiStark.lean` hangs the entrypoint
(and eventual verification logic) off it.
-/

public section

namespace MultiStark

def deserialize := ⟦
  -- ==========================================================================
  -- Wire-level type mirrors of `multi-stark/src/manual_codec.rs`.
  -- `U64`/`ByteStream` come from `IxVM.byteStream`; raw Goldilocks `Val` is the
  -- non-canonical `u64`, kept here as the 8 little-endian bytes (`U64`).
  -- ==========================================================================

  -- `ExtVal = BinomialExtensionField<Goldilocks, 2> = 𝔽_p[X]/(X² - 7)`, stored
  -- as its two Goldilocks coefficients `[c0, c1]` (= `c0 + c1·X`). On the wire
  -- each is a raw `u64` limb; `read_ext` reduces it into a field element.
  type Ext = [G; 2]

  -- A Merkle digest: `[u64; DIGEST_ELEMS]` with `DIGEST_ELEMS = 4`.
  type Digest = [U64; 4]

  -- `Commitment = MerkleCap<..>`: only the `cap: Vec<Digest>` is on the wire.
  type MerkleCap = List‹Digest›

  -- `OpenedValuesForRound<ExtVal> = Vec<Vec<Vec<ExtVal>>>`.
  type OpenedRound = List‹List‹List‹Ext›››

  -- The three trace/quotient commitments at the head of a `Proof`.
  enum Commitments {
    Mk(MerkleCap, MerkleCap, MerkleCap)
  }

  -- `BatchOpening<Val, Mmcs>`: per-round input opening of a FRI query.
  --   opened_values : Vec<Vec<Val>>   (one row of base-field values per matrix)
  --   opening_proof : Vec<Digest>     (Merkle authentication path)
  enum BatchOpening {
    Mk(List‹List‹U64››, List‹Digest›)
  }

  -- `CommitPhaseProofStep<ExtVal, ExtMmcs>`: one folding step of a FRI query.
  --   log_arity      : u8
  --   sibling_values : Vec<Ext>  (arity - 1 siblings)
  --   opening_proof  : Vec<Digest>
  enum CommitPhaseProofStep {
    Mk(U8, List‹Ext›, List‹Digest›)
  }

  -- `QueryProof<ExtVal, ExtMmcs, Vec<BatchOpening<Val, Mmcs>>>`.
  enum QueryProof {
    Mk(List‹BatchOpening›, List‹CommitPhaseProofStep›)
  }

  -- `PcsProof = FriProof<ExtVal, ExtMmcs, Witness = Val, ..>`.
  --   commit_phase_commits : Vec<MerkleCap>
  --   commit_pow_witnesses : Vec<Val>
  --   query_proofs         : Vec<QueryProof>
  --   final_poly           : Vec<Ext>
  --   query_pow_witness    : Val
  enum FriProof {
    Mk(List‹MerkleCap›, List‹U64›, List‹QueryProof›, List‹Ext›, U64)
  }

  -- `Option<OpenedRound>` for `preprocessed_opened_values`. A dedicated
  -- non-generic enum keeps constructor inference unambiguous.
  enum PreprocessedOpt {
    NoPreprocessed,
    SomePreprocessed(OpenedRound)
  }

  -- Mirror of `multi_stark::prover::Proof`, in serialization order.
  enum Proof {
    Mk(
      Commitments,        -- commitments
      List‹Ext›,          -- intermediate_accumulators
      List‹U8›,           -- log_degrees
      FriProof,           -- opening_proof
      OpenedRound,        -- quotient_opened_values
      PreprocessedOpt,    -- preprocessed_opened_values
      OpenedRound,        -- stage_1_opened_values
      OpenedRound         -- stage_2_opened_values
    )
  }

  -- ==========================================================================
  -- Byte-reading primitives. Every reader threads the remaining `ByteStream`.
  -- ==========================================================================

  fn read_u8(stream: ByteStream) -> (U8, ByteStream) {
    match load(stream) {
      ListNode.Cons(byte, rest) => (byte, rest),
      ListNode.Nil => (0u8, store(ListNode.Nil)),
    }
  }

  -- One raw `u64`: 8 little-endian bytes, kept as `U64` (no field reduction).
  fn read_u64(stream: ByteStream) -> (U64, ByteStream) {
    let (b0, s0) = read_u8(stream);
    let (b1, s1) = read_u8(s0);
    let (b2, s2) = read_u8(s1);
    let (b3, s3) = read_u8(s2);
    let (b4, s4) = read_u8(s3);
    let (b5, s5) = read_u8(s4);
    let (b6, s6) = read_u8(s5);
    let (b7, s7) = read_u8(s6);
    ([b0, b1, b2, b3, b4, b5, b6, b7], s7)
  }

  -- A bincode length prefix: a fixed-width `u64`, flattened to a field count.
  -- `flatten_u64` asserts the top byte is zero (< 2^56), always true for the
  -- list lengths in a proof.
  fn read_count(stream: ByteStream) -> (G, ByteStream) {
    let (val, s) = read_u64(stream);
    (flatten_u64(val), s)
  }

  -- Interpret a raw little-endian `u64` limb as a Goldilocks field element. The
  -- field add/mul reduce mod p, so a non-canonical wire repr (e.g. `0` shipped
  -- as `p = 0xFFFFFFFF00000001`) maps to the canonical field element.
  fn limb_to_field(b: U64) -> G {
    to_field(b[0])
      + 0x100 * to_field(b[1])
      + 0x10000 * to_field(b[2])
      + 0x1000000 * to_field(b[3])
      + 0x100000000 * to_field(b[4])
      + 0x10000000000 * to_field(b[5])
      + 0x1000000000000 * to_field(b[6])
      + 0x100000000000000 * to_field(b[7])
  }

  -- `ExtVal` -> two `u64` limbs (no length prefix), reduced to field coefficients.
  fn read_ext(stream: ByteStream) -> (Ext, ByteStream) {
    let (a, s0) = read_u64(stream);
    let (b, s1) = read_u64(s0);
    ([limb_to_field(a), limb_to_field(b)], s1)
  }

  -- Extension-field addition: componentwise.
  fn ext_add(a: Ext, b: Ext) -> Ext {
    [a[0] + b[0], a[1] + b[1]]
  }

  -- Extension-field multiplication in 𝔽_p[X]/(X² - 7):
  --   (a0 + a1·X)(b0 + b1·X) = (a0·b0 + 7·a1·b1) + (a0·b1 + a1·b0)·X.
  fn ext_mul(a: Ext, b: Ext) -> Ext {
    [a[0] * b[0] + 7 * (a[1] * b[1]), a[0] * b[1] + a[1] * b[0]]
  }

  -- Merkle digest -> `[u64; 4]`, no length prefix.
  fn read_digest(stream: ByteStream) -> (Digest, ByteStream) {
    let (a, s0) = read_u64(stream);
    let (b, s1) = read_u64(s0);
    let (c, s2) = read_u64(s1);
    let (d, s3) = read_u64(s2);
    ([a, b, c, d], s3)
  }

  -- ==========================================================================
  -- Length-prefixed `Vec<T>` readers. First-order, so one pair per element
  -- type: `read_T_vec` reads the `u64` length then loops `read_T_vec_n`.
  -- ==========================================================================

  fn read_u8_vec(stream: ByteStream) -> (List‹U8›, ByteStream) {
    let (n, s) = read_count(stream);
    read_u8_vec_n(s, n)
  }
  fn read_u8_vec_n(stream: ByteStream, n: G) -> (List‹U8›, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), stream),
      _ =>
        let (x, s) = read_u8(stream);
        let (rest, s2) = read_u8_vec_n(s, n - 1);
        (store(ListNode.Cons(x, rest)), s2),
    }
  }

  fn read_u64_vec(stream: ByteStream) -> (List‹U64›, ByteStream) {
    let (n, s) = read_count(stream);
    read_u64_vec_n(s, n)
  }
  fn read_u64_vec_n(stream: ByteStream, n: G) -> (List‹U64›, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), stream),
      _ =>
        let (x, s) = read_u64(stream);
        let (rest, s2) = read_u64_vec_n(s, n - 1);
        (store(ListNode.Cons(x, rest)), s2),
    }
  }

  fn read_ext_vec(stream: ByteStream) -> (List‹Ext›, ByteStream) {
    let (n, s) = read_count(stream);
    read_ext_vec_n(s, n)
  }
  fn read_ext_vec_n(stream: ByteStream, n: G) -> (List‹Ext›, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), stream),
      _ =>
        let (x, s) = read_ext(stream);
        let (rest, s2) = read_ext_vec_n(s, n - 1);
        (store(ListNode.Cons(x, rest)), s2),
    }
  }

  fn read_digest_vec(stream: ByteStream) -> (List‹Digest›, ByteStream) {
    let (n, s) = read_count(stream);
    read_digest_vec_n(s, n)
  }
  fn read_digest_vec_n(stream: ByteStream, n: G) -> (List‹Digest›, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), stream),
      _ =>
        let (x, s) = read_digest(stream);
        let (rest, s2) = read_digest_vec_n(s, n - 1);
        (store(ListNode.Cons(x, rest)), s2),
    }
  }

  -- `Vec<Vec<Val>>` for `BatchOpening.opened_values`.
  fn read_u64_vec_vec(stream: ByteStream) -> (List‹List‹U64››, ByteStream) {
    let (n, s) = read_count(stream);
    read_u64_vec_vec_n(s, n)
  }
  fn read_u64_vec_vec_n(stream: ByteStream, n: G) -> (List‹List‹U64››, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), stream),
      _ =>
        let (x, s) = read_u64_vec(stream);
        let (rest, s2) = read_u64_vec_vec_n(s, n - 1);
        (store(ListNode.Cons(x, rest)), s2),
    }
  }

  -- `OpenedRound = Vec<Vec<Vec<Ext>>>`, built bottom-up from `read_ext_vec`.
  fn read_ext_vec_vec(stream: ByteStream) -> (List‹List‹Ext››, ByteStream) {
    let (n, s) = read_count(stream);
    read_ext_vec_vec_n(s, n)
  }
  fn read_ext_vec_vec_n(stream: ByteStream, n: G) -> (List‹List‹Ext››, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), stream),
      _ =>
        let (x, s) = read_ext_vec(stream);
        let (rest, s2) = read_ext_vec_vec_n(s, n - 1);
        (store(ListNode.Cons(x, rest)), s2),
    }
  }

  fn read_opened_round(stream: ByteStream) -> (OpenedRound, ByteStream) {
    let (n, s) = read_count(stream);
    read_opened_round_n(s, n)
  }
  fn read_opened_round_n(stream: ByteStream, n: G) -> (OpenedRound, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), stream),
      _ =>
        let (x, s) = read_ext_vec_vec(stream);
        let (rest, s2) = read_opened_round_n(s, n - 1);
        (store(ListNode.Cons(x, rest)), s2),
    }
  }

  -- ==========================================================================
  -- Struct readers (fields in declaration order, no framing).
  -- ==========================================================================

  fn read_merkle_cap(stream: ByteStream) -> (MerkleCap, ByteStream) {
    read_digest_vec(stream)
  }
  fn read_merkle_cap_vec(stream: ByteStream) -> (List‹MerkleCap›, ByteStream) {
    let (n, s) = read_count(stream);
    read_merkle_cap_vec_n(s, n)
  }
  fn read_merkle_cap_vec_n(stream: ByteStream, n: G) -> (List‹MerkleCap›, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), stream),
      _ =>
        let (x, s) = read_merkle_cap(stream);
        let (rest, s2) = read_merkle_cap_vec_n(s, n - 1);
        (store(ListNode.Cons(x, rest)), s2),
    }
  }

  fn read_commitments(stream: ByteStream) -> (Commitments, ByteStream) {
    let (stage_1_trace, s0) = read_merkle_cap(stream);
    let (stage_2_trace, s1) = read_merkle_cap(s0);
    let (quotient_chunks, s2) = read_merkle_cap(s1);
    (Commitments.Mk(stage_1_trace, stage_2_trace, quotient_chunks), s2)
  }

  fn read_batch_opening(stream: ByteStream) -> (BatchOpening, ByteStream) {
    let (opened_values, s0) = read_u64_vec_vec(stream);
    let (opening_proof, s1) = read_digest_vec(s0);
    (BatchOpening.Mk(opened_values, opening_proof), s1)
  }
  fn read_batch_opening_vec(stream: ByteStream) -> (List‹BatchOpening›, ByteStream) {
    let (n, s) = read_count(stream);
    read_batch_opening_vec_n(s, n)
  }
  fn read_batch_opening_vec_n(stream: ByteStream, n: G) -> (List‹BatchOpening›, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), stream),
      _ =>
        let (x, s) = read_batch_opening(stream);
        let (rest, s2) = read_batch_opening_vec_n(s, n - 1);
        (store(ListNode.Cons(x, rest)), s2),
    }
  }

  fn read_commit_phase_step(stream: ByteStream) -> (CommitPhaseProofStep, ByteStream) {
    let (log_arity, s0) = read_u8(stream);
    let (sibling_values, s1) = read_ext_vec(s0);
    let (opening_proof, s2) = read_digest_vec(s1);
    (CommitPhaseProofStep.Mk(log_arity, sibling_values, opening_proof), s2)
  }
  fn read_commit_phase_step_vec(stream: ByteStream) -> (List‹CommitPhaseProofStep›, ByteStream) {
    let (n, s) = read_count(stream);
    read_commit_phase_step_vec_n(s, n)
  }
  fn read_commit_phase_step_vec_n(stream: ByteStream, n: G) -> (List‹CommitPhaseProofStep›, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), stream),
      _ =>
        let (x, s) = read_commit_phase_step(stream);
        let (rest, s2) = read_commit_phase_step_vec_n(s, n - 1);
        (store(ListNode.Cons(x, rest)), s2),
    }
  }

  fn read_query_proof(stream: ByteStream) -> (QueryProof, ByteStream) {
    let (input_proof, s0) = read_batch_opening_vec(stream);
    let (commit_phase_openings, s1) = read_commit_phase_step_vec(s0);
    (QueryProof.Mk(input_proof, commit_phase_openings), s1)
  }
  fn read_query_proof_vec(stream: ByteStream) -> (List‹QueryProof›, ByteStream) {
    let (n, s) = read_count(stream);
    read_query_proof_vec_n(s, n)
  }
  fn read_query_proof_vec_n(stream: ByteStream, n: G) -> (List‹QueryProof›, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), stream),
      _ =>
        let (x, s) = read_query_proof(stream);
        let (rest, s2) = read_query_proof_vec_n(s, n - 1);
        (store(ListNode.Cons(x, rest)), s2),
    }
  }

  fn read_fri_proof(stream: ByteStream) -> (FriProof, ByteStream) {
    let (commit_phase_commits, s0) = read_merkle_cap_vec(stream);
    let (commit_pow_witnesses, s1) = read_u64_vec(s0);
    let (query_proofs, s2) = read_query_proof_vec(s1);
    let (final_poly, s3) = read_ext_vec(s2);
    let (query_pow_witness, s4) = read_u64(s3);
    (FriProof.Mk(commit_phase_commits, commit_pow_witnesses, query_proofs,
                 final_poly, query_pow_witness), s4)
  }

  -- `Option<OpenedRound>`: 1 tag byte, then the value when `Some`.
  fn read_preprocessed(stream: ByteStream) -> (PreprocessedOpt, ByteStream) {
    let (tag, s) = read_u8(stream);
    match tag {
      0 => (PreprocessedOpt.NoPreprocessed, s),
      _ =>
        let (r, s2) = read_opened_round(s);
        (PreprocessedOpt.SomePreprocessed(r), s2),
    }
  }

  -- Full `Proof` in declaration order (see `manual_codec.rs::Reader::proof`).
  fn read_proof(stream: ByteStream) -> (Proof, ByteStream) {
    let (commitments, s0) = read_commitments(stream);
    let (intermediate_accumulators, s1) = read_ext_vec(s0);
    let (log_degrees, s2) = read_u8_vec(s1);
    let (opening_proof, s3) = read_fri_proof(s2);
    let (quotient_opened_values, s4) = read_opened_round(s3);
    let (preprocessed_opened_values, s5) = read_preprocessed(s4);
    let (stage_1_opened_values, s6) = read_opened_round(s5);
    let (stage_2_opened_values, s7) = read_opened_round(s6);
    (Proof.Mk(commitments, intermediate_accumulators, log_degrees, opening_proof,
              quotient_opened_values, preprocessed_opened_values,
              stage_1_opened_values, stage_2_opened_values), s7)
  }
⟧

end MultiStark

end
