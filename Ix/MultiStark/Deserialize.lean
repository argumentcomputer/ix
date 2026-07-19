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

The proof stream is pure non-deterministic advice on IO channel 0 (never
hashed — see `Ix/MultiStark.lean`), so the `read_proof` family reads it
**directly from the IO arena by index**: every reader threads a `(channel-0)
byte offset `i : G` and pulls fixed-size chunks with `io_read` (1/8/16/32
bytes — `io_read`'s length is static). No per-byte `ListNode` chain is ever
materialized, which removes one memory store + one load per proof byte.
Variable-length content loops a fixed-size read per element, exactly like
the old stream readers looped `read_u8`.

The byte-stream primitives (`read_u8`/`read_u64`/`read_count`/`read_digest`/
`read_merkle_cap` over `ByteStream`) remain for the vk/claims streams, whose
bytes are digest-bound and therefore flow through blake3 as materialized
streams anyway (`read_system`, `read_claims`).

`read_proof i` builds a `Proof` object and returns the end offset;
`Ix/MultiStark.lean` hangs the entrypoint (and full-consumption assert)
off it.
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
  -- as its two Goldilocks coefficients `[c0, c1]` (= `c0 + c1·X`), each held as
  -- canonical LE bytes (`[U8; 8]`) — the interface shape of `Goldilocks.lean`.
  type Ext = [[U8; 8]; 2]

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
  -- Byte-stream primitives (vk/claims streams; digest-bound bytes that flow
  -- through blake3 as materialized `ByteStream`s).
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

  -- Merkle digest -> `[u64; 4]`, no length prefix.
  fn read_digest(stream: ByteStream) -> (Digest, ByteStream) {
    let (a, s0) = read_u64(stream);
    let (b, s1) = read_u64(s0);
    let (c, s2) = read_u64(s1);
    let (d, s3) = read_u64(s2);
    ([a, b, c, d], s3)
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
  fn read_merkle_cap(stream: ByteStream) -> (MerkleCap, ByteStream) {
    read_digest_vec(stream)
  }

  -- ==========================================================================
  -- Indexed proof-stream primitives: read fixed-size chunks straight from the
  -- IO arena of channel 0 at byte offset `i`, returning the advanced offset.
  -- The cells come back as unconstrained field advice; `u8_from_field_unsafe`
  -- reinterprets them exactly as the stream readers did (same trust model —
  -- the proof is advice, and byte-ness is enforced downstream where needed).
  -- ==========================================================================

  fn read_u8_at(i: G) -> (U8, G) {
    let [b] = io_read(0, i, 1);
    (u8_from_field_unsafe(b), i + 1)
  }

  fn read_u64_at(i: G) -> (U64, G) {
    let [b0, b1, b2, b3, b4, b5, b6, b7] = io_read(0, i, 8);
    ([u8_from_field_unsafe(b0), u8_from_field_unsafe(b1),
      u8_from_field_unsafe(b2), u8_from_field_unsafe(b3),
      u8_from_field_unsafe(b4), u8_from_field_unsafe(b5),
      u8_from_field_unsafe(b6), u8_from_field_unsafe(b7)], i + 8)
  }

  fn read_count_at(i: G) -> (G, G) {
    let (val, j) = #read_u64_at(i);
    (flatten_u64(val), j)
  }

  -- `ExtVal` -> two `u64` limbs (no length prefix), each canonicalized into a
  -- Goldilocks element (`gl_reduce` maps a non-canonical wire repr, e.g. `0`
  -- shipped as `p`, to its canonical `< p` bytes).
  fn read_ext_at(i: G) -> (Ext, G) {
    let (a, j0) = #read_u64_at(i);
    let (b, j1) = #read_u64_at(j0);
    ([gl_reduce(a), gl_reduce(b)], j1)
  }

  fn read_digest_at(i: G) -> (Digest, G) {
    let (a, j0) = #read_u64_at(i);
    let (b, j1) = #read_u64_at(j0);
    let (c, j2) = #read_u64_at(j1);
    let (d, j3) = #read_u64_at(j2);
    ([a, b, c, d], j3)
  }

  -- ==========================================================================
  -- Length-prefixed `Vec<T>` readers over the indexed proof stream.
  -- First-order, so one pair per element type: `read_T_vec` reads the `u64`
  -- length then loops `read_T_vec_n`.
  -- ==========================================================================

  fn read_u8_vec(i: G) -> (List‹U8›, G) {
    let (n, j) = read_count_at(i);
    read_u8_vec_n(j, n)
  }
  fn read_u8_vec_n(i: G, n: G) -> (List‹U8›, G) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (x, j) = #read_u8_at(i);
        let (rest, j2) = read_u8_vec_n(j, n - 1);
        (store(ListNode.Cons(x, rest)), j2),
    }
  }

  fn read_u64_vec(i: G) -> (List‹U64›, G) {
    let (n, j) = read_count_at(i);
    read_u64_vec_n(j, n)
  }
  fn read_u64_vec_n(i: G, n: G) -> (List‹U64›, G) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (x, j) = #read_u64_at(i);
        let (rest, j2) = read_u64_vec_n(j, n - 1);
        (store(ListNode.Cons(x, rest)), j2),
    }
  }

  fn read_ext_vec(i: G) -> (List‹Ext›, G) {
    let (n, j) = read_count_at(i);
    read_ext_vec_n(j, n)
  }
  fn read_ext_vec_n(i: G, n: G) -> (List‹Ext›, G) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (x, j) = read_ext_at(i);
        let (rest, j2) = read_ext_vec_n(j, n - 1);
        (store(ListNode.Cons(x, rest)), j2),
    }
  }

  fn read_digest_vec_at(i: G) -> (List‹Digest›, G) {
    let (n, j) = read_count_at(i);
    read_digest_vec_at_n(j, n)
  }
  fn read_digest_vec_at_n(i: G, n: G) -> (List‹Digest›, G) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (x, j) = read_digest_at(i);
        let (rest, j2) = read_digest_vec_at_n(j, n - 1);
        (store(ListNode.Cons(x, rest)), j2),
    }
  }

  -- `Vec<Vec<Val>>` for `BatchOpening.opened_values`.
  fn read_u64_vec_vec(i: G) -> (List‹List‹U64››, G) {
    let (n, j) = read_count_at(i);
    read_u64_vec_vec_n(j, n)
  }
  fn read_u64_vec_vec_n(i: G, n: G) -> (List‹List‹U64››, G) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (x, j) = read_u64_vec(i);
        let (rest, j2) = read_u64_vec_vec_n(j, n - 1);
        (store(ListNode.Cons(x, rest)), j2),
    }
  }

  -- `OpenedRound = Vec<Vec<Vec<Ext>>>`, built bottom-up from `read_ext_vec`.
  fn read_ext_vec_vec(i: G) -> (List‹List‹Ext››, G) {
    let (n, j) = read_count_at(i);
    read_ext_vec_vec_n(j, n)
  }
  fn read_ext_vec_vec_n(i: G, n: G) -> (List‹List‹Ext››, G) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (x, j) = read_ext_vec(i);
        let (rest, j2) = read_ext_vec_vec_n(j, n - 1);
        (store(ListNode.Cons(x, rest)), j2),
    }
  }

  fn read_opened_round(i: G) -> (OpenedRound, G) {
    let (n, j) = read_count_at(i);
    read_opened_round_n(j, n)
  }
  fn read_opened_round_n(i: G, n: G) -> (OpenedRound, G) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (x, j) = read_ext_vec_vec(i);
        let (rest, j2) = read_opened_round_n(j, n - 1);
        (store(ListNode.Cons(x, rest)), j2),
    }
  }

  -- ==========================================================================
  -- Struct readers (fields in declaration order, no framing).
  -- ==========================================================================

  fn read_merkle_cap_at(i: G) -> (MerkleCap, G) {
    read_digest_vec_at(i)
  }
  fn read_merkle_cap_vec(i: G) -> (List‹MerkleCap›, G) {
    let (n, j) = read_count_at(i);
    read_merkle_cap_vec_n(j, n)
  }
  fn read_merkle_cap_vec_n(i: G, n: G) -> (List‹MerkleCap›, G) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (x, j) = read_merkle_cap_at(i);
        let (rest, j2) = read_merkle_cap_vec_n(j, n - 1);
        (store(ListNode.Cons(x, rest)), j2),
    }
  }

  fn read_commitments(i: G) -> (Commitments, G) {
    let (stage_1_trace, j0) = read_merkle_cap_at(i);
    let (stage_2_trace, j1) = read_merkle_cap_at(j0);
    let (quotient_chunks, j2) = read_merkle_cap_at(j1);
    (Commitments.Mk(stage_1_trace, stage_2_trace, quotient_chunks), j2)
  }

  fn read_batch_opening(i: G) -> (BatchOpening, G) {
    let (opened_values, j0) = read_u64_vec_vec(i);
    let (opening_proof, j1) = read_digest_vec_at(j0);
    (BatchOpening.Mk(opened_values, opening_proof), j1)
  }
  fn read_batch_opening_vec(i: G) -> (List‹BatchOpening›, G) {
    let (n, j) = read_count_at(i);
    read_batch_opening_vec_n(j, n)
  }
  fn read_batch_opening_vec_n(i: G, n: G) -> (List‹BatchOpening›, G) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (x, j) = read_batch_opening(i);
        let (rest, j2) = read_batch_opening_vec_n(j, n - 1);
        (store(ListNode.Cons(x, rest)), j2),
    }
  }

  fn read_commit_phase_step(i: G) -> (CommitPhaseProofStep, G) {
    let (log_arity, j0) = #read_u8_at(i);
    let (sibling_values, j1) = read_ext_vec(j0);
    let (opening_proof, j2) = read_digest_vec_at(j1);
    (CommitPhaseProofStep.Mk(log_arity, sibling_values, opening_proof), j2)
  }
  fn read_commit_phase_step_vec(i: G) -> (List‹CommitPhaseProofStep›, G) {
    let (n, j) = read_count_at(i);
    read_commit_phase_step_vec_n(j, n)
  }
  fn read_commit_phase_step_vec_n(i: G, n: G) -> (List‹CommitPhaseProofStep›, G) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (x, j) = read_commit_phase_step(i);
        let (rest, j2) = read_commit_phase_step_vec_n(j, n - 1);
        (store(ListNode.Cons(x, rest)), j2),
    }
  }

  fn read_query_proof(i: G) -> (QueryProof, G) {
    let (input_proof, j0) = read_batch_opening_vec(i);
    let (commit_phase_openings, j1) = read_commit_phase_step_vec(j0);
    (QueryProof.Mk(input_proof, commit_phase_openings), j1)
  }
  fn read_query_proof_vec(i: G) -> (List‹QueryProof›, G) {
    let (n, j) = read_count_at(i);
    read_query_proof_vec_n(j, n)
  }
  fn read_query_proof_vec_n(i: G, n: G) -> (List‹QueryProof›, G) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (x, j) = read_query_proof(i);
        let (rest, j2) = read_query_proof_vec_n(j, n - 1);
        (store(ListNode.Cons(x, rest)), j2),
    }
  }

  fn read_fri_proof(i: G) -> (FriProof, G) {
    let (commit_phase_commits, j0) = read_merkle_cap_vec(i);
    let (commit_pow_witnesses, j1) = read_u64_vec(j0);
    let (query_proofs, j2) = read_query_proof_vec(j1);
    let (final_poly, j3) = read_ext_vec(j2);
    let (query_pow_witness, j4) = #read_u64_at(j3);
    (FriProof.Mk(commit_phase_commits, commit_pow_witnesses, query_proofs,
                 final_poly, query_pow_witness), j4)
  }

  -- `Option<OpenedRound>`: 1 tag byte, then the value when `Some`.
  fn read_preprocessed(i: G) -> (PreprocessedOpt, G) {
    let (tag, j) = #read_u8_at(i);
    match tag {
      0 => (PreprocessedOpt.NoPreprocessed, j),
      _ =>
        let (r, j2) = read_opened_round(j);
        (PreprocessedOpt.SomePreprocessed(r), j2),
    }
  }

  -- Full `Proof` in declaration order (see `manual_codec.rs::Reader::proof`),
  -- read from the channel-0 IO arena starting at byte offset `i`. Returns the
  -- end offset; the entrypoint asserts it equals `idx + len` (fully consumed).
  fn read_proof(i: G) -> (Proof, G) {
    let (commitments, j0) = read_commitments(i);
    let (intermediate_accumulators, j1) = read_ext_vec(j0);
    let (log_degrees, j2) = read_u8_vec(j1);
    let (opening_proof, j3) = read_fri_proof(j2);
    let (quotient_opened_values, j4) = read_opened_round(j3);
    let (preprocessed_opened_values, j5) = read_preprocessed(j4);
    let (stage_1_opened_values, j6) = read_opened_round(j5);
    let (stage_2_opened_values, j7) = read_opened_round(j6);
    (Proof.Mk(commitments, intermediate_accumulators, log_degrees, opening_proof,
              quotient_opened_values, preprocessed_opened_values,
              stage_1_opened_values, stage_2_opened_values), j7)
  }
⟧

end MultiStark

end
