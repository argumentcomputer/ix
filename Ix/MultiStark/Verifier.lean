module
public import Ix.Aiur.Meta
public import Ix.IxVM.Core
public import Ix.IxVM.ByteStream
public import Ix.MultiStark.Deserialize
public import Ix.MultiStark.Keccak
public import Ix.MultiStark.Pcs
public import Ix.MultiStark.SystemDeserialize

/-!
# Multi-STARK verifier (Aiur)

Reimplementation of `multi-stark/src/verifier.rs` (`System::verify_multiple_claims`)
over the deserialized `Proof` (`Ix/MultiStark/Deserialize.lean`).

The Rust verifier runs these steps:

1. **Shape check** — proof array dimensions match the system's circuit count and
   column widths.
2. **Accumulator balance** — the last intermediate accumulator is zero (all
   lookup pushes/pulls cancel).
3. **Fiat-Shamir replay** — reconstruct the challenger: observe
   commitments / trace heights / claims, sample (lookup, fingerprint, α, ζ).
4. **PCS verification** — FRI opening proofs (see `Ix/MultiStark/Pcs.lean`).
5. **OOD evaluation** — recompute the composition polynomial at ζ and check
   `composition(ζ) · inv_vanishing(ζ) == quotient(ζ)`.

### Implemented here
* Step 1 (the system-independent part): the proof is internally consistent —
  `stage_1`, `stage_2` and `intermediate_accumulators` all have the same length
  (the circuit count) and it is non-zero.
* Step 2: accumulator balance — the last `intermediate_accumulator` is the zero
  extension element.
* Step 3: the Fiat-Shamir challenger replay (`fiat_shamir`). Prover-faithful:
  starts from the parameter-seeded challenger (`b"multi-stark/v0"` + the 7
  protocol parameters), observes the system shape, the verifying key's
  preprocessed commitment, the stage_1 commitment, the trace heights, and the
  length-prefixed public claims (in that order), then samples and re-observes
  the lookup/fingerprint challenges, observes stage_2 and the intermediate
  accumulators, samples α, observes the quotient commitment, and samples ζ —
  matching `verify_multiple_claims` byte-for-byte.
* Step 5: the out-of-domain composition/quotient check (`ood_verify`). For each
  circuit it recomputes `composition(ζ)` by replaying the AIR constraint folder
  (`VerifierConstraintFolder` + `LookupAir::eval`) over the deserialized
  symbolic system and the opened values, recomputes `quotient(ζ)` from the
  opened quotient chunks (barycentric `zps` weights over the split quotient
  domains), and asserts `composition(ζ) · inv_vanishing(ζ) == quotient(ζ)`.
  Validated end-to-end against a real factorial proof (the `recursive-verifier`
  test runner, `Tests/MultiStark.lean`): the verifier accepts the honest proof
  and rejects a tampered claim.

* Step 4: the PCS/FRI opening proof (`pcs_fri_verify`, `Ix/MultiStark/Pcs.lean`)
  — Merkle `verify_batch`, the challenger continuation, the FRI fold chain, and
  the final-polynomial check.

### Notes
* Base-field samples are rejection-sampled (`ch_sample_field`): a raw 8-byte
  limb in the band `[p, 2⁶⁴)` (probability ≈ 2⁻³²) is discarded and redrawn,
  consuming challenger bytes exactly as `SerializingChallenger64::sample` does.
-/

public section

namespace MultiStark

def verifier := ⟦
  -- An extension element `[c0, c1]` (`= c0 + c1·X`) is zero iff both Goldilocks
  -- coefficients are zero. (`read_ext` already reduced the limbs mod p.)
  fn ext_is_zero(e: Ext) -> G {
    eq_zero(e[0]) * eq_zero(e[1])
  }

  -- 1 iff the LAST element of the accumulator list is the zero extension
  -- element (Rust: `intermediate_accumulators.last() == Some(ExtVal::ZERO)`).
  -- The empty list returns 0 (there is no last element to balance).
  fn last_acc_is_zero(accs: List‹Ext›) -> G {
    match load(accs) {
      ListNode.Nil => 0,
      ListNode.Cons(e, rest) =>
        match load(rest) {
          ListNode.Nil => ext_is_zero(e),
          _ => last_acc_is_zero(rest),
        },
    }
  }

  -- ==========================================================================
  -- Fiat-Shamir challenger: `SerializingChallenger64<Val, HashChallenger<u8,
  -- Blake3, 32>>`. The inner byte challenger keeps an `input` buffer; a
  -- `sample` with empty `output` flushes (`input := output := blake3(input)`)
  -- and pops bytes from the END of the hash output. The outer layer serializes
  -- field elements as 8 little-endian bytes and samples field elements as
  -- 8-byte little-endian u64s.
  --
  -- The challenger is threaded as a pair `(input, output)` of byte lists, where
  -- `output` is held in pop order (front = next byte = hash byte 31, 30, …).
  -- ==========================================================================

  -- Cons 8 bytes (LSB-first) of `b` onto `tail` (one byte list segment).
  fn b8_onto(b: [U8; 8], tail: ByteStream) -> ByteStream {
    store(ListNode.Cons(b[0], store(ListNode.Cons(b[1], store(ListNode.Cons(b[2],
    store(ListNode.Cons(b[3], store(ListNode.Cons(b[4], store(ListNode.Cons(b[5],
    store(ListNode.Cons(b[6], store(ListNode.Cons(b[7], tail))))))))))))))))
  }

  -- A digest = `[u64; 4]` = 32 bytes (each limb little-endian) onto `tail`.
  fn digest_onto(d: Digest, tail: ByteStream) -> ByteStream {
    b8_onto(d[0], b8_onto(d[1], b8_onto(d[2], b8_onto(d[3], tail))))
  }

  -- A commitment (`MerkleCap` = `Vec<Digest>`): all digest bytes, onto `tail`.
  fn cap_onto(cap: MerkleCap, tail: ByteStream) -> ByteStream {
    match load(cap) {
      ListNode.Nil => tail,
      ListNode.Cons(d, rest) => digest_onto(d, cap_onto(rest, tail)),
    }
  }

  -- Observe `log_degrees`: each is a `Val::from_u8`, i.e. 8 LE bytes `[ld,0,…]`.
  fn log_degrees_onto(lds: List‹U8›, tail: ByteStream) -> ByteStream {
    match load(lds) {
      ListNode.Nil => tail,
      ListNode.Cons(ld, rest) =>
        b8_onto([ld, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], log_degrees_onto(rest, tail)),
    }
  }

  -- Reverse `l` onto `acc` (used to put a hash output into pop order).
  fn rev_onto(l: ByteStream, acc: ByteStream) -> ByteStream {
    match load(l) {
      ListNode.Nil => acc,
      ListNode.Cons(b, rest) => rev_onto(rest, store(ListNode.Cons(b, acc))),
    }
  }

  -- Sample one byte. If `output` is empty, flush: hash the `input` buffer, set
  -- the new input to the 32 hash bytes, and refill `output` (in pop order).
  fn ch_sample_byte(input: ByteStream, output: ByteStream) -> (U8, ByteStream, ByteStream) {
    match load(output) {
      ListNode.Cons(b, rest) => (b, input, rest),
      ListNode.Nil =>
        -- `HashChallenger<u8, Blake3, 32>` flush: hash the `input` buffer with
        -- blake3; `b3_flatten_onto` (Pcs.lean) gives the 32 output bytes, popped
        -- from the END (rev), with the `input := output := hash` update.
        let h = blake3(input);
        let fwd = b3_flatten_onto(h, store(ListNode.Nil));
        let rev = rev_onto(fwd, store(ListNode.Nil));
        let &ListNode.Cons(b, rest) = rev;
        (b, fwd, rest),
    }
  }

  -- Sample 8 bytes = `sample_array()` (for one base-field element, LE).
  fn ch_sample8(input: ByteStream, output: ByteStream) -> ([U8; 8], ByteStream, ByteStream) {
    let (b0, i0, o0) = ch_sample_byte(input, output);
    let (b1, i1, o1) = ch_sample_byte(i0, o0);
    let (b2, i2, o2) = ch_sample_byte(i1, o1);
    let (b3, i3, o3) = ch_sample_byte(i2, o2);
    let (b4, i4, o4) = ch_sample_byte(i3, o3);
    let (b5, i5, o5) = ch_sample_byte(i4, o4);
    let (b6, i6, o6) = ch_sample_byte(i5, o5);
    let (b7, i7, o7) = ch_sample_byte(i6, o6);
    ([b0, b1, b2, b3, b4, b5, b6, b7], i7, o7)
  }

  -- Sample one base-field element with REJECTION SAMPLING, mirroring
  -- `SerializingChallenger64::sample`'s inner loop: draw 8 bytes as a LE u64
  -- (the `log2_ceil(p) = 64` mask is a no-op for Goldilocks); if the raw value
  -- is ≥ p (probability ≈ 2⁻³²), DISCARD it and draw the next 8 bytes — a
  -- rejected draw consumes challenger bytes, shifting every later sample,
  -- exactly as in the reference. `gl_lt_p` decides `raw < p`; the accepted
  -- limb is canonical (< p) by construction.
  fn ch_sample_field(input: ByteStream, output: ByteStream) -> ([U8; 8], ByteStream, ByteStream) {
    let (raw, i1, o1) = ch_sample8(input, output);
    match gl_lt_p(raw) {
      1 => (raw, i1, o1),
      _ => ch_sample_field(i1, o1),
    }
  }

  -- Sample a degree-2 extension element: two base samples (`from_basis_*`),
  -- each rejection-sampled, returning their 8-byte LE limbs (canonical, but
  -- also re-observable as raw bytes) and the threaded challenger.
  fn ch_sample_ext(input: ByteStream, output: ByteStream) -> ([U8; 8], [U8; 8], ByteStream, ByteStream) {
    let (c0, i0, o0) = ch_sample_field(input, output);
    let (c1, i1, o1) = ch_sample_field(i0, o0);
    (c0, c1, i1, o1)
  }

  -- Prepend the 8 elements of `d` onto `tail` (generic list helper).
  fn cons8(d: [G; 8], tail: List‹G›) -> List‹G› {
    store(ListNode.Cons(d[0], store(ListNode.Cons(d[1], store(ListNode.Cons(d[2],
    store(ListNode.Cons(d[3], store(ListNode.Cons(d[4], store(ListNode.Cons(d[5],
    store(ListNode.Cons(d[6], store(ListNode.Cons(d[7], tail))))))))))))))))
  }

  -- `sample_bits(n)` (FRI query index). `SerializingChallenger64::sample_bits`
  -- reads one 8-byte sample as a little-endian u64 and masks the low `n` bits.
  -- We return the low `n` bits as a list (LSB first = the leaf→root Merkle/FRI
  -- path), built from the 8 sampled bytes' bit decompositions (via `cons8`),
  -- truncated to `n`.
  fn sample8_bits(bytes: [U8; 8]) -> List‹G› {
    cons8(u8_bit_decomposition(bytes[0]),
    cons8(u8_bit_decomposition(bytes[1]),
    cons8(u8_bit_decomposition(bytes[2]),
    cons8(u8_bit_decomposition(bytes[3]),
    cons8(u8_bit_decomposition(bytes[4]),
    cons8(u8_bit_decomposition(bytes[5]),
    cons8(u8_bit_decomposition(bytes[6]),
    cons8(u8_bit_decomposition(bytes[7]), store(ListNode.Nil)))))))))
  }
  fn take_bits(bits: List‹G›, n: G) -> List‹G› {
    match n {
      0 => store(ListNode.Nil),
      _ =>
        let &ListNode.Cons(b, rest) = bits;
        store(ListNode.Cons(b, take_bits(rest, n - 1))),
    }
  }
  fn ch_sample_bits(input: ByteStream, output: ByteStream, n: G)
      -> (List‹G›, ByteStream, ByteStream) {
    let (bytes, i1, o1) = ch_sample8(input, output);
    (take_bits(sample8_bits(bytes), n), i1, o1)
  }

  -- Append (observe) 8 little-endian bytes of `b` at the END of the challenger
  -- input buffer. The transcript is held front-to-back (front = first observed =
  -- first hashed, matching `blake3`'s absorption order), so an observation
  -- appends — `b8_onto` PREPENDS, hence the `list_concat`.
  fn snoc_b8(input: ByteStream, b: [U8; 8]) -> ByteStream {
    list_concat(input, b8_onto(b, store(ListNode.Nil)))
  }
  -- Append (observe) a commitment (`MerkleCap`) at the end of the buffer.
  fn snoc_cap(input: ByteStream, cap: MerkleCap) -> ByteStream {
    list_concat(input, cap_onto(cap, store(ListNode.Nil)))
  }
  -- The intermediate accumulators as a prepend-built stream, in order — each
  -- an `observe_algebra_element`: two canonical 8-LE-byte limbs. (`read_ext`
  -- reduced the limbs mod p, matching `as_canonical_u64` serialization.)
  -- Prepend-composed so observing all of them is one `list_concat`, not a
  -- per-element re-walk of the input buffer.
  fn accs_onto(accs: List‹Ext›, tail: ByteStream) -> ByteStream {
    match load(accs) {
      ListNode.Nil => tail,
      ListNode.Cons(e, rest) => b8_onto(gl_to_bytes(e[0]), b8_onto(gl_to_bytes(e[1]), accs_onto(rest, tail))),
    }
  }

  -- ==========================================================================
  -- PCS challenger continuation (Phase 4): the post-ζ transcript that
  -- `two_adic_pcs::verify` + `verify_fri` replay. Unlike `fiat_shamir` — where
  -- every sample is followed by an observe (so each sample re-flushes from an
  -- empty `output`) — the PCS phase has *consecutive* samples with no observe
  -- between (the PCS batch challenge α, then immediately the FRI batch challenge
  -- α). So both challenger buffers must be threaded: `output` carries the
  -- leftover hash bytes from one sample into the next instead of re-flushing.
  -- ==========================================================================

  -- Observe one `Val` (8 LE bytes): append to `input`, CLEAR `output` (any
  -- leftover sampled bytes are discarded), per `HashChallenger::observe`.
  fn ch_observe_val(input: ByteStream, v: U64) -> (ByteStream, ByteStream) {
    (snoc_b8(input, v), store(ListNode.Nil))
  }

  -- Sample a degree-2 extension element, threading BOTH challenger buffers so a
  -- following consecutive sample continues from the same hash `output` stream
  -- (no re-flush). Limbs are rejection-sampled (`ch_sample_field`), so they are
  -- canonical; the `gl_reduce` is a no-op kept for type/intent clarity.
  fn pcs_sample_ext(input: ByteStream, output: ByteStream)
      -> (Ext, ByteStream, ByteStream) {
    let (c0, c1, i1, o1) = ch_sample_ext(input, output);
    ([gl_val(c0), gl_val(c1)], i1, o1)
  }

  -- Append a claim's values (each `Val` as 8 LE bytes) onto `tail`, in order.
  fn claim_vals_onto(vals: List‹U64›, tail: ByteStream) -> ByteStream {
    match load(vals) {
      ListNode.Nil => tail,
      ListNode.Cons(v, rest) => b8_onto(v, claim_vals_onto(rest, tail)),
    }
  }
  -- Each claim, length-prefixed: `observe(Val::from_usize(claim.len()))` then
  -- `observe_slice(claim)`.
  fn claims_each_onto(claims: List‹List‹U64››, tail: ByteStream) -> ByteStream {
    match load(claims) {
      ListNode.Nil => tail,
      ListNode.Cons(c, rest) =>
        b8_onto(list_length_u64(c), claim_vals_onto(c, claims_each_onto(rest, tail))),
    }
  }
  -- Append every claim: the claim count, then each claim length-prefixed
  -- (`verify_multiple_claims`' claim observation, byte-for-byte).
  fn claims_onto(claims: List‹List‹U64››, tail: ByteStream) -> ByteStream {
    b8_onto(list_length_u64(claims), claims_each_onto(claims, tail))
  }

  -- `b"multi-stark/v0"` — the domain-separation tag the challenger seed
  -- starts with (`GoldilocksBlake3Config::new`).
  fn seed_tag_onto(tail: ByteStream) -> ByteStream {
    store(ListNode.Cons(109u8, store(ListNode.Cons(117u8, store(ListNode.Cons(108u8,
    store(ListNode.Cons(116u8, store(ListNode.Cons(105u8, store(ListNode.Cons(45u8,
    store(ListNode.Cons(115u8, store(ListNode.Cons(116u8, store(ListNode.Cons(97u8,
    store(ListNode.Cons(114u8, store(ListNode.Cons(107u8, store(ListNode.Cons(47u8,
    store(ListNode.Cons(118u8, store(ListNode.Cons(48u8,
    tail))))))))))))))))))))))))))))
  }
  -- Raw u64 wire words (protocol parameters + system shape), each as its 8 LE
  -- bytes, in order.
  fn limbs_onto(ls: List‹U64›, tail: ByteStream) -> ByteStream {
    match load(ls) {
      ListNode.Nil => tail,
      ListNode.Cons(l, rest) => b8_onto(l, limbs_onto(rest, tail)),
    }
  }

  -- The preprocessed commitment cap from the verifying key, or an empty cap
  -- (observes nothing) when there is none.
  fn opt_commit_cap(commit: OptCommit) -> MerkleCap {
    match commit {
      OptCommit.NoCommit => store(ListNode.Nil),
      OptCommit.SomeCommit(c) => c,
    }
  }

  -- Replay the verifier transcript and derive the four challenges
  -- `(lookup, fingerprint, alpha, zeta)`. Mirrors `verify_multiple_claims`'s
  -- challenger sequence exactly:
  --   seed = tag + protocol parameters; observe_shape (circuit count + 6
  --   metadata words per circuit) → preprocessed_commit (if any) → stage_1 →
  --   log_degrees → length-prefixed claims;
  --   sample lookup, observe it; sample fingerprint, observe it;
  --   observe stage_2; observe the intermediate accumulators; sample α;
  --   observe quotient; sample ζ.
  -- `observe` clears the challenger's output buffer, and every sample here is
  -- preceded by an observe, so each `ch_sample_ext` re-flushes from an empty
  -- output (hence the `store(ListNode.Nil)` output argument each time).
  -- Every sample is rejection-sampled (`ch_sample_field` inside
  -- `ch_sample_ext`), so a limb in the band `[p, 2⁶⁴)` is redrawn exactly as in
  -- the reference challenger, and the limbs observed back are canonical.
  -- Also returns the post-ζ challenger `input` buffer, which the PCS phase
  -- (Phase 4+) continues observing into. The leftover `output` after the ζ
  -- sample is discarded — the next challenger op is an observe (of the opened
  -- values), which clears `output` anyway.
  -- Each activation bit as an observed `Val` (8 LE bytes, 0 or 1).
  fn active_onto(active: List‹G›, tail: ByteStream) -> ByteStream {
    match load(active) {
      ListNode.Nil => tail,
      ListNode.Cons(b, rest) =>
        b8_onto([u8_from_field_unsafe(b), 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
                active_onto(rest, tail)),
    }
  }

  fn fiat_shamir(tlimbs: List‹U64›, active: List‹G›, prep: MerkleCap, s1: MerkleCap, s2: MerkleCap,
      q: MerkleCap, lds: List‹U8›, claims: List‹List‹U64››, accs: List‹Ext›)
      -> (Ext, Ext, Ext, Ext, ByteStream) {
    -- Initial transcript, front-to-back: seed tag, parameter + shape words
    -- (`tlimbs`, from the verifying key), the activation bitmap, prep,
    -- stage_1, log_degrees, claims. Built inner-to-outer with the prepend
    -- helpers so the result is in forward (observation) order.
    let input = claims_onto(claims, store(ListNode.Nil));
    let input = log_degrees_onto(lds, input);
    let input = cap_onto(s1, input);
    let input = cap_onto(prep, input);
    let input = active_onto(active, input);
    let input = limbs_onto(tlimbs, input);
    let input = seed_tag_onto(input);
    -- sample lookup challenge, then observe it back (append)
    let (l0, l1, input, _ol) = ch_sample_ext(input, store(ListNode.Nil));
    let input = snoc_b8(snoc_b8(input, l0), l1);
    -- sample fingerprint challenge, then observe it back
    let (f0, f1, input, _of) = ch_sample_ext(input, store(ListNode.Nil));
    let input = snoc_b8(snoc_b8(input, f0), f1);
    -- observe stage_2 commitment
    let input = snoc_cap(input, s2);
    -- observe the intermediate accumulators (public values entering the
    -- constraints; α and ζ must depend on them directly)
    let input = list_concat(input, accs_onto(accs, store(ListNode.Nil)));
    -- sample constraint challenge α (not observed)
    let (a0, a1, input, _oa) = ch_sample_ext(input, store(ListNode.Nil));
    -- observe quotient commitment
    let input = snoc_cap(input, q);
    -- sample out-of-domain point ζ; keep the resulting `input` for the PCS phase
    let (z0, z1, zinput, _oz) = ch_sample_ext(input, store(ListNode.Nil));
    ([gl_val(l0), gl_val(l1)],
     [gl_val(f0), gl_val(f1)],
     [gl_val(a0), gl_val(a1)],
     [gl_val(z0), gl_val(z1)],
     zinput)
  }

  -- ==========================================================================
  -- OOD evaluation domain math (`TwoAdicMultiplicativeCoset`, Goldilocks).
  -- The trace domain for a circuit of size 2^L is the order-2^L subgroup H
  -- (shift = 1) generated by `two_adic_gen(L)`.
  -- ==========================================================================

  -- e^(2^k) in the extension field.
  fn ext_exp_pow2(e: Ext, k: G) -> Ext {
    match k {
      0 => e,
      _ => ext_exp_pow2(eg_mul(e, e), k - 1),
    }
  }

  -- `two_adic_generator(bits)` — a primitive 2^bits root of unity in Goldilocks
  -- (`Plonky3/goldilocks/src/goldilocks.rs::TWO_ADIC_GENERATORS`).
  fn two_adic_gen(bits: G) -> Goldilocks {
    match bits {
      0  => 1,
      1  => 18446744069414584320,
      2  => 281474976710656,
      3  => 18446744069397807105,
      4  => 17293822564807737345,
      5  => 70368744161280,
      6  => 549755813888,
      7  => 17870292113338400769,
      8  => 13797081185216407910,
      9  => 1803076106186727246,
      10 => 11353340290879379826,
      11 => 455906449640507599,
      12 => 17492915097719143606,
      13 => 1532612707718625687,
      14 => 16207902636198568418,
      15 => 17776499369601055404,
      16 => 6115771955107415310,
      17 => 12380578893860276750,
      18 => 9306717745644682924,
      19 => 18146160046829613826,
      20 => 3511170319078647661,
      21 => 17654865857378133588,
      22 => 5416168637041100469,
      23 => 16905767614792059275,
      24 => 9713644485405565297,
      25 => 5456943929260765144,
      26 => 17096174751763063430,
      27 => 1213594585890690845,
      28 => 6414415596519834757,
      29 => 16116352524544190054,
      30 => 9123114210336311365,
      31 => 4614640910117430873,
      _  => 1753635133440165772,
    }
  }

  -- Vanishing polynomial of the trace domain (shift = 1, size 2^L) at point ζ:
  -- `Z_H(ζ) = ζ^(2^L) - 1`.
  fn trace_vanishing(zeta: Ext, l: G) -> Ext {
    eg_sub(ext_exp_pow2(zeta, l), [1, 0])
  }

  -- Lagrange selectors at ζ for the trace domain (shift = 1), mirroring
  -- `domain.rs::selectors_at_point`:
  --   is_first_row   = Z_H(ζ) / (ζ - 1)
  --   is_last_row    = Z_H(ζ) / (ζ - g⁻¹)
  --   is_transition  = ζ - g⁻¹
  --   inv_vanishing  = 1 / Z_H(ζ)
  -- where g = two_adic_gen(L) is the subgroup generator.
  fn trace_selectors(zeta: Ext, l: G) -> (Ext, Ext, Ext, Ext) {
    let zh = trace_vanishing(zeta, l);
    let ginv = gl_inverse(two_adic_gen(l));
    let is_first = eg_div(zh, eg_sub(zeta, [1, 0]));
    let is_last = eg_div(zh, eg_sub(zeta, [ginv, 0]));
    let is_trans = eg_sub(zeta, [ginv, 0]);
    let inv_van = eg_inverse(zh);
    (is_first, is_last, is_trans, inv_van)
  }

  -- Structural + accumulator + PCS checks of a deserialized proof (steps 1, 2,
  -- 4). Fiat-Shamir (step 3) and the OOD check (step 5) live in `ood_verify`,
  -- which needs the verifying key and the claims.
  --
  -- Returns 1 on success; `assert_eq!` aborts the (proof) execution on any
  -- failed check, exactly as the Rust verifier returns `Err`.
  fn verify(proof: Proof) -> G {
    match proof {
      Proof.Mk(_active, _commitments, accs, _log_degrees, _opening,
               _quotient, _preprocessed, stage_1, stage_2) =>
        -- Step 1 (shape, system-independent): the per-round opened-value lists
        -- and the accumulator list all have the same length = the circuit count.
        let num_circuits = list_length(accs);
        -- there must be at least one circuit (Rust: InvalidSystem)
        assert_eq!(eq_zero(num_circuits), 0);
        assert_eq!(list_length(stage_1), num_circuits);
        assert_eq!(list_length(stage_2), num_circuits);

        -- Step 2: accumulator balance — the last accumulator must be zero.
        assert_eq!(last_acc_is_zero(accs), 1);
        -- Step 4 (PCS/FRI) now runs inside `ood_verify`, which has the verifying
        -- key, the challenger continuation, and the opened values it needs.
        1,
    }
  }

  -- ==========================================================================
  -- Step 5: out-of-domain (OOD) evaluation.
  --
  -- Mirrors the per-circuit loop in `verifier.rs::verify_multiple_claims`
  -- (lines 329-434). For each circuit it recomputes the composition polynomial
  -- `composition(ζ)` from the opened values by replaying the AIR constraint
  -- folder (`VerifierConstraintFolder` + `LookupAir::eval`), recomputes the
  -- quotient `quotient(ζ)` from the opened quotient chunks via the barycentric
  -- weights `zps`, and asserts
  --   composition(ζ) · inv_vanishing(ζ) == quotient(ζ).
  --
  -- The challenges (lookup, fingerprint, α, ζ) come from `fiat_shamir` above.
  -- The running lookup accumulator starts from the public claims
  -- (`claims_acc`; ExtVal::ZERO when there are none).
  -- ==========================================================================

  -- One Horner fold step of the constraint folder: `acc := acc·α + x`
  -- (`VerifierConstraintFolder::assert_zero` / `assert_zero_ext`).
  fn ood_fold(acc: Ext, alpha: Ext, x: Ext) -> Ext {
    eg_add(eg_mul(acc, alpha), x)
  }

  -- Reconstruct an extension element from its two opened base coordinates,
  -- `from_ext_basis([c0, c1]) = c0 + c1·X` (the ExtVal basis is `[1, X]`).
  fn from_ext_basis(c0: Ext, c1: Ext) -> Ext {
    eg_add(c0, eg_mul(c1, [0, 1]))
  }

  -- A stage-2 / quotient opened row arrives as `stage_2_width·2` extension
  -- coordinates; fold consecutive pairs back into `stage_2_width` extension
  -- elements (Rust: `chunks_exact(2).map(from_ext_basis)`).
  fn reconstruct_ext_row(raw: List‹Ext›) -> List‹Ext› {
    match load(raw) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(c0, t1) =>
        let ListNode.Cons(c1, t2) = load(t1);
        store(ListNode.Cons(from_ext_basis(c0, c1), reconstruct_ext_row(t2))),
    }
  }

  -- Evaluate a symbolic AIR expression at the opened point (Rust:
  -- `SymbolicExpression::interpret`). Function-circuit `zeros` and lookup
  -- args/multiplicities only ever reference `Main`/`Preprocessed` entries
  -- (offset 0) and constants; the other entries never appear here.
  fn eval_sym(e: SymExpr, main: List‹Ext›, prep: List‹Ext›) -> Ext {
    match e {
      SymExpr.Var(entry, idx) =>
        match entry {
          SysEntry.Main(_o) => list_lookup(main, idx),
          SysEntry.Preprocessed(_o) => list_lookup(prep, idx),
          SysEntry.Stage2(_o) => [0, 0],
          SysEntry.Public => [0, 0],
          SysEntry.Stage2Public => [0, 0],
          SysEntry.Challenge => [0, 0],
        },
      SymExpr.IsFirstRow => [0, 0],
      SymExpr.IsLastRow => [0, 0],
      SymExpr.IsTransition => [0, 0],
      SymExpr.Const(c) => [c, 0],
      SymExpr.Add(x, y, _d) => eg_add(eval_sym(load(x), main, prep), eval_sym(load(y), main, prep)),
      SymExpr.Sub(x, y, _d) => eg_sub(eval_sym(load(x), main, prep), eval_sym(load(y), main, prep)),
      SymExpr.Neg(x, _d) => eg_neg(eval_sym(load(x), main, prep)),
      SymExpr.Mul(x, y, _d) => eg_mul(eval_sym(load(x), main, prep), eval_sym(load(y), main, prep)),
    }
  }

  -- `fingerprint(r, args) = Σ argᵢ·rⁱ` (Horner over the reversed argument list,
  -- `lookup.rs::fingerprint`).
  fn fingerprint_ext(r: Ext, args: List‹SymExpr›, main: List‹Ext›, prep: List‹Ext›) -> Ext {
    match load(args) {
      ListNode.Nil => [0, 0],
      ListNode.Cons(a, rest) =>
        eg_add(eval_sym(a, main, prep), eg_mul(r, fingerprint_ext(r, rest, main, prep))),
    }
  }

  -- Fold the inner-AIR `zeros` constraints (Function circuit): each is asserted
  -- zero on the main (stage-1) row, with no preprocessed row.
  fn fold_zeros(acc: Ext, alpha: Ext, zeros: List‹SymExpr›, main: List‹Ext›) -> Ext {
    match load(zeros) {
      ListNode.Nil => acc,
      ListNode.Cons(z, rest) =>
        fold_zeros(ood_fold(acc, alpha, eval_sym(z, main, store(ListNode.Nil))), alpha, rest, main),
    }
  }

  -- Fold the selector boolean checks (Function circuit): `assert_bool(row[s])`
  -- = `assert_zero(s·(s-1))` for `s` in the selector range `[idx, idx+count)`.
  fn fold_sel_bools(acc: Ext, alpha: Ext, main: List‹Ext›, idx: G, count: G) -> Ext {
    match count {
      0 => acc,
      _ =>
        let x = list_lookup(main, idx);
        let bc = eg_mul(x, eg_sub(x, [1, 0]));
        fold_sel_bools(ood_fold(acc, alpha, bc), alpha, main, idx + 1, count - 1),
    }
  }

  -- Fold the per-lookup constraints (`LookupAir::eval`): for lookup `k`,
  -- `assert_one_ext(messageₖ · minvₖ)` = `assert_zero_ext(messageₖ·minvₖ - 1)`,
  -- where `minvₖ = stage_2_row[1+k]` and
  -- `messageₖ = lookup_challenge + fingerprint(fingerprint_challenge, argsₖ)`.
  -- Simultaneously builds `acc_expr = stage_2_row[0] + Σ multiplicityₖ·minvₖ`.
  -- Returns `(folder_acc, acc_expr)`.
  fn fold_lookups(acc: Ext, alpha: Ext, lookups: List‹SysLookup›, k: G,
      main: List‹Ext›, prep: List‹Ext›, s2row: List‹Ext›,
      lch: Ext, fch: Ext, acc_expr: Ext) -> (Ext, Ext) {
    match load(lookups) {
      ListNode.Nil => (acc, acc_expr),
      ListNode.Cons(lk, rest) =>
        let SysLookup.Mk(mult_e, args) = lk;
        let minv = list_lookup(s2row, k + 1);
        let mult = eval_sym(mult_e, main, prep);
        let fp = fingerprint_ext(fch, args, main, prep);
        let message = eg_add(lch, fp);
        let c = eg_sub(eg_mul(message, minv), [1, 0]);
        let acc = ood_fold(acc, alpha, c);
        let acc_expr = eg_add(acc_expr, eg_mul(mult, minv));
        fold_lookups(acc, alpha, rest, k + 1, main, prep, s2row, lch, fch, acc_expr),
    }
  }

  -- The composition polynomial `composition(ζ)` for one circuit: replays the
  -- inner-AIR constraints (per air kind) followed by the lookup-argument
  -- constraints, folding each with `α` exactly as `LookupAir::eval` drives the
  -- verifier folder. `accp`/`naccp` are the current/next lookup accumulators.
  fn ood_composition(air: SysAir, lookups: List‹SysLookup›,
      main: List‹Ext›, main_next: List‹Ext›, s2row: List‹Ext›, s2next: List‹Ext›,
      prep: List‹Ext›, isf: Ext, isl: Ext, ist: Ext,
      lch: Ext, fch: Ext, accp: Ext, naccp: Ext, alpha: Ext) -> Ext {
    -- inner-AIR constraints first, then hand the accumulator to the lookup tail
    -- (split so each `match air` arm ends in a tail call — Aiur forbids
    -- non-tail matches).
    match air {
      SysAir.Function(c) =>
        let SysConstraints.Mk(zeros, ss, se, _w) = c;
        let acc = fold_zeros([0, 0], alpha, zeros, main);
        let acc = fold_sel_bools(acc, alpha, main, ss, se - ss);
        ood_comp_tail(acc, lookups, main, prep, s2row, s2next, isf, isl, ist, lch, fch, accp, naccp, alpha),
      SysAir.Memory(m) =>
        let SysMemory.Mk(_w) = m;
        -- `Memory::eval`: is_real = col 1, ptr = col 2 (current and next row).
        let is_real = list_lookup(main, 1);
        let ptr = list_lookup(main, 2);
        let is_real_next = list_lookup(main_next, 1);
        let ptr_next = list_lookup(main_next, 2);
        -- assert_bool(is_real)
        let acc = ood_fold([0, 0], alpha, eg_mul(is_real, eg_sub(is_real, [1, 0])));
        -- is_real_transition = is_real_next · is_transition
        let irt = eg_mul(is_real_next, ist);
        -- when(irt).assert_one(is_real) = irt·(is_real - 1)
        let acc = ood_fold(acc, alpha, eg_mul(irt, eg_sub(is_real, [1, 0])));
        -- when(irt).assert_eq(ptr+1, ptr_next) = irt·(ptr + 1 - ptr_next)
        let acc = ood_fold(acc, alpha, eg_mul(irt, eg_sub(eg_add(ptr, [1, 0]), ptr_next)));
        ood_comp_tail(acc, lookups, main, prep, s2row, s2next, isf, isl, ist, lch, fch, accp, naccp, alpha),
      SysAir.Bytes1 =>
        ood_comp_tail([0, 0], lookups, main, prep, s2row, s2next, isf, isl, ist, lch, fch, accp, naccp, alpha),
      SysAir.Bytes2 =>
        ood_comp_tail([0, 0], lookups, main, prep, s2row, s2next, isf, isl, ist, lch, fch, accp, naccp, alpha),
    }
  }

  -- Tail of `ood_composition`: fold the lookup-argument constraints onto the
  -- inner-AIR accumulator, then the three accumulator boundary constraints.
  fn ood_comp_tail(acc: Ext, lookups: List‹SysLookup›, main: List‹Ext›, prep: List‹Ext›,
      s2row: List‹Ext›, s2next: List‹Ext›, isf: Ext, isl: Ext, ist: Ext,
      lch: Ext, fch: Ext, accp: Ext, naccp: Ext, alpha: Ext) -> Ext {
    let (acc, acc_expr) =
      fold_lookups(acc, alpha, lookups, 0, main, prep, s2row, lch, fch, list_lookup(s2row, 0));
    let acc_col = list_lookup(s2row, 0);
    let next_acc_col = list_lookup(s2next, 0);
    -- when_first_row: acc_col = accp
    let acc = ood_fold(acc, alpha, eg_mul(isf, eg_sub(acc_col, accp)));
    -- when_transition: acc_expr = next_acc_col
    let acc = ood_fold(acc, alpha, eg_mul(ist, eg_sub(acc_expr, next_acc_col)));
    -- when_last_row: acc_expr = naccp
    ood_fold(acc, alpha, eg_mul(isl, eg_sub(acc_expr, naccp)))
  }

  -- ==========================================================================
  -- Quotient evaluation from the opened quotient chunks.
  --
  -- The trace domain is the order-2^L subgroup H (shift = 1). The quotient
  -- domain is the disjoint coset `7·H'` of size `2^(L+log_qd)` (7 = Goldilocks
  -- GENERATOR), split into `qd = 2^log_qd` chunk domains `Dⱼ` of size `2^L`,
  -- shift `7·g_q^j` where `g_q = two_adic_gen(L + log_qd)`. Then
  --   quotient(ζ) = Σⱼ zpsⱼ · from_ext_basis(chunkⱼ),
  --   zpsⱼ = Πₖ≠ⱼ Z_{Dₖ}(ζ) / Z_{Dₖ}(first_point(Dⱼ)),
  -- with `Z_{Dₖ}(x) = (x · shift_k⁻¹)^(2^L) - 1`.
  -- ==========================================================================

  -- base-field power `base^e` (e small: the chunk index, < qd).
  fn g_pow(base: Goldilocks, e: G) -> Goldilocks {
    match e {
      0 => 1,
      _ => gl_mul(base, g_pow(base, e - 1)),
    }
  }

  -- `Z_{Dⱼ}(x) = (x · shift_j⁻¹)^(2^L) - 1`, evaluated at extension point `x`.
  fn vanish_chunk(x: Ext, l: G, shiftinv: Goldilocks) -> Ext {
    eg_sub(ext_exp_pow2(eg_mul(x, [shiftinv, 0]), l), [1, 0])
  }

  -- `zpsₜ = Πⱼ≠ₜ Z_{Dⱼ}(ζ) / Z_{Dⱼ}(shift_t)`. Iterates j over `[jidx, jidx+rem)`.
  fn zps_prod(acc: Ext, zeta: Ext, l: G, g_q: Goldilocks, shift_t: Goldilocks, jidx: G, rem: G, t: G) -> Ext {
    match rem {
      0 => acc,
      _ =>
        let shiftinv = gl_inverse(gl_mul(7, g_pow(g_q, jidx)));
        -- skip the j = t factor (the chunk's own domain); branch in tail
        -- position so the inner match is not a non-tail match.
        match eq_zero(jidx - t) {
          1 => zps_prod(acc, zeta, l, g_q, shift_t, jidx + 1, rem - 1, t),
          _ =>
            let factor = eg_mul(vanish_chunk(zeta, l, shiftinv),
                                 eg_inverse(vanish_chunk([shift_t, 0], l, shiftinv)));
            zps_prod(eg_mul(acc, factor), zeta, l, g_q, shift_t, jidx + 1, rem - 1, t),
        },
    }
  }

  -- `quotient(ζ) = Σₜ zpsₜ · from_ext_basis(chunkₜ)`, iterating the `qd` chunks
  -- (`q_opened[idx][0] = [c0, c1]`).
  fn quotient_sum(acc: Ext, zeta: Ext, l: G, qd: G, g_q: Goldilocks,
      q_opened: OpenedRound, idx: G, rem: G, t: G) -> Ext {
    match rem {
      0 => acc,
      _ =>
        let shift_t = gl_mul(7, g_pow(g_q, t));
        let zps_t = zps_prod([1, 0], zeta, l, g_q, shift_t, 0, qd, t);
        let ch = list_lookup(q_opened, idx);
        let row = list_lookup(ch, 0);
        let qv = from_ext_basis(list_lookup(row, 0), list_lookup(row, 1));
        quotient_sum(eg_add(acc, eg_mul(zps_t, qv)), zeta, l, qd, g_q,
                     q_opened, idx + 1, rem - 1, t + 1),
    }
  }

  -- `quotient_degree = (max(md, 2) - 1).next_power_of_two()` and its log2.
  -- Tabulated for `max_constraint_degree ≤ 17` (covers all current circuits);
  -- larger degrees fall through to the `_` arm.
  fn quotient_degree_of(md: G) -> G {
    match md {
      0 => 1, 1 => 1, 2 => 1,
      3 => 2,
      4 => 4, 5 => 4,
      6 => 8, 7 => 8, 8 => 8, 9 => 8,
      10 => 16, 11 => 16, 12 => 16, 13 => 16, 14 => 16, 15 => 16, 16 => 16, 17 => 16,
      _ => 32,
    }
  }
  fn log_qd_of(md: G) -> G {
    match md {
      0 => 0, 1 => 0, 2 => 0,
      3 => 1,
      4 => 2, 5 => 2,
      6 => 3, 7 => 3, 8 => 3, 9 => 3,
      10 => 4, 11 => 4, 12 => 4, 13 => 4, 14 => 4, 15 => 4, 16 => 4, 17 => 4,
      _ => 5,
    }
  }

  -- The preprocessed opened row at ζ for circuit `i`, or `Nil` if the circuit
  -- has no preprocessed trace (`preprocessed_indices[i] = None`).
  fn ood_prep_row(prep_opt: PreprocessedOpt, oi: OptIdx) -> List‹Ext› {
    match oi {
      OptIdx.NoIdx => store(ListNode.Nil),
      OptIdx.SomeIdx(j) =>
        match prep_opt {
          PreprocessedOpt.NoPreprocessed => store(ListNode.Nil),
          PreprocessedOpt.SomePreprocessed(round) =>
            let pr = list_lookup(round, j);
            list_lookup(pr, 0),
        },
    }
  }

  -- Per-circuit OOD loop: for each circuit, recompute composition(ζ) and
  -- quotient(ζ) and assert `composition · inv_vanishing == quotient`. Threads
  -- the running lookup accumulator `accp` and the quotient-chunk offset `lastq`.
  fn ood_loop(circuits: List‹SysCircuit›, prep_indices: List‹OptIdx›,
      log_degrees: List‹U8›, accs: List‹Ext›,
      stage1: OpenedRound, stage2: OpenedRound, prep_opt: PreprocessedOpt,
      q_opened: OpenedRound, i: G, accp: Ext, lastq: G,
      lch: Ext, fch: Ext, alpha: Ext, zeta: Ext) -> G {
    match load(circuits) {
      ListNode.Nil => 1,
      ListNode.Cons(circ, rest) =>
        let SysCircuit.Mk(lair, _cc, md, _ph, _pw, _w1, _w2) = circ;
        let SysLookupAir.Mk(air, lookups) = lair;
        let l = to_field(list_lookup(log_degrees, i));
        let qd = quotient_degree_of(md);
        let log_qd = log_qd_of(md);
        let naccp = list_lookup(accs, i);
        let s1 = list_lookup(stage1, i);
        let main = list_lookup(s1, 0);
        let main_next = list_lookup(s1, 1);
        let s2 = list_lookup(stage2, i);
        let s2row = reconstruct_ext_row(list_lookup(s2, 0));
        let s2next = reconstruct_ext_row(list_lookup(s2, 1));
        let prep = ood_prep_row(prep_opt, list_lookup(prep_indices, i));
        let (isf, isl, ist, invv) = trace_selectors(zeta, l);
        let comp = ood_composition(air, lookups, main, main_next, s2row, s2next,
                                   prep, isf, isl, ist, lch, fch, accp, naccp, alpha);
        let g_q = two_adic_gen(l + log_qd);
        let quot = quotient_sum([0, 0], zeta, l, qd, g_q, q_opened, lastq, qd, 0);
        assert_eq!(eg_eq(eg_mul(comp, invv), quot), 1);
        ood_loop(rest, prep_indices, log_degrees, accs, stage1, stage2, prep_opt,
                 q_opened, i + 1, naccp, lastq + qd, lch, fch, alpha, zeta),
    }
  }

  -- The fingerprint of one claim's values: `Σ vᵢ · fch^i` (each `vᵢ` lifted from
  -- its raw u64 limb to an extension element). Mirrors `lookup::fingerprint`.
  fn fingerprint_vals(fch: Ext, vals: List‹U64›) -> Ext {
    match load(vals) {
      ListNode.Nil => [0, 0],
      ListNode.Cons(v, rest) =>
        eg_add([gl_val(v), 0], eg_mul(fch, fingerprint_vals(fch, rest))),
    }
  }

  -- The initial lookup accumulator built from the public claims:
  -- `acc = Σ_claims 1 / (lookup_challenge + fingerprint(fingerprint_challenge, claim))`
  -- (Rust `verify_multiple_claims`, lines 227-232). Empty claim list → zero.
  fn claims_acc(acc: Ext, claims: List‹List‹U64››, lch: Ext, fch: Ext) -> Ext {
    match load(claims) {
      ListNode.Nil => acc,
      ListNode.Cons(c, rest) =>
        let msg = eg_add(lch, fingerprint_vals(fch, c));
        claims_acc(eg_add(acc, eg_inverse(msg)), rest, lch, fch),
    }
  }

  -- Step 3 + 5: derive the challenges via the (prover-faithful) Fiat-Shamir
  -- replay over the verifying key's preprocessed commitment + the proof
  -- commitments + log_degrees + claims, seed the lookup accumulator from the
  -- claims, then run the OOD composition/quotient check for every circuit.
  -- Returns 1 on success (any mismatch aborts via `assert_eq!`).
  fn ood_verify(sys: Sys, proof: Proof, claims: List‹List‹U64››,
      num_queries: G, commit_pow_bits: G, log_blowup_pub: G) -> G {
    -- The FRI parameters (`num_queries`, `commit_pow_bits`, `log_blowup`) are
    -- public inputs. All parameters also live in the (digest-bound) verifying
    -- key — assert the public ones agree with it.
    let Sys.Mk(params, tlimbs, circuits, commit, prep_indices) = sys;
    let SysParams.Mk(log_blowup, _cap_height, _log_final_poly_len,
                     _max_log_arity, vk_num_queries, vk_commit_pow_bits,
                     _query_pow_bits) = params;
    assert_eq!(eq_zero(log_blowup - log_blowup_pub), 1);
    assert_eq!(eq_zero(vk_num_queries - num_queries), 1);
    assert_eq!(eq_zero(vk_commit_pow_bits - commit_pow_bits), 1);
    match proof {
      Proof.Mk(active, commitments, accs, log_degrees, opening,
               q_opened, prep_opt, stage1, stage2) =>
        -- Sparse activation: the bitmap covers the canonical circuit set;
        -- each bit must be boolean; every per-circuit proof sequence is
        -- indexed by ACTIVE position, so the verifying key's circuit and
        -- preprocessed-index lists are filtered to the active subset once
        -- and everything downstream runs on the filtered lists. Soundness
        -- of deactivation rests on the lookup accumulator: an inactive
        -- circuit contributes no sends or receives, and dishonestly
        -- deactivating a needed circuit leaves the final accumulator
        -- nonzero (checked in `verify`).
        assert_eq!(assert_bits(active), 1);
        assert_eq!(eq_zero(list_length(active) - list_length(circuits)), 1);
        let acirc = select_active_circuits(circuits, active);
        let aprep = select_active_prep(prep_indices, active);
        assert_eq!(eq_zero(list_length(acirc) - list_length(accs)), 1);
        let Commitments.Mk(s1c, s2c, qc) = commitments;
        let prep_cap = opt_commit_cap(commit);
        let (lch, fch, alpha, zeta, post_zeta_input) = fiat_shamir(tlimbs, active, prep_cap, s1c, s2c, qc, log_degrees, claims, accs);
        let acc0 = claims_acc([0, 0], claims, lch, fch);
        -- Step 5: OOD composition/quotient identity for every active circuit.
        let _ood = ood_loop(acirc, aprep, log_degrees, accs, stage1, stage2,
                 prep_opt, q_opened, 0, acc0, 0, lch, fch, alpha, zeta);
        pcs_fri_verify(post_zeta_input, stage1, stage2, q_opened, prep_opt, opening,
          s1c, s2c, qc, prep_cap, acirc, aprep, log_degrees, zeta,
          list_length(acirc), log_blowup, num_queries, commit_pow_bits),
    }
  }

  -- 1 iff every element of `l` is boolean (0 or 1).
  fn assert_bits(l: List‹G›) -> G {
    match load(l) {
      ListNode.Nil => 1,
      ListNode.Cons(b, rest) =>
        assert_eq!(b * (b - 1), 0);
        assert_bits(rest),
    }
  }
  -- The verifying key's circuits at active positions, in order.
  fn select_active_circuits(circuits: List‹SysCircuit›, active: List‹G›) -> List‹SysCircuit› {
    match load(circuits) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(c, crest) =>
        let &ListNode.Cons(b, arest) = active;
        match b {
          0 => select_active_circuits(crest, arest),
          _ => store(ListNode.Cons(c, select_active_circuits(crest, arest))),
        },
    }
  }
  -- The preprocessed-index entries at active positions, in order.
  fn select_active_prep(prep_indices: List‹OptIdx›, active: List‹G›) -> List‹OptIdx› {
    match load(prep_indices) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(p, prest) =>
        let &ListNode.Cons(b, arest) = active;
        match b {
          0 => select_active_prep(prest, arest),
          _ => store(ListNode.Cons(p, select_active_prep(prest, arest))),
        },
    }
  }

  -- Read the public claims from the verifier's IO channel. Wire format (set by
  -- the prover-side harness): u64 `num_claims`, then per claim a u64 `num_vals`
  -- followed by `num_vals` raw `u64` `Val`s (8 LE bytes each, canonical < p).
  fn read_claims(stream: ByteStream) -> (List‹List‹U64››, ByteStream) {
    let (n, s) = read_count(stream);
    read_claims_n(s, n)
  }
  fn read_claims_n(stream: ByteStream, n: G) -> (List‹List‹U64››, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), stream),
      _ =>
        let (c, s) = read_one_claim(stream);
        let (rest, s2) = read_claims_n(s, n - 1);
        (store(ListNode.Cons(c, rest)), s2),
    }
  }
  fn read_one_claim(stream: ByteStream) -> (List‹U64›, ByteStream) {
    let (m, s) = read_count(stream);
    read_claim_vals_n(s, m)
  }
  fn read_claim_vals_n(stream: ByteStream, n: G) -> (List‹U64›, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), stream),
      _ =>
        let (x, s) = read_u64(stream);
        let (rest, s2) = read_claim_vals_n(s, n - 1);
        (store(ListNode.Cons(x, rest)), s2),
    }
  }
⟧

end MultiStark

end
