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
3. **Fiat-Shamir replay** — reconstruct the Keccak challenger: observe
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
  observes the verifying key's preprocessed commitment, the stage_1 commitment,
  the trace heights, and the public claims (in that order), then samples and
  re-observes the lookup/fingerprint challenges, observes stage_2, samples α,
  observes the quotient commitment, and samples ζ — matching
  `verify_multiple_claims` byte-for-byte.
* Step 5: the out-of-domain composition/quotient check (`ood_verify`). For each
  circuit it recomputes `composition(ζ)` by replaying the AIR constraint folder
  (`VerifierConstraintFolder` + `LookupAir::eval`) over the deserialized
  symbolic system and the opened values, recomputes `quotient(ζ)` from the
  opened quotient chunks (barycentric `zps` weights over the split quotient
  domains), and asserts `composition(ζ) · inv_vanishing(ζ) == quotient(ζ)`.
  Validated end-to-end against a real factorial proof (the `recursive-verifier`
  test runner, `Tests/MultiStark.lean`): the verifier accepts the honest proof
  and rejects a tampered claim.

### Stubbed / TODO
* Base-field samples are rejection-sampled (`ch_sample_field`): a raw 8-byte
  limb in the band `[p, 2⁶⁴)` (probability ≈ 2⁻³²) is discarded and redrawn,
  consuming challenger bytes exactly as `SerializingChallenger64::sample` does.
* The PCS opening proof (`pcs_verify`) is still an accept-stub. With the PCS
  stubbed, this verifier checks every algebraic relation except FRI proximity,
  so it is not yet fully sound.
-/

public section

namespace MultiStark

def verifier := ⟦
  -- An extension element `[c0, c1]` (`= c0 + c1·X`) is zero iff both Goldilocks
  -- coefficients are zero. (`read_ext` already reduced the limbs mod p.)
  fn ext_is_zero(e: Ext) -> G {
    gl_is_zero(e[0]) * gl_is_zero(e[1])
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
  -- Keccak256Hash, 32>>`. The inner byte challenger keeps an `input` buffer; a
  -- `sample` with empty `output` flushes (`input := output := keccak256(input)`)
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
        let h = keccak256(input);
        let fwd = digest_onto(h, store(ListNode.Nil));
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
  -- exactly as in the reference. `raw < p` ⟺ `sub8(raw, p)` borrows. The
  -- accepted limb is canonical (< p) by construction.
  fn ch_sample_field(input: ByteStream, output: ByteStream) -> ([U8; 8], ByteStream, ByteStream) {
    let (raw, i1, o1) = ch_sample8(input, output);
    let (_d, borrow) = sub8(raw, gl_p());
    match borrow {
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

  -- `sample_bits(n)` (FRI query index). `SerializingChallenger64::sample_bits`
  -- reads one 8-byte sample as a little-endian u64 and masks the low `n` bits.
  -- We return the low `n` bits as a list (LSB first = the leaf→root Merkle/FRI
  -- path), built from the 8 sampled bytes' bit decompositions (reusing keccak's
  -- `cons8`), truncated to `n`.
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
  -- first hashed, matching `keccak256`'s absorption order), so an observation
  -- appends — `b8_onto` PREPENDS, hence the `list_concat`.
  fn snoc_b8(input: ByteStream, b: [U8; 8]) -> ByteStream {
    list_concat(input, b8_onto(b, store(ListNode.Nil)))
  }
  -- Append (observe) a commitment (`MerkleCap`) at the end of the buffer.
  fn snoc_cap(input: ByteStream, cap: MerkleCap) -> ByteStream {
    list_concat(input, cap_onto(cap, store(ListNode.Nil)))
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
    ([gl_reduce(c0), gl_reduce(c1)], i1, o1)
  }

  -- Append a claim's values (each `Val` as 8 LE bytes) onto `tail`, in order.
  fn claim_vals_onto(vals: List‹U64›, tail: ByteStream) -> ByteStream {
    match load(vals) {
      ListNode.Nil => tail,
      ListNode.Cons(v, rest) => b8_onto(v, claim_vals_onto(rest, tail)),
    }
  }
  -- Append every claim's values (`challenger.observe_slice(claim)` per claim).
  fn claims_onto(claims: List‹List‹U64››, tail: ByteStream) -> ByteStream {
    match load(claims) {
      ListNode.Nil => tail,
      ListNode.Cons(c, rest) => claim_vals_onto(c, claims_onto(rest, tail)),
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
  --   observe preprocessed_commit (if any) → stage_1 → log_degrees → claims;
  --   sample lookup, observe it; sample fingerprint, observe it;
  --   observe stage_2; sample α; observe quotient; sample ζ.
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
  fn fiat_shamir(prep: MerkleCap, s1: MerkleCap, s2: MerkleCap, q: MerkleCap,
      lds: List‹U8›, claims: List‹List‹U64››) -> (Ext, Ext, Ext, Ext, ByteStream) {
    -- Initial transcript, front-to-back: prep, stage_1, log_degrees, claims.
    -- Built inner-to-outer with the prepend helpers so the result is in
    -- forward (observation) order.
    let input = claims_onto(claims, store(ListNode.Nil));
    let input = log_degrees_onto(lds, input);
    let input = cap_onto(s1, input);
    let input = cap_onto(prep, input);
    -- sample lookup challenge, then observe it back (append)
    let (l0, l1, input, _ol) = ch_sample_ext(input, store(ListNode.Nil));
    let input = snoc_b8(snoc_b8(input, l0), l1);
    -- sample fingerprint challenge, then observe it back
    let (f0, f1, input, _of) = ch_sample_ext(input, store(ListNode.Nil));
    let input = snoc_b8(snoc_b8(input, f0), f1);
    -- observe stage_2 commitment
    let input = snoc_cap(input, s2);
    -- sample constraint challenge α (not observed)
    let (a0, a1, input, _oa) = ch_sample_ext(input, store(ListNode.Nil));
    -- observe quotient commitment
    let input = snoc_cap(input, q);
    -- sample out-of-domain point ζ; keep the resulting `input` for the PCS phase
    let (z0, z1, zinput, _oz) = ch_sample_ext(input, store(ListNode.Nil));
    ([gl_reduce(l0), gl_reduce(l1)],
     [gl_reduce(f0), gl_reduce(f1)],
     [gl_reduce(a0), gl_reduce(a1)],
     [gl_reduce(z0), gl_reduce(z1)],
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
  fn two_adic_gen(bits: G) -> [U8; 8] {
    match bits {
      0  => [1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
      1  => [0u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 255u8],
      2  => [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 1u8, 0u8],
      3  => [1u8, 0u8, 0u8, 255u8, 254u8, 255u8, 255u8, 255u8],
      4  => [1u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 239u8],
      5  => [0u8, 192u8, 255u8, 255u8, 255u8, 63u8, 0u8, 0u8],
      6  => [0u8, 0u8, 0u8, 0u8, 128u8, 0u8, 0u8, 0u8],
      7  => [1u8, 0u8, 0u8, 8u8, 255u8, 7u8, 0u8, 248u8],
      8  => [102u8, 169u8, 12u8, 230u8, 60u8, 20u8, 121u8, 191u8],
      9  => [78u8, 31u8, 65u8, 92u8, 42u8, 208u8, 5u8, 25u8],
      10 => [114u8, 217u8, 254u8, 139u8, 215u8, 42u8, 143u8, 157u8],
      11 => [207u8, 200u8, 161u8, 29u8, 128u8, 180u8, 83u8, 6u8],
      12 => [182u8, 252u8, 157u8, 149u8, 153u8, 81u8, 195u8, 242u8],
      13 => [151u8, 121u8, 209u8, 53u8, 35u8, 239u8, 68u8, 21u8],
      14 => [226u8, 161u8, 187u8, 16u8, 147u8, 9u8, 238u8, 224u8],
      15 => [172u8, 186u8, 6u8, 35u8, 254u8, 207u8, 178u8, 246u8],
      16 => [14u8, 69u8, 121u8, 191u8, 48u8, 150u8, 223u8, 84u8],
      17 => [14u8, 138u8, 61u8, 170u8, 232u8, 166u8, 208u8, 171u8],
      18 => [172u8, 190u8, 249u8, 5u8, 123u8, 26u8, 40u8, 129u8],
      19 => [2u8, 51u8, 170u8, 140u8, 107u8, 28u8, 212u8, 251u8],
      20 => [109u8, 231u8, 147u8, 94u8, 205u8, 46u8, 186u8, 48u8],
      21 => [84u8, 38u8, 50u8, 50u8, 245u8, 174u8, 2u8, 245u8],
      22 => [181u8, 70u8, 114u8, 230u8, 173u8, 24u8, 42u8, 75u8],
      23 => [139u8, 201u8, 251u8, 54u8, 19u8, 90u8, 157u8, 234u8],
      24 => [113u8, 225u8, 7u8, 195u8, 49u8, 204u8, 205u8, 134u8],
      25 => [216u8, 239u8, 207u8, 110u8, 151u8, 245u8, 186u8, 75u8],
      26 => [134u8, 226u8, 214u8, 120u8, 91u8, 208u8, 65u8, 237u8],
      27 => [29u8, 23u8, 90u8, 145u8, 216u8, 141u8, 215u8, 16u8],
      28 => [133u8, 68u8, 74u8, 0u8, 0u8, 149u8, 4u8, 89u8],
      29 => [102u8, 38u8, 109u8, 164u8, 59u8, 201u8, 168u8, 223u8],
      30 => [69u8, 8u8, 106u8, 184u8, 9u8, 208u8, 155u8, 126u8],
      31 => [89u8, 230u8, 136u8, 85u8, 117u8, 127u8, 10u8, 64u8],
      _  => [140u8, 135u8, 88u8, 218u8, 220u8, 41u8, 86u8, 24u8],
    }
  }

  -- Vanishing polynomial of the trace domain (shift = 1, size 2^L) at point ζ:
  -- `Z_H(ζ) = ζ^(2^L) - 1`.
  fn trace_vanishing(zeta: Ext, l: G) -> Ext {
    eg_sub(ext_exp_pow2(zeta, l), [gl_one(), gl_zero()])
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
    let is_first = eg_div(zh, eg_sub(zeta, [gl_one(), gl_zero()]));
    let is_last = eg_div(zh, eg_sub(zeta, [ginv, gl_zero()]));
    let is_trans = eg_sub(zeta, [ginv, gl_zero()]);
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
      Proof.Mk(_commitments, accs, _log_degrees, _opening,
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
  -- As with `fiat_shamir`, claims are not observed; this assumes the no-claims
  -- case, so the running lookup accumulator starts at the zero extension
  -- element (`acc` in Rust = ExtVal::ZERO).
  -- ==========================================================================

  -- One Horner fold step of the constraint folder: `acc := acc·α + x`
  -- (`VerifierConstraintFolder::assert_zero` / `assert_zero_ext`).
  fn ood_fold(acc: Ext, alpha: Ext, x: Ext) -> Ext {
    eg_add(eg_mul(acc, alpha), x)
  }

  -- Reconstruct an extension element from its two opened base coordinates,
  -- `from_ext_basis([c0, c1]) = c0 + c1·X` (the ExtVal basis is `[1, X]`).
  fn from_ext_basis(c0: Ext, c1: Ext) -> Ext {
    eg_add(c0, eg_mul(c1, [gl_zero(), gl_one()]))
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
          SysEntry.Stage2(_o) => [gl_zero(), gl_zero()],
          SysEntry.Public => [gl_zero(), gl_zero()],
          SysEntry.Stage2Public => [gl_zero(), gl_zero()],
          SysEntry.Challenge => [gl_zero(), gl_zero()],
        },
      SymExpr.IsFirstRow => [gl_zero(), gl_zero()],
      SymExpr.IsLastRow => [gl_zero(), gl_zero()],
      SymExpr.IsTransition => [gl_zero(), gl_zero()],
      SymExpr.Const(c) => [c, gl_zero()],
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
      ListNode.Nil => [gl_zero(), gl_zero()],
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
        let bc = eg_mul(x, eg_sub(x, [gl_one(), gl_zero()]));
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
        let c = eg_sub(eg_mul(message, minv), [gl_one(), gl_zero()]);
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
        let acc = fold_zeros([gl_zero(), gl_zero()], alpha, zeros, main);
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
        let acc = ood_fold([gl_zero(), gl_zero()], alpha, eg_mul(is_real, eg_sub(is_real, [gl_one(), gl_zero()])));
        -- is_real_transition = is_real_next · is_transition
        let irt = eg_mul(is_real_next, ist);
        -- when(irt).assert_one(is_real) = irt·(is_real - 1)
        let acc = ood_fold(acc, alpha, eg_mul(irt, eg_sub(is_real, [gl_one(), gl_zero()])));
        -- when(irt).assert_eq(ptr+1, ptr_next) = irt·(ptr + 1 - ptr_next)
        let acc = ood_fold(acc, alpha, eg_mul(irt, eg_sub(eg_add(ptr, [gl_one(), gl_zero()]), ptr_next)));
        ood_comp_tail(acc, lookups, main, prep, s2row, s2next, isf, isl, ist, lch, fch, accp, naccp, alpha),
      SysAir.Bytes1 =>
        ood_comp_tail([gl_zero(), gl_zero()], lookups, main, prep, s2row, s2next, isf, isl, ist, lch, fch, accp, naccp, alpha),
      SysAir.Bytes2 =>
        ood_comp_tail([gl_zero(), gl_zero()], lookups, main, prep, s2row, s2next, isf, isl, ist, lch, fch, accp, naccp, alpha),
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

  -- base-field power `base^e` (e small: the chunk index, < qd). `base` is a
  -- non-native Goldilocks element; `e` is a native loop counter.
  fn g_pow(base: [U8; 8], e: G) -> [U8; 8] {
    match e {
      0 => gl_one(),
      _ => gl_mul(base, g_pow(base, e - 1)),
    }
  }

  -- `Z_{Dⱼ}(x) = (x · shift_j⁻¹)^(2^L) - 1`, evaluated at extension point `x`.
  fn vanish_chunk(x: Ext, l: G, shiftinv: [U8; 8]) -> Ext {
    eg_sub(ext_exp_pow2(eg_mul(x, [shiftinv, gl_zero()]), l), [gl_one(), gl_zero()])
  }

  -- `zpsₜ = Πⱼ≠ₜ Z_{Dⱼ}(ζ) / Z_{Dⱼ}(shift_t)`. Iterates j over `[jidx, jidx+rem)`.
  fn zps_prod(acc: Ext, zeta: Ext, l: G, g_q: [U8; 8], shift_t: [U8; 8], jidx: G, rem: G, t: G) -> Ext {
    match rem {
      0 => acc,
      _ =>
        let shiftinv = gl_inverse(gl_mul(gl_seven(), g_pow(g_q, jidx)));
        -- skip the j = t factor (the chunk's own domain); branch in tail
        -- position so the inner match is not a non-tail match.
        match eq_zero(jidx - t) {
          1 => zps_prod(acc, zeta, l, g_q, shift_t, jidx + 1, rem - 1, t),
          _ =>
            let factor = eg_mul(vanish_chunk(zeta, l, shiftinv),
                                 eg_inverse(vanish_chunk([shift_t, gl_zero()], l, shiftinv)));
            zps_prod(eg_mul(acc, factor), zeta, l, g_q, shift_t, jidx + 1, rem - 1, t),
        },
    }
  }

  -- `quotient(ζ) = Σₜ zpsₜ · from_ext_basis(chunkₜ)`, iterating the `qd` chunks
  -- (`q_opened[idx][0] = [c0, c1]`).
  fn quotient_sum(acc: Ext, zeta: Ext, l: G, qd: G, g_q: [U8; 8],
      q_opened: OpenedRound, idx: G, rem: G, t: G) -> Ext {
    match rem {
      0 => acc,
      _ =>
        let shift_t = gl_mul(gl_seven(), g_pow(g_q, t));
        let zps_t = zps_prod([gl_one(), gl_zero()], zeta, l, g_q, shift_t, 0, qd, t);
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
        let quot = quotient_sum([gl_zero(), gl_zero()], zeta, l, qd, g_q, q_opened, lastq, qd, 0);
        assert_eq!(eg_eq(eg_mul(comp, invv), quot), 1);
        ood_loop(rest, prep_indices, log_degrees, accs, stage1, stage2, prep_opt,
                 q_opened, i + 1, naccp, lastq + qd, lch, fch, alpha, zeta),
    }
  }

  -- The fingerprint of one claim's values: `Σ vᵢ · fch^i` (each `vᵢ` lifted from
  -- its raw u64 limb to an extension element). Mirrors `lookup::fingerprint`.
  fn fingerprint_vals(fch: Ext, vals: List‹U64›) -> Ext {
    match load(vals) {
      ListNode.Nil => [gl_zero(), gl_zero()],
      ListNode.Cons(v, rest) =>
        eg_add([gl_reduce(v), gl_zero()], eg_mul(fch, fingerprint_vals(fch, rest))),
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
    -- public inputs. `log_blowup` also lives in the (digest-bound) verifying
    -- key's CommitmentParameters — assert the two agree.
    let Sys.Mk(params, circuits, commit, prep_indices) = sys;
    let SysParams.Mk(log_blowup, _cap_height) = params;
    assert_eq!(eq_zero(log_blowup - log_blowup_pub), 1);
    match proof {
      Proof.Mk(commitments, accs, log_degrees, opening,
               q_opened, prep_opt, stage1, stage2) =>
        let Commitments.Mk(s1c, s2c, qc) = commitments;
        let prep_cap = opt_commit_cap(commit);
        let (lch, fch, alpha, zeta, post_zeta_input) = fiat_shamir(prep_cap, s1c, s2c, qc, log_degrees, claims);
        let acc0 = claims_acc([gl_zero(), gl_zero()], claims, lch, fch);
        -- Step 5: OOD composition/quotient identity for every circuit.
        let _ood = ood_loop(circuits, prep_indices, log_degrees, accs, stage1, stage2,
                 prep_opt, q_opened, 0, acc0, 0, lch, fch, alpha, zeta);
        -- Step 4: FRI PCS proximity + opening consistency, continuing the same
        -- Fiat-Shamir transcript past ζ (observe opened values → α, βs, query).
        pcs_fri_verify(post_zeta_input, stage1, stage2, q_opened, prep_opt, opening,
          s1c, s2c, qc, prep_cap, circuits, prep_indices, log_degrees, zeta,
          list_length(circuits), log_blowup, num_queries, commit_pow_bits),
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
    read_u64_vec_n(s, m)
  }
⟧

end MultiStark

end
