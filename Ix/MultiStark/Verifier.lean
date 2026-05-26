module
public import Ix.Aiur.Meta
public import Ix.IxVM.Core
public import Ix.IxVM.ByteStream
public import Ix.MultiStark.Deserialize
public import Ix.MultiStark.Keccak
public import Ix.MultiStark.Pcs

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
* Step 4: the PCS check, via the accept-stub `pcs_verify`.

### Stubbed / TODO
* Steps 3 and 5 need extension-field (`GoldilocksExt2`) arithmetic, evaluation
  domains (vanishing polynomials, subgroup generators), the Keccak Fiat-Shamir
  challenger (`SerializingChallenger64<HashChallenger<u8, Keccak256Hash, 32>>`,
  which our `keccak256` can drive), and the per-circuit AIR constraint folder.
  None of that infrastructure exists in Aiur yet, so these steps are left as the
  next milestone. With the PCS stubbed and steps 3/5 absent, this verifier is a
  **structural** verifier, not yet sound.
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

  -- Sample a degree-2 extension element: two base samples (`from_basis_*`),
  -- returning their raw 8-byte LE limbs (so they can be re-observed) and the
  -- threaded challenger. NOTE: the ~2⁻³² rejection band (limb ≥ p) is not
  -- handled — `limb_to_field` reduces mod p instead. Honest rejection sampling
  -- is a TODO for bit-exact agreement with the prover.
  fn ch_sample_ext(input: ByteStream, output: ByteStream) -> ([U8; 8], [U8; 8], ByteStream, ByteStream) {
    let (c0, i0, o0) = ch_sample8(input, output);
    let (c1, i1, o1) = ch_sample8(i0, o0);
    (c0, c1, i1, o1)
  }

  -- Replay the verifier transcript and derive the four challenges
  -- `(lookup, fingerprint, alpha, zeta)`. Mirrors `verify_multiple_claims`'s
  -- challenger sequence. SIMPLIFICATIONS (TODO): the preprocessed commitment
  -- (from the verifying key) and the claims are not observed yet, and no
  -- rejection sampling is done — so the values are not yet prover-faithful when
  -- the system has preprocessed circuits / claims. The structure is exact.
  fn fiat_shamir(s1: MerkleCap, s2: MerkleCap, q: MerkleCap, lds: List‹U8›)
      -> (Ext, Ext, Ext, Ext) {
    -- observe stage_1 commitment, then the trace heights (log_degrees)
    let input = cap_onto(s1, store(ListNode.Nil));
    let input = log_degrees_onto(lds, input);
    -- sample lookup challenge, then observe it back
    let (l0, l1, input, _ol) = ch_sample_ext(input, store(ListNode.Nil));
    let input = b8_onto(l0, b8_onto(l1, input));
    -- sample fingerprint challenge, then observe it back
    let (f0, f1, input, _of) = ch_sample_ext(input, store(ListNode.Nil));
    let input = b8_onto(f0, b8_onto(f1, input));
    -- observe stage_2 commitment
    let input = cap_onto(s2, input);
    -- sample constraint challenge α (not observed)
    let (a0, a1, input, _oa) = ch_sample_ext(input, store(ListNode.Nil));
    -- observe quotient commitment
    let input = cap_onto(q, input);
    -- sample out-of-domain point ζ
    let (z0, z1, _input, _oz) = ch_sample_ext(input, store(ListNode.Nil));
    ([limb_to_field(l0), limb_to_field(l1)],
     [limb_to_field(f0), limb_to_field(f1)],
     [limb_to_field(a0), limb_to_field(a1)],
     [limb_to_field(z0), limb_to_field(z1)])
  }

  -- Structural + accumulator + Fiat-Shamir verification of a deserialized proof.
  --
  -- Returns 1 on success; `assert_eq!` aborts the (proof) execution on any
  -- failed check, exactly as the Rust verifier returns `Err`.
  fn verify(proof: Proof) -> G {
    match proof {
      Proof.Mk(commitments, accs, log_degrees, opening,
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

        -- Step 3: Fiat-Shamir challenger replay → (lookup, fingerprint, α, ζ).
        -- Derived here; consumed by the OOD check (step 5, still TODO).
        let Commitments.Mk(s1, s2, q) = commitments;
        let _challenges = fiat_shamir(s1, s2, q, log_degrees);

        -- Step 4: PCS opening proof (stubbed — accepts; see Pcs.lean).
        let _pcs = pcs_verify(opening);

        -- Step 5 (OOD composition/quotient check) is TODO — it needs the
        -- per-circuit AIR constraint folder and evaluation-domain arithmetic.
        1,
    }
  }
⟧

end MultiStark

end
