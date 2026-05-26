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

  -- ==========================================================================
  -- OOD evaluation domain math (`TwoAdicMultiplicativeCoset`, Goldilocks).
  -- The trace domain for a circuit of size 2^L is the order-2^L subgroup H
  -- (shift = 1) generated by `two_adic_gen(L)`.
  -- ==========================================================================

  -- x^(2^k): k repeated squarings (base field).
  fn exp_pow2(x: G, k: G) -> G {
    match k {
      0 => x,
      _ => exp_pow2(x * x, k - 1),
    }
  }

  -- e^(2^k) in the extension field.
  fn ext_exp_pow2(e: Ext, k: G) -> Ext {
    match k {
      0 => e,
      _ => ext_exp_pow2(ext_mul(e, e), k - 1),
    }
  }

  -- `two_adic_generator(bits)` — a primitive 2^bits root of unity in Goldilocks
  -- (`Plonky3/goldilocks/src/goldilocks.rs::TWO_ADIC_GENERATORS`).
  fn two_adic_gen(bits: G) -> G {
    match bits {
      0  => 0x0000000000000001,
      1  => 0xffffffff00000000,
      2  => 0x0001000000000000,
      3  => 0xfffffffeff000001,
      4  => 0xefffffff00000001,
      5  => 0x00003fffffffc000,
      6  => 0x0000008000000000,
      7  => 0xf80007ff08000001,
      8  => 0xbf79143ce60ca966,
      9  => 0x1905d02a5c411f4e,
      10 => 0x9d8f2ad78bfed972,
      11 => 0x0653b4801da1c8cf,
      12 => 0xf2c35199959dfcb6,
      13 => 0x1544ef2335d17997,
      14 => 0xe0ee099310bba1e2,
      15 => 0xf6b2cffe2306baac,
      16 => 0x54df9630bf79450e,
      17 => 0xabd0a6e8aa3d8a0e,
      18 => 0x81281a7b05f9beac,
      19 => 0xfbd41c6b8caa3302,
      20 => 0x30ba2ecd5e93e76d,
      21 => 0xf502aef532322654,
      22 => 0x4b2a18ade67246b5,
      23 => 0xea9d5a1336fbc98b,
      24 => 0x86cdcc31c307e171,
      25 => 0x4bbaf5976ecfefd8,
      26 => 0xed41d05b78d6e286,
      27 => 0x10d78dd8915a171d,
      28 => 0x59049500004a4485,
      29 => 0xdfa8c93ba46d2666,
      30 => 0x7e9bd009b86a0845,
      31 => 0x400a7f755588e659,
      _  => 0x185629dcda58878c,
    }
  }

  -- Vanishing polynomial of the trace domain (shift = 1, size 2^L) at point ζ:
  -- `Z_H(ζ) = ζ^(2^L) - 1`.
  fn trace_vanishing(zeta: Ext, l: G) -> Ext {
    ext_sub(ext_exp_pow2(zeta, l), [1, 0])
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
    let ginv = g_inverse(two_adic_gen(l));
    let is_first = ext_div(zh, ext_sub(zeta, [1, 0]));
    let is_last = ext_div(zh, ext_sub(zeta, [ginv, 0]));
    let is_trans = ext_sub(zeta, [ginv, 0]);
    let inv_van = ext_inverse(zh);
    (is_first, is_last, is_trans, inv_van)
  }

  -- Self-test for the OOD domain math: the subgroup generator is a primitive
  -- 2^L-th root of unity (g^(2^L) = 1, g^(2^(L-1)) = -1), and the vanishing
  -- polynomial is zero at a domain point.
  pub fn ood_domain_test() -> G {
    let g = two_adic_gen(3);
    assert_eq!(exp_pow2(g, 3), 1);
    assert_eq!(exp_pow2(g, 2), 0 - 1);
    let v = trace_vanishing([g, 0], 3);
    assert_eq!(v[0], 0);
    assert_eq!(v[1], 0);
    1
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

  -- Self-test for the extension-field arithmetic the OOD check is built on:
  -- base inverse (7·7⁻¹ = 1) and extension inverse ((3+5X)·(3+5X)⁻¹ = 1).
  pub fn ext_arith_test() -> G {
    assert_eq!(7 * g_inverse(7), 1);
    let a = [3, 5];
    let prod = ext_mul(a, ext_inverse(a));
    assert_eq!(prod[0], 1);
    assert_eq!(prod[1], 0);
    1
  }
⟧

end MultiStark

end
