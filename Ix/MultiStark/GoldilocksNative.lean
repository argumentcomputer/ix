module
public import Ix.Aiur.Meta

/-!
# Goldilocks arithmetic, NATIVE form (`Goldilocks = G`)

The single module where the recursive verifier assumes the Aiur outer
field IS Goldilocks (`aiur::G = p3_goldilocks`): the inner field's
types, values, and operations, base and extension. Everything
downstream (`Pcs.lean`, `Verifier.lean`) does its inner-field
arithmetic exclusively through calls into this interface — always
inlined (`@g_add(..)`, `@eg_mul(..)`), so every function here splices
away at compile time.

The point of the indirection: a future `GoldilocksForeign.lean` will
provide the same interface over a non-Goldilocks outer field (e.g. the
BLS12-381 scalar field for the KZG terminal stage), where a `Goldilocks`
value is a different representation and the operations are emulated.
Swapping fields is then a matter of choosing which module to merge into
the toplevel — no verifier-side changes.

Contents:

- the representation types: `Goldilocks` (native: `G` itself) and the
  degree-2 extension `ExtGoldilocks = 𝔽_p[X]/(X² − 7)` (a pair
  `[c0, c1] = c0 + c1·X`);
- pure values: `g_zero`/`g_one`/`g_two`, the binomial modulus `g_w`
  (X² = 7), the multiplicative-coset generator `g_generator` (7), and
  the maximal two-adic root `g_two_adic_root` (order 2^32);
- base ring ops `g_add`/`g_sub`/`g_neg`/`g_mul`, the zero test
  `g_is_zero` (a native boolean), and the hinted inverse `gl_inverse`;
- the extension algebra `eg_add`/`eg_sub`/`eg_neg`/`eg_mul`/
  `eg_inverse`/`eg_div`/`eg_eq` (inverses reduce to the hinted base
  inverse via conjugate/norm);
- the byte boundaries `gl_val` (ingest: wire limbs → value, the field
  sum wraps mod p — exactly the reduction), `gl_lt_p` (canonicality),
  and `gl_to_bytes` (egress: hinted canonical LE decomposition, pinned
  by range checks + recomposition + canonicality).

The extension algebra is validated against `multi-stark`'s native
Goldilocks (`gl_ops_ref` in `multi-stark/src/types.rs`) via the
`multi-stark` self-test suite.
-/

public section

namespace MultiStark

def goldilocksNative := ⟦
  type Goldilocks = G
  type ExtGoldilocks = [Goldilocks; 2]

  -- ==========================================================================
  -- Pure values.
  -- ==========================================================================
  fn g_zero() -> Goldilocks { 0 }
  fn g_one() -> Goldilocks { 1 }
  fn g_two() -> Goldilocks { 2 }
  -- The extension's binomial modulus: ExtGoldilocks = 𝔽_p[X]/(X² − W).
  fn g_w() -> Goldilocks { 7 }
  -- The multiplicative-coset generator (Plonky3 `Goldilocks::GENERATOR`).
  fn g_generator() -> Goldilocks { 7 }
  -- A primitive 2^32-th root of unity (Plonky3's maximal two-adic
  -- generator); smaller-order roots derive by squaring (`two_adic_gen`).
  fn g_two_adic_root() -> Goldilocks { 1753635133440165772 }

  -- ==========================================================================
  -- Ring operations. Native: the outer field's own `+`/`-`/`*`.
  -- ==========================================================================
  fn g_add(a: Goldilocks, b: Goldilocks) -> Goldilocks { a + b }
  fn g_sub(a: Goldilocks, b: Goldilocks) -> Goldilocks { a - b }
  fn g_neg(a: Goldilocks) -> Goldilocks { 0 - a }
  fn g_mul(a: Goldilocks, b: Goldilocks) -> Goldilocks { a * b }

  -- 1 iff the value is zero (as a native boolean flag).
  fn g_is_zero(a: Goldilocks) -> G { eq_zero(a) }

  -- ==========================================================================
  -- Base field inverse: hinted, verified with one multiplication.
  -- `t = x·i − 1; x·t == 0 ∧ i·t == 0` forces `i = x⁻¹` when `x ≠ 0` (first
  -- assert gives x·i = 1) and `i = 0` when `x = 0` (t = −1, second assert).
  -- Matches the reference semantics `0⁻¹ = 0` (Fermat: 0^(p−2) = 0).
  -- ==========================================================================
  fn gl_inverse(x: Goldilocks) -> Goldilocks {
    let iv = unconstrained_g_inverse(x);
    let t = (x * iv) - 1;
    assert_eq!(x * t, 0);
    assert_eq!(iv * t, 0);
    iv
  }

  -- ==========================================================================
  -- Byte boundaries (ingest/egress). Native-representation-specific by
  -- nature: they define what a `Goldilocks` value IS on the wire.
  -- ==========================================================================

  -- The native field value of 8 LE bytes: `Σ xᵢ·256ⁱ` (mod p). For an
  -- arbitrary 8-byte value (< 2⁶⁴ < 2p) the field sum wraps at most once,
  -- yielding exactly the reduced representative — so this is both the
  -- canonical-bytes recomposition AND the wire-limb reduction.
  fn gl_val(x: [U8; 8]) -> G {
    to_field(x[0]) + 256 * to_field(x[1]) + 65536 * to_field(x[2])
      + 16777216 * to_field(x[3]) + 4294967296 * to_field(x[4])
      + 1099511627776 * to_field(x[5]) + 281474976710656 * to_field(x[6])
      + 72057594037927936 * to_field(x[7])
  }

  -- 1 iff the 8-byte LE integer is < p. Since p = (2³² − 1)·2³² + 1, we have
  -- x ≥ p ⟺ (high word = 2³² − 1) ∧ (low word ≥ 1). The high word is maximal
  -- iff its byte sum is 4·255 = 1020 (each byte is ≤ 255), and the low word
  -- is zero iff its byte sum is zero (a sum of four bytes cannot wrap).
  -- Inputs must be range-checked bytes. (Used by the challenger's rejection
  -- sampling, which works on raw sampled bytes.)
  fn gl_lt_p(x: [U8; 8]) -> G {
    let hi_max = eq_zero(
      to_field(x[4]) + to_field(x[5]) + to_field(x[6]) + to_field(x[7]) - 1020);
    let lo_zero = eq_zero(
      to_field(x[0]) + to_field(x[1]) + to_field(x[2]) + to_field(x[3]));
    1 - (hi_max * (1 - lo_zero))
  }

  -- Decompose a native field value into its canonical 8 LE bytes (egress:
  -- challenger observations). The bytes are prover hints; the range checks +
  -- recomposition equality + canonicality check pin the unique canonical
  -- decomposition (two distinct byte strings < p have distinct field values).
  fn gl_to_bytes(v: G) -> [U8; 8] {
    let b = unconstrained_g_to_bytes(v);
    let (c0, c1) = u8_range_check(b[0], b[1]);
    let (c2, c3) = u8_range_check(b[2], b[3]);
    let (c4, c5) = u8_range_check(b[4], b[5]);
    let (c6, c7) = u8_range_check(b[6], b[7]);
    let r = [c0, c1, c2, c3, c4, c5, c6, c7];
    assert_eq!(@gl_val(r), v);
    assert_eq!(@gl_lt_p(r), 1);
    r
  }

  -- ==========================================================================
  -- Extension algebra ExtGoldilocks = 𝔽_p[X]/(X² − 7), over the base
  -- interface (no raw arithmetic below this line).
  -- ==========================================================================
  fn eg_add(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    [@g_add(a[0], b[0]), @g_add(a[1], b[1])]
  }
  fn eg_sub(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    [@g_sub(a[0], b[0]), @g_sub(a[1], b[1])]
  }
  fn eg_neg(a: ExtGoldilocks) -> ExtGoldilocks {
    [@g_neg(a[0]), @g_neg(a[1])]
  }
  -- (a0 + a1·X)(b0 + b1·X) = (a0·b0 + 7·a1·b1) + (a0·b1 + a1·b0)·X.
  fn eg_mul(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    [@g_add(@g_mul(a[0], b[0]), @g_mul(@g_w(), @g_mul(a[1], b[1]))),
     @g_add(@g_mul(a[0], b[1]), @g_mul(a[1], b[0]))]
  }
  -- conjugate ā = a0 − a1·X, norm a·ā = a0² − 7·a1² ∈ 𝔽_p, a⁻¹ = ā / norm.
  fn eg_inverse(a: ExtGoldilocks) -> ExtGoldilocks {
    let norm = @g_sub(@g_mul(a[0], a[0]), @g_mul(@g_w(), @g_mul(a[1], a[1])));
    let ninv = @gl_inverse(norm);
    [@g_mul(a[0], ninv), @g_mul(@g_neg(a[1]), ninv)]
  }
  fn eg_div(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    @eg_mul(a, @eg_inverse(b))
  }
  -- 1 iff two extension elements are equal.
  fn eg_eq(a: ExtGoldilocks, b: ExtGoldilocks) -> G {
    @g_is_zero(@g_sub(a[0], b[0])) * @g_is_zero(@g_sub(a[1], b[1]))
  }
⟧

end MultiStark

end
