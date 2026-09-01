module
public import Ix.Aiur.Meta

/-!
# Field interface: Goldilocks, NATIVE form (`Val = G`)

The single module where the recursive verifier assumes the Aiur outer
field IS Goldilocks (`aiur::G = p3_goldilocks`): the inner field's
types, values, and operations, base and extension. Everything
downstream (`Pcs/Fri.lean`, `Verifier.lean`, `Domain.lean`, the
deserializers) does its inner-field arithmetic exclusively through plain
calls into this interface (`val_add(..)`, `ext_mul(..)`). Whether a call
splices is the IMPLEMENTOR's decision (`inline fn`, see
`Ix/Aiur/Stages/Source.lean`): here every operation is trivial native
arithmetic, so all of them are `inline` and splice away at compile time.

The point of the indirection: `GoldilocksBytes.lean` provides the same
interface over a smaller outer field (e.g. KoalaBear under the Hypercube
backend), where a `Val` is a byte-limb representation and the operations
are emulated. Swapping fields is then a matter of choosing which module
to merge into the toplevel — no verifier-side changes.

Contents:

- the representation types: `Val` (native: `G` itself) and the degree-2
  extension `Ext = 𝔽_p[X]/(X² − 7)` (a pair `[c0, c1] = c0 + c1·X`);
- consts: `.VAL_ZERO`/`.VAL_ONE`/`.VAL_TWO`, the binomial modulus `.EXT_W`
  (X² = 7), the multiplicative-coset generator `val_generator` (7), and
  the maximal two-adic root `val_two_adic_root` (order 2^32);
- base ring ops `val_add`/`val_sub`/`val_neg`/`val_mul`, the zero test
  `val_is_zero` (a native boolean), and the hinted inverse `val_inverse`;
- the extension algebra `ext_add`/`ext_sub`/`ext_neg`/`ext_mul`/
  `ext_inverse`/`ext_div`/`ext_eq` (inverses reduce to the hinted base
  inverse via conjugate/norm);
- the byte boundaries `val_from_bytes` (ingest: wire limbs → value, the field
  sum wraps mod p — exactly the reduction), `bytes_lt_modulus` (canonicality),
  and `val_to_bytes` (egress: hinted canonical LE decomposition, pinned
  by range checks + recomposition + canonicality).

The extension algebra is validated against `multi-stark`'s native
Goldilocks (`gl_ops_ref` in `multi-stark/src/types.rs`) via the
`multi-stark` self-test suite.
-/

public section

namespace MultiStark

def goldilocksNative := ⟦
  type Val = G
  type Ext = [Val; 2]

  -- ==========================================================================
  -- Pure values.
  -- ==========================================================================
  const VAL_ZERO: Val = 0
  const VAL_ONE: Val = 1
  const VAL_TWO: Val = 2
  -- The extension's binomial modulus: ExtGoldilocks = 𝔽_p[X]/(X² − W).
  const EXT_W: Val = 7
  -- The multiplicative-coset generator (Plonky3 `Goldilocks::GENERATOR`).
  const VAL_GENERATOR: Val = 7
  -- A primitive 2^32-th root of unity (Plonky3's maximal two-adic
  -- generator); smaller-order roots derive by squaring (`two_adic_gen`).
  const VAL_TWO_ADIC_ROOT: Val = 1753635133440165772
  -- A small (< 2¹⁶) constant from its two little-endian bytes — the vk's
  -- ConstSmall ingest (byte sums cannot wrap, and 2¹⁶ < p in every field).
  inline fn val_from_u16(lo: U8, hi: U8) -> Val {
    to_field(lo) + 256 * to_field(hi)
  }

  -- ==========================================================================
  -- Ring operations. Native: the outer field's own `+`/`-`/`*`.
  -- ==========================================================================
  inline fn val_add(a: Val, b: Val) -> Val { a + b }
  inline fn val_sub(a: Val, b: Val) -> Val { a - b }
  inline fn val_neg(a: Val) -> Val { 0 - a }
  inline fn val_mul(a: Val, b: Val) -> Val { a * b }

  -- 1 iff the value is zero (as a native boolean flag).
  inline fn val_is_zero(a: Val) -> G { eq_zero(a) }

  -- ==========================================================================
  -- Base field inverse: hinted, verified with one multiplication.
  -- `t = x·i − 1; x·t == 0 ∧ i·t == 0` forces `i = x⁻¹` when `x ≠ 0` (first
  -- assert gives x·i = 1) and `i = 0` when `x = 0` (t = −1, second assert).
  -- Matches the reference semantics `0⁻¹ = 0` (Fermat: 0^(p−2) = 0).
  -- ==========================================================================
  inline fn val_inverse(x: Val) -> Val {
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
  inline fn val_from_bytes(x: [U8; 8]) -> G {
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
  inline fn bytes_lt_modulus(x: [U8; 8]) -> G {
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
  inline fn val_to_bytes(v: G) -> [U8; 8] {
    let b = unconstrained_g_to_bytes(v);
    let (c0, c1) = u8_range_check(b[0], b[1]);
    let (c2, c3) = u8_range_check(b[2], b[3]);
    let (c4, c5) = u8_range_check(b[4], b[5]);
    let (c6, c7) = u8_range_check(b[6], b[7]);
    let r = [c0, c1, c2, c3, c4, c5, c6, c7];
    assert_eq!(val_from_bytes(r), v);
    assert_eq!(bytes_lt_modulus(r), 1);
    r
  }

  -- ==========================================================================
  -- Extension algebra ExtGoldilocks = 𝔽_p[X]/(X² − 7), over the base
  -- interface (no raw arithmetic below this line).
  -- ==========================================================================
  inline fn ext_add(a: Ext, b: Ext) -> Ext {
    [val_add(a[0], b[0]), val_add(a[1], b[1])]
  }
  inline fn ext_sub(a: Ext, b: Ext) -> Ext {
    [val_sub(a[0], b[0]), val_sub(a[1], b[1])]
  }
  inline fn ext_neg(a: Ext) -> Ext {
    [val_neg(a[0]), val_neg(a[1])]
  }
  -- (a0 + a1·X)(b0 + b1·X) = (a0·b0 + 7·a1·b1) + (a0·b1 + a1·b0)·X.
  inline fn ext_mul(a: Ext, b: Ext) -> Ext {
    [val_add(val_mul(a[0], b[0]), val_mul(.EXT_W, val_mul(a[1], b[1]))),
     val_add(val_mul(a[0], b[1]), val_mul(a[1], b[0]))]
  }
  -- conjugate ā = a0 − a1·X, norm a·ā = a0² − 7·a1² ∈ 𝔽_p, a⁻¹ = ā / norm.
  inline fn ext_inverse(a: Ext) -> Ext {
    let norm = val_sub(val_mul(a[0], a[0]), val_mul(.EXT_W, val_mul(a[1], a[1])));
    let ninv = val_inverse(norm);
    [val_mul(a[0], ninv), val_mul(val_neg(a[1]), ninv)]
  }
  inline fn ext_div(a: Ext, b: Ext) -> Ext {
    ext_mul(a, ext_inverse(b))
  }
  -- 1 iff two extension elements are equal.
  inline fn ext_eq(a: Ext, b: Ext) -> G {
    val_is_zero(val_sub(a[0], b[0])) * val_is_zero(val_sub(a[1], b[1]))
  }
⟧

end MultiStark

end
