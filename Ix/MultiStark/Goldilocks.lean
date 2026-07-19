module
public import Ix.Aiur.Meta

/-!
# Goldilocks field arithmetic on the native field (`Goldilocks = G`)

The recursive verifier computes on the *inner* proof's field (Goldilocks) —
and Aiur's outer field IS Goldilocks (`aiur::G = p3_goldilocks`), so the
arithmetic runs directly on native `+`/`*`. A `Goldilocks` element is a
plain field value (canonical by construction — `G` is the field), and
`ExtGoldilocks = [G; 2]` is the degree-2 extension `𝔽_p[X]/(X² − 7)`.

Byte form exists only at true boundaries:

- **ingest**: wire limbs (`U64`, 8 LE bytes, possibly non-canonical) fold
  into native values with `gl_val`/`limb_to_field` (the field sum wraps
  mod p — exactly the reduction);
- **egress**: challenger observations need the canonical LE bytes;
  `gl_to_bytes` decomposes a native value via the `unconstrained_g_to_bytes`
  hint, pinned by u8 range checks, a recomposition equality, and a
  canonicality (`< p`) check — forcing the unique canonical decomposition.

Inverses are hinted (`unconstrained_g_inverse`) and verified with one
multiplication, never computed.

If Aiur is ever compiled to a different outer field (e.g. the BLS scalar
field), this module must be swapped for a field-agnostic byte-limb
implementation (see this file's git history for a complete one, validated
byte-for-byte against `multi-stark`'s `gl_ops_ref`).

Validated against `multi-stark`'s native Goldilocks (`gl_ops_ref` in
`multi-stark/src/types.rs`) via the `multi-stark` self-test suite.
-/

public section

namespace MultiStark

def goldilocks := ⟦
  type Goldilocks = G
  type ExtGoldilocks = [G; 2]

  fn gl_zero() -> Goldilocks { 0 }
  fn gl_one() -> Goldilocks { 1 }
  fn gl_two() -> Goldilocks { 2 }
  fn gl_seven() -> Goldilocks { 7 }

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
    let (c0, c1) = u8_range_check(to_field(b[0]), to_field(b[1]));
    let (c2, c3) = u8_range_check(to_field(b[2]), to_field(b[3]));
    let (c4, c5) = u8_range_check(to_field(b[4]), to_field(b[5]));
    let (c6, c7) = u8_range_check(to_field(b[6]), to_field(b[7]));
    let r = [c0, c1, c2, c3, c4, c5, c6, c7];
    assert_eq!(gl_val(r), v);
    assert_eq!(gl_lt_p(r), 1);
    r
  }

  -- ==========================================================================
  -- Base field ops: native.
  -- ==========================================================================
  fn gl_add(a: Goldilocks, b: Goldilocks) -> Goldilocks { a + b }
  fn gl_sub(a: Goldilocks, b: Goldilocks) -> Goldilocks { a - b }
  fn gl_neg(a: Goldilocks) -> Goldilocks { 0 - a }
  fn gl_mul(a: Goldilocks, b: Goldilocks) -> Goldilocks { a * b }
  fn gl_sq(a: Goldilocks) -> Goldilocks { a * a }
  fn gl_is_zero(x: Goldilocks) -> G { eq_zero(x) }
  fn gl_eq(a: Goldilocks, b: Goldilocks) -> G { eq_zero(a - b) }

  -- ==========================================================================
  -- Base field inverse / divide: hinted, verified with one multiplication.
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
  fn gl_div(a: Goldilocks, b: Goldilocks) -> Goldilocks { a * gl_inverse(b) }

  -- ==========================================================================
  -- Extension field ExtGoldilocks = 𝔽_p[X]/(X² − 7), native end-to-end.
  -- ==========================================================================
  fn eg_add(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    [a[0] + b[0], a[1] + b[1]]
  }
  fn eg_sub(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    [a[0] - b[0], a[1] - b[1]]
  }
  fn eg_neg(a: ExtGoldilocks) -> ExtGoldilocks {
    [0 - a[0], 0 - a[1]]
  }
  -- (a0 + a1·X)(b0 + b1·X) = (a0·b0 + 7·a1·b1) + (a0·b1 + a1·b0)·X.
  fn eg_mul(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    [(a[0] * b[0]) + (7 * (a[1] * b[1])), (a[0] * b[1]) + (a[1] * b[0])]
  }
  -- conjugate ā = a0 − a1·X, norm a·ā = a0² − 7·a1² ∈ 𝔽_p, a⁻¹ = ā / norm.
  -- The norm inverse is hinted and pinned like `gl_inverse`.
  fn eg_inverse(a: ExtGoldilocks) -> ExtGoldilocks {
    let norm = (a[0] * a[0]) - (7 * (a[1] * a[1]));
    let ninv = unconstrained_g_inverse(norm);
    let t = (norm * ninv) - 1;
    assert_eq!(norm * t, 0);
    assert_eq!(ninv * t, 0);
    [a[0] * ninv, (0 - a[1]) * ninv]
  }
  fn eg_div(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    eg_mul(a, eg_inverse(b))
  }
  -- 1 iff two extension elements are equal.
  fn eg_eq(a: ExtGoldilocks, b: ExtGoldilocks) -> G {
    eq_zero(a[0] - b[0]) * eq_zero(a[1] - b[1])
  }

⟧

end MultiStark

end
