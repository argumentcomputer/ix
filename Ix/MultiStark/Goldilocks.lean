module
public import Ix.Aiur.Meta

/-!
# Goldilocks field arithmetic on the native field (`Goldilocks = [U8; 8]`)

The recursive verifier computes on the *inner* proof's field (Goldilocks) —
and Aiur's own outer field IS Goldilocks (`aiur::G = p3_goldilocks`), so the
arithmetic here runs on native `+`/`*` instead of byte-limb emulation. The
interface stays byte-shaped: a `Goldilocks` element is its canonical value
`< p = 2⁶⁴ − 2³² + 1` held as 8 little-endian bytes (`[U8; 8]`), because the
transcript, blake3, and the wire format all consume canonical bytes, and
byte-exact equality is what the callers rely on.

Each op recomposes its operands (`gl_val`: a linear sum, memoized), computes
natively, and decomposes the result back to canonical bytes (`gl_of_val`).
The decomposition bytes are **non-deterministic hints**
(`unconstrained_g_to_bytes`), pinned in constrained code by u8 range checks,
a recomposition equality, and a canonicality check (`< p`) — together these
force the unique canonical decomposition. Inverses are likewise hinted
(`unconstrained_g_inverse`) and verified with one multiplication, never
computed by Fermat exponentiation.

`ExtGoldilocks = [Goldilocks; 2]` is the degree-2 extension `𝔽_p[X]/(X² − 7)`,
computed natively end-to-end: only its two result coordinates are decomposed.

If Aiur is ever compiled to a different outer field (e.g. the BLS scalar
field), this module must be swapped for a field-agnostic byte-limb
implementation (carry/borrow chains over the u8 gadgets — see this file's
git history for a complete one, validated byte-for-byte against
`multi-stark`'s `gl_ops_ref`).

Validated against `multi-stark`'s native Goldilocks (`gl_ops_ref` in
`multi-stark/src/types.rs`) via the `multi-stark` self-test suite.
-/

public section

namespace MultiStark

def goldilocks := ⟦
  type Goldilocks = [U8; 8]
  type ExtGoldilocks = [Goldilocks; 2]

  fn gl_zero() -> Goldilocks { [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8] }
  fn gl_one() -> Goldilocks { [1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8] }
  fn gl_two() -> Goldilocks { [2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8] }
  fn gl_seven() -> Goldilocks { [7u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8] }

  -- The native field value of 8 LE bytes: `Σ xᵢ·256ⁱ` (mod p). For canonical
  -- inputs (< p) this is exact and injective. For an arbitrary 8-byte value
  -- (< 2⁶⁴ < 2p) the field sum wraps once, yielding exactly the reduced
  -- representative — which is what `gl_reduce` exploits.
  fn gl_val(x: Goldilocks) -> G {
    to_field(x[0]) + 256 * to_field(x[1]) + 65536 * to_field(x[2])
      + 16777216 * to_field(x[3]) + 4294967296 * to_field(x[4])
      + 1099511627776 * to_field(x[5]) + 281474976710656 * to_field(x[6])
      + 72057594037927936 * to_field(x[7])
  }

  -- 1 iff the 8-byte LE integer is < p. Since p = (2³² − 1)·2³² + 1, we have
  -- x ≥ p ⟺ (high word = 2³² − 1) ∧ (low word ≥ 1). The high word is maximal
  -- iff its byte sum is 4·255 = 1020 (each byte is ≤ 255), and the low word
  -- is zero iff its byte sum is zero (a sum of four bytes cannot wrap).
  -- Inputs must be range-checked bytes.
  fn gl_lt_p(x: Goldilocks) -> G {
    let hi_max = eq_zero(
      to_field(x[4]) + to_field(x[5]) + to_field(x[6]) + to_field(x[7]) - 1020);
    let lo_zero = eq_zero(
      to_field(x[0]) + to_field(x[1]) + to_field(x[2]) + to_field(x[3]));
    1 - (hi_max * (1 - lo_zero))
  }

  -- Decompose a native field value into its canonical 8 LE bytes. The bytes
  -- are prover hints; the range checks + recomposition equality +
  -- canonicality check pin the unique canonical decomposition (two distinct
  -- byte strings < p have distinct field values).
  fn gl_of_val(v: G) -> Goldilocks {
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
  -- Base field ops: recompose → native op → canonical decomposition.
  -- ==========================================================================
  fn gl_add(a: Goldilocks, b: Goldilocks) -> Goldilocks {
    gl_of_val(gl_val(a) + gl_val(b))
  }
  fn gl_sub(a: Goldilocks, b: Goldilocks) -> Goldilocks {
    gl_of_val(gl_val(a) - gl_val(b))
  }
  fn gl_neg(a: Goldilocks) -> Goldilocks { gl_of_val(0 - gl_val(a)) }
  fn gl_mul(a: Goldilocks, b: Goldilocks) -> Goldilocks {
    gl_of_val(gl_val(a) * gl_val(b))
  }
  fn gl_sq(a: Goldilocks) -> Goldilocks {
    let v = gl_val(a);
    gl_of_val(v * v)
  }

  -- Canonicalize an arbitrary 8-byte value (possibly ≥ p, e.g. a raw hash
  -- limb or a non-canonical wire encoding): the field recomposition wraps
  -- once for values in [p, 2⁶⁴), so decomposing it back yields the canonical
  -- representative.
  fn gl_reduce(x: Goldilocks) -> Goldilocks { gl_of_val(gl_val(x)) }

  -- 1 iff `x` is the field zero. Works for non-canonical inputs too: the
  -- recomposition is ≡ 0 mod p exactly for the integer values 0 and p.
  fn gl_is_zero(x: Goldilocks) -> G { eq_zero(gl_val(x)) }

  -- 1 iff two canonical Goldilocks values are equal. Inputs must be
  -- canonical (`gl_*` outputs always are); recomposition is then injective.
  fn gl_eq(a: Goldilocks, b: Goldilocks) -> G {
    eq_zero(gl_val(a) - gl_val(b))
  }

  -- ==========================================================================
  -- Base field inverse / divide: hinted, verified with one multiplication.
  -- `t = x·i − 1; x·t == 0 ∧ i·t == 0` forces `i = x⁻¹` when `x ≠ 0` (first
  -- assert gives x·i = 1) and `i = 0` when `x = 0` (t = −1, second assert).
  -- Matches the reference semantics `0⁻¹ = 0` (Fermat: 0^(p−2) = 0).
  -- ==========================================================================
  fn gl_inverse(x: Goldilocks) -> Goldilocks {
    let xv = gl_val(x);
    let iv = unconstrained_g_inverse(xv);
    let t = xv * iv - 1;
    assert_eq!(xv * t, 0);
    assert_eq!(iv * t, 0);
    gl_of_val(iv)
  }
  fn gl_div(a: Goldilocks, b: Goldilocks) -> Goldilocks {
    gl_mul(a, gl_inverse(b))
  }

  -- ==========================================================================
  -- Extension field ExtGoldilocks = 𝔽_p[X]/(X² − 7), computed natively;
  -- only result coordinates are decomposed.
  -- ==========================================================================
  fn eg_add(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    [gl_add(a[0], b[0]), gl_add(a[1], b[1])]
  }
  fn eg_sub(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    [gl_sub(a[0], b[0]), gl_sub(a[1], b[1])]
  }
  fn eg_neg(a: ExtGoldilocks) -> ExtGoldilocks {
    [gl_neg(a[0]), gl_neg(a[1])]
  }
  -- (a0 + a1·X)(b0 + b1·X) = (a0·b0 + 7·a1·b1) + (a0·b1 + a1·b0)·X.
  fn eg_mul(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    let a0 = gl_val(a[0]);
    let a1 = gl_val(a[1]);
    let b0 = gl_val(b[0]);
    let b1 = gl_val(b[1]);
    [gl_of_val(a0 * b0 + 7 * (a1 * b1)), gl_of_val(a0 * b1 + a1 * b0)]
  }
  -- conjugate ā = a0 − a1·X, norm a·ā = a0² − 7·a1² ∈ 𝔽_p, a⁻¹ = ā / norm.
  -- The norm inverse is hinted and pinned like `gl_inverse`.
  fn eg_inverse(a: ExtGoldilocks) -> ExtGoldilocks {
    let a0 = gl_val(a[0]);
    let a1 = gl_val(a[1]);
    let norm = a0 * a0 - 7 * (a1 * a1);
    let ninv = unconstrained_g_inverse(norm);
    let t = norm * ninv - 1;
    assert_eq!(norm * t, 0);
    assert_eq!(ninv * t, 0);
    [gl_of_val(a0 * ninv), gl_of_val((0 - a1) * ninv)]
  }
  fn eg_div(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    eg_mul(a, eg_inverse(b))
  }
  -- 1 iff two extension elements are equal (both coordinates byte-exact).
  fn eg_eq(a: ExtGoldilocks, b: ExtGoldilocks) -> G {
    gl_eq(a[0], b[0]) * gl_eq(a[1], b[1])
  }

⟧

end MultiStark

end
