module
public import Ix.Aiur.Meta

/-!
# Goldilocks arithmetic, FOREIGN form (emulated in a LARGE outer field)

The same interface as `GoldilocksNative.lean` — types, values, and
operations, base and extension — implemented WITHOUT assuming the Aiur
outer field is Goldilocks, for an outer field LARGER than p²: the
BLS12-381 scalar field of the KZG terminal stage (~2²⁵⁵).

A `Goldilocks` element is ONE outer-field element holding its canonical
value `< p = 2⁶⁴ − 2³² + 1`. Because the outer field is wider than 128
bits, every operation's exact integer result fits in it, so the
arithmetic is never computed on limbs — it is computed natively in the
outer field and REDUCED BY CHECK:

    x · y = q·p + r   with  q < p,  r < p        (x·y < p² < |F|)
    x + y = q·p + r   with  q ∈ {0,1},  r < p    (x + y < 2p)

`q`/`r` are prover hints (`unconstrained_gl_divmod`), pinned by the
identity (one degree-2 constraint) and `< p` range checks (8 hinted
bytes, 4 `u8_range_check` lookups, recomposition, `gl_lt_p`). A
multiplication is one row of ~8 lookups; an addition ~4 — against the
hundreds of byte-gadget lookups of the former limb emulation. The
inverse is hinted (`unconstrained_gl_inverse`, mod p) and pinned with one
multiplication, replacing the 95-mul Fermat chain.

Soundness needs |F| > 2·p² (no wrap in the identities). The module
STILL RUNS under Goldilocks itself (the `fg_*` self-tests and the
foreign-verifier interpreter gate): there the hint is `(0, v)` and the
identities degenerate to `x·y ≡ r` with `r < p` pinning the value —
correct results, weaker (but sufficient) argument. `p` is spelled
`4294967295 · 4294967296 + 1` so no literal exceeds p (the exact-Nat
constants check), evaluating to p over a large field and to 0 over
Goldilocks.

INLINE-WRAPPER CONVENTION (unchanged): the interface fns are `@`-called
at every use site (the native form's convention — its ops splice to
trivial arithmetic); here each heavy op is a thin `@`-inlined wrapper
over a plain memoized `*_impl` call, so a call site costs one lookup and
the op's columns live once in the impl's circuit. Value constructors,
`g_is_zero` (canonical ⇒ `eq_zero`), `gl_lt_p`, `gl_from_u16`, and the
byte boundaries stay genuinely inline. Exactly one of
`goldilocksNative`/`goldilocksForeign` merges into a toplevel (same
names by design): `multiStarkForeign` is this module under the verifier,
the stage-3 program.
-/

public section

namespace MultiStark

def goldilocksForeign := ⟦
  -- One outer-field element, canonical value < p.
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
  -- A small (< 2¹⁶) constant from its two little-endian bytes — the vk's
  -- ConstSmall ingest.
  fn gl_from_u16(lo: U8, hi: U8) -> Goldilocks {
    to_field(lo) + 256 * to_field(hi)
  }
  -- p = 2⁶⁴ − 2³² + 1 = (2³² − 1)·2³² + 1, spelled in sub-p literals: the
  -- modulus over a large outer field, 0 over Goldilocks itself.
  fn gl_p() -> G { 4294967295 * 4294967296 + 1 }

  -- ==========================================================================
  -- Byte boundaries and the range check (ingest/egress). The canonical LE
  -- bytes of an outer-field value < 2⁶⁴ are a prover hint
  -- (`unconstrained_g_to_bytes` — exact for such values), pinned by the
  -- range checks + recomposition; `gl_lt_p` then decides canonicality.
  -- ==========================================================================

  -- 1 iff the 8-byte LE integer is < p. Since p = (2³² − 1)·2³² + 1, we have
  -- x ≥ p ⟺ (high word = 2³² − 1) ∧ (low word ≥ 1). The high word is maximal
  -- iff its byte sum is 4·255 = 1020 (each byte is ≤ 255), and the low word
  -- is zero iff its byte sum is zero (a sum of four bytes cannot wrap).
  -- Inputs must be range-checked bytes.
  fn gl_lt_p(x: [U8; 8]) -> G {
    let hi_max = eq_zero(
      to_field(x[4]) + to_field(x[5]) + to_field(x[6]) + to_field(x[7]) - 1020);
    let lo_zero = eq_zero(
      to_field(x[0]) + to_field(x[1]) + to_field(x[2]) + to_field(x[3]));
    1 - (hi_max * (1 - lo_zero))
  }

  -- The outer-field value of 8 LE bytes: Σ xᵢ·256ⁱ — exact over a large
  -- field (< 2⁶⁴), the mod-p reduction over Goldilocks.
  fn gl_bytes_val(x: [U8; 8]) -> G {
    to_field(x[0]) + 256 * to_field(x[1]) + 65536 * to_field(x[2])
      + 16777216 * to_field(x[3]) + 4294967296 * to_field(x[4])
      + 1099511627776 * to_field(x[5]) + 281474976710656 * to_field(x[6])
      + 72057594037927936 * to_field(x[7])
  }

  -- Egress: the canonical 8 LE bytes of a Goldilocks value — the hinted
  -- decomposition, range-checked, recomposed, and canonicality-checked
  -- (two distinct byte strings < p have distinct values).
  fn gl_to_bytes(v: Goldilocks) -> [U8; 8] {
    let b = unconstrained_g_to_bytes(v);
    let (c0, c1) = u8_range_check(b[0], b[1]);
    let (c2, c3) = u8_range_check(b[2], b[3]);
    let (c4, c5) = u8_range_check(b[4], b[5]);
    let (c6, c7) = u8_range_check(b[6], b[7]);
    let r = [c0, c1, c2, c3, c4, c5, c6, c7];
    assert_eq!(@gl_bytes_val(r), v, "gl_to_bytes: recomposition");
    assert_eq!(@gl_lt_p(r), 1, "gl_to_bytes: canonical");
    r
  }

  -- The range check `v < p` (returns 1): `gl_to_bytes` with the bytes
  -- discarded. Every reduced result is pinned through this.
  fn gl_range(v: G) -> G {
    let b = unconstrained_g_to_bytes(v);
    let (c0, c1) = u8_range_check(b[0], b[1]);
    let (c2, c3) = u8_range_check(b[2], b[3]);
    let (c4, c5) = u8_range_check(b[4], b[5]);
    let (c6, c7) = u8_range_check(b[6], b[7]);
    let r = [c0, c1, c2, c3, c4, c5, c6, c7];
    assert_eq!(@gl_bytes_val(r), v, "gl_range: recomposition");
    assert_eq!(@gl_lt_p(r), 1, "gl_range: < p");
    1
  }

  -- Wire-limb ingest: an arbitrary 8-byte LE value (< 2⁶⁴ < 2p) — the
  -- exact sum over a large field — reduces by one boolean multiple of p.
  fn gl_val(x: [U8; 8]) -> Goldilocks { gl_val_impl(x) }
  fn gl_val_impl(x: [U8; 8]) -> Goldilocks {
    let v = @gl_bytes_val(x);
    let (q, r) = unconstrained_gl_divmod(v);
    assert_eq!(q * (q - 1), 0, "gl_val: q boolean");
    assert_eq!(v, q * @gl_p() + r, "gl_val: identity");
    assert_eq!(@gl_range(r), 1);
    r
  }

  -- ==========================================================================
  -- Base ring ops (mod p): compute exactly in the outer field, reduce by
  -- check.
  -- ==========================================================================

  -- x + y < 2p: one boolean multiple of p.
  fn g_add(x: Goldilocks, y: Goldilocks) -> Goldilocks { g_add_impl(x, y) }
  fn g_add_impl(x: Goldilocks, y: Goldilocks) -> Goldilocks {
    let (q, r) = unconstrained_gl_divmod(x + y);
    assert_eq!(q * (q - 1), 0, "g_add: q boolean");
    assert_eq!(x + y, q * @gl_p() + r, "g_add: identity");
    assert_eq!(@gl_range(r), 1);
    r
  }

  -- (x + p) − y ∈ (0, 2p): one boolean multiple of p. Evaluation ORDER
  -- matters in the outer field: `x + p` first (≥ p > y), so the subtraction
  -- never wraps — `x − y + p` would wrap at `x − y` for x < y.
  fn g_sub(x: Goldilocks, y: Goldilocks) -> Goldilocks { g_sub_impl(x, y) }
  fn g_sub_impl(x: Goldilocks, y: Goldilocks) -> Goldilocks {
    let s = x + @gl_p() - y;
    let (q, r) = unconstrained_gl_divmod(s);
    assert_eq!(q * (q - 1), 0, "g_sub: q boolean");
    assert_eq!(s, q * @gl_p() + r, "g_sub: identity");
    assert_eq!(@gl_range(r), 1);
    r
  }

  fn g_neg(x: Goldilocks) -> Goldilocks { g_sub_impl(0, x) }

  -- Canonical representation: zero iff the outer value is zero.
  fn g_is_zero(x: Goldilocks) -> G { eq_zero(x) }

  -- x · y < p²: q < p and r < p are both pinned — without the bound on q
  -- a prover could shift mass between the two.
  fn g_mul(x: Goldilocks, y: Goldilocks) -> Goldilocks { g_mul_impl(x, y) }
  fn g_mul_impl(x: Goldilocks, y: Goldilocks) -> Goldilocks {
    let (q, r) = unconstrained_gl_divmod(x * y);
    assert_eq!(x * y, q * @gl_p() + r, "g_mul: identity");
    assert_eq!(@gl_range(q), 1);
    assert_eq!(@gl_range(r), 1);
    r
  }

  -- ==========================================================================
  -- Base field inverse: hinted (mod p), pinned by one multiplication.
  -- `x·i ≡ 1` when x ≠ 0, `i = 0` when x = 0 (matching `0⁻¹ = 0`).
  -- ==========================================================================
  fn gl_inverse(x: Goldilocks) -> Goldilocks { gl_inverse_impl(x) }
  fn gl_inverse_impl(x: Goldilocks) -> Goldilocks {
    let i = unconstrained_gl_inverse(x);
    assert_eq!(@gl_range(i), 1);
    let z = eq_zero(x);
    assert_eq!(g_mul_impl(x, i), 1 - z, "gl_inverse: x*i");
    assert_eq!(i * z, 0, "gl_inverse: zero case");
    i
  }

  -- ==========================================================================
  -- Extension algebra ExtGoldilocks = 𝔽_p[X]/(X² − 7), over the base
  -- interface. The impl bodies are textually the native form's; the
  -- interface fns are one-call wrappers per the module convention.
  -- ==========================================================================
  fn eg_add(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    eg_add_impl(a, b)
  }
  fn eg_add_impl(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    [@g_add(a[0], b[0]), @g_add(a[1], b[1])]
  }
  fn eg_sub(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    eg_sub_impl(a, b)
  }
  fn eg_sub_impl(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    [@g_sub(a[0], b[0]), @g_sub(a[1], b[1])]
  }
  fn eg_neg(a: ExtGoldilocks) -> ExtGoldilocks {
    [@g_neg(a[0]), @g_neg(a[1])]
  }
  -- (a0 + a1·X)(b0 + b1·X) = (a0·b0 + 7·a1·b1) + (a0·b1 + a1·b0)·X.
  fn eg_mul(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    eg_mul_impl(a, b)
  }
  fn eg_mul_impl(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    [@g_add(@g_mul(a[0], b[0]), @g_mul(@g_w(), @g_mul(a[1], b[1]))),
     @g_add(@g_mul(a[0], b[1]), @g_mul(a[1], b[0]))]
  }
  -- conjugate ā = a0 − a1·X, norm a·ā = a0² − 7·a1² ∈ 𝔽_p, a⁻¹ = ā / norm.
  fn eg_inverse(a: ExtGoldilocks) -> ExtGoldilocks { eg_inverse_impl(a) }
  fn eg_inverse_impl(a: ExtGoldilocks) -> ExtGoldilocks {
    let norm = @g_sub(@g_mul(a[0], a[0]), @g_mul(@g_w(), @g_mul(a[1], a[1])));
    let ninv = @gl_inverse(norm);
    [@g_mul(a[0], ninv), @g_mul(@g_neg(a[1]), ninv)]
  }
  fn eg_div(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    eg_mul_impl(a, eg_inverse_impl(b))
  }
  -- 1 iff two extension elements are equal.
  fn eg_eq(a: ExtGoldilocks, b: ExtGoldilocks) -> G {
    @g_is_zero(@g_sub(a[0], b[0])) * @g_is_zero(@g_sub(a[1], b[1]))
  }

  -- ==========================================================================
  -- Self-tests (vs `gl_ops_ref` — the same vectors the native form's suite
  -- pins, plus the boundary ops). Values are canonical integers.
  -- ==========================================================================
  pub fn fg_addsub_test() -> G {
    let a = 18364758544493064720; -- 0xFEDCBA9876543210
    let b = 1311768467463790320;  -- 0x123456789ABCDEF0
    assert_eq!(@g_add(a, b), 1229782942542270719);
    assert_eq!(@g_sub(a, b), 17052990077029274400);
    assert_eq!(@g_sub(b, a), 1393753992385309921);
    -- edge: (p-1) + 5 ≡ 4 ; 5 - (p-1) ≡ 6
    let pm1 = 18446744069414584320;
    assert_eq!(@g_add(pm1, 5), 4);
    assert_eq!(@g_sub(5, pm1), 6);
    1
  }
  pub fn fg_muldiv_test() -> G {
    let a = 18364758544493064720; -- 0xFEDCBA9876543210
    let b = 1311768467463790320;  -- 0x123456789ABCDEF0
    assert_eq!(@g_mul(a, b), 18080541965438139092);
    assert_eq!(@gl_inverse(a), 7352237129603030369);
    -- edge: (p-1)·5 ≡ p-5
    let pm1 = 18446744069414584320;
    assert_eq!(@g_mul(pm1, 5), 18446744069414584316);
    -- a·a⁻¹ = 1 and b·b⁻¹ = 1; 0⁻¹ = 0
    assert_eq!(@g_mul(a, @gl_inverse(a)), 1);
    assert_eq!(@g_mul(b, @gl_inverse(b)), 1);
    assert_eq!(@gl_inverse(0), 0);
    1
  }
  pub fn fg_ext_ops_test() -> G {
    -- e0 = (0xFEDCBA9876543210, 0x0123456789ABCDEF), e1 = (0x1111111122222222, 0x3333333344444444)
    let e0 = [18364758544493064720, 81985529216486895];
    let e1 = [1229782938533634594, 3689348815028241476];
    let s = @eg_add(e0, e1);
    assert_eq!(s[0], 1147797413612114993);
    assert_eq!(s[1], 3771334344244728371);
    let m = @eg_mul(e0, e1);
    assert_eq!(m[0], 9707086647507742218);
    assert_eq!(m[1], 4837146220115323607);
    let inv = @eg_inverse(e0);
    assert_eq!(inv[0], 15624774584742309597);
    assert_eq!(inv[1], 17771582427853906802);
    let d = @eg_div(e0, e1);
    assert_eq!(d[0], 4566604814623980330);
    assert_eq!(d[1], 10158067406679060168);
    -- e0 · e0⁻¹ = 1
    let one = @eg_mul(e0, @eg_inverse(e0));
    assert_eq!(one[0], 1);
    assert_eq!(one[1], 0);
    1
  }
  pub fn fg_boundary_test() -> G {
    -- gl_val reduces a non-canonical wire limb: p + 3 → 3; a canonical value
    -- passes through.
    let p_plus_3 = [4u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 255u8];
    assert_eq!(@gl_val(p_plus_3), 3);
    let a = [16u8, 50u8, 84u8, 118u8, 152u8, 186u8, 220u8, 254u8];
    assert_eq!(@gl_val(a), 18364758544493064720);
    -- gl_to_bytes inverts gl_val on canonical values.
    let ab = @gl_to_bytes(@gl_val(a));
    assert_eq!(to_field(ab[0]), 16);
    assert_eq!(to_field(ab[7]), 254);
    -- gl_lt_p: p is not < p; p − 1 is.
    assert_eq!(@gl_lt_p([1u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 255u8]), 0);
    assert_eq!(@gl_lt_p([0u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 255u8]), 1);
    -- g_is_zero on zero and one; two-adic root sanity: root^(2^31) = p − 1
    -- (31 squarings), and squaring once more gives 1.
    assert_eq!(@g_is_zero(@g_zero()), 1);
    assert_eq!(@g_is_zero(@g_one()), 0);
    let r31 = gl_sq_n(@g_two_adic_root(), 31);
    assert_eq!(r31, 18446744069414584320);
    assert_eq!(@g_mul(r31, r31), 1);
    1
  }
  -- n repeated squarings (test helper).
  fn gl_sq_n(x: Goldilocks, n: G) -> Goldilocks {
    match n {
      0 => x,
      _ => gl_sq_n(g_mul_impl(x, x), n - 1),
    }
  }
⟧

end MultiStark

end
