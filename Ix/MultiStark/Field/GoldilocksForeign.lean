module
public import Ix.Aiur.Meta

/-!
# Field interface: Goldilocks, FOREIGN form (emulated in a LARGE outer field)

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
bytes, 4 `u8_range_check` lookups, recomposition, `bytes_lt_modulus`). A
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
`val_is_zero` (canonical ⇒ `eq_zero`), `bytes_lt_modulus`, `val_from_u16`, and the
byte boundaries stay genuinely inline. Exactly one of
`goldilocksNative`/`goldilocksForeign` merges into a toplevel (same
names by design): `multiStarkForeign` is this module under the verifier,
the stage-3 program.
-/

public section

namespace MultiStark

def goldilocksForeign := ⟦
  -- One outer-field element, canonical value < p.
  type Val = G
  type Ext = [Val; 2]

  -- ==========================================================================
  -- Pure values.
  -- ==========================================================================
  fn val_zero() -> Val { 0 }
  fn val_one() -> Val { 1 }
  fn val_two() -> Val { 2 }
  -- The extension's binomial modulus: ExtGoldilocks = 𝔽_p[X]/(X² − W).
  fn ext_w() -> Val { 7 }
  -- The multiplicative-coset generator (Plonky3 `Goldilocks::GENERATOR`).
  fn val_generator() -> Val { 7 }
  -- A primitive 2^32-th root of unity (Plonky3's maximal two-adic
  -- generator); smaller-order roots derive by squaring (`two_adic_gen`).
  fn val_two_adic_root() -> Val { 1753635133440165772 }
  -- A small (< 2¹⁶) constant from its two little-endian bytes — the vk's
  -- ConstSmall ingest.
  fn val_from_u16(lo: U8, hi: U8) -> Val {
    to_field(lo) + 256 * to_field(hi)
  }
  -- p = 2⁶⁴ − 2³² + 1 = (2³² − 1)·2³² + 1, spelled in sub-p literals: the
  -- modulus over a large outer field, 0 over Goldilocks itself.
  fn val_modulus() -> G { 4294967295 * 4294967296 + 1 }

  -- ==========================================================================
  -- Byte boundaries and the range check (ingest/egress). The canonical LE
  -- bytes of an outer-field value < 2⁶⁴ are a prover hint
  -- (`unconstrained_g_to_bytes` — exact for such values), pinned by the
  -- range checks + recomposition; `bytes_lt_modulus` then decides canonicality.
  -- ==========================================================================

  -- 1 iff the 8-byte LE integer is < p. Since p = (2³² − 1)·2³² + 1, we have
  -- x ≥ p ⟺ (high word = 2³² − 1) ∧ (low word ≥ 1). The high word is maximal
  -- iff its byte sum is 4·255 = 1020 (each byte is ≤ 255), and the low word
  -- is zero iff its byte sum is zero (a sum of four bytes cannot wrap).
  -- Inputs must be range-checked bytes.
  fn bytes_lt_modulus(x: [U8; 8]) -> G {
    let hi_max = eq_zero(
      to_field(x[4]) + to_field(x[5]) + to_field(x[6]) + to_field(x[7]) - 1020);
    let lo_zero = eq_zero(
      to_field(x[0]) + to_field(x[1]) + to_field(x[2]) + to_field(x[3]));
    1 - (hi_max * (1 - lo_zero))
  }

  -- The outer-field value of 8 LE bytes: Σ xᵢ·256ⁱ — exact over a large
  -- field (< 2⁶⁴), the mod-p reduction over Goldilocks.
  fn bytes_val(x: [U8; 8]) -> G {
    to_field(x[0]) + 256 * to_field(x[1]) + 65536 * to_field(x[2])
      + 16777216 * to_field(x[3]) + 4294967296 * to_field(x[4])
      + 1099511627776 * to_field(x[5]) + 281474976710656 * to_field(x[6])
      + 72057594037927936 * to_field(x[7])
  }

  -- Egress: the canonical 8 LE bytes of a Goldilocks value — the hinted
  -- decomposition, range-checked, recomposed, and canonicality-checked
  -- (two distinct byte strings < p have distinct values).
  fn val_to_bytes(v: Val) -> [U8; 8] {
    let b = unconstrained_g_to_bytes(v);
    let (c0, c1) = u8_range_check(b[0], b[1]);
    let (c2, c3) = u8_range_check(b[2], b[3]);
    let (c4, c5) = u8_range_check(b[4], b[5]);
    let (c6, c7) = u8_range_check(b[6], b[7]);
    let r = [c0, c1, c2, c3, c4, c5, c6, c7];
    assert_eq!(@bytes_val(r), v, "val_to_bytes: recomposition");
    assert_eq!(@bytes_lt_modulus(r), 1, "val_to_bytes: canonical");
    r
  }

  -- The range check `v < p` (returns 1): `val_to_bytes` with the bytes
  -- discarded. Every reduced result is pinned through this.
  fn val_range(v: G) -> G {
    let b = unconstrained_g_to_bytes(v);
    let (c0, c1) = u8_range_check(b[0], b[1]);
    let (c2, c3) = u8_range_check(b[2], b[3]);
    let (c4, c5) = u8_range_check(b[4], b[5]);
    let (c6, c7) = u8_range_check(b[6], b[7]);
    let r = [c0, c1, c2, c3, c4, c5, c6, c7];
    assert_eq!(@bytes_val(r), v, "val_range: recomposition");
    assert_eq!(@bytes_lt_modulus(r), 1, "val_range: < p");
    1
  }

  -- Wire-limb ingest: an arbitrary 8-byte LE value (< 2⁶⁴ < 2p) — the
  -- exact sum over a large field — reduces by one boolean multiple of p.
  fn val_from_bytes(x: [U8; 8]) -> Val { val_from_bytes_impl(x) }
  fn val_from_bytes_impl(x: [U8; 8]) -> Val {
    let v = @bytes_val(x);
    let (q, r) = unconstrained_gl_divmod(v);
    assert_eq!(q * (q - 1), 0, "val_from_bytes: q boolean");
    assert_eq!(v, q * @val_modulus() + r, "val_from_bytes: identity");
    assert_eq!(@val_range(r), 1);
    r
  }

  -- ==========================================================================
  -- Base ring ops (mod p): compute exactly in the outer field, reduce by
  -- check.
  -- ==========================================================================

  -- x + y < 2p: one boolean multiple of p.
  fn val_add(x: Val, y: Val) -> Val { val_add_impl(x, y) }
  fn val_add_impl(x: Val, y: Val) -> Val {
    let (q, r) = unconstrained_gl_divmod(x + y);
    assert_eq!(q * (q - 1), 0, "val_add: q boolean");
    assert_eq!(x + y, q * @val_modulus() + r, "val_add: identity");
    assert_eq!(@val_range(r), 1);
    r
  }

  -- (x + p) − y ∈ (0, 2p): one boolean multiple of p. Evaluation ORDER
  -- matters in the outer field: `x + p` first (≥ p > y), so the subtraction
  -- never wraps — `x − y + p` would wrap at `x − y` for x < y.
  fn val_sub(x: Val, y: Val) -> Val { val_sub_impl(x, y) }
  fn val_sub_impl(x: Val, y: Val) -> Val {
    let s = x + @val_modulus() - y;
    let (q, r) = unconstrained_gl_divmod(s);
    assert_eq!(q * (q - 1), 0, "val_sub: q boolean");
    assert_eq!(s, q * @val_modulus() + r, "val_sub: identity");
    assert_eq!(@val_range(r), 1);
    r
  }

  fn val_neg(x: Val) -> Val { val_sub_impl(0, x) }

  -- Canonical representation: zero iff the outer value is zero.
  fn val_is_zero(x: Val) -> G { eq_zero(x) }

  -- x · y < p²: q < p and r < p are both pinned — without the bound on q
  -- a prover could shift mass between the two.
  fn val_mul(x: Val, y: Val) -> Val { val_mul_impl(x, y) }
  fn val_mul_impl(x: Val, y: Val) -> Val {
    let (q, r) = unconstrained_gl_divmod(x * y);
    assert_eq!(x * y, q * @val_modulus() + r, "val_mul: identity");
    assert_eq!(@val_range(q), 1);
    assert_eq!(@val_range(r), 1);
    r
  }

  -- ==========================================================================
  -- Base field inverse: hinted (mod p), pinned by one multiplication.
  -- `x·i ≡ 1` when x ≠ 0, `i = 0` when x = 0 (matching `0⁻¹ = 0`).
  -- ==========================================================================
  fn val_inverse(x: Val) -> Val { val_inverse_impl(x) }
  fn val_inverse_impl(x: Val) -> Val {
    let i = unconstrained_gl_inverse(x);
    assert_eq!(@val_range(i), 1);
    let z = eq_zero(x);
    assert_eq!(val_mul_impl(x, i), 1 - z, "val_inverse: x*i");
    assert_eq!(i * z, 0, "val_inverse: zero case");
    i
  }

  -- ==========================================================================
  -- Extension algebra ExtGoldilocks = 𝔽_p[X]/(X² − 7), over the base
  -- interface. The impl bodies are textually the native form's; the
  -- interface fns are one-call wrappers per the module convention.
  -- ==========================================================================
  fn ext_add(a: Ext, b: Ext) -> Ext {
    ext_add_impl(a, b)
  }
  fn ext_add_impl(a: Ext, b: Ext) -> Ext {
    [@val_add(a[0], b[0]), @val_add(a[1], b[1])]
  }
  fn ext_sub(a: Ext, b: Ext) -> Ext {
    ext_sub_impl(a, b)
  }
  fn ext_sub_impl(a: Ext, b: Ext) -> Ext {
    [@val_sub(a[0], b[0]), @val_sub(a[1], b[1])]
  }
  fn ext_neg(a: Ext) -> Ext {
    [@val_neg(a[0]), @val_neg(a[1])]
  }
  -- (a0 + a1·X)(b0 + b1·X) = (a0·b0 + 7·a1·b1) + (a0·b1 + a1·b0)·X.
  fn ext_mul(a: Ext, b: Ext) -> Ext {
    ext_mul_impl(a, b)
  }
  fn ext_mul_impl(a: Ext, b: Ext) -> Ext {
    [@val_add(@val_mul(a[0], b[0]), @val_mul(@ext_w(), @val_mul(a[1], b[1]))),
     @val_add(@val_mul(a[0], b[1]), @val_mul(a[1], b[0]))]
  }
  -- conjugate ā = a0 − a1·X, norm a·ā = a0² − 7·a1² ∈ 𝔽_p, a⁻¹ = ā / norm.
  fn ext_inverse(a: Ext) -> Ext { ext_inverse_impl(a) }
  fn ext_inverse_impl(a: Ext) -> Ext {
    let norm = @val_sub(@val_mul(a[0], a[0]), @val_mul(@ext_w(), @val_mul(a[1], a[1])));
    let ninv = @val_inverse(norm);
    [@val_mul(a[0], ninv), @val_mul(@val_neg(a[1]), ninv)]
  }
  fn ext_div(a: Ext, b: Ext) -> Ext {
    ext_mul_impl(a, ext_inverse_impl(b))
  }
  -- 1 iff two extension elements are equal.
  fn ext_eq(a: Ext, b: Ext) -> G {
    @val_is_zero(@val_sub(a[0], b[0])) * @val_is_zero(@val_sub(a[1], b[1]))
  }

  -- ==========================================================================
  -- Self-tests (vs `gl_ops_ref` — the same vectors the native form's suite
  -- pins, plus the boundary ops). Values are canonical integers.
  -- ==========================================================================
  pub fn fg_addsub_test() -> G {
    let a = 18364758544493064720; -- 0xFEDCBA9876543210
    let b = 1311768467463790320;  -- 0x123456789ABCDEF0
    assert_eq!(@val_add(a, b), 1229782942542270719);
    assert_eq!(@val_sub(a, b), 17052990077029274400);
    assert_eq!(@val_sub(b, a), 1393753992385309921);
    -- edge: (p-1) + 5 ≡ 4 ; 5 - (p-1) ≡ 6
    let pm1 = 18446744069414584320;
    assert_eq!(@val_add(pm1, 5), 4);
    assert_eq!(@val_sub(5, pm1), 6);
    1
  }
  pub fn fg_muldiv_test() -> G {
    let a = 18364758544493064720; -- 0xFEDCBA9876543210
    let b = 1311768467463790320;  -- 0x123456789ABCDEF0
    assert_eq!(@val_mul(a, b), 18080541965438139092);
    assert_eq!(@val_inverse(a), 7352237129603030369);
    -- edge: (p-1)·5 ≡ p-5
    let pm1 = 18446744069414584320;
    assert_eq!(@val_mul(pm1, 5), 18446744069414584316);
    -- a·a⁻¹ = 1 and b·b⁻¹ = 1; 0⁻¹ = 0
    assert_eq!(@val_mul(a, @val_inverse(a)), 1);
    assert_eq!(@val_mul(b, @val_inverse(b)), 1);
    assert_eq!(@val_inverse(0), 0);
    1
  }
  pub fn fg_ext_ops_test() -> G {
    -- e0 = (0xFEDCBA9876543210, 0x0123456789ABCDEF), e1 = (0x1111111122222222, 0x3333333344444444)
    let e0 = [18364758544493064720, 81985529216486895];
    let e1 = [1229782938533634594, 3689348815028241476];
    let s = @ext_add(e0, e1);
    assert_eq!(s[0], 1147797413612114993);
    assert_eq!(s[1], 3771334344244728371);
    let m = @ext_mul(e0, e1);
    assert_eq!(m[0], 9707086647507742218);
    assert_eq!(m[1], 4837146220115323607);
    let inv = @ext_inverse(e0);
    assert_eq!(inv[0], 15624774584742309597);
    assert_eq!(inv[1], 17771582427853906802);
    let d = @ext_div(e0, e1);
    assert_eq!(d[0], 4566604814623980330);
    assert_eq!(d[1], 10158067406679060168);
    -- e0 · e0⁻¹ = 1
    let one = @ext_mul(e0, @ext_inverse(e0));
    assert_eq!(one[0], 1);
    assert_eq!(one[1], 0);
    1
  }
  pub fn fg_boundary_test() -> G {
    -- val_from_bytes reduces a non-canonical wire limb: p + 3 → 3; a canonical value
    -- passes through.
    let p_plus_3 = [4u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 255u8];
    assert_eq!(@val_from_bytes(p_plus_3), 3);
    let a = [16u8, 50u8, 84u8, 118u8, 152u8, 186u8, 220u8, 254u8];
    assert_eq!(@val_from_bytes(a), 18364758544493064720);
    -- val_to_bytes inverts val_from_bytes on canonical values.
    let ab = @val_to_bytes(@val_from_bytes(a));
    assert_eq!(to_field(ab[0]), 16);
    assert_eq!(to_field(ab[7]), 254);
    -- bytes_lt_modulus: p is not < p; p − 1 is.
    assert_eq!(@bytes_lt_modulus([1u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 255u8]), 0);
    assert_eq!(@bytes_lt_modulus([0u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 255u8]), 1);
    -- val_is_zero on zero and one; two-adic root sanity: root^(2^31) = p − 1
    -- (31 squarings), and squaring once more gives 1.
    assert_eq!(@val_is_zero(@val_zero()), 1);
    assert_eq!(@val_is_zero(@val_one()), 0);
    let r31 = val_sq_n(@val_two_adic_root(), 31);
    assert_eq!(r31, 18446744069414584320);
    assert_eq!(@val_mul(r31, r31), 1);
    1
  }
  -- n repeated squarings (test helper).
  fn val_sq_n(x: Val, n: G) -> Val {
    match n {
      0 => x,
      _ => val_sq_n(val_mul_impl(x, x), n - 1),
    }
  }
⟧

end MultiStark

end
