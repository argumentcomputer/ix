module
public import Ix.Aiur.Meta

/-!
# Non-native Goldilocks field arithmetic (`Goldilocks = [U8; 8]`)

The recursive verifier computes on the *inner* proof's field (Goldilocks),
but Aiur compiles the verifier to its *own* (outer) field — which is **not
always Goldilocks** (it may be the BLS scalar field). So inner-field arithmetic
cannot use Aiur's native `+`/`*` (those compute in the outer field); it must be
**emulated** on bytes.

A `Goldilocks` element is its canonical value `< p = 2⁶⁴ − 2³² + 1` held as 8
little-endian bytes (`[U8; 8]`), and `ExtGoldilocks = [Goldilocks; 2]` is the
degree-2 extension `𝔽_p[X]/(X² − 7)`. All ops are built from the u8 gadgets
(`u8_add`/`u8_sub`/`u8_mul` give full carry/borrow/16-bit-product), so they are
field-agnostic and produce bytes directly (no field→byte decomposition needed).

`EPSILON = 2³² − 1`, and `2⁶⁴ ≡ EPSILON (mod p)`, the basis of the reductions.

Validated byte-for-byte against `multi-stark`'s native Goldilocks (`gl_ops_ref`
in `multi-stark/src/types.rs`).
-/

public section

namespace MultiStark

def goldilocks := ⟦
  type Goldilocks = [U8; 8]
  type ExtGoldilocks = [Goldilocks; 2]

  -- p = 2⁶⁴ − 2³² + 1 and EPSILON = 2³² − 1, little-endian.
  fn gl_p() -> Goldilocks { [1u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 255u8] }
  fn gl_eps() -> Goldilocks { [255u8, 255u8, 255u8, 255u8, 0u8, 0u8, 0u8, 0u8] }
  fn gl_zero() -> Goldilocks { [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8] }
  fn gl_one() -> Goldilocks { [1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8] }

  -- ==========================================================================
  -- Byte-vector primitives (carry/borrow chains over the u8 gadgets).
  -- ==========================================================================

  -- Add two bytes with a carry-in (0/1). Returns (sum byte, carry-out 0/1).
  -- `u8_add` adds only two bytes; the carry-in is folded with a second add. At
  -- most one of the two overflow flags fires, so the carry-out stays 0/1.
  fn adc(a: U8, b: U8, cin: G) -> (U8, G) {
    let (s1, o1) = u8_add(a, b);
    let (s2, o2) = u8_add(s1, u8_from_field_unsafe(cin));
    (s2, to_field(o1) + to_field(o2))
  }

  -- Subtract two bytes with a borrow-in (0/1). Returns (diff byte, borrow-out).
  fn sbb(a: U8, b: U8, bin: G) -> (U8, G) {
    let (d1, w1) = u8_sub(a, b);
    let (d2, w2) = u8_sub(d1, u8_from_field_unsafe(bin));
    (d2, to_field(w1) + to_field(w2))
  }

  -- 8-byte (64-bit) add. Returns the 8-byte sum and the final carry (0/1).
  fn add8(a: Goldilocks, b: Goldilocks) -> (Goldilocks, G) {
    let (r0, c0) = adc(a[0], b[0], 0);
    let (r1, c1) = adc(a[1], b[1], c0);
    let (r2, c2) = adc(a[2], b[2], c1);
    let (r3, c3) = adc(a[3], b[3], c2);
    let (r4, c4) = adc(a[4], b[4], c3);
    let (r5, c5) = adc(a[5], b[5], c4);
    let (r6, c6) = adc(a[6], b[6], c5);
    let (r7, c7) = adc(a[7], b[7], c6);
    ([r0, r1, r2, r3, r4, r5, r6, r7], c7)
  }

  -- 8-byte (64-bit) subtract. Returns the 8-byte difference and final borrow.
  fn sub8(a: Goldilocks, b: Goldilocks) -> (Goldilocks, G) {
    let (r0, w0) = sbb(a[0], b[0], 0);
    let (r1, w1) = sbb(a[1], b[1], w0);
    let (r2, w2) = sbb(a[2], b[2], w1);
    let (r3, w3) = sbb(a[3], b[3], w2);
    let (r4, w4) = sbb(a[4], b[4], w3);
    let (r5, w5) = sbb(a[5], b[5], w4);
    let (r6, w6) = sbb(a[6], b[6], w5);
    let (r7, w7) = sbb(a[7], b[7], w6);
    ([r0, r1, r2, r3, r4, r5, r6, r7], w7)
  }

  -- Branchless select on a 0/1 flag: `cond ? x : y` (per byte). `cond` is a
  -- field element in {0,1}; each result byte equals x[i] or y[i] (both < 256),
  -- so `u8_from_field_unsafe` is safe.
  fn sel(cond: G, x: U8, y: U8) -> U8 {
    u8_from_field_unsafe(to_field(x) * cond + to_field(y) * (1 - cond))
  }
  fn select8(cond: G, x: Goldilocks, y: Goldilocks) -> Goldilocks {
    [sel(cond, x[0], y[0]), sel(cond, x[1], y[1]), sel(cond, x[2], y[2]),
     sel(cond, x[3], y[3]), sel(cond, x[4], y[4]), sel(cond, x[5], y[5]),
     sel(cond, x[6], y[6]), sel(cond, x[7], y[7])]
  }

  -- ==========================================================================
  -- Base field add / sub (mod p).
  -- ==========================================================================

  -- a + b mod p. The raw sum is `c·2⁶⁴ + s` with `c ∈ {0,1}`, value `< 2p`:
  --   • c = 1 ⇒ s < p (since 2⁶⁴ > p), and `2⁶⁴ + s − p = s + EPSILON`
  --     (a non-overflowing add since the true result is < p);
  --   • c = 0 ⇒ reduce by one conditional subtraction of p (when s ≥ p).
  fn gl_add(a: Goldilocks, b: Goldilocks) -> Goldilocks {
    let (s, c) = add8(a, b);
    let (s_minus_p, borrow) = sub8(s, gl_p());  -- borrow = 1 iff s < p
    let (s_plus_eps, _) = add8(s, gl_eps());
    let c0 = select8(1 - borrow, s_minus_p, s); -- c=0 branch: (s≥p ? s−p : s)
    select8(c, s_plus_eps, c0)
  }

  -- a − b mod p. `sub8` borrow = 1 iff a < b, in which case the true result is
  -- `(a − b mod 2⁶⁴) − EPSILON = a − b + p`.
  fn gl_sub(a: Goldilocks, b: Goldilocks) -> Goldilocks {
    let (d, borrow) = sub8(a, b);
    let (d_minus_eps, _) = sub8(d, gl_eps());
    select8(borrow, d_minus_eps, d)
  }

  fn gl_neg(a: Goldilocks) -> Goldilocks { gl_sub(gl_zero(), a) }
  fn gl_seven() -> Goldilocks { [7u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8] }
  fn gl_two() -> Goldilocks { [2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8] }

  -- Canonicalize an arbitrary 8-byte value (possibly ≥ p, e.g. a raw hash limb
  -- or a non-canonical wire encoding) to the canonical representative `< p`.
  -- Any 8-byte value is `< 2⁶⁴ < 2p`, so one conditional subtraction of p
  -- suffices (borrow = 1 iff x < p ⇒ already canonical).
  fn gl_reduce(x: Goldilocks) -> Goldilocks {
    let (xmp, borrow) = sub8(x, gl_p());
    select8(borrow, x, xmp)
  }

  -- 1 iff `x` is the field zero (canonicalize first, then test all bytes zero).
  -- The byte sum is `< 8·256 = 2048`, so `eq_zero` of the sum is field-agnostic.
  fn gl_is_zero(x: Goldilocks) -> G {
    let r = gl_reduce(x);
    eq_zero(to_field(r[0]) + to_field(r[1]) + to_field(r[2]) + to_field(r[3])
          + to_field(r[4]) + to_field(r[5]) + to_field(r[6]) + to_field(r[7]))
  }

  -- 1 iff two canonical Goldilocks values are equal (byte-exact). Inputs must be
  -- canonical (`gl_*` outputs always are); each `to_field` difference is small.
  fn gl_eq(a: Goldilocks, b: Goldilocks) -> G {
    eq_zero(to_field(a[0]) - to_field(b[0])) * eq_zero(to_field(a[1]) - to_field(b[1]))
      * eq_zero(to_field(a[2]) - to_field(b[2])) * eq_zero(to_field(a[3]) - to_field(b[3]))
      * eq_zero(to_field(a[4]) - to_field(b[4])) * eq_zero(to_field(a[5]) - to_field(b[5]))
      * eq_zero(to_field(a[6]) - to_field(b[6])) * eq_zero(to_field(a[7]) - to_field(b[7]))
  }

  -- ==========================================================================
  -- Base field multiply (mod p): schoolbook 64×64 → 128-bit product, then the
  -- Goldilocks `reduce128` (ported from Plonky3 `goldilocks.rs`).
  -- ==========================================================================

  -- 8-byte × 1-byte → 9-byte product (`a · m`, with `a < 2⁶⁴`, `m < 2⁸`, so the
  -- result is `< 2⁷²`). Column `k` is `lo_k + hi_{k-1} + carry`, and the carry
  -- provably stays in {0,1} (each column sum ≤ 255+255+1 = 511 < 512).
  fn mul1(a: Goldilocks, m: U8) -> [U8; 9] {
    let (l0, h0) = u8_mul(a[0], m);
    let (l1, h1) = u8_mul(a[1], m);
    let (l2, h2) = u8_mul(a[2], m);
    let (l3, h3) = u8_mul(a[3], m);
    let (l4, h4) = u8_mul(a[4], m);
    let (l5, h5) = u8_mul(a[5], m);
    let (l6, h6) = u8_mul(a[6], m);
    let (l7, h7) = u8_mul(a[7], m);
    let (r1, c1) = adc(l1, h0, 0);
    let (r2, c2) = adc(l2, h1, c1);
    let (r3, c3) = adc(l3, h2, c2);
    let (r4, c4) = adc(l4, h3, c3);
    let (r5, c5) = adc(l5, h4, c4);
    let (r6, c6) = adc(l6, h5, c5);
    let (r7, c7) = adc(l7, h6, c6);
    let (r8, _)  = adc(h7, 0u8, c7);
    [l0, r1, r2, r3, r4, r5, r6, r7, r8]
  }

  -- 16-byte (128-bit) add, carry chain. The final carry is discarded (used only
  -- to accumulate partial-product rows whose total provably fits in 128 bits).
  fn add16(x: [U8; 16], y: [U8; 16]) -> [U8; 16] {
    let (r0,  c0)  = adc(x[0],  y[0],  0);
    let (r1,  c1)  = adc(x[1],  y[1],  c0);
    let (r2,  c2)  = adc(x[2],  y[2],  c1);
    let (r3,  c3)  = adc(x[3],  y[3],  c2);
    let (r4,  c4)  = adc(x[4],  y[4],  c3);
    let (r5,  c5)  = adc(x[5],  y[5],  c4);
    let (r6,  c6)  = adc(x[6],  y[6],  c5);
    let (r7,  c7)  = adc(x[7],  y[7],  c6);
    let (r8,  c8)  = adc(x[8],  y[8],  c7);
    let (r9,  c9)  = adc(x[9],  y[9],  c8);
    let (r10, c10) = adc(x[10], y[10], c9);
    let (r11, c11) = adc(x[11], y[11], c10);
    let (r12, c12) = adc(x[12], y[12], c11);
    let (r13, c13) = adc(x[13], y[13], c12);
    let (r14, c14) = adc(x[14], y[14], c13);
    let (r15, _)   = adc(x[15], y[15], c14);
    [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15]
  }

  -- Full 64×64 → 128-bit product as 16 little-endian bytes. Eight single-byte
  -- rows `a · b[i]`, each shifted left by `i` bytes and accumulated.
  fn mul128(a: Goldilocks, b: Goldilocks) -> [U8; 16] {
    let m0 = mul1(a, b[0]);
    let m1 = mul1(a, b[1]);
    let m2 = mul1(a, b[2]);
    let m3 = mul1(a, b[3]);
    let m4 = mul1(a, b[4]);
    let m5 = mul1(a, b[5]);
    let m6 = mul1(a, b[6]);
    let m7 = mul1(a, b[7]);
    let acc = [m0[0], m0[1], m0[2], m0[3], m0[4], m0[5], m0[6], m0[7], m0[8],
               0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
    let rb1 = [0u8, m1[0], m1[1], m1[2], m1[3], m1[4], m1[5], m1[6], m1[7], m1[8],
               0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
    let acc = add16(acc, rb1);
    let rb2 = [0u8, 0u8, m2[0], m2[1], m2[2], m2[3], m2[4], m2[5], m2[6], m2[7], m2[8],
               0u8, 0u8, 0u8, 0u8, 0u8];
    let acc = add16(acc, rb2);
    let rb3 = [0u8, 0u8, 0u8, m3[0], m3[1], m3[2], m3[3], m3[4], m3[5], m3[6], m3[7], m3[8],
               0u8, 0u8, 0u8, 0u8];
    let acc = add16(acc, rb3);
    let rb4 = [0u8, 0u8, 0u8, 0u8, m4[0], m4[1], m4[2], m4[3], m4[4], m4[5], m4[6], m4[7], m4[8],
               0u8, 0u8, 0u8];
    let acc = add16(acc, rb4);
    let rb5 = [0u8, 0u8, 0u8, 0u8, 0u8, m5[0], m5[1], m5[2], m5[3], m5[4], m5[5], m5[6], m5[7], m5[8],
               0u8, 0u8];
    let acc = add16(acc, rb5);
    let rb6 = [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, m6[0], m6[1], m6[2], m6[3], m6[4], m6[5], m6[6], m6[7], m6[8],
               0u8];
    let acc = add16(acc, rb6);
    let rb7 = [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, m7[0], m7[1], m7[2], m7[3], m7[4], m7[5], m7[6], m7[7], m7[8]];
    add16(acc, rb7)
  }

  -- Reduce a 128-bit value (16 LE bytes) mod p. Port of Plonky3 `reduce128`:
  -- with `x = x_lo + x_hi·2⁶⁴`, split `x_hi = x_hi_lo + x_hi_hi·2³²`; then
  -- `2⁶⁴ ≡ EPSILON` and `2⁹⁶ ≡ −1` give `x ≡ x_lo − x_hi_hi + x_hi_lo·EPSILON`.
  -- A final conditional subtraction of p canonicalizes (Plonky3 keeps a
  -- non-canonical u64; we need the canonical bytes).
  fn reduce128(p: [U8; 16]) -> Goldilocks {
    let xlo = [p[0], p[1], p[2], p[3], p[4], p[5], p[6], p[7]];
    let xhl = [p[8], p[9], p[10], p[11], 0u8, 0u8, 0u8, 0u8];   -- low 32 bits of x_hi
    let xhh = [p[12], p[13], p[14], p[15], 0u8, 0u8, 0u8, 0u8]; -- high 32 bits of x_hi
    -- t0 = x_lo − x_hi_hi (subtract EPSILON on borrow; cannot underflow).
    let (t0w, borrow) = sub8(xlo, xhh);
    let (t0b, _) = sub8(t0w, gl_eps());
    let t0 = select8(borrow, t0b, t0w);
    -- t1 = x_hi_lo · EPSILON  (< 2⁶⁴, so only the low 8 product bytes matter).
    let t1full = mul128(xhl, gl_eps());
    let t1 = [t1full[0], t1full[1], t1full[2], t1full[3],
              t1full[4], t1full[5], t1full[6], t1full[7]];
    -- t2 = t0 + t1  (add EPSILON on overflow; result stays < 2⁶⁴).
    let (t2w, carry) = add8(t0, t1);
    let (t2c, _) = add8(t2w, gl_eps());
    let t2 = select8(carry, t2c, t2w);
    -- canonicalize: borrow2 = 1 iff t2 < p ⇒ keep t2, else subtract p.
    let (t2mp, borrow2) = sub8(t2, gl_p());
    select8(borrow2, t2, t2mp)
  }

  fn gl_mul(a: Goldilocks, b: Goldilocks) -> Goldilocks { reduce128(mul128(a, b)) }
  fn gl_sq(a: Goldilocks) -> Goldilocks { gl_mul(a, a) }

  -- ==========================================================================
  -- Base field inverse / divide via Fermat: a⁻¹ = a^(p−2).
  -- p − 2 = 2⁶⁴ − 2³² − 1 — in binary: bit 32 is 0, every other bit is 1
  -- (31 ones, one zero, 32 ones). `gl_run` applies `n` steps of `acc ← acc²·b`.
  -- ==========================================================================
  fn gl_run(acc: Goldilocks, base: Goldilocks, n: G) -> Goldilocks {
    match n {
      0 => acc,
      _ => gl_run(gl_mul(gl_sq(acc), base), base, n - 1),
    }
  }
  fn gl_inverse(x: Goldilocks) -> Goldilocks {
    let acc = gl_run(x, x, 30);  -- bits 63..33: 31 ones (initial acc = x is bit 63)
    let acc = gl_sq(acc);        -- bit 32: a single 0
    gl_run(acc, x, 32)           -- bits 31..0: 32 ones
  }
  fn gl_div(a: Goldilocks, b: Goldilocks) -> Goldilocks { gl_mul(a, gl_inverse(b)) }

  -- ==========================================================================
  -- Extension field ExtGoldilocks = 𝔽_p[X]/(X² − 7).
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
    [gl_add(gl_mul(a[0], b[0]), gl_mul(gl_seven(), gl_mul(a[1], b[1]))),
     gl_add(gl_mul(a[0], b[1]), gl_mul(a[1], b[0]))]
  }
  -- conjugate ā = a0 − a1·X, norm a·ā = a0² − 7·a1² ∈ 𝔽_p, a⁻¹ = ā / norm.
  fn eg_inverse(a: ExtGoldilocks) -> ExtGoldilocks {
    let norm = gl_sub(gl_sq(a[0]), gl_mul(gl_seven(), gl_sq(a[1])));
    let ninv = gl_inverse(norm);
    [gl_mul(a[0], ninv), gl_mul(gl_neg(a[1]), ninv)]
  }
  fn eg_div(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    eg_mul(a, eg_inverse(b))
  }
  -- 1 iff two extension elements are equal (both coordinates byte-exact).
  fn eg_eq(a: ExtGoldilocks, b: ExtGoldilocks) -> G {
    gl_eq(a[0], b[0]) * gl_eq(a[1], b[1])
  }

  -- ==========================================================================
  -- Self-test (vs `gl_ops_ref`).
  -- ==========================================================================
  fn assert_g8(x: Goldilocks, e: Goldilocks) -> G {
    assert_eq!(to_field(x[0]), to_field(e[0]));
    assert_eq!(to_field(x[1]), to_field(e[1]));
    assert_eq!(to_field(x[2]), to_field(e[2]));
    assert_eq!(to_field(x[3]), to_field(e[3]));
    assert_eq!(to_field(x[4]), to_field(e[4]));
    assert_eq!(to_field(x[5]), to_field(e[5]));
    assert_eq!(to_field(x[6]), to_field(e[6]));
    assert_eq!(to_field(x[7]), to_field(e[7]));
    1
  }
  pub fn gl_addsub_test() -> G {
    let a = [16u8, 50u8, 84u8, 118u8, 152u8, 186u8, 220u8, 254u8]; -- 0xFEDCBA9876543210
    let b = [240u8, 222u8, 188u8, 154u8, 120u8, 86u8, 52u8, 18u8]; -- 0x123456789ABCDEF0
    assert_eq!(assert_g8(gl_add(a, b), [255u8, 16u8, 17u8, 17u8, 18u8, 17u8, 17u8, 17u8]), 1);
    assert_eq!(assert_g8(gl_sub(a, b), [32u8, 83u8, 151u8, 219u8, 31u8, 100u8, 168u8, 236u8]), 1);
    assert_eq!(assert_g8(gl_sub(b, a), [225u8, 172u8, 104u8, 36u8, 223u8, 155u8, 87u8, 19u8]), 1);
    -- edge: (p-1) + 5 ≡ 4 ; 5 - (p-1) ≡ 6
    let pm1 = [0u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 255u8]; -- 0xFFFFFFFF00000000
    let five = [5u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
    assert_eq!(assert_g8(gl_add(pm1, five), [4u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]), 1);
    assert_eq!(assert_g8(gl_sub(five, pm1), [6u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]), 1);
    1
  }

  fn assert_eg(x: ExtGoldilocks, e0: Goldilocks, e1: Goldilocks) -> G {
    assert_eq!(assert_g8(x[0], e0), 1);
    assert_eq!(assert_g8(x[1], e1), 1);
    1
  }
  pub fn gl_muldiv_test() -> G {
    let a = [16u8, 50u8, 84u8, 118u8, 152u8, 186u8, 220u8, 254u8]; -- 0xFEDCBA9876543210
    let b = [240u8, 222u8, 188u8, 154u8, 120u8, 86u8, 52u8, 18u8]; -- 0x123456789ABCDEF0
    assert_eq!(assert_g8(gl_mul(a, b), [212u8, 186u8, 123u8, 108u8, 31u8, 253u8, 234u8, 250u8]), 1);
    assert_eq!(assert_g8(gl_inverse(a), [97u8, 29u8, 109u8, 46u8, 183u8, 100u8, 8u8, 102u8]), 1);
    assert_eq!(assert_g8(gl_div(a, b), [63u8, 59u8, 61u8, 54u8, 46u8, 255u8, 29u8, 186u8]), 1);
    -- edge: (p-1)·5 ≡ p-5
    let pm1 = [0u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 255u8];
    let five = [5u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
    assert_eq!(assert_g8(gl_mul(pm1, five), [252u8, 255u8, 255u8, 255u8, 254u8, 255u8, 255u8, 255u8]), 1);
    -- a·a⁻¹ = 1 and b·b⁻¹ = 1
    assert_eq!(assert_g8(gl_mul(a, gl_inverse(a)), gl_one()), 1);
    assert_eq!(assert_g8(gl_mul(b, gl_inverse(b)), gl_one()), 1);
    1
  }
  pub fn eg_ops_test() -> G {
    -- e0 = (0xFEDCBA9876543210, 0x0123456789ABCDEF), e1 = (0x1111111122222222, 0x3333333344444444)
    let e0 = [[16u8, 50u8, 84u8, 118u8, 152u8, 186u8, 220u8, 254u8],
              [239u8, 205u8, 171u8, 137u8, 103u8, 69u8, 35u8, 1u8]];
    let e1 = [[34u8, 34u8, 34u8, 34u8, 17u8, 17u8, 17u8, 17u8],
              [68u8, 68u8, 68u8, 68u8, 51u8, 51u8, 51u8, 51u8]];
    assert_eq!(assert_eg(eg_add(e0, e1),
      [49u8, 84u8, 118u8, 152u8, 170u8, 203u8, 237u8, 15u8],
      [51u8, 18u8, 240u8, 205u8, 154u8, 120u8, 86u8, 52u8]), 1);
    assert_eq!(assert_eg(eg_mul(e0, e1),
      [10u8, 238u8, 162u8, 36u8, 224u8, 127u8, 182u8, 134u8],
      [215u8, 234u8, 152u8, 224u8, 219u8, 254u8, 32u8, 67u8]), 1);
    assert_eq!(assert_eg(eg_inverse(e0),
      [221u8, 238u8, 29u8, 131u8, 179u8, 89u8, 214u8, 216u8],
      [114u8, 99u8, 206u8, 108u8, 15u8, 88u8, 161u8, 246u8]), 1);
    assert_eq!(assert_eg(eg_div(e0, e1),
      [42u8, 59u8, 64u8, 77u8, 226u8, 214u8, 95u8, 63u8],
      [200u8, 46u8, 148u8, 147u8, 124u8, 180u8, 248u8, 140u8]), 1);
    -- e0 · e0⁻¹ = 1
    assert_eq!(assert_eg(eg_mul(e0, eg_inverse(e0)), gl_one(), gl_zero()), 1);
    1
  }
⟧

end MultiStark

end
