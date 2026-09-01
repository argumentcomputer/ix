module
public import Ix.Aiur.Meta

/-!
# Field-width profile, KOALABEAR form

The same interface as `Width/Goldilocks.lean` for an outer field of 31 bits
(KoalaBear, `p = 2³¹ − 2²⁴ + 1 = 2130706433`, under the Hypercube backend),
where nothing 32-bit packs injectively:

- `u32_lt` compares through hinted 3-byte decompositions — a CHECKED
  24-bit comparison: an index at or beyond 2²⁴ fails the recomposition
  pin, never wraps. (The kernel's index space — de Bruijn depths, spine
  lengths, counts — lives far below 2²⁴; the `IDX_MAX` sentinel is its
  +∞.)
- `u32_add`/`u32_add3` are `u8_add` carry chains (wrapping, like the
  Goldilocks forms — only the encoding differs, not the semantics).
- `PackedDigest = [G; 16]`: blake3 digests pack 2 LE bytes per element
  (2¹⁶ < p in any field this profile serves).
- `u32_split` decomposes a field-held value into 4 LE bytes with a
  CANONICALITY pin against KoalaBear's `p` (the 4-byte recomposition wraps
  mod p, so the byte comparison against `p`'s bytes is what makes the
  decomposition unique). This is the one `p`-specific function.
- `canon_addr_chunk` compares the 4 address bytes big-endian, one byte at
  a time, through the kernel's ordering combinators.

The plain (non-`inline`) functions are deliberate: their bodies carry
lookups, so calls memoize into one circuit instead of splicing per site —
the implementor's half of the inline convention.

All of this is byte logic: it computes identical results under the
Goldilocks interpreter for in-range values, which is how the parity suite
validates it before any KoalaBear machinery runs.
-/

public section

namespace IxVM

def widthKoalaBear := ⟦
  -- Blake3 digests as 16 elements of 2 packed LE bytes.
  type PackedDigest = [G; 16]

  fn b3_pack(h: [[U8; 4]; 8]) -> PackedDigest {
    let [w0, w1, w2, w3, w4, w5, w6, w7] = h;
    [to_field(w0[0]) + 256 * to_field(w0[1]), to_field(w0[2]) + 256 * to_field(w0[3]),
     to_field(w1[0]) + 256 * to_field(w1[1]), to_field(w1[2]) + 256 * to_field(w1[3]),
     to_field(w2[0]) + 256 * to_field(w2[1]), to_field(w2[2]) + 256 * to_field(w2[3]),
     to_field(w3[0]) + 256 * to_field(w3[1]), to_field(w3[2]) + 256 * to_field(w3[3]),
     to_field(w4[0]) + 256 * to_field(w4[1]), to_field(w4[2]) + 256 * to_field(w4[3]),
     to_field(w5[0]) + 256 * to_field(w5[1]), to_field(w5[2]) + 256 * to_field(w5[3]),
     to_field(w6[0]) + 256 * to_field(w6[1]), to_field(w6[2]) + 256 * to_field(w6[3]),
     to_field(w7[0]) + 256 * to_field(w7[1]), to_field(w7[2]) + 256 * to_field(w7[3])]
  }

  -- Hinted 3-byte decomposition of an index `< 2²⁴`; the recomposition pin
  -- makes it unique (the sum is `< 2²⁴ < p`, it cannot wrap) and makes any
  -- wider value fail.
  inline fn u24_split(x: G) -> (U8, U8, U8) {
    let [h0, h1, h2, h3, h4, h5, h6, h7] = unconstrained_g_to_bytes(x);
    let (b0, b1) = u8_range_check(h0, h1);
    let (b2, b2x) = u8_range_check(h2, h2);
    assert_eq!(x, to_field(b0) + 256 * to_field(b1) + 65536 * to_field(b2),
      "u32_lt: value exceeds 2^24 (narrow-field index bound)");
    (b0, b1, b2)
  }

  -- Checked 24-bit less-than on field-held indices: byte-lexicographic
  -- from the high byte.
  fn u32_lt(a: G, b: G) -> G {
    let (a0, a1, a2) = u24_split(a);
    let (b0, b1, b2) = u24_split(b);
    match to_field(a2) - to_field(b2) {
      0 =>
        match to_field(a1) - to_field(b1) {
          0 => u8_less_than(a0, b0),
          _ => u8_less_than(a1, b1),
        },
      _ => u8_less_than(a2, b2),
    }
  }

  -- Wrapping little-endian u32 addition as a `u8_add` carry chain (cf.
  -- `u64_add`); the final carry-out is dropped.
  fn u32_add(a: [U8; 4], b: [U8; 4]) -> [U8; 4] {
    let [a0, a1, a2, a3] = a;
    let [b0, b1, b2, b3] = b;
    let (s0, c1) = u8_add(a0, b0);
    let (t1, o1) = u8_add(a1, b1);
    let (s1, c1a) = u8_add(t1, c1);
    let c2 = u8_from_field_unsafe(to_field(o1) + to_field(c1a));
    let (t2, o2) = u8_add(a2, b2);
    let (s2, c2a) = u8_add(t2, c2);
    let c3 = u8_from_field_unsafe(to_field(o2) + to_field(c2a));
    let (t3, o3) = u8_add(a3, b3);
    let (s3, c3a) = u8_add(t3, c3);
    [s0, s1, s2, s3]
  }

  -- Wrapping sum of three u32s: two chained wrapping adds (mod-2³²
  -- addition is associative, so the composition equals the 3-way sum).
  fn u32_add3(a: [U8; 4], b: [U8; 4], c: [U8; 4]) -> [U8; 4] {
    u32_add(u32_add(a, b), c)
  }
⟧

def kernelWidthKoalaBear := ⟦
  -- The +∞ index sentinel of the 24-bit index space.
  const IDX_MAX: G = 16777215

  -- The four little-endian bytes of a field-held value. The 4-byte
  -- recomposition wraps mod p, so on its own it also admits the bytes of
  -- `x + p`; the canonicality pin against p's bytes (p = 0x7F000001, LE
  -- `[1, 0, 0, 127]`) excludes the alias and makes the decomposition
  -- unique for every canonical `x < p`.
  inline fn u32_split(x: G) -> [U8; 4] {
    let [h0, h1, h2, h3, h4, h5, h6, h7] = unconstrained_g_to_bytes(x);
    let (b0, b1) = u8_range_check(h0, h1);
    let (b2, b3) = u8_range_check(h2, h3);
    assert_eq!(x, to_field(b0) + 256 * to_field(b1)
               + 65536 * to_field(b2) + 16777216 * to_field(b3),
      "u32 byte split does not recompose to the original value");
    -- Canonicality, branch-free: either the top byte is below p's
    -- (`hi_lt = 1`), or it EQUALS p's top byte and the low three are all
    -- zero (p = 0x7F000001, so the only canonical value with top byte 127
    -- is p - 1 = 0x7F000000... and every value strictly below it).
    let hi_lt = u8_less_than(b3, 127u8);
    assert_eq!((1 - hi_lt) * (to_field(b3) - 127), 0,
      "u32 byte split: value is not canonical (top byte exceeds p's)");
    assert_eq!((1 - hi_lt) * (to_field(b2) + to_field(b1) + to_field(b0)), 0,
      "u32 byte split: value is not canonical (>= p)");
    [b0, b1, b2, b3]
  }

  -- Big-endian byte-wise comparison of one 4-byte address chunk, through
  -- the kernel's ordering combinators (single bytes are far below 2²⁴, so
  -- `canon_ord_cmp_g`'s `u32_lt` stays in range).
  fn canon_addr_chunk(x0: G, x1: G, x2: G, x3: G,
                    y0: G, y1: G, y2: G, y3: G) -> G {
    canon_ord_then(canon_ord_cmp_g(x0, y0),
      canon_ord_then(canon_ord_cmp_g(x1, y1),
        canon_ord_then(canon_ord_cmp_g(x2, y2), canon_ord_cmp_g(x3, y3))))
  }
⟧

end IxVM

end
