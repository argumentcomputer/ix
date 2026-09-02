module
public import Ix.Aiur.Meta

/-!
# Field-width profile, GOLDILOCKS form

The IxVM operations whose circuit encoding depends on the outer field's
width, gathered behind one interface so a narrower field (KoalaBear under
the Hypercube backend) swaps implementations instead of touching the
kernel. The Goldilocks forms below exploit `p > 2³²`: packed-u32 hints with
virtual carries, 4-byte injective packings, and the u32 index space.

Two toplevels, because the consumers differ:

* `widthGoldilocks` — the CORE profile, merged wherever `byteStream`/
  `blake3` go (the kernel AND the recursive verifier): the wrapping u32
  adds, the u32 comparison, and the packed digest representation.
* `kernelWidthGoldilocks` — kernel-only extras (merged into `ixVMFull`
  alongside the core): the index sentinel, the u32 byte split, and the
  packed address-chunk comparison (which references the kernel's
  `canon_ord_cmp_g`).

A future `Width/Small.lean` provides the same names for fields of 31 bits
or less: byte carry chains for the adds, a 24-bit comparison (a checked
embedding — values at or beyond 2²⁴ fail, never wrap), 2-byte digest
packing (`PackedDigest = [G; 16]`), and byte-wise address chunks.

See also `Ix/IxVM/U64/` — the bytes ↔ field boundary of the byte-level
`U64`, the same pattern for 64-bit values.
-/

public section

namespace IxVM

def widthGoldilocks := ⟦
  -- Blake3 output words packed 4 LE bytes -> 1 field element (injective:
  -- 2^32 < p, unlike full 8-byte limbs), 8 elements per digest. The packed
  -- form is the public-input digest representation shared by the kernel's
  -- `verify_claim` and the recursive verifier's entrypoint.
  type PackedDigest = [G; 8]

  inline fn b3_pack_w(w: [U8; 4]) -> G {
    to_field(w[0]) + 256 * to_field(w[1]) + 65536 * to_field(w[2])
      + 16777216 * to_field(w[3])
  }

  inline fn b3_pack(h: [[U8; 4]; 8]) -> PackedDigest {
    let [w0, w1, w2, w3, w4, w5, w6, w7] = h;
    [b3_pack_w(w0), b3_pack_w(w1), b3_pack_w(w2), b3_pack_w(w3),
     b3_pack_w(w4), b3_pack_w(w5), b3_pack_w(w6), b3_pack_w(w7)]
  }

  -- u32 less-than on field-held values `< 2^32` (indices, lengths, counts;
  -- the op's carry-chain identity needs `p > 2^33`).
  inline fn u32_lt(a: G, b: G) -> G {
    u32_less_than(a, b)
  }

  -- Wrapping little-endian u32 addition. The four result bytes are advice and
  -- are range-checked here. The carry is the virtual expression
  -- `(a + b - result) / 2^32`; constraining it to be boolean uniquely pins the
  -- wrapping result, so a separate packed-sum equality would be redundant.
  inline fn u32_add(a: [U8; 4], b: [U8; 4]) -> [U8; 4] {
    let (raw, carry) = unconstrained_u32_add(a, b);
    let (z0, z1) = u8_range_check(raw[0], raw[1]);
    let (z2, z3) = u8_range_check(raw[2], raw[3]);

    assert_eq!(carry * carry, carry, "u32_add: carry is not boolean");

    [z0, z1, z2, z3]
  }

  -- Wrapping sum of three little-endian u32s. The output costs two paired
  -- range-check lookups. The virtual carry is
  -- `(a + b + c - result) / 2^32`; constraining it to {0, 1, 2} uniquely pins
  -- the result, so no separate packed-sum equality is needed.
  inline fn u32_add3(a: [U8; 4], b: [U8; 4], c: [U8; 4]) -> [U8; 4] {
    let (raw, carry) = unconstrained_u32_add3(a, b, c);
    let (z0, z1) = u8_range_check(raw[0], raw[1]);
    let (z2, z3) = u8_range_check(raw[2], raw[3]);

    assert_eq!(carry * (carry - 1) * (carry - 2), 0,
      "u32_add3: carry is not in {0, 1, 2}");

    [z0, z1, z2, z3]
  }
⟧

def kernelWidthGoldilocks := ⟦
  -- The +∞ index sentinel: the largest value the profile's `u32_lt`
  -- supports. `Subst`'s loose-bound-variable analysis returns it for
  -- "no loose BVar", and takes minima against it.
  const IDX_MAX: G = 4294967295

  -- The four little-endian bytes of a field-held u32. The `#split_u32`
  -- hint provides the bytes; the recomposition assert pins them (unique
  -- because the packed sum is `< 2^32 < p`).
  inline fn u32_split(x: G) -> [U8; 4] {
    match #split_u32(x) {
      (rb0, rb1, rb2, rb3) =>
        let b0 = u8_xor(u8_from_field_unsafe(rb0), 0u8);
        let b1 = u8_xor(u8_from_field_unsafe(rb1), 0u8);
        let b2 = u8_xor(u8_from_field_unsafe(rb2), 0u8);
        let b3 = u8_xor(u8_from_field_unsafe(rb3), 0u8);
        assert_eq!(x, to_field(b0) + 256 * to_field(b1)
                   + 65536 * to_field(b2) + 16777216 * to_field(b3),
          "u32 byte split does not recompose to the original value");
        [b0, b1, b2, b3],
    }
  }

  -- Compare one 4-byte big-endian chunk of two addresses: pack each side
  -- (injective, `< 2^32 < p`) and compare once, instead of four byte
  -- comparisons.
  fn canon_addr_chunk(x0: G, x1: G, x2: G, x3: G,
                    y0: G, y1: G, y2: G, y3: G) -> G {
    let xv = x0 * 16777216 + x1 * 65536 + x2 * 256 + x3;
    let yv = y0 * 16777216 + y1 * 65536 + y2 * 256 + y3;
    canon_ord_cmp_g(xv, yv)
  }
⟧

/-- Verifier-only wire plumbing over the outer field: interpreting raw
little-endian `u64` wire limbs as outer-field counts, the canonical wire
decomposition of a count, and digest-limb equality. Lives outside the core
profile because `count_to_bytes` references the field interface's
`bytes_lt_modulus`, which only verifier toplevels merge. Goldilocks forms:
the 8-byte fold is injective enough for counts (`< p` pinned) and digest
compares are exact on canonical hash outputs. -/
def widthGoldilocksWire := ⟦
  -- Interpret a raw little-endian `u64` limb as an OUTER-field element (byte
  -- recomposition; reduces mod the outer modulus when the limb exceeds it).
  -- Wire plumbing over the outer field — counts, digest-limb comparisons —
  -- NOT inner-field ingest: semantic inner values go through
  -- `val_from_bytes`, which lands in the merged module's representation.
  inline fn limb_to_field(b: U64) -> G {
    to_field(b[0])
      + 0x100 * to_field(b[1])
      + 0x10000 * to_field(b[2])
      + 0x1000000 * to_field(b[3])
      + 0x100000000 * to_field(b[4])
      + 0x10000000000 * to_field(b[5])
      + 0x1000000000000 * to_field(b[6])
      + 0x100000000000000 * to_field(b[7])
  }

  -- The canonical 8-LE-byte decomposition of an OUTER-field count (a value
  -- known < 2⁶⁴ by construction: shape words, derived widths). The bytes are
  -- prover hints; range checks + recomposition + the `< p` check pin the
  -- unique decomposition (a count `c < 2³² − 1` would also admit the bytes
  -- of `c + p` — rejected by `bytes_lt_modulus`).
  fn count_to_bytes(v: G) -> [U8; 8] {
    let b = unconstrained_g_to_bytes(v);
    let (c0, c1) = u8_range_check(b[0], b[1]);
    let (c2, c3) = u8_range_check(b[2], b[3]);
    let (c4, c5) = u8_range_check(b[4], b[5]);
    let (c6, c7) = u8_range_check(b[6], b[7]);
    let r = [c0, c1, c2, c3, c4, c5, c6, c7];
    assert_eq!(limb_to_field(r), v);
    assert_eq!(bytes_lt_modulus(r), 1);
    r
  }

  -- 1 iff two wire limbs are equal. Folded compare: exact for canonical
  -- (< 2⁶⁴, hash-output) limbs over a 64-bit field.
  inline fn wire_limb_eq(a: U64, b: U64) -> G {
    eq_zero(limb_to_field(a) - limb_to_field(b))
  }
⟧

end IxVM

end
