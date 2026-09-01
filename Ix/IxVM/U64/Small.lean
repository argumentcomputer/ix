module
public import Ix.Aiur.Meta

/-!
# U64 field boundary, SMALL-FIELD form

The same interface as `U64/Goldilocks.lean` — `flatten_u64` and
`idx_to_u64`, the bytes ↔ field boundary of the IxVM's byte-level `U64` —
for an outer field too small to hold 7 bytes injectively (e.g. KoalaBear,
p ≈ 2³¹, under the Hypercube backend).

A value packs 3 bytes (`< 2²⁴`), and the five high bytes must be zero:
that is a CHECKED EMBEDDING, not a truncation. A u64 at or beyond 2²⁴
reaching this boundary fails the assert rather than wrapping — the same
"the field cannot represent this program" discipline the compiler applies
to constants. The bound is 3 bytes rather than 4 so that the packing never
wraps in any field of 25 bits or more (a 4-byte packing would need p > 2³²,
which KoalaBear does not satisfy).

Soundness is the same argument as the Goldilocks form: `flatten_u64` on
range-checked bytes with the high bytes pinned to zero is injective (the
sum is `< 2²⁴ < p`, so it cannot wrap); `idx_to_u64` range-checks the
hinted bytes, and the recomposition assert pins them to the index.
-/

public section

namespace IxVM

def u64Small := ⟦
  -- Pack little-endian bytes into a field element: b0 + 256·b1 + 65536·b2.
  -- The five high bytes must be zero (checked embedding, < 2²⁴).
  --
  -- INJECTIVITY IS CONDITIONAL ON THE CALLER, exactly as in the Goldilocks
  -- form: `[U8; 8]` is nominal typing, so only range-checked bytes make
  -- the decomposition unique. With every byte in [0, 256) the sum is below
  -- 2²⁴ < p and cannot wrap.
  fn flatten_u64(x: [U8; 8]) -> G {
    let [b0, b1, b2, b3, b4, b5, b6, b7] = x;
    assert_eq!(to_field(b3) + to_field(b4) + to_field(b5) + to_field(b6) + to_field(b7), 0,
      "u64 -> field: value exceeds 2^24 (small-field boundary)");
    to_field(b0) + 0x100 * to_field(b1) + 0x10000 * to_field(b2)
  }

  -- Decompose a field element (an index or count below 2²⁴) into its
  -- little-endian bytes. The eight-byte hint gives the canonical value's
  -- bytes; every byte is range-checked, and `flatten_u64` both pins the
  -- high bytes to zero and recomposes to `idx`, so the byte string is the
  -- unique one for the index. Indices at or beyond 2²⁴ fail the assert
  -- rather than truncating silently — a liveness bound only.
  fn idx_to_u64(idx: G) -> U64 {
    let [h0, h1, h2, h3, h4, h5, h6, h7] = unconstrained_g_to_bytes(idx);
    let (b0, b1) = u8_range_check(h0, h1);
    let (b2, b3) = u8_range_check(h2, h3);
    let (b4, b5) = u8_range_check(h4, h5);
    let (b6, b7) = u8_range_check(h6, h7);
    let bytes = [b0, b1, b2, b3, b4, b5, b6, b7];
    assert_eq!(flatten_u64(bytes), idx,
      "index bytes do not recompose to the index");
    bytes
  }
⟧

end IxVM

end
