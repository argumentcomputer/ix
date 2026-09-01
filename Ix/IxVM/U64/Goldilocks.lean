module
public import Ix.Aiur.Meta

/-!
# U64 field boundary, GOLDILOCKS form

The IxVM's `U64` is `[U8; 8]` and all of its arithmetic (`u64_add`,
`u64_mul`, borrows, bitwise ops, comparisons) is byte-level — carry chains
over the u8 gadgets whose intermediate sums stay below 2²⁰ — so it runs
unchanged over any field of 31 bits or more. The ONE place the outer
field's width shows is the boundary between bytes and field elements:

* `flatten_u64 : [U8; 8] → G` — pack bytes into a field element;
* `idx_to_u64 : G → U64` — its inverse, from a hinted decomposition.

Those two functions are the U64 interface. This module is the Goldilocks
implementation: a value packs 7 bytes (`< 2⁵⁶ < p`), the widest range a
64-bit field can hold injectively. `U64/Small.lean` provides the same
interface for smaller fields (3 bytes). Exactly one merges into a toplevel
(same names by design); the IxVM kernel and the recursive verifier's
deserializer both consume the interface.
-/

public section

namespace IxVM

def u64Goldilocks := ⟦
  -- Flatten a [U8; 8] (U64 little-endian bytes) into a single G via
  -- b0 + 256 * b1 + ... + 256^6 * b6. The most significant byte (b7) must be zero;
  -- this is enforced by assert_eq!, limiting the range to 7 bytes (< 2^56).
  --
  -- INJECTIVITY IS CONDITIONAL ON THE CALLER. `[U8; 8]` is nominal typing,
  -- not a constraint — `u8_from_field_unsafe` mints a `U8` holding any
  -- field element — so this function alone does NOT pin a unique input
  -- for a given output. With unchecked bytes the sum is satisfiable many
  -- ways (`b1 = k`, `b0 = x - 256k`). Only when every byte is
  -- range-checked does `b7 = 0` bound the value by 2^56 - 1, which is
  -- below Goldilocks `p`, so the sum cannot wrap and the decomposition is
  -- unique.
  --
  -- Callers relying on that uniqueness must therefore supply
  -- range-checked bytes, and must not lose the `b7 = 0` assert: widening
  -- this to a full u64 would silently break them, since 8-byte strings
  -- are not injective into the field (a value and value + p collide).
  -- `Ingress.idx_to_u64` is one such caller — it pins a projection index
  -- whose bytes are hashed into a member's content address.
  fn flatten_u64(x: [U8; 8]) -> G {
    let [b0, b1, b2, b3, b4, b5, b6, b7] = x;
    assert_eq!(to_field(b7), 0,
      "u64 -> field: value exceeds 2^56 (top byte must be zero)");
    to_field(b0) + 0x100 * to_field(b1) + 0x10000 * to_field(b2)
      + 0x1000000 * to_field(b3) + 0x100000000 * to_field(b4)
      + 0x10000000000 * to_field(b5) + 0x1000000000000 * to_field(b6)
  }

  -- Pack a member/ctor index into the u64 projection field as a
  -- little-endian [U8; 8].
  --
  -- The bytes come from the `unconstrained_g_to_bytes` hint and are then
  -- CONSTRAINED, because field -> bytes is not free: `flatten_u64` goes
  -- bytes -> field for nothing, but the reverse needs the bytes supplied
  -- as advice and pinned. Three obligations, all discharged here:
  --
  --   * every byte is range-checked into [0, 256) (`u8_range_check`
  --     takes a pair per lookup row, so eight bytes cost four);
  --   * the bytes must RECOMPOSE to `idx`;
  --   * the recomposition must be CANONICAL. This one is load-bearing:
  --     Goldilocks is 2^64 - 2^32 + 1, so an arbitrary eight-byte string
  --     is not injective into the field — values at or above `p` wrap,
  --     and a prover could hand over a second string recomposing to the
  --     same element.
  --
  -- Uniqueness is the soundness property, since the synthesized
  -- projection address is blake3 over these serialized bytes: a prover
  -- free to pick a different string for one index would get a second
  -- address for a member, or collide two members onto one address. The
  -- earlier `u8_from_field_unsafe` version truncated and did exactly
  -- that for members 0 and 256.
  --
  -- Indices at or beyond 2^56 fail the assert rather than truncating
  -- silently — a liveness bound only, and far past any real block or
  -- constructor count.
  fn idx_to_u64(idx: G) -> U64 {
    let [h0, h1, h2, h3, h4, h5, h6, h7] = unconstrained_g_to_bytes(idx);
    let (b0, b1) = u8_range_check(h0, h1);
    let (b2, b3) = u8_range_check(h2, h3);
    let (b4, b5) = u8_range_check(h4, h5);
    let (b6, b7) = u8_range_check(h6, h7);
    let bytes = [b0, b1, b2, b3, b4, b5, b6, b7];
    -- `flatten_u64` contributes the top-byte-is-zero assert and the sum.
    -- It does NOT range-check its input and so is not injective on its
    -- own; uniqueness here holds only because the range checks above
    -- bound every byte. Both halves are load-bearing — dropping either
    -- lets a prover pick a second byte string for the same index.
    assert_eq!(flatten_u64(bytes), idx,
      "projection index bytes do not recompose to the index");
    bytes
  }
⟧

end IxVM

end
