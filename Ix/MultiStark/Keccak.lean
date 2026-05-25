module
public import Ix.Aiur.Meta
public import Ix.IxVM.Core
public import Ix.IxVM.ByteStream

/-!
# Keccak-256 in Aiur

The hash multi-stark uses (`p3_keccak`: `Keccak256Hash` + `KeccakF` permutation,
keccak-f[1600] sponge). This is the Ethereum/original Keccak variant
(`tiny_keccak::Keccak::v256`): pad `10*1` with first pad byte `0x01` and final
`0x80`, rate = 136 bytes (17 lanes), capacity 512, 256-bit output.

Representation:
* lane  = 64-bit word = `[U8; 8]`, little-endian bytes (byte 0 = least significant).
* state = `[Lane; 25]`, lane index `L(x,y) = x + 5*y`.

Bit ops use the `u8` gadgets (`u8_xor`/`u8_and`; NOT = `u8_xor(b, 0xFF)`).
Rotations go through `u8_bit_decomposition` (u8 → `[field; 8]`) and a generic
bit-list rotate, recomposing bytes with `u8_from_field_unsafe`.

**Scope:** single-block only — message length ≤ 135 bytes (one keccak-f call).
Multi-block absorption is future work.
-/

public section

namespace MultiStark

def keccak := ⟦
  -- A 64-bit Keccak lane: a pointer to 8 little-endian bytes. Storing lanes
  -- behind a pointer keeps the state (and every lane-passing function) one
  -- column wide instead of eight.
  type Lane = &[U8; 8]

  -- The keccak-f state: a pointer to the 5×5 = 25 lanes. Passed behind a
  -- pointer too, so state-threading functions stay one column wide.
  type State = &[Lane; 25]

  -- ==========================================================================
  -- Lane bit-logic (byte-wise u8 gadgets).
  -- ==========================================================================

  fn xor8(a: Lane, b: Lane) -> Lane {
    let x = load(a);
    let y = load(b);
    store([u8_xor(x[0], y[0]), u8_xor(x[1], y[1]), u8_xor(x[2], y[2]), u8_xor(x[3], y[3]),
           u8_xor(x[4], y[4]), u8_xor(x[5], y[5]), u8_xor(x[6], y[6]), u8_xor(x[7], y[7])])
  }

  fn and8(a: Lane, b: Lane) -> Lane {
    let x = load(a);
    let y = load(b);
    store([u8_and(x[0], y[0]), u8_and(x[1], y[1]), u8_and(x[2], y[2]), u8_and(x[3], y[3]),
           u8_and(x[4], y[4]), u8_and(x[5], y[5]), u8_and(x[6], y[6]), u8_and(x[7], y[7])])
  }

  -- Bitwise NOT via XOR with 0xFF (keeps the byte `u8`-typed).
  fn not8(a: Lane) -> Lane {
    let x = load(a);
    store([u8_xor(x[0], 255u8), u8_xor(x[1], 255u8), u8_xor(x[2], 255u8), u8_xor(x[3], 255u8),
           u8_xor(x[4], 255u8), u8_xor(x[5], 255u8), u8_xor(x[6], 255u8), u8_xor(x[7], 255u8)])
  }

  -- ==========================================================================
  -- Generic cyclic left-rotation of a lane by `n` bits (0 ≤ n < 64).
  -- Decompose to a 64-element bit list (LSB first), reindex, recompose.
  -- ==========================================================================

  -- Prepend the 8 bits of a byte decomposition (LSB first) onto `tail`.
  fn cons8(d: [G; 8], tail: List‹G›) -> List‹G› {
    store(ListNode.Cons(d[0], store(ListNode.Cons(d[1], store(ListNode.Cons(d[2],
    store(ListNode.Cons(d[3], store(ListNode.Cons(d[4], store(ListNode.Cons(d[5],
    store(ListNode.Cons(d[6], store(ListNode.Cons(d[7], tail))))))))))))))))
  }

  -- Lane → 64 bits, index z = 8*byte + bit, LSB first.
  fn lane_bits(l: Lane) -> List‹G› {
    let v = load(l);
    cons8(u8_bit_decomposition(v[0]),
    cons8(u8_bit_decomposition(v[1]),
    cons8(u8_bit_decomposition(v[2]),
    cons8(u8_bit_decomposition(v[3]),
    cons8(u8_bit_decomposition(v[4]),
    cons8(u8_bit_decomposition(v[5]),
    cons8(u8_bit_decomposition(v[6]),
    cons8(u8_bit_decomposition(v[7]), store(ListNode.Nil)))))))))
  }

  -- x mod 64 for x in [0, 127]: drop the 64-bit (bit 6).
  fn mod64(x: G) -> G {
    let bits = u8_bit_decomposition(u8_from_field_unsafe(x));
    x - 64 * bits[6]
  }

  -- Recompose a byte (as `u8`) from bits[off .. off+7] (LSB first). Indexed
  -- access is inlined as `list_drop` (not `list_lookup`): `list_drop` recurses
  -- on the same list pointer, so the consecutive drops here share the cached
  -- drop-chain (far better caching than `list_lookup`).
  fn byte_from_bits(bs: List‹G›, off: G) -> U8 {
    -- One `list_drop` to the byte's first bit; the remaining 7 bits are the
    -- successive tails (a deref each), so no further drops are needed.
    let &ListNode.Cons(b0, r0) = list_drop(bs, off);
    let &ListNode.Cons(b1, r1) = r0;
    let &ListNode.Cons(b2, r2) = r1;
    let &ListNode.Cons(b3, r3) = r2;
    let &ListNode.Cons(b4, r4) = r3;
    let &ListNode.Cons(b5, r5) = r4;
    let &ListNode.Cons(b6, r6) = r5;
    let &ListNode.Cons(b7, _) = r6;
    u8_from_field_unsafe(
      b0 + 2 * b1 + 4 * b2 + 8 * b3 + 16 * b4 + 32 * b5 + 64 * b6 + 128 * b7)
  }

  fn lane_from_bits(bs: List‹G›) -> Lane {
    store([byte_from_bits(bs, 0), byte_from_bits(bs, 8), byte_from_bits(bs, 16), byte_from_bits(bs, 24),
           byte_from_bits(bs, 32), byte_from_bits(bs, 40), byte_from_bits(bs, 48), byte_from_bits(bs, 56)])
  }

  -- Build the rotated bit list: output position p (0..63) takes source
  -- bit (p - n) mod 64 = mod64(p + 64 - n).
  fn build_rot(bs: List‹G›, n: G, p: G) -> List‹G› {
    match 64 - p {
      0 => store(ListNode.Nil),
      _ =>
        let src = mod64(p + 64 - n);
        let &ListNode.Cons(head, _) = list_drop(bs, src);
        store(ListNode.Cons(head, build_rot(bs, n, p + 1))),
    }
  }

  fn rotl(l: Lane, n: G) -> Lane {
    lane_from_bits(build_rot(lane_bits(l), n, 0))
  }

  -- ==========================================================================
  -- keccak-f[1600]: 24 rounds of θ ρ π χ ι.
  -- ==========================================================================

  fn keccak_round(sp: State, rc: Lane) -> State {
    let s = load(sp);
    -- θ: column parities and the D correction.
    let c0 = xor8(xor8(xor8(xor8(s[0], s[5]), s[10]), s[15]), s[20]);
    let c1 = xor8(xor8(xor8(xor8(s[1], s[6]), s[11]), s[16]), s[21]);
    let c2 = xor8(xor8(xor8(xor8(s[2], s[7]), s[12]), s[17]), s[22]);
    let c3 = xor8(xor8(xor8(xor8(s[3], s[8]), s[13]), s[18]), s[23]);
    let c4 = xor8(xor8(xor8(xor8(s[4], s[9]), s[14]), s[19]), s[24]);
    let d0 = xor8(c4, rotl(c1, 1));
    let d1 = xor8(c0, rotl(c2, 1));
    let d2 = xor8(c1, rotl(c3, 1));
    let d3 = xor8(c2, rotl(c4, 1));
    let d4 = xor8(c3, rotl(c0, 1));
    let a0 = xor8(s[0], d0);   let a1 = xor8(s[1], d1);   let a2 = xor8(s[2], d2);
    let a3 = xor8(s[3], d3);   let a4 = xor8(s[4], d4);
    let a5 = xor8(s[5], d0);   let a6 = xor8(s[6], d1);   let a7 = xor8(s[7], d2);
    let a8 = xor8(s[8], d3);   let a9 = xor8(s[9], d4);
    let a10 = xor8(s[10], d0); let a11 = xor8(s[11], d1); let a12 = xor8(s[12], d2);
    let a13 = xor8(s[13], d3); let a14 = xor8(s[14], d4);
    let a15 = xor8(s[15], d0); let a16 = xor8(s[16], d1); let a17 = xor8(s[17], d2);
    let a18 = xor8(s[18], d3); let a19 = xor8(s[19], d4);
    let a20 = xor8(s[20], d0); let a21 = xor8(s[21], d1); let a22 = xor8(s[22], d2);
    let a23 = xor8(s[23], d3); let a24 = xor8(s[24], d4);
    -- ρ + π: B[dest] = rotl(A'[src], offset).
    let b0  = a0;
    let b1  = rotl(a6, 44);
    let b2  = rotl(a12, 43);
    let b3  = rotl(a18, 21);
    let b4  = rotl(a24, 14);
    let b5  = rotl(a3, 28);
    let b6  = rotl(a9, 20);
    let b7  = rotl(a10, 3);
    let b8  = rotl(a16, 45);
    let b9  = rotl(a22, 61);
    let b10 = rotl(a1, 1);
    let b11 = rotl(a7, 6);
    let b12 = rotl(a13, 25);
    let b13 = rotl(a19, 8);
    let b14 = rotl(a20, 18);
    let b15 = rotl(a4, 27);
    let b16 = rotl(a5, 36);
    let b17 = rotl(a11, 10);
    let b18 = rotl(a17, 15);
    let b19 = rotl(a23, 56);
    let b20 = rotl(a2, 62);
    let b21 = rotl(a8, 55);
    let b22 = rotl(a14, 39);
    let b23 = rotl(a15, 41);
    let b24 = rotl(a21, 2);
    -- χ: A''[x][y] = B[x][y] ^ (¬B[x+1][y] & B[x+2][y]).
    let e0  = xor8(b0,  and8(not8(b1),  b2));
    let e1  = xor8(b1,  and8(not8(b2),  b3));
    let e2  = xor8(b2,  and8(not8(b3),  b4));
    let e3  = xor8(b3,  and8(not8(b4),  b0));
    let e4  = xor8(b4,  and8(not8(b0),  b1));
    let e5  = xor8(b5,  and8(not8(b6),  b7));
    let e6  = xor8(b6,  and8(not8(b7),  b8));
    let e7  = xor8(b7,  and8(not8(b8),  b9));
    let e8  = xor8(b8,  and8(not8(b9),  b5));
    let e9  = xor8(b9,  and8(not8(b5),  b6));
    let e10 = xor8(b10, and8(not8(b11), b12));
    let e11 = xor8(b11, and8(not8(b12), b13));
    let e12 = xor8(b12, and8(not8(b13), b14));
    let e13 = xor8(b13, and8(not8(b14), b10));
    let e14 = xor8(b14, and8(not8(b10), b11));
    let e15 = xor8(b15, and8(not8(b16), b17));
    let e16 = xor8(b16, and8(not8(b17), b18));
    let e17 = xor8(b17, and8(not8(b18), b19));
    let e18 = xor8(b18, and8(not8(b19), b15));
    let e19 = xor8(b19, and8(not8(b15), b16));
    let e20 = xor8(b20, and8(not8(b21), b22));
    let e21 = xor8(b21, and8(not8(b22), b23));
    let e22 = xor8(b22, and8(not8(b23), b24));
    let e23 = xor8(b23, and8(not8(b24), b20));
    let e24 = xor8(b24, and8(not8(b20), b21));
    -- ι: add round constant to lane (0,0).
    let f0 = xor8(e0, rc);
    store([f0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14,
           e15, e16, e17, e18, e19, e20, e21, e22, e23, e24])
  }

  -- Round constant for round `i` (little-endian byte lane). A match (not an
  -- array `get`, which needs a literal index) so it can be indexed at runtime.
  fn rc_lane(i: G) -> Lane {
    match i {
      0  => store([0x01u8, 0u8,    0u8, 0u8,    0u8, 0u8, 0u8, 0u8   ]),
      1  => store([0x82u8, 0x80u8, 0u8, 0u8,    0u8, 0u8, 0u8, 0u8   ]),
      2  => store([0x8au8, 0x80u8, 0u8, 0u8,    0u8, 0u8, 0u8, 0x80u8]),
      3  => store([0x00u8, 0x80u8, 0u8, 0x80u8, 0u8, 0u8, 0u8, 0x80u8]),
      4  => store([0x8bu8, 0x80u8, 0u8, 0u8,    0u8, 0u8, 0u8, 0u8   ]),
      5  => store([0x01u8, 0u8,    0u8, 0x80u8, 0u8, 0u8, 0u8, 0u8   ]),
      6  => store([0x81u8, 0x80u8, 0u8, 0x80u8, 0u8, 0u8, 0u8, 0x80u8]),
      7  => store([0x09u8, 0x80u8, 0u8, 0u8,    0u8, 0u8, 0u8, 0x80u8]),
      8  => store([0x8au8, 0u8,    0u8, 0u8,    0u8, 0u8, 0u8, 0u8   ]),
      9  => store([0x88u8, 0u8,    0u8, 0u8,    0u8, 0u8, 0u8, 0u8   ]),
      10 => store([0x09u8, 0x80u8, 0u8, 0x80u8, 0u8, 0u8, 0u8, 0u8   ]),
      11 => store([0x0au8, 0u8,    0u8, 0x80u8, 0u8, 0u8, 0u8, 0u8   ]),
      12 => store([0x8bu8, 0x80u8, 0u8, 0x80u8, 0u8, 0u8, 0u8, 0u8   ]),
      13 => store([0x8bu8, 0u8,    0u8, 0u8,    0u8, 0u8, 0u8, 0x80u8]),
      14 => store([0x89u8, 0x80u8, 0u8, 0u8,    0u8, 0u8, 0u8, 0x80u8]),
      15 => store([0x03u8, 0x80u8, 0u8, 0u8,    0u8, 0u8, 0u8, 0x80u8]),
      16 => store([0x02u8, 0x80u8, 0u8, 0u8,    0u8, 0u8, 0u8, 0x80u8]),
      17 => store([0x80u8, 0u8,    0u8, 0u8,    0u8, 0u8, 0u8, 0x80u8]),
      18 => store([0x0au8, 0x80u8, 0u8, 0u8,    0u8, 0u8, 0u8, 0u8   ]),
      19 => store([0x0au8, 0u8,    0u8, 0x80u8, 0u8, 0u8, 0u8, 0x80u8]),
      20 => store([0x81u8, 0x80u8, 0u8, 0x80u8, 0u8, 0u8, 0u8, 0x80u8]),
      21 => store([0x80u8, 0x80u8, 0u8, 0u8,    0u8, 0u8, 0u8, 0x80u8]),
      22 => store([0x01u8, 0u8,    0u8, 0x80u8, 0u8, 0u8, 0u8, 0u8   ]),
      _  => store([0x08u8, 0x80u8, 0u8, 0x80u8, 0u8, 0u8, 0u8, 0x80u8]),
    }
  }

  -- Apply the last `n` keccak-f rounds recursively (round index 24 - n), so
  -- each round is its own call frame rather than 24 inlined copies (`fold`),
  -- keeping the circuit narrow. `keccak_f_fold(s, 24)` is the full permutation.
  fn keccak_f_fold(s: State, n: G) -> State {
    match n {
      0 => s,
      _ => keccak_f_fold(keccak_round(s, rc_lane(24 - n)), n - 1),
    }
  }

  -- ==========================================================================
  -- Single-block sponge (keccak-256, message ≤ 135 bytes).
  -- ==========================================================================

  -- Pad bytes for positions i..135 once the message is exhausted. `first`=1 at
  -- position `len` (gets the 0x01 pad bit); position 135 gets the 0x80 bit
  -- (combining to 0x81 when len == 135).
  -- `first` is 1 on the first pad position (gets 0x01), 0 afterwards. The 0x80
  -- bit lands on position 135 (combining to 0x81 when first==1 there). Uses
  -- `eq_zero` (an op) instead of a match so it stays tail-position-compilable.
  fn build_pad(i: G, first: G) -> ByteStream {
    match 136 - i {
      0 => store(ListNode.Nil),
      _ =>
        store(ListNode.Cons(u8_from_field_unsafe(first + 128 * eq_zero(135 - i)),
                            build_pad(i + 1, 0))),
    }
  }

  -- Take one 136-byte rate block from `stream` starting at position `i`.
  -- Returns (block, rest, full): a length-136 byte list, the unconsumed stream,
  -- and full=1 if 136 message bytes were consumed (no padding yet), else 0 (the
  -- message ended in this block, so pad10*1 was applied). When the stream is
  -- already empty this yields an all-padding block with full=0 — the extra
  -- block keccak appends when the message length is a multiple of 136.
  fn read_block(stream: ByteStream, i: G) -> (ByteStream, ByteStream, G) {
    match 136 - i {
      0 => (store(ListNode.Nil), stream, 1),
      _ => match load(stream) {
        ListNode.Cons(b, rest) =>
          let (blk, r, f) = read_block(rest, i + 1);
          (store(ListNode.Cons(b, blk)), r, f),
        ListNode.Nil => (build_pad(i, 1), store(ListNode.Nil), 0),
      },
    }
  }

  fn rate_lane(rate: ByteStream, b: G) -> Lane {
    -- One `list_drop` to the lane's first byte; the next 7 are successive tails.
    let &ListNode.Cons(r0, t0) = list_drop(rate, b);
    let &ListNode.Cons(r1, t1) = t0;
    let &ListNode.Cons(r2, t2) = t1;
    let &ListNode.Cons(r3, t3) = t2;
    let &ListNode.Cons(r4, t4) = t3;
    let &ListNode.Cons(r5, t5) = t4;
    let &ListNode.Cons(r6, t6) = t5;
    let &ListNode.Cons(r7, _) = t6;
    store([r0, r1, r2, r3, r4, r5, r6, r7])
  }

  -- XOR one 136-byte rate block into the first 17 lanes, then permute.
  fn absorb_one(sp: State, rate: ByteStream) -> State {
    let state = load(sp);
    let s = store([
      xor8(state[0],  rate_lane(rate, 0)),   xor8(state[1],  rate_lane(rate, 8)),
      xor8(state[2],  rate_lane(rate, 16)),  xor8(state[3],  rate_lane(rate, 24)),
      xor8(state[4],  rate_lane(rate, 32)),  xor8(state[5],  rate_lane(rate, 40)),
      xor8(state[6],  rate_lane(rate, 48)),  xor8(state[7],  rate_lane(rate, 56)),
      xor8(state[8],  rate_lane(rate, 64)),  xor8(state[9],  rate_lane(rate, 72)),
      xor8(state[10], rate_lane(rate, 80)),  xor8(state[11], rate_lane(rate, 88)),
      xor8(state[12], rate_lane(rate, 96)),  xor8(state[13], rate_lane(rate, 104)),
      xor8(state[14], rate_lane(rate, 112)), xor8(state[15], rate_lane(rate, 120)),
      xor8(state[16], rate_lane(rate, 128)),
      state[17], state[18], state[19], state[20], state[21], state[22], state[23], state[24]
    ]);
    keccak_f_fold(s, 24)
  }

  -- Absorb every rate block of the (padded) message into the state.
  fn absorb_blocks(stream: ByteStream, state: State) -> State {
    let (block, rest, full) = read_block(stream, 0);
    let st2 = absorb_one(state, block);
    match full {
      0 => st2,
      _ => absorb_blocks(rest, st2),
    }
  }

  -- keccak-256: absorb the byte stream into the zero state, then squeeze the
  -- first 32 bytes (lanes 0..3). Lanes are `load`ed back to inline bytes so the
  -- digest is a plain `[[U8; 8]; 4]`.
  fn keccak256(bytes: ByteStream) -> [[U8; 8]; 4] {
    let z = store([0u8; 8]);
    let init = store([z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z]);
    let sp = absorb_blocks(bytes, init);
    let s = load(sp);
    [load(s[0]), load(s[1]), load(s[2]), load(s[3])]
  }

  -- ==========================================================================
  -- Test entrypoint: hash the IO-channel bytes (key [0]) and return 32 bytes.
  -- ==========================================================================

  pub fn keccak256_test() -> [[U8; 8]; 4] {
    let (idx, len) = io_get_info([0]);
    let bytes = #read_byte_stream(idx, len);
    keccak256(bytes)
  }
⟧

/-- Standalone keccak-256 toplevel: `core` + `byteStream` + the implementation. -/
def keccakToplevel : Except Aiur.Global Aiur.Source.Toplevel := do
  let t ← IxVM.core.merge IxVM.byteStream
  t.merge keccak

end MultiStark

end
