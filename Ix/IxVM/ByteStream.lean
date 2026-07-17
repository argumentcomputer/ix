module
public import Ix.Aiur.Meta

public section

namespace IxVM

def byteStream := ⟦
  type ByteStream = List‹U8›

  type U64 = [U8; 8]

  fn read_byte_stream(channel: G, idx: G, len: G) -> ByteStream {
    match len {
      0 => store(ListNode.Nil),
      _ =>
        let tail = read_byte_stream(channel, idx + 1, len - 1);
        let [byte] = io_read(channel, idx, 1);
        store(ListNode.Cons(u8_from_field_unsafe(byte), tail)),
    }
  }

  -- Count bytes needed to represent a u64.
  -- Important: this implementation differs from the Lean and Rust ones, returning
  -- 1 for [0; 8] instead of 0.
  fn u64_byte_count(x: U64) -> U8 {
    match x {
      [_, 0, 0, 0, 0, 0, 0, 0] => 1u8,
      [_, _, 0, 0, 0, 0, 0, 0] => 2u8,
      [_, _, _, 0, 0, 0, 0, 0] => 3u8,
      [_, _, _, _, 0, 0, 0, 0] => 4u8,
      [_, _, _, _, _, 0, 0, 0] => 5u8,
      [_, _, _, _, _, _, 0, 0] => 6u8,
      [_, _, _, _, _, _, _, 0] => 7u8,
      _ => 8u8,
    }
  }

  fn u64_is_zero(x: U64) -> G {
    match x {
      [0, 0, 0, 0, 0, 0, 0, 0] => 1,
      _ => 0,
    }
  }

  fn u32_add(a: [U8; 4], b: [U8; 4]) -> [U8; 4] {
    let [a0, a1, a2, a3] = a;
    let [b0, b1, b2, b3] = b;

    -- Byte 0, no initial carry
    let (sum0, carry1) = u8_add(a0, b0);

    -- Byte 1
    let (sum1, overflow1) = u8_add(a1, b1);
    let (sum1_with_carry, carry1a) = u8_add(sum1, carry1);
    -- `overflow1` and `carry1a` cannot both be 1: a carry out of `a1 + b1`
    -- forces `sum1 <= 254`, so `sum1 + carry1` cannot carry. Combining them is
    -- a cheap field add (no lookup); the sum is 0/1, reinterpreted as `u8`.
    let carry2 = u8_from_field_unsafe(to_field(overflow1) + to_field(carry1a));

    -- Byte 2
    let (sum2, overflow2) = u8_add(a2, b2);
    let (sum2_with_carry, carry2a) = u8_add(sum2, carry2);
    let carry3 = u8_from_field_unsafe(to_field(overflow2) + to_field(carry2a));

    -- Byte 3
    let (sum3, _x) = u8_add(a3, b3);
    let (sum3_with_carry, _x) = u8_add(sum3, carry3);

    [sum0, sum1_with_carry, sum2_with_carry, sum3_with_carry]
  }

  -- Little-endian sum of three 32-bit words in one carry-propagation pass:
  -- each byte column accumulates with chained `u8_add` (running partial stays
  -- < 256) and the 0/1 carry bits fold into the next column with a free field
  -- add. 11 `u8_add`s vs 14 for two chained `u32_add`s. Column carry is
  -- floor(column_sum / 256) <= 2 (< 256), safe to feed back to `u8_add`.
  fn u32_add3(a: [U8; 4], b: [U8; 4], c: [U8; 4]) -> [U8; 4] {
    let [a0, a1, a2, a3] = a;
    let [b0, b1, b2, b3] = b;
    let [c0, c1, c2, c3] = c;

    -- Byte 0, no initial carry
    let (sum0, overflow0a) = u8_add(a0, b0);
    let (sum0, overflow0b) = u8_add(sum0, c0);
    let carry1 = u8_from_field_unsafe(to_field(overflow0a) + to_field(overflow0b));

    -- Byte 1
    let (sum1, overflow1a) = u8_add(a1, b1);
    let (sum1, overflow1b) = u8_add(sum1, c1);
    let (sum1_with_carry, carry1a) = u8_add(sum1, carry1);
    let carry2 = u8_from_field_unsafe(
      to_field(overflow1a) + to_field(overflow1b) + to_field(carry1a));

    -- Byte 2
    let (sum2, overflow2a) = u8_add(a2, b2);
    let (sum2, overflow2b) = u8_add(sum2, c2);
    let (sum2_with_carry, carry2a) = u8_add(sum2, carry2);
    let carry3 = u8_from_field_unsafe(
      to_field(overflow2a) + to_field(overflow2b) + to_field(carry2a));

    -- Byte 3
    let (sum3, _x) = u8_add(a3, b3);
    let (sum3, _x) = u8_add(sum3, c3);
    let (sum3_with_carry, _x) = u8_add(sum3, carry3);

    [sum0, sum1_with_carry, sum2_with_carry, sum3_with_carry]
  }

  fn u32_xor(a: [U8; 4], b: [U8; 4]) -> [U8; 4] {
    let c0 = u8_xor(a[0], b[0]);
    let c1 = u8_xor(a[1], b[1]);
    let c2 = u8_xor(a[2], b[2]);
    let c3 = u8_xor(a[3], b[3]);
    [c0, c1, c2, c3]
  }

  fn u32_and(a: [U8; 4], b: [U8; 4]) -> [U8; 4] {
    let c0 = u8_and(a[0], b[0]);
    let c1 = u8_and(a[1], b[1]);
    let c2 = u8_and(a[2], b[2]);
    let c3 = u8_and(a[3], b[3]);
    [c0, c1, c2, c3]
  }

  -- Right-rotations of a little-endian word. rotr16 / rotr8 are pure byte
  -- moves (free); rotr12 / rotr7 are a byte move composed with the chained
  -- 4-/7-bit gadget (two lookups + two free field adds each).
  fn u32_rotr16(w: [U8; 4]) -> [U8; 4] {
    let [w0, w1, w2, w3] = w;
    [w2, w3, w0, w1]
  }

  fn u32_rotr8(w: [U8; 4]) -> [U8; 4] {
    let [w0, w1, w2, w3] = w;
    [w1, w2, w3, w0]
  }

  fn u32_rotr12(w: [U8; 4]) -> [U8; 4] {
    let [w0, w1, w2, w3] = w;
    let (e0, e1, e2) = u8_chain_rotr4(w1, w2);
    let (f0, f1, f2) = u8_chain_rotr4(w3, w0);
    [e0, u8_from_field_unsafe(to_field(e1) + to_field(f2)), f0,
     u8_from_field_unsafe(to_field(f1) + to_field(e2))]
  }

  fn u32_rotr7(w: [U8; 4]) -> [U8; 4] {
    let [w0, w1, w2, w3] = w;
    let (g0, g1, g2) = u8_chain_rotr7(w0, w1);
    let (h0, h1, h2) = u8_chain_rotr7(w2, w3);
    [g0, u8_from_field_unsafe(to_field(g1) + to_field(h2)), h0,
     u8_from_field_unsafe(to_field(h1) + to_field(g2))]
  }

  -- Byte-by-byte `u64` equality
  fn u64_eq(a: U64, b: U64) -> G {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    match [to_field(a0) - to_field(b0), to_field(a1) - to_field(b1),
           to_field(a2) - to_field(b2), to_field(a3) - to_field(b3),
           to_field(a4) - to_field(b4), to_field(a5) - to_field(b5),
           to_field(a6) - to_field(b6), to_field(a7) - to_field(b7)] {
      [0, 0, 0, 0, 0, 0, 0, 0] => 1,
      _ => 0,
    }
  }

  -- `u64` addition with carry propagation (little-endian bytes).
  -- Returns the sum together with the final carry-out.
  fn u64_add(a: U64, b: U64) -> (U64, U8) {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    let (s0, c1) = u8_add(a0, b0);
    let (t1, o1) = u8_add(a1, b1);
    let (s1, c1a) = u8_add(t1, c1);
    let c2 = u8_from_field_unsafe(to_field(o1) + to_field(c1a));
    let (t2, o2) = u8_add(a2, b2);
    let (s2, c2a) = u8_add(t2, c2);
    let c3 = u8_from_field_unsafe(to_field(o2) + to_field(c2a));
    let (t3, o3) = u8_add(a3, b3);
    let (s3, c3a) = u8_add(t3, c3);
    let c4 = u8_from_field_unsafe(to_field(o3) + to_field(c3a));
    let (t4, o4) = u8_add(a4, b4);
    let (s4, c4a) = u8_add(t4, c4);
    let c5 = u8_from_field_unsafe(to_field(o4) + to_field(c4a));
    let (t5, o5) = u8_add(a5, b5);
    let (s5, c5a) = u8_add(t5, c5);
    let c6 = u8_from_field_unsafe(to_field(o5) + to_field(c5a));
    let (t6, o6) = u8_add(a6, b6);
    let (s6, c6a) = u8_add(t6, c6);
    let c7 = u8_from_field_unsafe(to_field(o6) + to_field(c6a));
    let (t7, o7) = u8_add(a7, b7);
    let (s7, c7a) = u8_add(t7, c7);
    let final_carry = u8_from_field_unsafe(to_field(o7) + to_field(c7a));
    ([s0, s1, s2, s3, s4, s5, s6, s7], final_carry)
  }

  -- `u64` subtraction via repeated decrement (correct for small b)
  fn u64_sub(a: U64, b: U64) -> U64 {
    match u64_is_zero(b) {
      1 => a,
      0 => u64_sub(relaxed_u64_pred(a), relaxed_u64_pred(b)),
    }
  }

  fn g_or(a: G, b: G) -> G {
    match (a, b) {
      (0, 0) => 0,
      _ => 1,
    }
  }

  -- Computes the successor of an `u64` assumed to be properly represented in
  -- little-endian bytes. If that's not the case, this implementation has UB.
  fn relaxed_u64_succ(bytes: U64) -> U64 {
    let [b0, b1, b2, b3, b4, b5, b6, b7] = bytes;
    -- Incrementing a byte known to be `< 255` cannot overflow, so add as a
    -- cheap `G` and reinterpret (no `u8_add` lookup).
    match b0 {
      255 => match b1 {
        255 => match b2 {
          255 => match b3 {
            255 => match b4 {
              255 => match b5 {
                255 => match b6 {
                  255 => match b7 {
                    255 => [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
                    _ => [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, u8_from_field_unsafe(to_field(b7) + 1)],
                  },
                  _ => [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, u8_from_field_unsafe(to_field(b6) + 1), b7],
                },
                _ => [0u8, 0u8, 0u8, 0u8, 0u8, u8_from_field_unsafe(to_field(b5) + 1), b6, b7],
              },
              _ => [0u8, 0u8, 0u8, 0u8, u8_from_field_unsafe(to_field(b4) + 1), b5, b6, b7],
            },
            _ => [0u8, 0u8, 0u8, u8_from_field_unsafe(to_field(b3) + 1), b4, b5, b6, b7],
          },
          _ => [0u8, 0u8, u8_from_field_unsafe(to_field(b2) + 1), b3, b4, b5, b6, b7],
        },
        _ => [0u8, u8_from_field_unsafe(to_field(b1) + 1), b2, b3, b4, b5, b6, b7],
      },
      _ => [u8_from_field_unsafe(to_field(b0) + 1), b1, b2, b3, b4, b5, b6, b7],
    }
  }

  fn relaxed_u64_be_add_2_bytes(u64: U64, bs: [U8; 2]) -> U64 {
    -- Byte 0, no initial carry
    let (sum0, carry1) = u8_add(u64[7], bs[1]);

    -- Byte 1
    let (sum1, overflow1) = u8_add(u64[6], bs[0]);
    let (sum1_with_carry, carry1a) = u8_add(sum1, carry1);
    let carry2 = u8_from_field_unsafe(to_field(overflow1) + to_field(carry1a));

    -- Other bytes
    let (sum2, carry3) = u8_add(u64[5], carry2);
    let (sum3, carry4) = u8_add(u64[4], carry3);
    let (sum4, carry5) = u8_add(u64[3], carry4);
    let (sum5, carry6) = u8_add(u64[2], carry5);
    let (sum6, carry7) = u8_add(u64[1], carry6);
    let (sum7, _carry8) = u8_add(u64[0], carry7);

    [sum7, sum6, sum5, sum4, sum3, sum2, sum1, sum0]
  }

  fn u32_be_add(a: [U8; 4], b: [U8; 4]) -> [U8; 4] {
    -- Byte 0, no initial carry
    let (sum0, carry1) = u8_add(a[3], b[3]);

    -- Byte 1
    let (sum1, overflow1) = u8_add(a[2], b[2]);
    let (sum1_with_carry, carry1a) = u8_add(sum1, carry1);
    let carry2 = u8_from_field_unsafe(to_field(overflow1) + to_field(carry1a));

    -- Byte 2
    let (sum2, overflow2) = u8_add(a[1], b[1]);
    let (sum2_with_carry, carry2a) = u8_add(sum2, carry2);
    let carry3 = u8_from_field_unsafe(to_field(overflow2) + to_field(carry2a));

    -- Byte 3
    let (sum3, _x) = u8_add(a[0], b[0]);
    let (sum3_with_carry, _x) = u8_add(sum3, carry3);

    [sum3_with_carry, sum2_with_carry, sum1_with_carry, sum0]
  }

  -- Computes the predecessor of an `u64` assumed to be properly represented in
  -- little-endian bytes. If that's not the case, this implementation has UB.
  fn relaxed_u64_pred(bytes: U64) -> U64 {
    let [b0, b1, b2, b3, b4, b5, b6, b7] = bytes;
    -- Decrementing a byte known to be `> 0` cannot underflow, so subtract as a
    -- cheap `G` and reinterpret (no `u8_sub` lookup).
    match b0 {
      0 => match b1 {
        0 => match b2 {
          0 => match b3 {
            0 => match b4 {
              0 => match b5 {
                0 => match b6 {
                  0 => match b7 {
                    0 => [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
                    _ => [255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, u8_from_field_unsafe(to_field(b7) - 1)],
                  },
                  _ => [255u8, 255u8, 255u8, 255u8, 255u8, 255u8, u8_from_field_unsafe(to_field(b6) - 1), b7],
                },
                _ => [255u8, 255u8, 255u8, 255u8, 255u8, u8_from_field_unsafe(to_field(b5) - 1), b6, b7],
              },
              _ => [255u8, 255u8, 255u8, 255u8, u8_from_field_unsafe(to_field(b4) - 1), b5, b6, b7],
            },
            _ => [255u8, 255u8, 255u8, u8_from_field_unsafe(to_field(b3) - 1), b4, b5, b6, b7],
          },
          _ => [255u8, 255u8, u8_from_field_unsafe(to_field(b2) - 1), b3, b4, b5, b6, b7],
        },
        _ => [255u8, u8_from_field_unsafe(to_field(b1) - 1), b2, b3, b4, b5, b6, b7],
      },
      _ => [u8_from_field_unsafe(to_field(b0) - 1), b1, b2, b3, b4, b5, b6, b7],
    }
  }

  -- Flatten a [U8; 8] (U64 little-endian bytes) into a single G via
  -- b0 + 256 * b1 + ... + 256^6 * b6. The most significant byte (b7) must be zero;
  -- this is enforced by assert_eq!, limiting the range to 7 bytes (< 2^56).
  fn flatten_u64(x: [U8; 8]) -> G {
    let [b0, b1, b2, b3, b4, b5, b6, b7] = x;
    assert_eq!(to_field(b7), 0);
    to_field(b0) + 0x100 * to_field(b1) + 0x10000 * to_field(b2)
      + 0x1000000 * to_field(b3) + 0x100000000 * to_field(b4)
      + 0x10000000000 * to_field(b5) + 0x1000000000000 * to_field(b6)
  }
⟧

end IxVM

end
