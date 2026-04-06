module
public import Ix.Aiur.Meta

public section

namespace IxVM

def byteStream := ⟦
  enum ByteStream {
    Cons(G, &ByteStream),
    Nil
  }

  type U64 = [G; 8]

  fn byte_stream_concat(a: ByteStream, b: ByteStream) -> ByteStream {
    match a {
      ByteStream.Nil => b,
      ByteStream.Cons(byte, &rest) =>
        ByteStream.Cons(byte, store(byte_stream_concat(rest, b))),
    }
  }

  fn byte_stream_length(bytes: ByteStream) -> U64 {
    match bytes {
      ByteStream.Nil => [0; 8],
      ByteStream.Cons(_, &rest) => relaxed_u64_succ(byte_stream_length(rest)),
    }
  }

  fn read_byte_stream(idx: G, len: G) -> ByteStream {
    match len {
      0 => ByteStream.Nil,
      _ =>
        let tail = read_byte_stream(idx + 1, len - 1);
        let [byte] = io_read(idx, 1);
        ByteStream.Cons(byte, store(tail)),
    }
  }

  -- TODO remove this function
  fn byte_stream_is_empty(input: ByteStream) -> G {
    match input {
      ByteStream.Cons(_, _) => 0,
      ByteStream.Nil => 1,
    }
  }

  -- Count bytes needed to represent a u64.
  -- Important: this implementation differs from the Lean and Rust ones, returning
  -- 1 for [0; 8] instead of 0.
  fn u64_byte_count(x: U64) -> G {
    match x {
      [_, 0, 0, 0, 0, 0, 0, 0] => 1,
      [_, _, 0, 0, 0, 0, 0, 0] => 2,
      [_, _, _, 0, 0, 0, 0, 0] => 3,
      [_, _, _, _, 0, 0, 0, 0] => 4,
      [_, _, _, _, _, 0, 0, 0] => 5,
      [_, _, _, _, _, _, 0, 0] => 6,
      [_, _, _, _, _, _, _, 0] => 7,
      _ => 8,
    }
  }

  fn u64_is_zero(x: U64) -> G {
    match x {
      [0, 0, 0, 0, 0, 0, 0, 0] => 1,
      _ => 0,
    }
  }

  -- Reconstructs a byte from its bits in little-endian.
  fn u8_recompose(bits: U64) -> G {
    let [b0, b1, b2, b3, b4, b5, b6, b7] = bits;
    b0 + 2 * b1 + 4 * b2 + 8 * b3 + 16 * b4 + 32 * b5 + 64 * b6 + 128 * b7
  }

  fn u32_add(a: [G; 4], b: [G; 4]) -> [G; 4] {
    let [a0, a1, a2, a3] = a;
    let [b0, b1, b2, b3] = b;

    -- Byte 0, no initial carry
    let (sum0, carry1) = u8_add(a0, b0);

    -- Byte 1
    let (sum1, overflow1) = u8_add(a1, b1);
    let (sum1_with_carry, carry1a) = u8_add(sum1, carry1);
    let carry2 = u8_xor(overflow1, carry1a);

    -- Byte 2
    let (sum2, overflow2) = u8_add(a2, b2);
    let (sum2_with_carry, carry2a) = u8_add(sum2, carry2);
    let carry3 = u8_xor(overflow2, carry2a);

    -- Byte 3
    let (sum3, _x) = u8_add(a3, b3);
    let (sum3_with_carry, _x) = u8_add(sum3, carry3);

    [sum0, sum1_with_carry, sum2_with_carry, sum3_with_carry]
  }

  fn u32_xor(a: [G; 4], b: [G; 4]) -> [G; 4] {
    let c0 = u8_xor(a[0], b[0]);
    let c1 = u8_xor(a[1], b[1]);
    let c2 = u8_xor(a[2], b[2]);
    let c3 = u8_xor(a[3], b[3]);
    [c0, c1, c2, c3]
  }

  fn u32_and(a: [G; 4], b: [G; 4]) -> [G; 4] {
    let c0 = u8_and(a[0], b[0]);
    let c1 = u8_and(a[1], b[1]);
    let c2 = u8_and(a[2], b[2]);
    let c3 = u8_and(a[3], b[3]);
    [c0, c1, c2, c3]
  }

  -- Byte-by-byte `u64` equality
  fn u64_eq(a: U64, b: U64) -> G {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    match [a0 - b0, a1 - b1, a2 - b2, a3 - b3, a4 - b4, a5 - b5, a6 - b6, a7 - b7] {
      [0, 0, 0, 0, 0, 0, 0, 0] => 1,
      _ => 0,
    }
  }

  -- `u64` addition with carry propagation (little-endian bytes)
  fn u64_add(a: U64, b: U64) -> U64 {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    let (s0, c1) = u8_add(a0, b0);
    let (t1, o1) = u8_add(a1, b1);
    let (s1, c1a) = u8_add(t1, c1);
    let c2 = u8_xor(o1, c1a);
    let (t2, o2) = u8_add(a2, b2);
    let (s2, c2a) = u8_add(t2, c2);
    let c3 = u8_xor(o2, c2a);
    let (t3, o3) = u8_add(a3, b3);
    let (s3, c3a) = u8_add(t3, c3);
    let c4 = u8_xor(o3, c3a);
    let (t4, o4) = u8_add(a4, b4);
    let (s4, c4a) = u8_add(t4, c4);
    let c5 = u8_xor(o4, c4a);
    let (t5, o5) = u8_add(a5, b5);
    let (s5, c5a) = u8_add(t5, c5);
    let c6 = u8_xor(o5, c5a);
    let (t6, o6) = u8_add(a6, b6);
    let (s6, c6a) = u8_add(t6, c6);
    let c7 = u8_xor(o6, c6a);
    let (t7, _) = u8_add(a7, b7);
    let (s7, _) = u8_add(t7, c7);
    [s0, s1, s2, s3, s4, s5, s6, s7]
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
    match b0 {
      255 => match b1 {
        255 => match b2 {
          255 => match b3 {
            255 => match b4 {
              255 => match b5 {
                255 => match b6 {
                  255 => match b7 {
                    255 => [0, 0, 0, 0, 0, 0, 0, 0],
                    _ => [0, 0, 0, 0, 0, 0, 0, b7 + 1],
                  },
                  _ => [0, 0, 0, 0, 0, 0, b6 + 1, b7],
                },
                _ => [0, 0, 0, 0, 0, b5 + 1, b6, b7],
              },
              _ => [0, 0, 0, 0, b4 + 1, b5, b6, b7],
            },
            _ => [0, 0, 0, b3 + 1, b4, b5, b6, b7],
          },
          _ => [0, 0, b2 + 1, b3, b4, b5, b6, b7],
        },
        _ => [0, b1 + 1, b2, b3, b4, b5, b6, b7],
      },
      _ => [b0 + 1, b1, b2, b3, b4, b5, b6, b7],
    }
  }

  fn relaxed_u64_be_add_2_bytes(u64: U64, bs: [G; 2]) -> U64 {
    -- Byte 0, no initial carry
    let (sum0, carry1) = u8_add(u64[7], bs[1]);

    -- Byte 1
    let (sum1, overflow1) = u8_add(u64[6], bs[0]);
    let (sum1_with_carry, carry1a) = u8_add(sum1, carry1);
    let carry2 = u8_xor(overflow1, carry1a);

    -- Other bytes
    let (sum2, carry3) = u8_add(u64[5], carry2);
    let (sum3, carry4) = u8_add(u64[4], carry3);
    let (sum4, carry5) = u8_add(u64[3], carry4);
    let (sum5, carry6) = u8_add(u64[2], carry5);
    let (sum6, carry7) = u8_add(u64[1], carry6);
    let (sum7, _carry8) = u8_add(u64[0], carry7);

    [sum7, sum6, sum5, sum4, sum3, sum2, sum1, sum0]
  }

  fn u32_be_add(a: [G; 4], b: [G; 4]) -> [G; 4] {
    -- Byte 0, no initial carry
    let (sum0, carry1) = u8_add(a[3], b[3]);

    -- Byte 1
    let (sum1, overflow1) = u8_add(a[2], b[2]);
    let (sum1_with_carry, carry1a) = u8_add(sum1, carry1);
    let carry2 = u8_xor(overflow1, carry1a);

    -- Byte 2
    let (sum2, overflow2) = u8_add(a[1], b[1]);
    let (sum2_with_carry, carry2a) = u8_add(sum2, carry2);
    let carry3 = u8_xor(overflow2, carry2a);

    -- Byte 3
    let (sum3, _x) = u8_add(a[0], b[0]);
    let (sum3_with_carry, _x) = u8_add(sum3, carry3);

    [sum3_with_carry, sum2_with_carry, sum1_with_carry, sum0]
  }

  -- Computes the predecessor of an `u64` assumed to be properly represented in
  -- little-endian bytes. If that's not the case, this implementation has UB.
  fn relaxed_u64_pred(bytes: U64) -> U64 {
    let [b0, b1, b2, b3, b4, b5, b6, b7] = bytes;
    match b0 {
      0 => match b1 {
        0 => match b2 {
          0 => match b3 {
            0 => match b4 {
              0 => match b5 {
                0 => match b6 {
                  0 => match b7 {
                    0 => [0, 0, 0, 0, 0, 0, 0, 0],
                    _ => [255, 255, 255, 255, 255, 255, 255, b7 - 1],
                  },
                  _ => [255, 255, 255, 255, 255, 255, b6 - 1, b7],
                },
                _ => [255, 255, 255, 255, 255, b5 - 1, b6, b7],
              },
              _ => [255, 255, 255, 255, b4 - 1, b5, b6, b7],
            },
            _ => [255, 255, 255, b3 - 1, b4, b5, b6, b7],
          },
          _ => [255, 255, b2 - 1, b3, b4, b5, b6, b7],
        },
        _ => [255, b1 - 1, b2, b3, b4, b5, b6, b7],
      },
      _ => [b0 - 1, b1, b2, b3, b4, b5, b6, b7],
    }
  }

  fn u64_list_length(xs: List‹U64›) -> U64 {
    match xs {
      List.Nil => [0; 8],
      List.Cons(_, rest) => relaxed_u64_succ(u64_list_length(load(rest))),
    }
  }

  -- Flatten a [G; 8] (U64 little-endian bytes) into a single G via
  -- b0 + 256 * b1 + ... + 256^6 * b6. The most significant byte (b7) must be zero;
  -- this is enforced by assert_eq!, limiting the range to 7 bytes (< 2^56).
  fn flatten_u64(x: [G; 8]) -> G {
    let [b0, b1, b2, b3, b4, b5, b6, b7] = x;
    assert_eq!(b7, 0);
    b0 + 0x100 * b1 + 0x10000 * b2 + 0x1000000 * b3
      + 0x100000000 * b4 + 0x10000000000 * b5 + 0x1000000000000 * b6
  }
⟧

end IxVM

end
