import Ix.Aiur.Meta

namespace IxVM

def u64 := ⟦
  fn u64_is_zero(x: [G; 8]) -> G {
    match x {
      [0, 0, 0, 0, 0, 0, 0, 0] => 1,
      _ => 0,
    }
  }

  -- Reconstructs a byte from its bits in little-endian.
  fn u8_recompose(bits: [G; 8]) -> G {
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

  -- Computes the successor of an `u64` assumed to be properly represented in
  -- little-endian bytes. If that's not the case, this implementation has UB.
  fn relaxed_u64_succ(bytes: [G; 8]) -> [G; 8] {
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

  fn relaxed_u64_be_add_2_bytes(u64: [G; 8], bs: [G; 2]) -> [G; 8] {
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
⟧

end IxVM
