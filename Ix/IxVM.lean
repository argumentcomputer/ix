import Ix.Aiur.Meta

def ixVM := ⟦
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
    let [a0, a1, a2, a3] = a;
    let [b0, b1, b2, b3] = b;
    let c0 = u8_xor(a0, b0);
    let c1 = u8_xor(a1, b1);
    let c2 = u8_xor(a2, b2);
    let c3 = u8_xor(a3, b3);
    [c0, c1, c2, c3]
  }

  fn u8_recompose(bits: [G; 8]) -> G {
    let [b0, b1, b2, b3, b4, b5, b6, b7] = bits;
    b0 + 2 * b1 + 4 * b2 + 8 * b3 + 16 * b4 + 32 * b5 + 64 * b6 + 128 * b7
  }

  fn blake3_g_function(
    a: [G; 4],
    b: [G; 4],
    c: [G; 4],
    d: [G; 4],
    x: [G; 4],
    y: [G; 4]
  ) -> [[G; 4]; 4] {
    let a = u32_add(u32_add(a, b), x);
    let [d0, d1, d2, d3] = u32_xor(d, a);
    let d = [d2, d3, d0, d1]; -- Right-rotated 16

    let c = u32_add(c, d);
    let [b0, b1, b2, b3] = u32_xor(b, c);
    let [b00, b01, b02, b03, b04, b05, b06, b07] = u8_bit_decomposition(b0);
    let [b10, b11, b12, b13, b14, b15, b16, b17] = u8_bit_decomposition(b1);
    let [b20, b21, b22, b23, b24, b25, b26, b27] = u8_bit_decomposition(b2);
    let [b30, b31, b32, b33, b34, b35, b36, b37] = u8_bit_decomposition(b3);
    let b0 = u8_recompose([b14, b15, b16, b17, b20, b21, b22, b23]);
    let b1 = u8_recompose([b24, b25, b26, b27, b30, b31, b32, b33]);
    let b2 = u8_recompose([b34, b35, b36, b37, b00, b01, b02, b03]);
    let b3 = u8_recompose([b04, b05, b06, b07, b10, b11, b12, b13]);
    let b = [b0, b1, b2, b3]; -- Right-rotated 12

    let a = u32_add(u32_add(a, b), y);
    let [d0, d1, d2, d3] = u32_xor(d, a);
    let d = [d1, d2, d3, d0]; -- Right-rotated 8

    let c = u32_add(c, d);
    let [b0, b1, b2, b3] = u32_xor(b, c);
    let [b00, b01, b02, b03, b04, b05, b06, b07] = u8_bit_decomposition(b0);
    let [b10, b11, b12, b13, b14, b15, b16, b17] = u8_bit_decomposition(b1);
    let [b20, b21, b22, b23, b24, b25, b26, b27] = u8_bit_decomposition(b2);
    let [b30, b31, b32, b33, b34, b35, b36, b37] = u8_bit_decomposition(b3);
    let b0 = u8_recompose([b07, b10, b11, b12, b13, b14, b15, b16]);
    let b1 = u8_recompose([b17, b20, b21, b22, b23, b24, b25, b26]);
    let b2 = u8_recompose([b27, b30, b31, b32, b33, b34, b35, b36]);
    let b3 = u8_recompose([b37, b00, b01, b02, b03, b04, b05, b06]);
    let b = [b0, b1, b2, b3]; -- Right-rotated 7

    [a, b, c, d]
  }

  fn blake3_compress_inner_j(state: [[G; 4]; 32]) -> [[G; 4]; 32] {
    -- Round 0
    let [a, b, c, d] = blake3_g_function(
      state[0], state[4], state[8], state[12], state[16], state[17]
    );
    let state = set(state, 0, a);
    let state = set(state, 4, b);
    let state = set(state, 8, c);
    let state = set(state, 12, d);

    -- Round 1
    let [a, b, c, d] = blake3_g_function(
      state[1], state[5], state[9], state[13], state[18], state[19]
    );
    let state = set(state, 1, a);
    let state = set(state, 5, b);
    let state = set(state, 9, c);
    let state = set(state, 13, d);

    -- Round 2
    let [a, b, c, d] = blake3_g_function(
      state[2], state[6], state[10], state[14], state[20], state[21]
    );
    let state = set(state, 2, a);
    let state = set(state, 6, b);
    let state = set(state, 10, c);
    let state = set(state, 14, d);

    -- Round 3
    let [a, b, c, d] = blake3_g_function(
      state[3], state[7], state[11], state[15], state[22], state[23]
    );
    let state = set(state, 3, a);
    let state = set(state, 7, b);
    let state = set(state, 11, c);
    let state = set(state, 15, d);

    -- Round 4
    let [a, b, c, d] = blake3_g_function(
      state[0], state[5], state[10], state[15], state[24], state[25]
    );
    let state = set(state, 0, a);
    let state = set(state, 5, b);
    let state = set(state, 10, c);
    let state = set(state, 15, d);

    -- Round 5
    let [a, b, c, d] = blake3_g_function(
      state[1], state[6], state[11], state[12], state[26], state[27]
    );
    let state = set(state, 1, a);
    let state = set(state, 6, b);
    let state = set(state, 11, c);
    let state = set(state, 12, d);

    -- Round 6
    let [a, b, c, d] = blake3_g_function(
      state[2], state[7], state[8], state[13], state[28], state[29]
    );
    let state = set(state, 2, a);
    let state = set(state, 7, b);
    let state = set(state, 8, c);
    let state = set(state, 13, d);

    -- Round 7
    let [a, b, c, d] = blake3_g_function(
      state[3], state[4], state[9], state[14], state[30], state[31]
    );
    let state = set(state, 3, a);
    let state = set(state, 4, b);
    let state = set(state, 9, c);
    let state = set(state, 14, d);

    state
  }

  fn blake3_compress_inner_perm(state: [[G; 4]; 32]) -> [[G; 4]; 32] {
    let new_state = set(state, 16, state[18]);
    let new_state = set(new_state, 17, state[22]);
    let new_state = set(new_state, 18, state[19]);
    let new_state = set(new_state, 19, state[26]);
    let new_state = set(new_state, 20, state[23]);
    let new_state = set(new_state, 21, state[16]);
    let new_state = set(new_state, 22, state[20]);
    let new_state = set(new_state, 23, state[29]);
    let new_state = set(new_state, 24, state[17]);
    let new_state = set(new_state, 25, state[27]);
    let new_state = set(new_state, 26, state[28]);
    let new_state = set(new_state, 27, state[21]);
    let new_state = set(new_state, 28, state[25]);
    let new_state = set(new_state, 29, state[30]);
    let new_state = set(new_state, 30, state[31]);
    let new_state = set(new_state, 31, state[24]);
    new_state
  }

  fn blake3_compress(
    chaining_value: [[G; 4]; 8],
    block_words: [[G; 4]; 16],
    counter: [G; 8],
    block_len: [G; 4],
    flags: [G; 4]
  ) -> [[G; 4]; 16] {
    let IV0 = [103, 230,   9, 106];
    let IV1 = [133, 174, 103, 187];
    let IV2 = [114, 243, 110,  60];
    let IV3 = [ 58, 245,  79, 165];

    let counter_low = counter[0 .. 4];
    let counter_high = counter[4 .. 8];

    let state: [[G; 4]; 32] = [
      chaining_value[0], chaining_value[1], chaining_value[2], chaining_value[3],
      chaining_value[4], chaining_value[5], chaining_value[6], chaining_value[7],
                    IV0,               IV1,               IV2,               IV3,
            counter_low,      counter_high,         block_len,             flags,
         block_words[0],    block_words[1],    block_words[2],    block_words[3],
         block_words[4],    block_words[5],    block_words[6],    block_words[7],
         block_words[8],    block_words[9],   block_words[10],   block_words[11],
        block_words[12],   block_words[13],   block_words[14],   block_words[15]
    ];

    -- Round 0
    let state = blake3_compress_inner_j(state);
    let state = blake3_compress_inner_perm(state);

    -- Round 1
    let state = blake3_compress_inner_j(state);
    let state = blake3_compress_inner_perm(state);

    -- Round 2
    let state = blake3_compress_inner_j(state);
    let state = blake3_compress_inner_perm(state);

    -- Round 3
    let state = blake3_compress_inner_j(state);
    let state = blake3_compress_inner_perm(state);

    -- Round 4
    let state = blake3_compress_inner_j(state);
    let state = blake3_compress_inner_perm(state);

    -- Round 5
    let state = blake3_compress_inner_j(state);
    let state = blake3_compress_inner_perm(state);

    -- Round 6
    let state = blake3_compress_inner_j(state);

    [
      u32_xor(state[0], state[8]),
      u32_xor(state[1], state[9]),
      u32_xor(state[2], state[10]),
      u32_xor(state[3], state[11]),
      u32_xor(state[4], state[12]),
      u32_xor(state[5], state[13]),
      u32_xor(state[6], state[14]),
      u32_xor(state[7], state[15]),
      u32_xor(state[8], chaining_value[0]),
      u32_xor(state[9], chaining_value[1]),
      u32_xor(state[10], chaining_value[2]),
      u32_xor(state[11], chaining_value[3]),
      u32_xor(state[12], chaining_value[4]),
      u32_xor(state[13], chaining_value[5]),
      u32_xor(state[14], chaining_value[6]),
      u32_xor(state[15], chaining_value[7])
    ]
  }
⟧
