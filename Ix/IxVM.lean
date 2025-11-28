import Ix.Aiur.Meta

namespace IxVM

def byteStream := ⟦
  enum ByteStream {
    Cons(G, &ByteStream),
    Nil
  }

  #[unconstrained]
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
⟧

def blake3Aux := ⟦
  -- TODO remove this function
  fn chunk_count_is_zero(chunk_count: [G; 8]) -> G {
    eq_zero(chunk_count[0])
      * eq_zero(chunk_count[1])
      * eq_zero(chunk_count[2])
      * eq_zero(chunk_count[3])
      * eq_zero(chunk_count[4])
      * eq_zero(chunk_count[5])
      * eq_zero(chunk_count[6])
      * eq_zero(chunk_count[7])
  }

  fn assign_block_value(block: [[G; 4]; 16], idx: G, val: G) -> [[G; 4]; 16] {
    match idx {
      0 => set(block, 0, set(block[0], 0, val)),
      1 => set(block, 0, set(block[0], 1, val)),
      2 => set(block, 0, set(block[0], 2, val)),
      3 => set(block, 0, set(block[0], 3, val)),
      4 => set(block, 1, set(block[1], 0, val)),
      5 => set(block, 1, set(block[1], 1, val)),
      6 => set(block, 1, set(block[1], 2, val)),
      7 => set(block, 1, set(block[1], 3, val)),
      8 => set(block, 2, set(block[2], 0, val)),
      9 => set(block, 2, set(block[2], 1, val)),
      10 => set(block, 2, set(block[2], 2, val)),
      11 => set(block, 2, set(block[2], 3, val)),
      12 => set(block, 3, set(block[3], 0, val)),
      13 => set(block, 3, set(block[3], 1, val)),
      14 => set(block, 3, set(block[3], 2, val)),
      15 => set(block, 3, set(block[3], 3, val)),
      16 => set(block, 4, set(block[4], 0, val)),
      17 => set(block, 4, set(block[4], 1, val)),
      18 => set(block, 4, set(block[4], 2, val)),
      19 => set(block, 4, set(block[4], 3, val)),
      20 => set(block, 5, set(block[5], 0, val)),
      21 => set(block, 5, set(block[5], 1, val)),
      22 => set(block, 5, set(block[5], 2, val)),
      23 => set(block, 5, set(block[5], 3, val)),
      24 => set(block, 6, set(block[6], 0, val)),
      25 => set(block, 6, set(block[6], 1, val)),
      26 => set(block, 6, set(block[6], 2, val)),
      27 => set(block, 6, set(block[6], 3, val)),
      28 => set(block, 7, set(block[7], 0, val)),
      29 => set(block, 7, set(block[7], 1, val)),
      30 => set(block, 7, set(block[7], 2, val)),
      31 => set(block, 7, set(block[7], 3, val)),
      32 => set(block, 8, set(block[8], 0, val)),
      33 => set(block, 8, set(block[8], 1, val)),
      34 => set(block, 8, set(block[8], 2, val)),
      35 => set(block, 8, set(block[8], 3, val)),
      36 => set(block, 9, set(block[9], 0, val)),
      37 => set(block, 9, set(block[9], 1, val)),
      38 => set(block, 9, set(block[9], 2, val)),
      39 => set(block, 9, set(block[9], 3, val)),
      40 => set(block, 10, set(block[10], 0, val)),
      41 => set(block, 10, set(block[10], 1, val)),
      42 => set(block, 10, set(block[10], 2, val)),
      43 => set(block, 10, set(block[10], 3, val)),
      44 => set(block, 11, set(block[11], 0, val)),
      45 => set(block, 11, set(block[11], 1, val)),
      46 => set(block, 11, set(block[11], 2, val)),
      47 => set(block, 11, set(block[11], 3, val)),
      48 => set(block, 12, set(block[12], 0, val)),
      49 => set(block, 12, set(block[12], 1, val)),
      50 => set(block, 12, set(block[12], 2, val)),
      51 => set(block, 12, set(block[12], 3, val)),
      52 => set(block, 13, set(block[13], 0, val)),
      53 => set(block, 13, set(block[13], 1, val)),
      54 => set(block, 13, set(block[13], 2, val)),
      55 => set(block, 13, set(block[13], 3, val)),
      56 => set(block, 14, set(block[14], 0, val)),
      57 => set(block, 14, set(block[14], 1, val)),
      58 => set(block, 14, set(block[14], 2, val)),
      59 => set(block, 14, set(block[14], 3, val)),
      60 => set(block, 15, set(block[15], 0, val)),
      61 => set(block, 15, set(block[15], 1, val)),
      62 => set(block, 15, set(block[15], 2, val)),
      63 => set(block, 15, set(block[15], 3, val)),
    }
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
⟧

def blake3 := ⟦
  enum Layer {
    Push(&Layer, [[G; 4]; 8]),
    Nil
  }

  enum MaybeDigest {
    None,
    Some([[G; 4]; 8])
  }

  fn blake3(input: ByteStream) -> [[G; 4]; 8] {
    let IV = [[103, 230, 9, 106], [133, 174, 103, 187], [114, 243, 110, 60], [58, 245, 79, 165], [127, 82, 14, 81], [140, 104, 5, 155], [171, 217, 131, 31], [25, 205, 224, 91]];
    blake3_compress_layer(blake3_compress_chunks(input, [[0; 4]; 16], 0, 0, [0; 8], IV, Layer.Nil))
  }

  fn blake3_next_layer(layer: Layer, digest: [[G; 4]; 8], root: G) -> (MaybeDigest, Layer) {
    match layer {
      Layer.Nil => (MaybeDigest.Some(digest), Layer.Nil),
      Layer.Push(layer, other) =>
        let (last, new_layer) = blake3_next_layer(load(layer), other, 0);
        match last {
          MaybeDigest.None => (MaybeDigest.Some(digest), new_layer),
          MaybeDigest.Some(last) =>
            let PARENT = 4;
            let ROOT = 8;
            let IV = [[103, 230, 9, 106], [133, 174, 103, 187], [114, 243, 110, 60], [58, 245, 79, 165], [127, 82, 14, 81], [140, 104, 5, 155], [171, 217, 131, 31], [25, 205, 224, 91]];
            let [x0, x1, x2, x3, x4, x5, x6, x7] = last;
            let [x8, x9, x10, x11, x12, x13, x14, x15] = digest;
            let blocks = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15];
            match new_layer {
              Layer.Nil =>
                let flags = PARENT + ROOT * root;
                let digest = blake3_compress(IV, blocks, [0; 8], 64, flags);
                (MaybeDigest.None, Layer.Push(store(new_layer), digest)),
              _ =>
                let flags = PARENT;
                let digest = blake3_compress(IV, blocks, [0; 8], 64, flags);
                (MaybeDigest.None, Layer.Push(store(new_layer), digest)),
            },
        },
    }
  }

  fn blake3_compress_layer(layer: Layer) -> [[G; 4]; 8] {
    let Layer.Push(rest, digest) = layer;
    match load(rest) {
      Layer.Nil => digest,
      rest =>
        let (last, new_merkle) = blake3_next_layer(rest, digest, 1);
        match last {
          MaybeDigest.None => blake3_compress_layer(new_merkle),
          MaybeDigest.Some(last) => blake3_compress_layer(Layer.Push(store(new_merkle), last)),
        },
    }
  }

  fn blake3_compress_chunks(
    input: ByteStream,
    block_buffer: [[G; 4]; 16],
    block_index: G,
    chunk_index: G,
    chunk_count: [G; 8],
    block_digest: [[G; 4]; 8],
    layer: Layer
  ) -> Layer {
    let CHUNK_START = 1;
    let CHUNK_END = 2;
    let PARENT = 4;
    let ROOT = 8;
    match (input, block_index, chunk_index) {
      (ByteStream.Nil, 0, 0) =>
        match chunk_count {
          [0, 0, 0, 0, 0, 0, 0, 0] =>
            let flags = ROOT + CHUNK_START + CHUNK_END;
            Layer.Push(store(layer), blake3_compress(block_digest, block_buffer, chunk_count, 0, flags)),
          _ => layer,
        },

      (ByteStream.Nil, 0, _) => Layer.Push(store(layer), block_digest),

      (ByteStream.Nil, _, _) =>
        let flags = CHUNK_END + chunk_count_is_zero(chunk_count) * ROOT + eq_zero(chunk_index - block_index) * CHUNK_START;
        Layer.Push(store(layer), blake3_compress(block_digest, block_buffer, chunk_count, block_index, flags)),

      (ByteStream.Cons(head, input_ptr), 63, 1023) =>
        let input = load(input_ptr);
        let flags = ROOT * byte_stream_is_empty(input) * chunk_count_is_zero(chunk_count) + CHUNK_END;
        let block_buffer = assign_block_value(block_buffer, block_index, head);
        let IV = [[103, 230, 9, 106], [133, 174, 103, 187], [114, 243, 110, 60], [58, 245, 79, 165], [127, 82, 14, 81], [140, 104, 5, 155], [171, 217, 131, 31], [25, 205, 224, 91]];
        let empty_buffer = [[0; 4]; 16];
        let layer = Layer.Push(store(layer), blake3_compress(block_digest, block_buffer, chunk_count, 64, flags));
        blake3_compress_chunks(input, empty_buffer, 0, 0, relaxed_u64_succ(chunk_count), IV, layer),

      (ByteStream.Cons(head, input_ptr), 63, _) =>
        let input = load(input_ptr);
        let block_buffer = assign_block_value(block_buffer, block_index, head);
        let chunk_end_flag = byte_stream_is_empty(input) * CHUNK_END;
        let root_flag = byte_stream_is_empty(input) * chunk_count_is_zero(chunk_count) * ROOT;
        let chunk_start_flag = eq_zero(chunk_index - block_index) * CHUNK_START;
        let flags = chunk_end_flag + root_flag + chunk_start_flag;
        let block_digest = blake3_compress(
            block_digest,
            block_buffer,
            chunk_count,
            64,
            flags
        );
        let empty_buffer = [[0; 4]; 16];
        blake3_compress_chunks(
            input,
            empty_buffer,
            0,
            chunk_index + 1,
            chunk_count,
            block_digest,
            layer
        ),

      (ByteStream.Cons(head, input_ptr), _, _) =>
        let input = load(input_ptr);
        let block_buffer = assign_block_value(block_buffer, block_index, head);
        blake3_compress_chunks(
            input,
            block_buffer,
            block_index + 1,
            chunk_index + 1,
            chunk_count,
            block_digest,
            layer
        ),
    }
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

  -- TODO:
  -- `block_words` could be two arguments of type [[G; 4]; 8]
  fn blake3_compress(
    chaining_value: [[G; 4]; 8],
    block_words: [[G; 4]; 16],
    counter: [G; 8],
    block_len: G,
    flags: G
  ) -> [[G; 4]; 8] {
    let IV0 = [103, 230,   9, 106];
    let IV1 = [133, 174, 103, 187];
    let IV2 = [114, 243, 110,  60];
    let IV3 = [ 58, 245,  79, 165];

    let counter_low = counter[0 .. 4];
    let counter_high = counter[4 .. 8];

    let block_len_u32 = [block_len, 0, 0, 0];
    let flags_u32 = [flags, 0, 0, 0];
    let state: [[G; 4]; 32] = [
      chaining_value[0], chaining_value[1], chaining_value[2], chaining_value[3],
      chaining_value[4], chaining_value[5], chaining_value[6], chaining_value[7],
                    IV0,               IV1,               IV2,               IV3,
            counter_low,      counter_high,     block_len_u32,         flags_u32,
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
      u32_xor(state[7], state[15])
    ]
  }
⟧

def ixonAux := ⟦
    -- TODO: remove this function
  #[unconstrained]
  fn deserialize_addr(stream: ByteStream, addr: [[G; 4]; 8], i: G) -> ([[G; 4]; 8], ByteStream) {
    match stream {
      ByteStream.Cons(byte, tail_ptr) =>
        match i {
          0 =>
            let addr = set(addr, 0, set(addr[0], 0, byte));
            deserialize_addr(load(tail_ptr), addr, 1),
          1 =>
            let addr = set(addr, 0, set(addr[0], 1, byte));
            deserialize_addr(load(tail_ptr), addr, 2),
          2 =>
            let addr = set(addr, 0, set(addr[0], 2, byte));
            deserialize_addr(load(tail_ptr), addr, 3),
          3 =>
            let addr = set(addr, 0, set(addr[0], 3, byte));
            deserialize_addr(load(tail_ptr), addr, 4),
          4 =>
            let addr = set(addr, 1, set(addr[1], 0, byte));
            deserialize_addr(load(tail_ptr), addr, 5),
          5 =>
            let addr = set(addr, 1, set(addr[1], 1, byte));
            deserialize_addr(load(tail_ptr), addr, 6),
          6 =>
            let addr = set(addr, 1, set(addr[1], 2, byte));
            deserialize_addr(load(tail_ptr), addr, 7),
          7 =>
            let addr = set(addr, 1, set(addr[1], 3, byte));
            deserialize_addr(load(tail_ptr), addr, 8),
          8 =>
            let addr = set(addr, 2, set(addr[2], 0, byte));
            deserialize_addr(load(tail_ptr), addr, 9),
          9 =>
            let addr = set(addr, 2, set(addr[2], 1, byte));
            deserialize_addr(load(tail_ptr), addr, 10),
          10 =>
            let addr = set(addr, 2, set(addr[2], 2, byte));
            deserialize_addr(load(tail_ptr), addr, 11),
          11 =>
            let addr = set(addr, 2, set(addr[2], 3, byte));
            deserialize_addr(load(tail_ptr), addr, 12),
          12 =>
            let addr = set(addr, 3, set(addr[3], 0, byte));
            deserialize_addr(load(tail_ptr), addr, 13),
          13 =>
            let addr = set(addr, 3, set(addr[3], 1, byte));
            deserialize_addr(load(tail_ptr), addr, 14),
          14 =>
            let addr = set(addr, 3, set(addr[3], 2, byte));
            deserialize_addr(load(tail_ptr), addr, 15),
          15 =>
            let addr = set(addr, 3, set(addr[3], 3, byte));
            deserialize_addr(load(tail_ptr), addr, 16),
          16 =>
            let addr = set(addr, 4, set(addr[4], 0, byte));
            deserialize_addr(load(tail_ptr), addr, 17),
          17 =>
            let addr = set(addr, 4, set(addr[4], 1, byte));
            deserialize_addr(load(tail_ptr), addr, 18),
          18 =>
            let addr = set(addr, 4, set(addr[4], 2, byte));
            deserialize_addr(load(tail_ptr), addr, 19),
          19 =>
            let addr = set(addr, 4, set(addr[4], 3, byte));
            deserialize_addr(load(tail_ptr), addr, 20),
          20 =>
            let addr = set(addr, 5, set(addr[5], 0, byte));
            deserialize_addr(load(tail_ptr), addr, 21),
          21 =>
            let addr = set(addr, 5, set(addr[5], 1, byte));
            deserialize_addr(load(tail_ptr), addr, 22),
          22 =>
            let addr = set(addr, 5, set(addr[5], 2, byte));
            deserialize_addr(load(tail_ptr), addr, 23),
          23 =>
            let addr = set(addr, 5, set(addr[5], 3, byte));
            deserialize_addr(load(tail_ptr), addr, 24),
          24 =>
            let addr = set(addr, 6, set(addr[6], 0, byte));
            deserialize_addr(load(tail_ptr), addr, 25),
          25 =>
            let addr = set(addr, 6, set(addr[6], 1, byte));
            deserialize_addr(load(tail_ptr), addr, 26),
          26 =>
            let addr = set(addr, 6, set(addr[6], 2, byte));
            deserialize_addr(load(tail_ptr), addr, 27),
          27 =>
            let addr = set(addr, 6, set(addr[6], 3, byte));
            deserialize_addr(load(tail_ptr), addr, 28),
          28 =>
            let addr = set(addr, 7, set(addr[7], 0, byte));
            deserialize_addr(load(tail_ptr), addr, 29),
          29 =>
            let addr = set(addr, 7, set(addr[7], 1, byte));
            deserialize_addr(load(tail_ptr), addr, 30),
          30 =>
            let addr = set(addr, 7, set(addr[7], 2, byte));
            deserialize_addr(load(tail_ptr), addr, 31),
          31 =>
            let addr = set(addr, 7, set(addr[7], 3, byte));
            (addr, load(tail_ptr)),
        },
    }
  }

  #[unconstrained]
  fn encode_tag_head(x: G, y: G, z: G) -> G {
    match (x, y, z) {
      (0b0000, 0b0, 0b000) => 0b00000000,
      (0b0000, 0b0, 0b001) => 0b00000001,
      (0b0000, 0b0, 0b010) => 0b00000010,
      (0b0000, 0b0, 0b011) => 0b00000011,
      (0b0000, 0b0, 0b100) => 0b00000100,
      (0b0000, 0b0, 0b101) => 0b00000101,
      (0b0000, 0b0, 0b110) => 0b00000110,
      (0b0000, 0b0, 0b111) => 0b00000111,
      (0b0000, 0b1, 0b000) => 0b00001000,
      (0b0000, 0b1, 0b001) => 0b00001001,
      (0b0000, 0b1, 0b010) => 0b00001010,
      (0b0000, 0b1, 0b011) => 0b00001011,
      (0b0000, 0b1, 0b100) => 0b00001100,
      (0b0000, 0b1, 0b101) => 0b00001101,
      (0b0000, 0b1, 0b110) => 0b00001110,
      (0b0000, 0b1, 0b111) => 0b00001111,
      (0b0001, 0b0, 0b000) => 0b00010000,
      (0b0001, 0b0, 0b001) => 0b00010001,
      (0b0001, 0b0, 0b010) => 0b00010010,
      (0b0001, 0b0, 0b011) => 0b00010011,
      (0b0001, 0b0, 0b100) => 0b00010100,
      (0b0001, 0b0, 0b101) => 0b00010101,
      (0b0001, 0b0, 0b110) => 0b00010110,
      (0b0001, 0b0, 0b111) => 0b00010111,
      (0b0001, 0b1, 0b000) => 0b00011000,
      (0b0001, 0b1, 0b001) => 0b00011001,
      (0b0001, 0b1, 0b010) => 0b00011010,
      (0b0001, 0b1, 0b011) => 0b00011011,
      (0b0001, 0b1, 0b100) => 0b00011100,
      (0b0001, 0b1, 0b101) => 0b00011101,
      (0b0001, 0b1, 0b110) => 0b00011110,
      (0b0001, 0b1, 0b111) => 0b00011111,
      (0b0010, 0b0, 0b000) => 0b00100000,
      (0b0010, 0b0, 0b001) => 0b00100001,
      (0b0010, 0b0, 0b010) => 0b00100010,
      (0b0010, 0b0, 0b011) => 0b00100011,
      (0b0010, 0b0, 0b100) => 0b00100100,
      (0b0010, 0b0, 0b101) => 0b00100101,
      (0b0010, 0b0, 0b110) => 0b00100110,
      (0b0010, 0b0, 0b111) => 0b00100111,
      (0b0010, 0b1, 0b000) => 0b00101000,
      (0b0010, 0b1, 0b001) => 0b00101001,
      (0b0010, 0b1, 0b010) => 0b00101010,
      (0b0010, 0b1, 0b011) => 0b00101011,
      (0b0010, 0b1, 0b100) => 0b00101100,
      (0b0010, 0b1, 0b101) => 0b00101101,
      (0b0010, 0b1, 0b110) => 0b00101110,
      (0b0010, 0b1, 0b111) => 0b00101111,
      (0b0011, 0b0, 0b000) => 0b00110000,
      (0b0011, 0b0, 0b001) => 0b00110001,
      (0b0011, 0b0, 0b010) => 0b00110010,
      (0b0011, 0b0, 0b011) => 0b00110011,
      (0b0011, 0b0, 0b100) => 0b00110100,
      (0b0011, 0b0, 0b101) => 0b00110101,
      (0b0011, 0b0, 0b110) => 0b00110110,
      (0b0011, 0b0, 0b111) => 0b00110111,
      (0b0011, 0b1, 0b000) => 0b00111000,
      (0b0011, 0b1, 0b001) => 0b00111001,
      (0b0011, 0b1, 0b010) => 0b00111010,
      (0b0011, 0b1, 0b011) => 0b00111011,
      (0b0011, 0b1, 0b100) => 0b00111100,
      (0b0011, 0b1, 0b101) => 0b00111101,
      (0b0011, 0b1, 0b110) => 0b00111110,
      (0b0011, 0b1, 0b111) => 0b00111111,
      (0b0100, 0b0, 0b000) => 0b01000000,
      (0b0100, 0b0, 0b001) => 0b01000001,
      (0b0100, 0b0, 0b010) => 0b01000010,
      (0b0100, 0b0, 0b011) => 0b01000011,
      (0b0100, 0b0, 0b100) => 0b01000100,
      (0b0100, 0b0, 0b101) => 0b01000101,
      (0b0100, 0b0, 0b110) => 0b01000110,
      (0b0100, 0b0, 0b111) => 0b01000111,
      (0b0100, 0b1, 0b000) => 0b01001000,
      (0b0100, 0b1, 0b001) => 0b01001001,
      (0b0100, 0b1, 0b010) => 0b01001010,
      (0b0100, 0b1, 0b011) => 0b01001011,
      (0b0100, 0b1, 0b100) => 0b01001100,
      (0b0100, 0b1, 0b101) => 0b01001101,
      (0b0100, 0b1, 0b110) => 0b01001110,
      (0b0100, 0b1, 0b111) => 0b01001111,
      (0b0101, 0b0, 0b000) => 0b01010000,
      (0b0101, 0b0, 0b001) => 0b01010001,
      (0b0101, 0b0, 0b010) => 0b01010010,
      (0b0101, 0b0, 0b011) => 0b01010011,
      (0b0101, 0b0, 0b100) => 0b01010100,
      (0b0101, 0b0, 0b101) => 0b01010101,
      (0b0101, 0b0, 0b110) => 0b01010110,
      (0b0101, 0b0, 0b111) => 0b01010111,
      (0b0101, 0b1, 0b000) => 0b01011000,
      (0b0101, 0b1, 0b001) => 0b01011001,
      (0b0101, 0b1, 0b010) => 0b01011010,
      (0b0101, 0b1, 0b011) => 0b01011011,
      (0b0101, 0b1, 0b100) => 0b01011100,
      (0b0101, 0b1, 0b101) => 0b01011101,
      (0b0101, 0b1, 0b110) => 0b01011110,
      (0b0101, 0b1, 0b111) => 0b01011111,
      (0b0110, 0b0, 0b000) => 0b01100000,
      (0b0110, 0b0, 0b001) => 0b01100001,
      (0b0110, 0b0, 0b010) => 0b01100010,
      (0b0110, 0b0, 0b011) => 0b01100011,
      (0b0110, 0b0, 0b100) => 0b01100100,
      (0b0110, 0b0, 0b101) => 0b01100101,
      (0b0110, 0b0, 0b110) => 0b01100110,
      (0b0110, 0b0, 0b111) => 0b01100111,
      (0b0110, 0b1, 0b000) => 0b01101000,
      (0b0110, 0b1, 0b001) => 0b01101001,
      (0b0110, 0b1, 0b010) => 0b01101010,
      (0b0110, 0b1, 0b011) => 0b01101011,
      (0b0110, 0b1, 0b100) => 0b01101100,
      (0b0110, 0b1, 0b101) => 0b01101101,
      (0b0110, 0b1, 0b110) => 0b01101110,
      (0b0110, 0b1, 0b111) => 0b01101111,
      (0b0111, 0b0, 0b000) => 0b01110000,
      (0b0111, 0b0, 0b001) => 0b01110001,
      (0b0111, 0b0, 0b010) => 0b01110010,
      (0b0111, 0b0, 0b011) => 0b01110011,
      (0b0111, 0b0, 0b100) => 0b01110100,
      (0b0111, 0b0, 0b101) => 0b01110101,
      (0b0111, 0b0, 0b110) => 0b01110110,
      (0b0111, 0b0, 0b111) => 0b01110111,
      (0b0111, 0b1, 0b000) => 0b01111000,
      (0b0111, 0b1, 0b001) => 0b01111001,
      (0b0111, 0b1, 0b010) => 0b01111010,
      (0b0111, 0b1, 0b011) => 0b01111011,
      (0b0111, 0b1, 0b100) => 0b01111100,
      (0b0111, 0b1, 0b101) => 0b01111101,
      (0b0111, 0b1, 0b110) => 0b01111110,
      (0b0111, 0b1, 0b111) => 0b01111111,
      (0b1000, 0b0, 0b000) => 0b10000000,
      (0b1000, 0b0, 0b001) => 0b10000001,
      (0b1000, 0b0, 0b010) => 0b10000010,
      (0b1000, 0b0, 0b011) => 0b10000011,
      (0b1000, 0b0, 0b100) => 0b10000100,
      (0b1000, 0b0, 0b101) => 0b10000101,
      (0b1000, 0b0, 0b110) => 0b10000110,
      (0b1000, 0b0, 0b111) => 0b10000111,
      (0b1000, 0b1, 0b000) => 0b10001000,
      (0b1000, 0b1, 0b001) => 0b10001001,
      (0b1000, 0b1, 0b010) => 0b10001010,
      (0b1000, 0b1, 0b011) => 0b10001011,
      (0b1000, 0b1, 0b100) => 0b10001100,
      (0b1000, 0b1, 0b101) => 0b10001101,
      (0b1000, 0b1, 0b110) => 0b10001110,
      (0b1000, 0b1, 0b111) => 0b10001111,
      (0b1001, 0b0, 0b000) => 0b10010000,
      (0b1001, 0b0, 0b001) => 0b10010001,
      (0b1001, 0b0, 0b010) => 0b10010010,
      (0b1001, 0b0, 0b011) => 0b10010011,
      (0b1001, 0b0, 0b100) => 0b10010100,
      (0b1001, 0b0, 0b101) => 0b10010101,
      (0b1001, 0b0, 0b110) => 0b10010110,
      (0b1001, 0b0, 0b111) => 0b10010111,
      (0b1001, 0b1, 0b000) => 0b10011000,
      (0b1001, 0b1, 0b001) => 0b10011001,
      (0b1001, 0b1, 0b010) => 0b10011010,
      (0b1001, 0b1, 0b011) => 0b10011011,
      (0b1001, 0b1, 0b100) => 0b10011100,
      (0b1001, 0b1, 0b101) => 0b10011101,
      (0b1001, 0b1, 0b110) => 0b10011110,
      (0b1001, 0b1, 0b111) => 0b10011111,
      (0b1010, 0b0, 0b000) => 0b10100000,
      (0b1010, 0b0, 0b001) => 0b10100001,
      (0b1010, 0b0, 0b010) => 0b10100010,
      (0b1010, 0b0, 0b011) => 0b10100011,
      (0b1010, 0b0, 0b100) => 0b10100100,
      (0b1010, 0b0, 0b101) => 0b10100101,
      (0b1010, 0b0, 0b110) => 0b10100110,
      (0b1010, 0b0, 0b111) => 0b10100111,
      (0b1010, 0b1, 0b000) => 0b10101000,
      (0b1010, 0b1, 0b001) => 0b10101001,
      (0b1010, 0b1, 0b010) => 0b10101010,
      (0b1010, 0b1, 0b011) => 0b10101011,
      (0b1010, 0b1, 0b100) => 0b10101100,
      (0b1010, 0b1, 0b101) => 0b10101101,
      (0b1010, 0b1, 0b110) => 0b10101110,
      (0b1010, 0b1, 0b111) => 0b10101111,
      (0b1011, 0b0, 0b000) => 0b10110000,
      (0b1011, 0b0, 0b001) => 0b10110001,
      (0b1011, 0b0, 0b010) => 0b10110010,
      (0b1011, 0b0, 0b011) => 0b10110011,
      (0b1011, 0b0, 0b100) => 0b10110100,
      (0b1011, 0b0, 0b101) => 0b10110101,
      (0b1011, 0b0, 0b110) => 0b10110110,
      (0b1011, 0b0, 0b111) => 0b10110111,
      (0b1011, 0b1, 0b000) => 0b10111000,
      (0b1011, 0b1, 0b001) => 0b10111001,
      (0b1011, 0b1, 0b010) => 0b10111010,
      (0b1011, 0b1, 0b011) => 0b10111011,
      (0b1011, 0b1, 0b100) => 0b10111100,
      (0b1011, 0b1, 0b101) => 0b10111101,
      (0b1011, 0b1, 0b110) => 0b10111110,
      (0b1011, 0b1, 0b111) => 0b10111111,
      (0b1100, 0b0, 0b000) => 0b11000000,
      (0b1100, 0b0, 0b001) => 0b11000001,
      (0b1100, 0b0, 0b010) => 0b11000010,
      (0b1100, 0b0, 0b011) => 0b11000011,
      (0b1100, 0b0, 0b100) => 0b11000100,
      (0b1100, 0b0, 0b101) => 0b11000101,
      (0b1100, 0b0, 0b110) => 0b11000110,
      (0b1100, 0b0, 0b111) => 0b11000111,
      (0b1100, 0b1, 0b000) => 0b11001000,
      (0b1100, 0b1, 0b001) => 0b11001001,
      (0b1100, 0b1, 0b010) => 0b11001010,
      (0b1100, 0b1, 0b011) => 0b11001011,
      (0b1100, 0b1, 0b100) => 0b11001100,
      (0b1100, 0b1, 0b101) => 0b11001101,
      (0b1100, 0b1, 0b110) => 0b11001110,
      (0b1100, 0b1, 0b111) => 0b11001111,
      (0b1101, 0b0, 0b000) => 0b11010000,
      (0b1101, 0b0, 0b001) => 0b11010001,
      (0b1101, 0b0, 0b010) => 0b11010010,
      (0b1101, 0b0, 0b011) => 0b11010011,
      (0b1101, 0b0, 0b100) => 0b11010100,
      (0b1101, 0b0, 0b101) => 0b11010101,
      (0b1101, 0b0, 0b110) => 0b11010110,
      (0b1101, 0b0, 0b111) => 0b11010111,
      (0b1101, 0b1, 0b000) => 0b11011000,
      (0b1101, 0b1, 0b001) => 0b11011001,
      (0b1101, 0b1, 0b010) => 0b11011010,
      (0b1101, 0b1, 0b011) => 0b11011011,
      (0b1101, 0b1, 0b100) => 0b11011100,
      (0b1101, 0b1, 0b101) => 0b11011101,
      (0b1101, 0b1, 0b110) => 0b11011110,
      (0b1101, 0b1, 0b111) => 0b11011111,
      (0b1110, 0b0, 0b000) => 0b11100000,
      (0b1110, 0b0, 0b001) => 0b11100001,
      (0b1110, 0b0, 0b010) => 0b11100010,
      (0b1110, 0b0, 0b011) => 0b11100011,
      (0b1110, 0b0, 0b100) => 0b11100100,
      (0b1110, 0b0, 0b101) => 0b11100101,
      (0b1110, 0b0, 0b110) => 0b11100110,
      (0b1110, 0b0, 0b111) => 0b11100111,
      (0b1110, 0b1, 0b000) => 0b11101000,
      (0b1110, 0b1, 0b001) => 0b11101001,
      (0b1110, 0b1, 0b010) => 0b11101010,
      (0b1110, 0b1, 0b011) => 0b11101011,
      (0b1110, 0b1, 0b100) => 0b11101100,
      (0b1110, 0b1, 0b101) => 0b11101101,
      (0b1110, 0b1, 0b110) => 0b11101110,
      (0b1110, 0b1, 0b111) => 0b11101111,
      (0b1111, 0b0, 0b000) => 0b11110000,
      (0b1111, 0b0, 0b001) => 0b11110001,
      (0b1111, 0b0, 0b010) => 0b11110010,
      (0b1111, 0b0, 0b011) => 0b11110011,
      (0b1111, 0b0, 0b100) => 0b11110100,
      (0b1111, 0b0, 0b101) => 0b11110101,
      (0b1111, 0b0, 0b110) => 0b11110110,
      (0b1111, 0b0, 0b111) => 0b11110111,
      (0b1111, 0b1, 0b000) => 0b11111000,
      (0b1111, 0b1, 0b001) => 0b11111001,
      (0b1111, 0b1, 0b010) => 0b11111010,
      (0b1111, 0b1, 0b011) => 0b11111011,
      (0b1111, 0b1, 0b100) => 0b11111100,
      (0b1111, 0b1, 0b101) => 0b11111101,
      (0b1111, 0b1, 0b110) => 0b11111110,
      (0b1111, 0b1, 0b111) => 0b11111111,
    }
  }

  #[unconstrained]
  fn decode_tag_head(head: G) -> (G, G, G) {
    match head {
      0b00000000 => (0b0000, 0b0, 0b000),
      0b00000001 => (0b0000, 0b0, 0b001),
      0b00000010 => (0b0000, 0b0, 0b010),
      0b00000011 => (0b0000, 0b0, 0b011),
      0b00000100 => (0b0000, 0b0, 0b100),
      0b00000101 => (0b0000, 0b0, 0b101),
      0b00000110 => (0b0000, 0b0, 0b110),
      0b00000111 => (0b0000, 0b0, 0b111),
      0b00001000 => (0b0000, 0b1, 0b000),
      0b00001001 => (0b0000, 0b1, 0b001),
      0b00001010 => (0b0000, 0b1, 0b010),
      0b00001011 => (0b0000, 0b1, 0b011),
      0b00001100 => (0b0000, 0b1, 0b100),
      0b00001101 => (0b0000, 0b1, 0b101),
      0b00001110 => (0b0000, 0b1, 0b110),
      0b00001111 => (0b0000, 0b1, 0b111),
      0b00010000 => (0b0001, 0b0, 0b000),
      0b00010001 => (0b0001, 0b0, 0b001),
      0b00010010 => (0b0001, 0b0, 0b010),
      0b00010011 => (0b0001, 0b0, 0b011),
      0b00010100 => (0b0001, 0b0, 0b100),
      0b00010101 => (0b0001, 0b0, 0b101),
      0b00010110 => (0b0001, 0b0, 0b110),
      0b00010111 => (0b0001, 0b0, 0b111),
      0b00011000 => (0b0001, 0b1, 0b000),
      0b00011001 => (0b0001, 0b1, 0b001),
      0b00011010 => (0b0001, 0b1, 0b010),
      0b00011011 => (0b0001, 0b1, 0b011),
      0b00011100 => (0b0001, 0b1, 0b100),
      0b00011101 => (0b0001, 0b1, 0b101),
      0b00011110 => (0b0001, 0b1, 0b110),
      0b00011111 => (0b0001, 0b1, 0b111),
      0b00100000 => (0b0010, 0b0, 0b000),
      0b00100001 => (0b0010, 0b0, 0b001),
      0b00100010 => (0b0010, 0b0, 0b010),
      0b00100011 => (0b0010, 0b0, 0b011),
      0b00100100 => (0b0010, 0b0, 0b100),
      0b00100101 => (0b0010, 0b0, 0b101),
      0b00100110 => (0b0010, 0b0, 0b110),
      0b00100111 => (0b0010, 0b0, 0b111),
      0b00101000 => (0b0010, 0b1, 0b000),
      0b00101001 => (0b0010, 0b1, 0b001),
      0b00101010 => (0b0010, 0b1, 0b010),
      0b00101011 => (0b0010, 0b1, 0b011),
      0b00101100 => (0b0010, 0b1, 0b100),
      0b00101101 => (0b0010, 0b1, 0b101),
      0b00101110 => (0b0010, 0b1, 0b110),
      0b00101111 => (0b0010, 0b1, 0b111),
      0b00110000 => (0b0011, 0b0, 0b000),
      0b00110001 => (0b0011, 0b0, 0b001),
      0b00110010 => (0b0011, 0b0, 0b010),
      0b00110011 => (0b0011, 0b0, 0b011),
      0b00110100 => (0b0011, 0b0, 0b100),
      0b00110101 => (0b0011, 0b0, 0b101),
      0b00110110 => (0b0011, 0b0, 0b110),
      0b00110111 => (0b0011, 0b0, 0b111),
      0b00111000 => (0b0011, 0b1, 0b000),
      0b00111001 => (0b0011, 0b1, 0b001),
      0b00111010 => (0b0011, 0b1, 0b010),
      0b00111011 => (0b0011, 0b1, 0b011),
      0b00111100 => (0b0011, 0b1, 0b100),
      0b00111101 => (0b0011, 0b1, 0b101),
      0b00111110 => (0b0011, 0b1, 0b110),
      0b00111111 => (0b0011, 0b1, 0b111),
      0b01000000 => (0b0100, 0b0, 0b000),
      0b01000001 => (0b0100, 0b0, 0b001),
      0b01000010 => (0b0100, 0b0, 0b010),
      0b01000011 => (0b0100, 0b0, 0b011),
      0b01000100 => (0b0100, 0b0, 0b100),
      0b01000101 => (0b0100, 0b0, 0b101),
      0b01000110 => (0b0100, 0b0, 0b110),
      0b01000111 => (0b0100, 0b0, 0b111),
      0b01001000 => (0b0100, 0b1, 0b000),
      0b01001001 => (0b0100, 0b1, 0b001),
      0b01001010 => (0b0100, 0b1, 0b010),
      0b01001011 => (0b0100, 0b1, 0b011),
      0b01001100 => (0b0100, 0b1, 0b100),
      0b01001101 => (0b0100, 0b1, 0b101),
      0b01001110 => (0b0100, 0b1, 0b110),
      0b01001111 => (0b0100, 0b1, 0b111),
      0b01010000 => (0b0101, 0b0, 0b000),
      0b01010001 => (0b0101, 0b0, 0b001),
      0b01010010 => (0b0101, 0b0, 0b010),
      0b01010011 => (0b0101, 0b0, 0b011),
      0b01010100 => (0b0101, 0b0, 0b100),
      0b01010101 => (0b0101, 0b0, 0b101),
      0b01010110 => (0b0101, 0b0, 0b110),
      0b01010111 => (0b0101, 0b0, 0b111),
      0b01011000 => (0b0101, 0b1, 0b000),
      0b01011001 => (0b0101, 0b1, 0b001),
      0b01011010 => (0b0101, 0b1, 0b010),
      0b01011011 => (0b0101, 0b1, 0b011),
      0b01011100 => (0b0101, 0b1, 0b100),
      0b01011101 => (0b0101, 0b1, 0b101),
      0b01011110 => (0b0101, 0b1, 0b110),
      0b01011111 => (0b0101, 0b1, 0b111),
      0b01100000 => (0b0110, 0b0, 0b000),
      0b01100001 => (0b0110, 0b0, 0b001),
      0b01100010 => (0b0110, 0b0, 0b010),
      0b01100011 => (0b0110, 0b0, 0b011),
      0b01100100 => (0b0110, 0b0, 0b100),
      0b01100101 => (0b0110, 0b0, 0b101),
      0b01100110 => (0b0110, 0b0, 0b110),
      0b01100111 => (0b0110, 0b0, 0b111),
      0b01101000 => (0b0110, 0b1, 0b000),
      0b01101001 => (0b0110, 0b1, 0b001),
      0b01101010 => (0b0110, 0b1, 0b010),
      0b01101011 => (0b0110, 0b1, 0b011),
      0b01101100 => (0b0110, 0b1, 0b100),
      0b01101101 => (0b0110, 0b1, 0b101),
      0b01101110 => (0b0110, 0b1, 0b110),
      0b01101111 => (0b0110, 0b1, 0b111),
      0b01110000 => (0b0111, 0b0, 0b000),
      0b01110001 => (0b0111, 0b0, 0b001),
      0b01110010 => (0b0111, 0b0, 0b010),
      0b01110011 => (0b0111, 0b0, 0b011),
      0b01110100 => (0b0111, 0b0, 0b100),
      0b01110101 => (0b0111, 0b0, 0b101),
      0b01110110 => (0b0111, 0b0, 0b110),
      0b01110111 => (0b0111, 0b0, 0b111),
      0b01111000 => (0b0111, 0b1, 0b000),
      0b01111001 => (0b0111, 0b1, 0b001),
      0b01111010 => (0b0111, 0b1, 0b010),
      0b01111011 => (0b0111, 0b1, 0b011),
      0b01111100 => (0b0111, 0b1, 0b100),
      0b01111101 => (0b0111, 0b1, 0b101),
      0b01111110 => (0b0111, 0b1, 0b110),
      0b01111111 => (0b0111, 0b1, 0b111),
      0b10000000 => (0b1000, 0b0, 0b000),
      0b10000001 => (0b1000, 0b0, 0b001),
      0b10000010 => (0b1000, 0b0, 0b010),
      0b10000011 => (0b1000, 0b0, 0b011),
      0b10000100 => (0b1000, 0b0, 0b100),
      0b10000101 => (0b1000, 0b0, 0b101),
      0b10000110 => (0b1000, 0b0, 0b110),
      0b10000111 => (0b1000, 0b0, 0b111),
      0b10001000 => (0b1000, 0b1, 0b000),
      0b10001001 => (0b1000, 0b1, 0b001),
      0b10001010 => (0b1000, 0b1, 0b010),
      0b10001011 => (0b1000, 0b1, 0b011),
      0b10001100 => (0b1000, 0b1, 0b100),
      0b10001101 => (0b1000, 0b1, 0b101),
      0b10001110 => (0b1000, 0b1, 0b110),
      0b10001111 => (0b1000, 0b1, 0b111),
      0b10010000 => (0b1001, 0b0, 0b000),
      0b10010001 => (0b1001, 0b0, 0b001),
      0b10010010 => (0b1001, 0b0, 0b010),
      0b10010011 => (0b1001, 0b0, 0b011),
      0b10010100 => (0b1001, 0b0, 0b100),
      0b10010101 => (0b1001, 0b0, 0b101),
      0b10010110 => (0b1001, 0b0, 0b110),
      0b10010111 => (0b1001, 0b0, 0b111),
      0b10011000 => (0b1001, 0b1, 0b000),
      0b10011001 => (0b1001, 0b1, 0b001),
      0b10011010 => (0b1001, 0b1, 0b010),
      0b10011011 => (0b1001, 0b1, 0b011),
      0b10011100 => (0b1001, 0b1, 0b100),
      0b10011101 => (0b1001, 0b1, 0b101),
      0b10011110 => (0b1001, 0b1, 0b110),
      0b10011111 => (0b1001, 0b1, 0b111),
      0b10100000 => (0b1010, 0b0, 0b000),
      0b10100001 => (0b1010, 0b0, 0b001),
      0b10100010 => (0b1010, 0b0, 0b010),
      0b10100011 => (0b1010, 0b0, 0b011),
      0b10100100 => (0b1010, 0b0, 0b100),
      0b10100101 => (0b1010, 0b0, 0b101),
      0b10100110 => (0b1010, 0b0, 0b110),
      0b10100111 => (0b1010, 0b0, 0b111),
      0b10101000 => (0b1010, 0b1, 0b000),
      0b10101001 => (0b1010, 0b1, 0b001),
      0b10101010 => (0b1010, 0b1, 0b010),
      0b10101011 => (0b1010, 0b1, 0b011),
      0b10101100 => (0b1010, 0b1, 0b100),
      0b10101101 => (0b1010, 0b1, 0b101),
      0b10101110 => (0b1010, 0b1, 0b110),
      0b10101111 => (0b1010, 0b1, 0b111),
      0b10110000 => (0b1011, 0b0, 0b000),
      0b10110001 => (0b1011, 0b0, 0b001),
      0b10110010 => (0b1011, 0b0, 0b010),
      0b10110011 => (0b1011, 0b0, 0b011),
      0b10110100 => (0b1011, 0b0, 0b100),
      0b10110101 => (0b1011, 0b0, 0b101),
      0b10110110 => (0b1011, 0b0, 0b110),
      0b10110111 => (0b1011, 0b0, 0b111),
      0b10111000 => (0b1011, 0b1, 0b000),
      0b10111001 => (0b1011, 0b1, 0b001),
      0b10111010 => (0b1011, 0b1, 0b010),
      0b10111011 => (0b1011, 0b1, 0b011),
      0b10111100 => (0b1011, 0b1, 0b100),
      0b10111101 => (0b1011, 0b1, 0b101),
      0b10111110 => (0b1011, 0b1, 0b110),
      0b10111111 => (0b1011, 0b1, 0b111),
      0b11000000 => (0b1100, 0b0, 0b000),
      0b11000001 => (0b1100, 0b0, 0b001),
      0b11000010 => (0b1100, 0b0, 0b010),
      0b11000011 => (0b1100, 0b0, 0b011),
      0b11000100 => (0b1100, 0b0, 0b100),
      0b11000101 => (0b1100, 0b0, 0b101),
      0b11000110 => (0b1100, 0b0, 0b110),
      0b11000111 => (0b1100, 0b0, 0b111),
      0b11001000 => (0b1100, 0b1, 0b000),
      0b11001001 => (0b1100, 0b1, 0b001),
      0b11001010 => (0b1100, 0b1, 0b010),
      0b11001011 => (0b1100, 0b1, 0b011),
      0b11001100 => (0b1100, 0b1, 0b100),
      0b11001101 => (0b1100, 0b1, 0b101),
      0b11001110 => (0b1100, 0b1, 0b110),
      0b11001111 => (0b1100, 0b1, 0b111),
      0b11010000 => (0b1101, 0b0, 0b000),
      0b11010001 => (0b1101, 0b0, 0b001),
      0b11010010 => (0b1101, 0b0, 0b010),
      0b11010011 => (0b1101, 0b0, 0b011),
      0b11010100 => (0b1101, 0b0, 0b100),
      0b11010101 => (0b1101, 0b0, 0b101),
      0b11010110 => (0b1101, 0b0, 0b110),
      0b11010111 => (0b1101, 0b0, 0b111),
      0b11011000 => (0b1101, 0b1, 0b000),
      0b11011001 => (0b1101, 0b1, 0b001),
      0b11011010 => (0b1101, 0b1, 0b010),
      0b11011011 => (0b1101, 0b1, 0b011),
      0b11011100 => (0b1101, 0b1, 0b100),
      0b11011101 => (0b1101, 0b1, 0b101),
      0b11011110 => (0b1101, 0b1, 0b110),
      0b11011111 => (0b1101, 0b1, 0b111),
      0b11100000 => (0b1110, 0b0, 0b000),
      0b11100001 => (0b1110, 0b0, 0b001),
      0b11100010 => (0b1110, 0b0, 0b010),
      0b11100011 => (0b1110, 0b0, 0b011),
      0b11100100 => (0b1110, 0b0, 0b100),
      0b11100101 => (0b1110, 0b0, 0b101),
      0b11100110 => (0b1110, 0b0, 0b110),
      0b11100111 => (0b1110, 0b0, 0b111),
      0b11101000 => (0b1110, 0b1, 0b000),
      0b11101001 => (0b1110, 0b1, 0b001),
      0b11101010 => (0b1110, 0b1, 0b010),
      0b11101011 => (0b1110, 0b1, 0b011),
      0b11101100 => (0b1110, 0b1, 0b100),
      0b11101101 => (0b1110, 0b1, 0b101),
      0b11101110 => (0b1110, 0b1, 0b110),
      0b11101111 => (0b1110, 0b1, 0b111),
      0b11110000 => (0b1111, 0b0, 0b000),
      0b11110001 => (0b1111, 0b0, 0b001),
      0b11110010 => (0b1111, 0b0, 0b010),
      0b11110011 => (0b1111, 0b0, 0b011),
      0b11110100 => (0b1111, 0b0, 0b100),
      0b11110101 => (0b1111, 0b0, 0b101),
      0b11110110 => (0b1111, 0b0, 0b110),
      0b11110111 => (0b1111, 0b0, 0b111),
      0b11111000 => (0b1111, 0b1, 0b000),
      0b11111001 => (0b1111, 0b1, 0b001),
      0b11111010 => (0b1111, 0b1, 0b010),
      0b11111011 => (0b1111, 0b1, 0b011),
      0b11111100 => (0b1111, 0b1, 0b100),
      0b11111101 => (0b1111, 0b1, 0b101),
      0b11111110 => (0b1111, 0b1, 0b110),
      0b11111111 => (0b1111, 0b1, 0b111),
    }
  }

  #[unconstrained]
  fn u64_get_trimmed_le(len: G, stream: ByteStream) -> ([G; 8], ByteStream) {
    let u64 = [0; 8];
    match len {
      1 => match stream {
        ByteStream.Cons(b0, tail_ptr) => (set(u64, 0, b0), load(tail_ptr)),
      },
      2 => match stream {
        ByteStream.Cons(b0, tail_ptr) =>
          match load(tail_ptr) {
            ByteStream.Cons(b1, tail_ptr) =>
              let u64 = set(u64, 0, b0);
              (set(u64, 1, b1), load(tail_ptr)),
          },
      },
      3 => match stream {
        ByteStream.Cons(b0, tail_ptr) =>
          match load(tail_ptr) {
            ByteStream.Cons(b1, tail_ptr) =>
              match load(tail_ptr) {
                ByteStream.Cons(b2, tail_ptr) =>
                  let u64 = set(u64, 0, b0);
                  let u64 = set(u64, 1, b1);
                  (set(u64, 2, b2), load(tail_ptr)),
              },
          },
      },
      4 => match stream {
        ByteStream.Cons(b0, tail_ptr) =>
          match load(tail_ptr) {
            ByteStream.Cons(b1, tail_ptr) =>
              match load(tail_ptr) {
                ByteStream.Cons(b2, tail_ptr) =>
                  match load(tail_ptr) {
                    ByteStream.Cons(b3, tail_ptr) =>
                      let u64 = set(u64, 0, b0);
                      let u64 = set(u64, 1, b1);
                      let u64 = set(u64, 2, b2);
                      (set(u64, 3, b3), load(tail_ptr)),
                  },
              },
          },
      },
      5 => match stream {
        ByteStream.Cons(b0, tail_ptr) =>
          match load(tail_ptr) {
            ByteStream.Cons(b1, tail_ptr) =>
              match load(tail_ptr) {
                ByteStream.Cons(b2, tail_ptr) =>
                  match load(tail_ptr) {
                    ByteStream.Cons(b3, tail_ptr) =>
                      match load(tail_ptr) {
                        ByteStream.Cons(b4, tail_ptr) =>
                          let u64 = set(u64, 0, b0);
                          let u64 = set(u64, 1, b1);
                          let u64 = set(u64, 2, b2);
                          let u64 = set(u64, 3, b3);
                          (set(u64, 4, b4), load(tail_ptr)),
                      },
                  },
              },
          },
      },
      5 => match stream {
        ByteStream.Cons(b0, tail_ptr) =>
          match load(tail_ptr) {
            ByteStream.Cons(b1, tail_ptr) =>
              match load(tail_ptr) {
                ByteStream.Cons(b2, tail_ptr) =>
                  match load(tail_ptr) {
                    ByteStream.Cons(b3, tail_ptr) =>
                      match load(tail_ptr) {
                        ByteStream.Cons(b4, tail_ptr) =>
                          match load(tail_ptr) {
                            ByteStream.Cons(b5, tail_ptr) =>
                              let u64 = set(u64, 0, b0);
                              let u64 = set(u64, 1, b1);
                              let u64 = set(u64, 2, b2);
                              let u64 = set(u64, 3, b3);
                              let u64 = set(u64, 4, b4);
                              (set(u64, 5, b5), load(tail_ptr)),
                          },
                      },
                  },
              },
          },
      },
      6 => match stream {
        ByteStream.Cons(b0, tail_ptr) =>
          match load(tail_ptr) {
            ByteStream.Cons(b1, tail_ptr) =>
              match load(tail_ptr) {
                ByteStream.Cons(b2, tail_ptr) =>
                  match load(tail_ptr) {
                    ByteStream.Cons(b3, tail_ptr) =>
                      match load(tail_ptr) {
                        ByteStream.Cons(b4, tail_ptr) =>
                          match load(tail_ptr) {
                            ByteStream.Cons(b5, tail_ptr) =>
                              match load(tail_ptr) {
                                ByteStream.Cons(b6, tail_ptr) =>
                                  let u64 = set(u64, 0, b0);
                                  let u64 = set(u64, 1, b1);
                                  let u64 = set(u64, 2, b2);
                                  let u64 = set(u64, 3, b3);
                                  let u64 = set(u64, 4, b4);
                                  let u64 = set(u64, 5, b5);
                                  (set(u64, 6, b6), load(tail_ptr)),
                              },
                          },
                      },
                  },
              },
          },
      },
      7 => match stream {
        ByteStream.Cons(b0, tail_ptr) =>
          match load(tail_ptr) {
            ByteStream.Cons(b1, tail_ptr) =>
              match load(tail_ptr) {
                ByteStream.Cons(b2, tail_ptr) =>
                  match load(tail_ptr) {
                    ByteStream.Cons(b3, tail_ptr) =>
                      match load(tail_ptr) {
                        ByteStream.Cons(b4, tail_ptr) =>
                          match load(tail_ptr) {
                            ByteStream.Cons(b5, tail_ptr) =>
                              match load(tail_ptr) {
                                ByteStream.Cons(b6, tail_ptr) =>
                                  match load(tail_ptr) {
                                    ByteStream.Cons(b7, tail_ptr) =>
                                      let u64 = set(u64, 0, b0);
                                      let u64 = set(u64, 1, b1);
                                      let u64 = set(u64, 2, b2);
                                      let u64 = set(u64, 3, b3);
                                      let u64 = set(u64, 4, b4);
                                      let u64 = set(u64, 5, b5);
                                      let u64 = set(u64, 6, b6);
                                      (set(u64, 7, b7), load(tail_ptr)),
                                  },
                              },
                          },
                      },
                  },
              },
          },
      },
    }
  }
⟧

def ixon := ⟦
  enum Address {
    Bytes([[G; 4]; 8])
  }

  enum Nat {
    Bytes(ByteStream)
  }

  enum Tag4 {
    Mk(G, [G; 8])
  }

  enum DefKind {
    Definition,
    Opaque,
    Theorem
  }

  enum BuiltIn {
    Obj,
    Neutral,
    Unreachable
  }

  enum DefinitionSafety {
    Unsafe,
    Safe,
    Partial
  }

  enum Ixon {
    NAnon,                                 -- 0x00, anonymous name
    NStr(Address, Address),                -- 0x01, string name
    NNum(Address, Address),                -- 0x02, number name
    UZero,                                 -- 0x03, universe zero
    USucc(Address),                        -- 0x04, universe successor
    UMax(Address, Address),                -- 0x05, universe max
    UIMax(Address, Address),               -- 0x06, universe impredicative max
    UVar(Nat),                             -- 0x1X, universe variable
    EVar(Nat),                             -- 0x2X, expression variable
    -- ERef(Address, Vec<Address>),           -- 0x3X, expression reference
    -- ERec(Nat, Vec<Address>),               -- 0x4X, expression recursion
    -- EPrj(Address, Nat, Address),           -- 0x5X, expression projection
    ESort(Address),                        -- 0x80, expression sort
    EStr(Address),                         -- 0x81, expression string
    ENat(Address),                         -- 0x82, expression natural
    EApp(Address, Address),                -- 0x83, expression application
    ELam(Address, Address),                -- 0x84, expression lambda
    EAll(Address, Address),                -- 0x85, expression forall
    ELet(G, Address, Address, Address),    -- 0x86, 0x87, expression let. TODO: change the first argument to a Bool
    Blob(ByteStream),                      -- 0x9X, tagged bytes
    -- Defn(Definition),                      -- 0xA0, definition constant
    -- Recr(Recursor),                        -- 0xA1, recursor constant
    -- Axio(Axiom),                           -- 0xA2, axiom constant
    -- Quot(Quotient),                        -- 0xA3, quotient constant
    -- CPrj(ConstructorProj),                 -- 0xA4, constructor projection
    -- RPrj(RecursorProj),                    -- 0xA5, recursor projection
    -- IPrj(InductiveProj),                   -- 0xA6, inductive projection
    -- DPrj(DefinitionProj),
    -- 0xA7, definition projection
    -- Muts(Vec<MutConst>),                   -- 0xBX, mutual constants
    -- Prof(Proof),                              -- 0xE0, zero-knowledge proof
    Eval(Address, Address, Address, Address), -- 0xE1, evaluation claim
    Chck(Address, Address, Address),          -- 0xE2, typechecking claim
    Comm(Address, Address),                   -- 0xE3, cryptographic commitment
    -- Envn(Env),                             -- 0xE4, multi-claim environment
    Prim(BuiltIn)                             -- 0xE5, compiler built-ins
    -- Meta(Metadata)
    -- 0xFX, metadata
  }

  fn serialize(ixon: Ixon, stream: ByteStream) -> ByteStream {
    match ixon {
      Ixon.NAnon => ByteStream.Cons(0x00, store(stream)),
      Ixon.NStr(Address.Bytes(n), Address.Bytes(s)) =>
        let tag = 0x01;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(n[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(s[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.NNum(Address.Bytes(n), Address.Bytes(s)) =>
        let tag = 0x02;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(n[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(s[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.UZero => ByteStream.Cons(0x03, store(stream)),
      Ixon.USucc(Address.Bytes(n)) =>
        let tag = 0x04;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(n[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.UMax(Address.Bytes(n), Address.Bytes(s)) =>
        let tag = 0x05;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(n[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(s[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.UIMax(Address.Bytes(n), Address.Bytes(s)) =>
        let tag = 0x06;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(n[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(s[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.ESort(Address.Bytes(n)) =>
        let tag = 0x80;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(n[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.EStr(Address.Bytes(n)) =>
        let tag = 0x81;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(n[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.ENat(Address.Bytes(n)) =>
        let tag = 0x82;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(n[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.EApp(Address.Bytes(n), Address.Bytes(s)) =>
        let tag = 0x83;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(n[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(s[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.ELam(Address.Bytes(n), Address.Bytes(s)) =>
        let tag = 0x84;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(n[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(s[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.EAll(Address.Bytes(n), Address.Bytes(s)) =>
        let tag = 0x85;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(n[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(s[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.ELet(b, Address.Bytes(n), Address.Bytes(s), Address.Bytes(t)) =>
        let tag = 0x87 - b;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(n[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(s[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(t[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.Eval(Address.Bytes(a), Address.Bytes(b), Address.Bytes(c), Address.Bytes(d)) =>
        let tag = 0xE1;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(a[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(b[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(c[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(d[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.Chck(Address.Bytes(a), Address.Bytes(b), Address.Bytes(c)) =>
        let tag = 0xE2;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(a[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(b[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(c[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.Comm(Address.Bytes(a), Address.Bytes(b)) =>
        let tag = 0xE3;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(a[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(b[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.Blob(bytes) =>
        let len: [G; 8] = length(bytes);
        let flag = 0x9;
        let todo = push_front_head(flag, len, append(stream, bytes));
        todo,
    }
  }

  fn push_front_head(flag: G, len: [G; 8], stream: ByteStream) -> ByteStream {
    match len {
      [b1, 0, 0, 0, 0, 0, 0, 0] =>
        -- 248 is minus 8 in u8
        let (_, large) = u8_add(b1, 248);
        match large {
          0 =>
            let tag = encode_tag_head(flag, 0, num_bytes);
            ByteStream.Cons(tag, stream),
          1 =>
            let tag = encode_tag_head(flag, 1, num_bytes);
            ByteStream.Cons(tag, store(fold(1..0, stream, |stream, @i| ByteStream.Cons(tag, len[@i])))),
        },
      [_, _, 0, 0, 0, 0, 0, 0] =>
        let tag = encode_tag_head(flag, 1, num_bytes);
        ByteStream.Cons(tag, store(fold(2..0, stream, |stream, @i| ByteStream.Cons(tag, len[@i])))),
      [_, _, _, 0, 0, 0, 0, 0] =>
        let tag = encode_tag_head(flag, 1, num_bytes);
        ByteStream.Cons(tag, store(fold(3..0, stream, |stream, @i| ByteStream.Cons(tag, len[@i])))),
      [_, _, _, _, 0, 0, 0, 0] =>
        let tag = encode_tag_head(flag, 1, num_bytes);
        ByteStream.Cons(tag, store(fold(4..0, stream, |stream, @i| ByteStream.Cons(tag, len[@i])))),
      [_, _, _, _, _, 0, 0, 0] =>
        let tag = encode_tag_head(flag, 1, num_bytes);
        ByteStream.Cons(tag, store(fold(5..0, stream, |stream, @i| ByteStream.Cons(tag, len[@i])))),
      [_, _, _, _, _, _, 0, 0] =>
        let tag = encode_tag_head(flag, 1, num_bytes);
        ByteStream.Cons(tag, store(fold(6..0, stream, |stream, @i| ByteStream.Cons(tag, len[@i])))),
      [_, _, _, _, _, _, _, 0] =>
        let tag = encode_tag_head(flag, 1, num_bytes);
        ByteStream.Cons(tag, store(fold(7..0, stream, |stream, @i| ByteStream.Cons(tag, len[@i])))),
      [_, _, _, _, _, _, _, _] =>
        let tag = encode_tag_head(flag, 1, num_bytes);
        ByteStream.Cons(tag, store(fold(8..0, stream, |stream, @i| ByteStream.Cons(tag, len[@i])))),
    }
  }

  #[unconstrained]
  fn deserialize_tag(stream: ByteStream) -> (Tag4, ByteStream) {
    match stream {
      ByteStream.Cons(head, tail_ptr) =>
        let (flag, large, small) = decode_tag_head(head);
        match large {
          0 => (Tag4.Mk(flag, [small, 0, 0, 0, 0, 0, 0, 0]), load(tail_ptr)),
          1 =>
            let (u64, tail) = u64_get_trimmed_le(small + 1, load(tail_ptr));
            (Tag4.Mk(flag, u64), tail),
        },
    }
  }

  #[unconstrained]
  fn deserialize_byte_stream(stream: ByteStream, count: [G; 8], size: [G; 8]) -> (ByteStream, ByteStream) {
    match (size[0]-count[0], size[1]-count[1], size[2]-count[2], size[3]-count[3],
           size[4]-count[4], size[5]-count[5], size[6]-count[6], size[7]-count[7]) {
      (0, 0, 0, 0, 0, 0, 0, 0) => (ByteStream.Nil, stream),
      _ => match stream {
        ByteStream.Cons(byte, tail_ptr) =>
          let (tail_de, remaining) = deserialize_byte_stream(
            load(tail_ptr),
            relaxed_u64_succ(count),
            size
          );
          (ByteStream.Cons(byte, store(tail_de)), remaining),
      },
    }
  }

  #[unconstrained]
  fn deserialize(stream: ByteStream) -> Ixon {
    match stream {
      ByteStream.Cons(0x00, _) => Ixon.NAnon,
      ByteStream.Cons(0x01, tail_ptr) =>
        let tail = load(tail_ptr);
        -- let (addr1, tail) = fold(0..8, ([[0; 4]; 8], tail), |acc, @i|
        --   fold(0..4, acc, |(acc_addr, acc_stream), @j|
        --     let ByteStream.Cons(byte, acc_stream_tail_ptr) = acc_stream;
        --     (set(acc_addr, @i, set(acc_addr[@i], @j, byte)), load(acc_stream_tail_ptr))));
        -- let (addr2, _tail) = fold(0..8, ([[0; 4]; 8], tail), |acc, @i|
        --   fold(0..4, acc, |(acc_addr, acc_stream), @j|
        --     let ByteStream.Cons(byte, acc_stream_tail_ptr) = acc_stream;
        --     (set(acc_addr, @i, set(acc_addr[@i], @j, byte)), load(acc_stream_tail_ptr))));
        let (addr1, tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        let (addr2, _tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        Ixon.NStr(Address.Bytes(addr1), Address.Bytes(addr2)),
      ByteStream.Cons(0x02, tail_ptr) =>
        let tail = load(tail_ptr);
        let (addr1, tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        let (addr2, _tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        Ixon.NNum(Address.Bytes(addr1), Address.Bytes(addr2)),
      ByteStream.Cons(0x03, _) => Ixon.UZero,
      ByteStream.Cons(0x04, tail_ptr) =>
        let tail = load(tail_ptr);
        let (addr, _tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        Ixon.USucc(Address.Bytes(addr)),
      ByteStream.Cons(0x05, tail_ptr) =>
        let tail = load(tail_ptr);
        let (addr1, tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        let (addr2, _tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        Ixon.UMax(Address.Bytes(addr1), Address.Bytes(addr2)),
      ByteStream.Cons(0x06, tail_ptr) =>
        let tail = load(tail_ptr);
        let (addr1, tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        let (addr2, _tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        Ixon.UIMax(Address.Bytes(addr1), Address.Bytes(addr2)),
      ByteStream.Cons(0x80, tail_ptr) =>
        let tail = load(tail_ptr);
        let (addr, _tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        Ixon.ESort(Address.Bytes(addr)),
      ByteStream.Cons(0x81, tail_ptr) =>
        let tail = load(tail_ptr);
        let (addr, _tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        Ixon.EStr(Address.Bytes(addr)),
      ByteStream.Cons(0x82, tail_ptr) =>
        let tail = load(tail_ptr);
        let (addr, _tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        Ixon.ENat(Address.Bytes(addr)),
      ByteStream.Cons(0x83, tail_ptr) =>
        let tail = load(tail_ptr);
        let (addr1, tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        let (addr2, _tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        Ixon.EApp(Address.Bytes(addr1), Address.Bytes(addr2)),
      ByteStream.Cons(0x84, tail_ptr) =>
        let tail = load(tail_ptr);
        let (addr1, tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        let (addr2, _tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        Ixon.ELam(Address.Bytes(addr1), Address.Bytes(addr2)),
      ByteStream.Cons(0x85, tail_ptr) =>
        let tail = load(tail_ptr);
        let (addr1, tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        let (addr2, _tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        Ixon.EAll(Address.Bytes(addr1), Address.Bytes(addr2)),
      ByteStream.Cons(0x86, tail_ptr) =>
        let tail = load(tail_ptr);
        let (addr1, tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        let (addr2, tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        let (addr3, _tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        Ixon.ELet(1, Address.Bytes(addr1), Address.Bytes(addr2), Address.Bytes(addr3)),
      ByteStream.Cons(0x87, tail_ptr) =>
        let tail = load(tail_ptr);
        let (addr1, tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        let (addr2, tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        let (addr3, _tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        Ixon.ELet(0, Address.Bytes(addr1), Address.Bytes(addr2), Address.Bytes(addr3)),
      ByteStream.Cons(0xE1, tail_ptr) =>
        let tail = load(tail_ptr);
        let (addr1, tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        let (addr2, tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        let (addr3, tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        let (addr4, _tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        Ixon.Eval(
          Address.Bytes(addr1), Address.Bytes(addr2),
          Address.Bytes(addr3), Address.Bytes(addr4)
        ),
      ByteStream.Cons(0xE2, tail_ptr) =>
        let tail = load(tail_ptr);
        let (addr1, tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        let (addr2, tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        let (addr3, _tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        Ixon.Chck(Address.Bytes(addr1), Address.Bytes(addr2), Address.Bytes(addr3)),
      ByteStream.Cons(0xE3, tail_ptr) =>
        let tail = load(tail_ptr);
        let (addr1, tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        let (addr2, _tail) = deserialize_addr(tail, [[0; 4]; 8], 0);
        Ixon.Comm(Address.Bytes(addr1), Address.Bytes(addr2)),
      _ => -- Variable sizes
        let (tag, stream) = deserialize_tag(stream);
        match tag {
          Tag4.Mk(1, size) =>
            let (bytes, _) = deserialize_byte_stream(stream, [0; 8], size);
            Ixon.UVar(Nat.Bytes(bytes)),
          Tag4.Mk(2, size) =>
            let (bytes, _) = deserialize_byte_stream(stream, [0; 8], size);
            Ixon.EVar(Nat.Bytes(bytes)),
          Tag4.Mk(9, size) =>
            let (bytes, _) = deserialize_byte_stream(stream, [0; 8], size);
            Ixon.Blob(bytes),
        },
    }
  }
⟧

def entrypoints := ⟦
  /- # Test entrypoints -/

  fn blake3_test() -> [[G; 4]; 8] {
    let (idx, len) = io_get_info([0]);
    let byte_stream = read_byte_stream(idx, len);
    blake3(byte_stream)
  }

  fn ixon_blake3_test(h: [[G; 4]; 8]) {
    let key = [
      h[0][0], h[0][1], h[0][2], h[0][3],
      h[1][0], h[1][1], h[1][2], h[1][3],
      h[2][0], h[2][1], h[2][2], h[2][3],
      h[3][0], h[3][1], h[3][2], h[3][3],
      h[4][0], h[4][1], h[4][2], h[4][3],
      h[5][0], h[5][1], h[5][2], h[5][3],
      h[6][0], h[6][1], h[6][2], h[6][3],
      h[7][0], h[7][1], h[7][2], h[7][3]
    ];
    let (idx, len) = io_get_info(key);
    let bytes_unconstrained = read_byte_stream(idx, len);
    let ixon_unconstrained = deserialize(bytes_unconstrained);
    let bytes = serialize(ixon_unconstrained, ByteStream.Nil);
    let bytes_hash = blake3(bytes);
    assert_eq!(h, bytes_hash);
  }

  /- # Benchmark entrypoints -/

  fn blake3_bench(num_hashes: G) -> G {
    let num_hashes_pred = num_hashes - 1;
    let key = [num_hashes_pred];
    let (idx, len) = io_get_info(key);
    let byte_stream = read_byte_stream(idx, len);
    let _x = blake3(byte_stream);
    match num_hashes_pred {
      0 => 0,
      _ => blake3_bench(num_hashes_pred),
    }
  }
⟧

def ixVM : Except Aiur.Global Aiur.Toplevel := do
  let vm ← byteStream.merge blake3Aux
  let vm ← vm.merge blake3
  let vm ← vm.merge ixonAux
  let vm ← vm.merge ixon
  vm.merge entrypoints

end IxVM
