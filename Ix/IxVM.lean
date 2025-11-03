import Ix.Aiur.Meta

def ixVM := ⟦
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

  -- TODO remove this function
  fn byte_stream_is_empty(input: ByteStream) -> G {
    match input {
      ByteStream.Cons(_, _) => 0,
      ByteStream.Nil => 1,
    }
  }

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

  /- # Test entrypoints -/

  fn blake3_test() -> [[G; 4]; 8] {
    let (idx, len) = io_get_info([0]);
    let byte_stream = read_byte_stream(idx, len);
    blake3(byte_stream)
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
