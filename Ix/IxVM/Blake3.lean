module
public import Ix.Aiur.Meta

public section

namespace IxVM

def blake3 := ⟦
  /- # Test entrypoints -/

  pub fn blake3_test() -> [[G; 4]; 8] {
    let (idx, len) = io_get_info([0]);
    let byte_stream = #read_byte_stream(idx, len);
    blake3(byte_stream)
  }

  /- # Benchmark entrypoints -/

  pub fn blake3_bench(num_hashes: G) -> G {
    let num_hashes_pred = num_hashes - 1;
    let key = [num_hashes_pred];
    let (idx, len) = io_get_info(key);
    let byte_stream = #read_byte_stream(idx, len);
    let _ = blake3(byte_stream);
    match num_hashes_pred {
      0 => 0,
      _ => blake3_bench(num_hashes_pred),
    }
  }

  /- # Implementation -/

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
    blake3_compress_layer(load(blake3_compress_chunks(input, store(ListNode.Nil), 0, 0, [0; 8], IV, store(Layer.Nil))))
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

  -- Hot chunk loop. The 64-byte block buffer is NOT threaded here as a
  -- `[[G; 4]; 16]` value — that cost 64 columns of `inputSize` plus a +64-aux
  -- `assign_block_value` call on every row. Instead bytes accumulate into a
  -- reverse-ordered linked list (`byte_acc`); each hot row is a single `store`.
  fn blake3_compress_chunks(
    input: ByteStream,
    byte_acc: ByteStream,
    block_index: G,
    chunk_index: G,
    chunk_count: U64,
    block_digest: [[G; 4]; 8],
    layer: &Layer
  ) -> &Layer {
    match load(input) {
      -- Input exhausted: hand off to the cold finalize circuit.
      ListNode.Nil =>
        blake3_finish(byte_acc, block_index, chunk_index, chunk_count, block_digest, layer),
      ListNode.Cons(head, input) =>
        let byte_acc = store(ListNode.Cons(head, byte_acc));
        match block_index {
          63 => blake3_compress_block(input, byte_acc, chunk_index, chunk_count, block_digest, layer),
          _ => blake3_compress_chunks(input, byte_acc, block_index + 1, chunk_index + 1, chunk_count, block_digest, layer),
        },
    }
  }

  -- Materializes a 64-byte accumulator list into a `[[G; 4]; 16]` block. The
  -- list is reverse-ordered (head = most recently appended byte = position 63).
  -- 64 unrolled `load`s, one circuit row per call — keeps the 64-wide buffer
  -- out of the hot loop and out of `inputSize`.
  fn bytes_to_block(byte_acc: ByteStream) -> [[G; 4]; 16] {
    let ListNode.Cons(b63, l) = load(byte_acc);
    let ListNode.Cons(b62, l) = load(l);
    let ListNode.Cons(b61, l) = load(l);
    let ListNode.Cons(b60, l) = load(l);
    let ListNode.Cons(b59, l) = load(l);
    let ListNode.Cons(b58, l) = load(l);
    let ListNode.Cons(b57, l) = load(l);
    let ListNode.Cons(b56, l) = load(l);
    let ListNode.Cons(b55, l) = load(l);
    let ListNode.Cons(b54, l) = load(l);
    let ListNode.Cons(b53, l) = load(l);
    let ListNode.Cons(b52, l) = load(l);
    let ListNode.Cons(b51, l) = load(l);
    let ListNode.Cons(b50, l) = load(l);
    let ListNode.Cons(b49, l) = load(l);
    let ListNode.Cons(b48, l) = load(l);
    let ListNode.Cons(b47, l) = load(l);
    let ListNode.Cons(b46, l) = load(l);
    let ListNode.Cons(b45, l) = load(l);
    let ListNode.Cons(b44, l) = load(l);
    let ListNode.Cons(b43, l) = load(l);
    let ListNode.Cons(b42, l) = load(l);
    let ListNode.Cons(b41, l) = load(l);
    let ListNode.Cons(b40, l) = load(l);
    let ListNode.Cons(b39, l) = load(l);
    let ListNode.Cons(b38, l) = load(l);
    let ListNode.Cons(b37, l) = load(l);
    let ListNode.Cons(b36, l) = load(l);
    let ListNode.Cons(b35, l) = load(l);
    let ListNode.Cons(b34, l) = load(l);
    let ListNode.Cons(b33, l) = load(l);
    let ListNode.Cons(b32, l) = load(l);
    let ListNode.Cons(b31, l) = load(l);
    let ListNode.Cons(b30, l) = load(l);
    let ListNode.Cons(b29, l) = load(l);
    let ListNode.Cons(b28, l) = load(l);
    let ListNode.Cons(b27, l) = load(l);
    let ListNode.Cons(b26, l) = load(l);
    let ListNode.Cons(b25, l) = load(l);
    let ListNode.Cons(b24, l) = load(l);
    let ListNode.Cons(b23, l) = load(l);
    let ListNode.Cons(b22, l) = load(l);
    let ListNode.Cons(b21, l) = load(l);
    let ListNode.Cons(b20, l) = load(l);
    let ListNode.Cons(b19, l) = load(l);
    let ListNode.Cons(b18, l) = load(l);
    let ListNode.Cons(b17, l) = load(l);
    let ListNode.Cons(b16, l) = load(l);
    let ListNode.Cons(b15, l) = load(l);
    let ListNode.Cons(b14, l) = load(l);
    let ListNode.Cons(b13, l) = load(l);
    let ListNode.Cons(b12, l) = load(l);
    let ListNode.Cons(b11, l) = load(l);
    let ListNode.Cons(b10, l) = load(l);
    let ListNode.Cons(b9, l) = load(l);
    let ListNode.Cons(b8, l) = load(l);
    let ListNode.Cons(b7, l) = load(l);
    let ListNode.Cons(b6, l) = load(l);
    let ListNode.Cons(b5, l) = load(l);
    let ListNode.Cons(b4, l) = load(l);
    let ListNode.Cons(b3, l) = load(l);
    let ListNode.Cons(b2, l) = load(l);
    let ListNode.Cons(b1, l) = load(l);
    let ListNode.Cons(b0, _) = load(l);
    [
      [b0, b1, b2, b3], [b4, b5, b6, b7], [b8, b9, b10, b11], [b12, b13, b14, b15],
      [b16, b17, b18, b19], [b20, b21, b22, b23], [b24, b25, b26, b27], [b28, b29, b30, b31],
      [b32, b33, b34, b35], [b36, b37, b38, b39], [b40, b41, b42, b43], [b44, b45, b46, b47],
      [b48, b49, b50, b51], [b52, b53, b54, b55], [b56, b57, b58, b59], [b60, b61, b62, b63]
    ]
  }

  -- Prepends `n` zero bytes to a partial block accumulator so it can be fed to
  -- `bytes_to_block`. Cold: only the trailing partial block of a hash uses it.
  fn pad_block(acc: ByteStream, n: G) -> ByteStream {
    match n {
      0 => acc,
      _ => pad_block(store(ListNode.Cons(0, acc)), n - 1),
    }
  }

  -- Cold finalize circuit for `blake3_compress_chunks`: input is exhausted, so
  -- emit the trailing layer node. Quarantines the `blake3_compress` call and
  -- the partial-block materialization out of the hot chunk loop.
  fn blake3_finish(
    byte_acc: ByteStream,
    block_index: G,
    chunk_index: G,
    chunk_count: U64,
    block_digest: [[G; 4]; 8],
    layer: &Layer
  ) -> &Layer {
    let CHUNK_START = 1;
    let CHUNK_END = 2;
    let ROOT = 8;
    match (block_index, chunk_index) {
      (0, 0) =>
        match chunk_count {
          [0, 0, 0, 0, 0, 0, 0, 0] =>
            let flags = ROOT + CHUNK_START + CHUNK_END;
            store(Layer.Push(layer, blake3_compress(block_digest, [[0; 4]; 16], chunk_count, 0, flags))),
          _ => layer,
        },
      (0, _) => store(Layer.Push(layer, block_digest)),
      (_, _) =>
        let flags = CHUNK_END + u64_is_zero(chunk_count) * ROOT + eq_zero(chunk_index - block_index) * CHUNK_START;
        let block = bytes_to_block(pad_block(byte_acc, 64 - block_index));
        store(Layer.Push(layer, blake3_compress(block_digest, block, chunk_count, block_index, flags))),
    }
  }

  -- Cold continuation of `blake3_compress_chunks`: runs once per filled 64-byte
  -- block. Materializes the byte accumulator, runs `blake3_compress`, pushes the
  -- digest, and resets the accumulator for the next block.
  fn blake3_compress_block(
    input: ByteStream,
    byte_acc: ByteStream,
    chunk_index: G,
    chunk_count: U64,
    block_digest: [[G; 4]; 8],
    layer: &Layer
  ) -> &Layer {
    let CHUNK_START = 1;
    let CHUNK_END = 2;
    let ROOT = 8;
    let block = bytes_to_block(byte_acc);
    match chunk_index {
      1023 =>
        let flags = ROOT * list_is_empty(input) * u64_is_zero(chunk_count) + CHUNK_END;
        let IV = [[103, 230, 9, 106], [133, 174, 103, 187], [114, 243, 110, 60], [58, 245, 79, 165], [127, 82, 14, 81], [140, 104, 5, 155], [171, 217, 131, 31], [25, 205, 224, 91]];
        let layer = store(Layer.Push(layer, blake3_compress(block_digest, block, chunk_count, 64, flags)));
        blake3_compress_chunks(input, store(ListNode.Nil), 0, 0, relaxed_u64_succ(chunk_count), IV, layer),
      _ =>
        let chunk_end_flag = list_is_empty(input) * CHUNK_END;
        let root_flag = list_is_empty(input) * u64_is_zero(chunk_count) * ROOT;
        let chunk_start_flag = eq_zero(chunk_index - 63) * CHUNK_START;
        let flags = chunk_end_flag + root_flag + chunk_start_flag;
        let block_digest = blake3_compress(block_digest, block, chunk_count, 64, flags);
        blake3_compress_chunks(input, store(ListNode.Nil), 0, chunk_index + 1, chunk_count, block_digest, layer),
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
    counter: U64,
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

end IxVM

end
