import Aiur.Modules.Frontend

/-! BLAKE3 XOF output with the same chunk tree and compression rounds as the
shared hash library. XOF blocks cannot be reconstructed from a 32-byte digest,
so the root's chaining value and block are kept: `chunk` stops before a
chunk's last block (which is the root for single-chunk input), and `root`
returns the two children of the root parent. Tree layers otherwise hold only
chaining values. The first half of each XOF block is the ordinary compression
output from `Blake3::compress`; `rounds` returns the second half of the final
state, which only the XOF needs. -/
namespace MultiStark.Source

def kzgBlake3 : Aiur.Modules.Program Nat := aiur⟦
module KzgBlake3 {
  type U32 = UInt32::U32;
  type U64 = UInt64::U64;
  type CV = [U32; 8];
  type Block = [U32; 16];

  fn rounds(stage: Field, state: [U32; 32]) -> CV {
    match stage {
      7 => [state[8], state[9], state[10], state[11], state[12], state[13], state[14], state[15]],
      _ => {
        let next = Blake3::compress_inner_j(state);
        let next = (next with { [16] = state[18] });
        let next = (next with { [17] = state[22] });
        let next = (next with { [18] = state[19] });
        let next = (next with { [19] = state[26] });
        let next = (next with { [20] = state[23] });
        let next = (next with { [21] = state[16] });
        let next = (next with { [22] = state[20] });
        let next = (next with { [23] = state[29] });
        let next = (next with { [24] = state[17] });
        let next = (next with { [25] = state[27] });
        let next = (next with { [26] = state[28] });
        let next = (next with { [27] = state[21] });
        let next = (next with { [28] = state[25] });
        let next = (next with { [29] = state[30] });
        let next = (next with { [30] = state[31] });
        let next = (next with { [31] = state[24] });
        rounds(stage + 1, next)
      },
    }
  }

  fn compress_full(cv: CV, block: Block, counter: U64, length: Field, flags: Field) -> Block {
    let iv = Blake3::iv();
    let low = UInt32::from_bytes(counter[0 .. 4]);
    let high = UInt32::from_bytes(counter[4 .. 8]);
    let length_word = UInt32::from_bytes([UInt8::from_field(length), UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0]);
    let flags_word = UInt32::from_bytes([UInt8::from_field(flags), UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0]);
    let state = [
      cv[0], cv[1], cv[2], cv[3], cv[4], cv[5], cv[6], cv[7],
      iv[0], iv[1], iv[2], iv[3], low, high, length_word, flags_word,
      block[0], block[1], block[2], block[3], block[4], block[5], block[6], block[7],
      block[8], block[9], block[10], block[11], block[12], block[13], block[14], block[15]
    ];
    let first = Blake3::compress(0, state);
    let second = rounds(0, state);
    [first[0], first[1], first[2], first[3], first[4], first[5], first[6], first[7], UInt32::xor(second[0], cv[0]), UInt32::xor(second[1], cv[1]), UInt32::xor(second[2], cv[2]), UInt32::xor(second[3], cv[3]), UInt32::xor(second[4], cv[4]), UInt32::xor(second[5], cv[5]), UInt32::xor(second[6], cv[6]), UInt32::xor(second[7], cv[7])]
  }

  fn read_block(input: Bytes::Stream, count: Field, reverse: Bytes::Stream)
      -> (Bytes::Stream, Field, Bytes::Stream) {
    match count {
      64 => (reverse, count, input),
      _ => match *input {
        Lists::Node::Nil => (reverse, count, input),
        Lists::Node::Cons(byte, rest) => read_block(rest, count + 1, &(Lists::Node::Cons(byte, reverse))),
      },
    }
  }

  inline fn last_block(reverse: Bytes::Stream, length: Field) -> Block {
    Blake3::bytes_to_block(Blake3::pad_block(reverse, 64 - length))
  }

  fn chunk(input: Bytes::Stream, counter: U64, index: Field, cv: CV)
      -> (&CV, Bytes::Stream, Field, Field, Bytes::Stream) {
    let (reverse, length, rest) = read_block(input, 0, &(Lists::Node::Nil));
    let start = Fields::is_zero(index);
    let last = 1 - (1 - Lists::is_empty(rest)) * (1 - Fields::is_zero(index - 15));
    match last {
      1 => (&(cv), reverse, length, start + 2, rest),
      0 => chunk(rest, counter, index + 1, Blake3::compress_init(cv, last_block(reverse, length), counter, length, start)),
    }
  }

  fn chunks(input: Bytes::Stream, counter: U64) -> Lists::List<&CV> {
    let (cv, reverse, length, flags, rest) = chunk(input, counter, 0, Blake3::iv());
    let value = &(Blake3::compress_init(*cv, last_block(reverse, length), counter, length, flags));
    match *rest {
      Lists::Node::Nil => &(Lists::Node::Cons(value, &(Lists::Node::Nil))),
      _ => &(Lists::Node::Cons(value, chunks(rest, UInt64::wrapping_succ(counter)))),
    }
  }

  inline fn join(left: &CV, right: &CV) -> Block {
    let a = *left;
    let b = *right;
    [a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]]
  }

  fn parent(left: &CV, right: &CV) -> &CV {
    &(Blake3::compress_init(Blake3::iv(), join(left, right), [UInt8::BYTE_0;8], 64, 4))
  }

  fn next_layer(layer: Lists::List<&CV>) -> Lists::List<&CV> {
    match *layer {
      Lists::Node::Nil => layer,
      Lists::Node::Cons(first, rest) => match *rest {
        Lists::Node::Nil => layer,
        Lists::Node::Cons(second, tail) => &(Lists::Node::Cons(parent(first, second), next_layer(tail))),
      },
    }
  }

  fn root(layer: Lists::List<&CV>) -> (&CV, &CV) {
    let Lists::Node::Cons(first, rest) = *layer;
    let Lists::Node::Cons(second, tail) = *rest;
    match *tail { Lists::Node::Nil => (first, second), _ => root(next_layer(layer)) }
  }

  fn xof_output(cv: CV, block: Block, length: Field, flags: Field) -> (Block, CV) {
    let first = compress_full(cv, block, [UInt8::BYTE_0;8], length, flags + 8);
    let second = compress_full(cv, block,
      [UInt8::BYTE_1, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0,
       UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0], length, flags + 8);
    (first, [second[0], second[1], second[2], second[3], second[4], second[5], second[6], second[7]])
  }

  -- Word streams. A message is whole little-endian words followed by
  -- `tail_length` (0..3) bytes, `length = 4 * words + tail_length` in all.

  -- Moves the pending bytes of an input to its end: each output word takes
  -- the carried bytes and the front of the next input word.
  fn realign(lead: Field, carry: [UInt8::U8; 3], words: KzgIO::Words) -> (KzgIO::Words, [UInt8::U8; 3]) {
    match *words {
      Lists::Node::Nil => (words, carry),
      Lists::Node::Cons(w, rest) => { let w = UInt32::to_bytes(w); match lead {
        1 => {
          let (tail, last) = realign(lead, [w[3], UInt8::BYTE_0, UInt8::BYTE_0], rest);
          (&(Lists::Node::Cons(UInt32::from_bytes([carry[0], w[0], w[1], w[2]]), tail)), last)
        },
        2 => {
          let (tail, last) = realign(lead, [w[2], w[3], UInt8::BYTE_0], rest);
          (&(Lists::Node::Cons(UInt32::from_bytes([carry[0], carry[1], w[0], w[1]]), tail)), last)
        },
        3 => {
          let (tail, last) = realign(lead, [w[1], w[2], w[3]], rest);
          (&(Lists::Node::Cons(UInt32::from_bytes([carry[0], carry[1], carry[2], w[0]]), tail)), last)
        },
      }},
    }
  }

  fn aligned(input: KzgIO::Input) -> (KzgIO::Words, Field, [UInt8::U8; 3]) {
    let (words, offset) = input;
    match offset {
      0 => (words, 0, [UInt8::BYTE_0; 3]),
      _ => {
        let Lists::Node::Cons(w, rest) = *words; let w = UInt32::to_bytes(w);
        match offset {
          1 => {let (body, tail) = realign(3, [w[1], w[2], w[3]], rest); (body, 3, tail)},
          2 => {let (body, tail) = realign(2, [w[2], w[3], UInt8::BYTE_0], rest); (body, 2, tail)},
          3 => {let (body, tail) = realign(1, [w[3], UInt8::BYTE_0, UInt8::BYTE_0], rest); (body, 1, tail)},
        }
      },
    }
  }

  inline fn take16(words: KzgIO::Words) -> (Block, KzgIO::Words) {
    let Lists::Node::Cons(w0, l) = *words; let Lists::Node::Cons(w1, l) = *l;
    let Lists::Node::Cons(w2, l) = *l; let Lists::Node::Cons(w3, l) = *l;
    let Lists::Node::Cons(w4, l) = *l; let Lists::Node::Cons(w5, l) = *l;
    let Lists::Node::Cons(w6, l) = *l; let Lists::Node::Cons(w7, l) = *l;
    let Lists::Node::Cons(w8, l) = *l; let Lists::Node::Cons(w9, l) = *l;
    let Lists::Node::Cons(w10, l) = *l; let Lists::Node::Cons(w11, l) = *l;
    let Lists::Node::Cons(w12, l) = *l; let Lists::Node::Cons(w13, l) = *l;
    let Lists::Node::Cons(w14, l) = *l; let Lists::Node::Cons(w15, l) = *l;
    ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15], l)
  }

  fn zero_words(count: Field) -> KzgIO::Words {
    match count {
      0 => &(Lists::Node::Nil),
      _ => &(Lists::Node::Cons(UInt32::ZERO, zero_words(count - 1))),
    }
  }

  -- The final block's words, the tail word and zero padding to sixteen words.
  fn pad_words(words: KzgIO::Words, tail_length: Field, tail: [UInt8::U8; 3], used: Field) -> KzgIO::Words {
    match *words {
      Lists::Node::Cons(w, rest) => &(Lists::Node::Cons(w, pad_words(rest, tail_length, tail, used + 1))),
      Lists::Node::Nil => match tail_length {
        0 => zero_words(16 - used),
        _ => &(Lists::Node::Cons(UInt32::from_bytes([tail[0], tail[1], tail[2], UInt8::BYTE_0]), zero_words(15 - used))),
      },
    }
  }

  -- Chaining values of the chunks of a multi-chunk message, and the root
  -- compression input: the last chunk's chaining value before its final
  -- block, that block, its length and flags without ROOT (the parent node
  -- input for a multi-chunk message). `full` counts the 64-byte blocks
  -- before the final one.
  fn word_chunks(words: KzgIO::Words, full: Field, index: Field, counter: U64, cv: CV,
      final_length: Field, tail_length: Field, tail: [UInt8::U8; 3])
      -> (Lists::List<&CV>, &(CV, Block, Field, Field)) {
    match full {
      0 => final_chunk(words, index, counter, cv, final_length, tail_length, tail),
      _ => {
        let (block, rest) = take16(words);
        let start = Fields::is_zero(index);
        let last = Fields::is_zero(index - 15);
        let next = Blake3::compress_init(cv, block, counter, 64, start + 2 * last);
        match last {
          1 => {
            let (cvs, root) = word_chunks(rest, full - 1, 0, UInt64::wrapping_succ(counter), Blake3::iv(),
              final_length, tail_length, tail);
            (&(Lists::Node::Cons(&(next), cvs)), root)
          },
          0 => word_chunks(rest, full - 1, index + 1, counter, next, final_length, tail_length, tail),
        }
      },
    }
  }

  fn final_chunk(words: KzgIO::Words, index: Field, counter: U64, cv: CV,
      final_length: Field, tail_length: Field, tail: [UInt8::U8; 3])
      -> (Lists::List<&CV>, &(CV, Block, Field, Field)) {
    let (block, _rest) = take16(pad_words(words, tail_length, tail, 0));
    let flags = Fields::is_zero(index) + 2;
    match UInt64::is_zero(counter) {
      1 => (&(Lists::Node::Nil), &(cv, block, final_length, flags)),
      0 => (&(Lists::Node::Cons(&(Blake3::compress_init(cv, block, counter, final_length, flags)), &(Lists::Node::Nil))),
        &(cv, block, final_length, flags)),
    }
  }

  -- Root compression input of the message: chaining value, block, length,
  -- flags without ROOT. `words` and `tail_length` must spell exactly
  -- `length` bytes.
  fn word_root(words: KzgIO::Words, length: Field, tail_length: Field, tail: [UInt8::U8; 3]) -> (CV, Block, Field, Field) {
    let empty = Fields::is_zero(length);
    let full = hint::<Field>("kzg.io.div", (length - 1 + empty, 64));
    let final_length = length - 64 * full;
    assert_eq!(UInt32::less_than_fields(final_length - 1 + empty, 64), 1, "KZG hash block split");
    let (cvs, last) = word_chunks(words, full, 0, [UInt8::BYTE_0; 8], Blake3::iv(), final_length, tail_length, tail);
    match *cvs {
      Lists::Node::Nil => *last,
      _ => {
        let (left, right) = root(cvs);
        (Blake3::iv(), join(left, right), 64, 4)
      },
    }
  }

  inline fn hash_words(words: KzgIO::Words, length: Field, tail_length: Field, tail: [UInt8::U8; 3]) -> CV {
    let (cv, block, block_length, flags) = word_root(words, length, tail_length, tail);
    Blake3::compress_init(cv, block, [UInt8::BYTE_0; 8], block_length, flags + 8)
  }

  fn hash_input(input: KzgIO::Input, length: Field) -> CV {
    let (words, tail_length, tail) = aligned(input);
    hash_words(words, length, tail_length, tail)
  }

  fn xof96_words(words: KzgIO::Words, length: Field, tail_length: Field, tail: [UInt8::U8; 3]) -> (Block, CV) {
    let (cv, block, block_length, flags) = word_root(words, length, tail_length, tail);
    xof_output(cv, block, block_length, flags)
  }

  fn xof96(input: Bytes::Stream) -> (Block, CV) {
    let counter = [UInt8::BYTE_0;8];
    let (cv, reverse, length, flags, rest) = chunk(input, counter, 0, Blake3::iv());
    let last = last_block(reverse, length);
    match *rest {
      Lists::Node::Nil => xof_output(*cv, last, length, flags),
      _ => {
        let first = &(Blake3::compress_init(*cv, last, counter, length, flags));
        let (left, right) = root(&(Lists::Node::Cons(first, chunks(rest, UInt64::wrapping_succ(counter)))));
        xof_output(Blake3::iv(), join(left, right), 64, 4)
      },
    }
  }
}
⟧

end MultiStark.Source
