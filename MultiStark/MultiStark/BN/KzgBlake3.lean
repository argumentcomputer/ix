import Aiur.Modules.Frontend

/-! BLAKE3 XOF output with the same chunk tree and compression rounds as the
shared hash library. Root output descriptors retain the chaining value and
last block, because XOF blocks cannot be reconstructed from a 32-byte digest. -/
namespace MultiStark.Source

def kzgBlake3 : Aiur.Modules.Program Nat := aiur⟦
module KzgBlake3 {
  type U32 = UInt32::U32;
  type U64 = UInt64::U64;
  type CV = [U32; 8];
  type Block = [U32; 16];
  type Output = &(CV, Block, U64, Field, Field);

  fn rounds(stage: Field, state: [U32; 32]) -> [U32; 32] {
    match stage {
      7 => state,
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
    let state = rounds(0, [
      cv[0], cv[1], cv[2], cv[3], cv[4], cv[5], cv[6], cv[7],
      iv[0], iv[1], iv[2], iv[3], low, high, length_word, flags_word,
      block[0], block[1], block[2], block[3], block[4], block[5], block[6], block[7],
      block[8], block[9], block[10], block[11], block[12], block[13], block[14], block[15]
    ]);
    [UInt32::xor(state[0], state[8]), UInt32::xor(state[1], state[9]), UInt32::xor(state[2], state[10]), UInt32::xor(state[3], state[11]), UInt32::xor(state[4], state[12]), UInt32::xor(state[5], state[13]), UInt32::xor(state[6], state[14]), UInt32::xor(state[7], state[15]), UInt32::xor(state[8], cv[0]), UInt32::xor(state[9], cv[1]), UInt32::xor(state[10], cv[2]), UInt32::xor(state[11], cv[3]), UInt32::xor(state[12], cv[4]), UInt32::xor(state[13], cv[5]), UInt32::xor(state[14], cv[6]), UInt32::xor(state[15], cv[7])]
  }

  fn chaining(output: Output) -> CV {
    let (cv, block, counter, length, flags) = *output;
    Blake3::compress_init(cv, block, counter, length, flags)
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

  fn chunk(input: Bytes::Stream, counter: U64, index: Field, cv: CV) -> (Output, Bytes::Stream) {
    let (reverse, length, rest) = read_block(input, 0, &(Lists::Node::Nil));
    let block = Blake3::bytes_to_block(Blake3::pad_block(reverse, 64 - length));
    let start = Fields::is_zero(index);
    let last = 1 - (1 - Lists::is_empty(rest)) * (1 - Fields::is_zero(index - 15));
    match last {
      1 => (&(cv, block, counter, length, start + 2), rest),
      0 => chunk(rest, counter, index + 1, Blake3::compress_init(cv, block, counter, length, start)),
    }
  }

  fn chunks(input: Bytes::Stream, counter: U64) -> Lists::List<Output> {
    let (output, rest) = chunk(input, counter, 0, Blake3::iv());
    match *rest {
      Lists::Node::Nil => &(Lists::Node::Cons(output, &(Lists::Node::Nil))),
      _ => &(Lists::Node::Cons(output, chunks(rest, UInt64::wrapping_succ(counter)))),
    }
  }

  fn parent(left: Output, right: Output) -> Output {
    let a = chaining(left);
    let b = chaining(right);
    &(Blake3::iv(), [a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7],
      b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]], [UInt8::BYTE_0;8], 64, 4)
  }

  fn next_layer(layer: Lists::List<Output>) -> Lists::List<Output> {
    match *layer {
      Lists::Node::Nil => layer,
      Lists::Node::Cons(first, rest) => match *rest {
        Lists::Node::Nil => layer,
        Lists::Node::Cons(second, tail) => &(Lists::Node::Cons(parent(first, second), next_layer(tail))),
      },
    }
  }

  fn root(layer: Lists::List<Output>) -> Output {
    let Lists::Node::Cons(first, rest) = *layer;
    match *rest { Lists::Node::Nil => first, _ => root(next_layer(layer)) }
  }

  fn xof96(input: Bytes::Stream) -> (Block, CV) {
    let output = root(chunks(input, [UInt8::BYTE_0;8]));
    let (cv, block, _counter, length, flags) = *output;
    let first = compress_full(cv, block, [UInt8::BYTE_0;8], length, flags + 8);
    let second = compress_full(cv, block,
      [UInt8::BYTE_1, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0,
       UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0], length, flags + 8);
    (first, [second[0], second[1], second[2], second[3], second[4], second[5], second[6], second[7]])
  }
}
⟧

end MultiStark.Source
