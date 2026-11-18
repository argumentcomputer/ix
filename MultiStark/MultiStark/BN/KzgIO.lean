import Aiur.Modules.Frontend

/-! Strict canonical byte ingress for the BN254 verifier. Structural integers
are u32 little-endian; field values are canonical 32-byte little-endian Fr.
Advice never decides canonicality or performs proof verification. -/
namespace MultiStark.Source

def kzgIO : Aiur.Modules.Program Nat := aiur⟦
module KzgIO {
  type Digest = [Field; 8];

  type U8 = UInt8::U8;
  type U32 = UInt32::U32;
  type Words = Lists::List<U32>;

  -- A byte stream read from the front: a word list and the offset (0..3) of
  -- the next byte in its first word. Bytes before that offset are not part
  -- of the stream. Every byte is a checked `U8`, and the stream ends exactly
  -- where its word list does, so a read past the end fails.
  type Input = (Words, Field);

  fn read_words(channel: Field, remaining: Field, offset: Field) -> Words {
    match remaining {
      0 => &(Lists::Node::Nil),
      _ => {
        let word = UInt32::from_fields(hint::<[Field; 4]>("kzg.io.read4", (channel, offset)));
        &(Lists::Node::Cons(word, read_words(channel, remaining - 1, offset + 4)))
      },
    }
  }

  inline fn read_byte(channel: Field, offset: Field) -> U8 {
    UInt8::from_field(hint::<Field>("kzg.io.read1", (channel, offset)))
  }

  -- `count = 4 * words + lead`. `lead` must be 0..3; any other advice makes
  -- `words` a field element far beyond every finite stream, so the word reads
  -- that follow cannot terminate.
  fn split4(count: Field) -> (Field, Field) {
    let words = hint::<Field>("kzg.io.div", (count, 4));
    let lead = count - 4 * words;
    match lead { 0 => (words, 0), 1 => (words, 1), 2 => (words, 2), 3 => (words, 3) }
  }

  -- The first `count mod 4` bytes end the first word, so the rest is whole words.
  fn sized_channel(channel: Field) -> (Input, Field) {
    let length = hint::<Field>("kzg.io.length", channel);
    assert_eq!(UInt32::less_than_fields(length, 67108865), 1, "KZG input exceeds 64 MiB");
    let (words, lead) = split4(length);
    let zero = UInt8::BYTE_0;
    let input = match lead {
      0 => (read_words(channel, words, 0), 0),
      1 => (&(Lists::Node::Cons(UInt32::from_bytes([zero, zero, zero, read_byte(channel, 0)]), read_words(channel, words, 1))), 3),
      2 => (&(Lists::Node::Cons(UInt32::from_bytes([zero, zero, read_byte(channel, 0), read_byte(channel, 1)]), read_words(channel, words, 2))), 2),
      3 => (&(Lists::Node::Cons(UInt32::from_bytes([zero, read_byte(channel, 0), read_byte(channel, 1), read_byte(channel, 2)]), read_words(channel, words, 3))), 1),
    };
    (input, length)
  }

  inline fn channel(channel: Field) -> Input {
    let (input, _length) = sized_channel(channel); input
  }

  fn byte(input: Input) -> (U8, Input) {
    let (words, offset) = input;
    let Lists::Node::Cons(w, rest) = *words; let w = UInt32::to_bytes(w);
    match offset {
      0 => (w[0], (words, 1)),
      1 => (w[1], (words, 2)),
      2 => (w[2], (words, 3)),
      3 => (w[3], (rest, 0)),
    }
  }

  inline fn tag(input: Input) -> (Field, Input) {
    let (value, rest) = byte(input);
    (UInt8::to_field(value), rest)
  }

  inline fn word(input: Input) -> (U32, Input) {
    let (words, offset) = input;
    let Lists::Node::Cons(w, rest) = *words;
    match offset {
      0 => (w, (rest, 0)),
      _ => {
        let Lists::Node::Cons(v, _next) = *rest;
        let w = UInt32::to_bytes(w); let v = UInt32::to_bytes(v);
        match offset {
          1 => (UInt32::from_bytes([w[1], w[2], w[3], v[0]]), (rest, 1)),
          2 => (UInt32::from_bytes([w[2], w[3], v[0], v[1]]), (rest, 2)),
          3 => (UInt32::from_bytes([w[3], v[0], v[1], v[2]]), (rest, 3)),
        }
      },
    }
  }

  fn u32(input: Input) -> (Field, Input) {
    let (w, rest) = word(input);
    (UInt32::compact_field(UInt32::compact(w)), rest)
  }

  fn next_word(input: Input) -> (U32, Input) { word(input) }

  -- 32 bytes: eight words, or nine when the stream is not word aligned.
  fn read32(input: Input) -> ([U8; 32], Input) {
    let (words, offset) = input;
    let Lists::Node::Cons(w0, l) = *words; let Lists::Node::Cons(w1, l) = *l;
    let Lists::Node::Cons(w2, l) = *l; let Lists::Node::Cons(w3, l) = *l;
    let Lists::Node::Cons(w4, l) = *l; let Lists::Node::Cons(w5, l) = *l;
    let Lists::Node::Cons(w6, l) = *l; let Lists::Node::Cons(w7, l) = *l;
    let w0 = UInt32::to_bytes(w0); let w1 = UInt32::to_bytes(w1); let w2 = UInt32::to_bytes(w2); let w3 = UInt32::to_bytes(w3);
    let w4 = UInt32::to_bytes(w4); let w5 = UInt32::to_bytes(w5); let w6 = UInt32::to_bytes(w6); let w7 = UInt32::to_bytes(w7);
    match offset {
      0 => ([w0[0], w0[1], w0[2], w0[3], w1[0], w1[1], w1[2], w1[3], w2[0], w2[1], w2[2], w2[3], w3[0], w3[1], w3[2], w3[3], w4[0], w4[1], w4[2], w4[3], w5[0], w5[1], w5[2], w5[3], w6[0], w6[1], w6[2], w6[3], w7[0], w7[1], w7[2], w7[3]], (l, 0)),
      _ => {
        let Lists::Node::Cons(w8, _next) = *l; let w8 = UInt32::to_bytes(w8);
        match offset {
          1 => ([w0[1], w0[2], w0[3], w1[0], w1[1], w1[2], w1[3], w2[0], w2[1], w2[2], w2[3], w3[0], w3[1], w3[2], w3[3], w4[0], w4[1], w4[2], w4[3], w5[0], w5[1], w5[2], w5[3], w6[0], w6[1], w6[2], w6[3], w7[0], w7[1], w7[2], w7[3], w8[0]], (l, 1)),
          2 => ([w0[2], w0[3], w1[0], w1[1], w1[2], w1[3], w2[0], w2[1], w2[2], w2[3], w3[0], w3[1], w3[2], w3[3], w4[0], w4[1], w4[2], w4[3], w5[0], w5[1], w5[2], w5[3], w6[0], w6[1], w6[2], w6[3], w7[0], w7[1], w7[2], w7[3], w8[0], w8[1]], (l, 2)),
          3 => ([w0[3], w1[0], w1[1], w1[2], w1[3], w2[0], w2[1], w2[2], w2[3], w3[0], w3[1], w3[2], w3[3], w4[0], w4[1], w4[2], w4[3], w5[0], w5[1], w5[2], w5[3], w6[0], w6[1], w6[2], w6[3], w7[0], w7[1], w7[2], w7[3], w8[0], w8[1], w8[2]], (l, 3)),
        }
      },
    }
  }

  fn copy_words(input: Input, count: Field) -> (Words, Input) {
    match count {
      0 => (&(Lists::Node::Nil), input),
      _ => {
        let (head, input) = next_word(input);
        let (tail, rest) = copy_words(input, count - 1);
        (&(Lists::Node::Cons(head, tail)), rest)
      },
    }
  }

  -- The next `count` bytes as a stream of their own.
  fn read_bytes(input: Input, count: Field) -> (Input, Input) {
    let (words, lead) = split4(count);
    let zero = UInt8::BYTE_0;
    match lead {
      0 => {let (body, rest) = copy_words(input, words); ((body, 0), rest)},
      1 => {
        let (a, input) = byte(input);
        let (body, rest) = copy_words(input, words);
        ((&(Lists::Node::Cons(UInt32::from_bytes([zero, zero, zero, a]), body)), 3), rest)
      },
      2 => {
        let (a, input) = byte(input); let (b, input) = byte(input);
        let (body, rest) = copy_words(input, words);
        ((&(Lists::Node::Cons(UInt32::from_bytes([zero, zero, a, b]), body)), 2), rest)
      },
      3 => {
        let (a, input) = byte(input); let (b, input) = byte(input); let (c, input) = byte(input);
        let (body, rest) = copy_words(input, words);
        ((&(Lists::Node::Cons(UInt32::from_bytes([zero, a, b, c]), body)), 1), rest)
      },
    }
  }

  inline fn blob(input: Input) -> (Input, Input) {
    let (count, input) = u32(input);
    read_bytes(input, count)
  }

  inline fn finish(input: Input) -> () {
    let (words, offset) = input; assert_eq!(offset, 0, "KZG trailing bytes"); let Lists::Node::Nil = *words; ()
  }

  fn equal_bytes(a: Input, b: Input) -> () {
    let (x, i) = a; let (y, j) = b;
    match (*x, *y) {
      (Lists::Node::Nil, Lists::Node::Nil) => {assert_eq!(i, 0, "KZG byte mismatch"); assert_eq!(j, 0, "KZG byte mismatch"); ()},
      _ => match i + 4 * j {
        0 => {
          let Lists::Node::Cons(p, xs) = *x; let Lists::Node::Cons(q, ys) = *y;
          assert_eq!(UInt32::compact_field(UInt32::compact(p)), UInt32::compact_field(UInt32::compact(q)), "KZG byte mismatch");
          equal_bytes((xs, 0), (ys, 0))
        },
        _ => {
          let (p, a) = byte(a); let (q, b) = byte(b);
          assert_eq!(UInt8::to_field(p), UInt8::to_field(q), "KZG byte mismatch");
          equal_bytes(a, b)
        },
      },
    }
  }

  inline fn magic(input: Input, expected: [Field; 8]) -> Input {
    let (low, input) = next_word(input); let low = UInt32::to_bytes(low);
    let (high, input) = next_word(input); let high = UInt32::to_bytes(high);
    assert_eq!([UInt8::to_field(low[0]), UInt8::to_field(low[1]), UInt8::to_field(low[2]), UInt8::to_field(low[3]),
      UInt8::to_field(high[0]), UInt8::to_field(high[1]), UInt8::to_field(high[2]), UInt8::to_field(high[3])],
      expected, "KZG wire version mismatch");
    input
  }

  -- Prepends the 32 bytes as eight words.
  inline fn prepend_words32(bytes: [U8; 32], tail: Words) -> Words {
    let tail = &(Lists::Node::Cons(UInt32::from_bytes([bytes[28], bytes[29], bytes[30], bytes[31]]), tail));
    let tail = &(Lists::Node::Cons(UInt32::from_bytes([bytes[24], bytes[25], bytes[26], bytes[27]]), tail));
    let tail = &(Lists::Node::Cons(UInt32::from_bytes([bytes[20], bytes[21], bytes[22], bytes[23]]), tail));
    let tail = &(Lists::Node::Cons(UInt32::from_bytes([bytes[16], bytes[17], bytes[18], bytes[19]]), tail));
    let tail = &(Lists::Node::Cons(UInt32::from_bytes([bytes[12], bytes[13], bytes[14], bytes[15]]), tail));
    let tail = &(Lists::Node::Cons(UInt32::from_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]), tail));
    let tail = &(Lists::Node::Cons(UInt32::from_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]), tail));
    &(Lists::Node::Cons(UInt32::from_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]), tail))
  }

  fn scalar_from_bytes(bytes: [UInt8::U8; 32]) -> Field {
    let a0 = 1 * UInt8::to_field(bytes[0]) + 256 * UInt8::to_field(bytes[1]) + 65536 * UInt8::to_field(bytes[2]) + 16777216 * UInt8::to_field(bytes[3]) + 4294967296 * UInt8::to_field(bytes[4]) + 1099511627776 * UInt8::to_field(bytes[5]) + 281474976710656 * UInt8::to_field(bytes[6]) + 72057594037927936 * UInt8::to_field(bytes[7]) + 18446744073709551616 * UInt8::to_field(bytes[8]) + 4722366482869645213696 * UInt8::to_field(bytes[9]);
    let a1 = 1 * UInt8::to_field(bytes[10]) + 256 * UInt8::to_field(bytes[11]) + 65536 * UInt8::to_field(bytes[12]) + 16777216 * UInt8::to_field(bytes[13]) + 4294967296 * UInt8::to_field(bytes[14]) + 1099511627776 * UInt8::to_field(bytes[15]) + 281474976710656 * UInt8::to_field(bytes[16]) + 72057594037927936 * UInt8::to_field(bytes[17]) + 18446744073709551616 * UInt8::to_field(bytes[18]) + 4722366482869645213696 * UInt8::to_field(bytes[19]);
    let a2 = 1 * UInt8::to_field(bytes[20]) + 256 * UInt8::to_field(bytes[21]) + 65536 * UInt8::to_field(bytes[22]) + 16777216 * UInt8::to_field(bytes[23]) + 4294967296 * UInt8::to_field(bytes[24]) + 1099511627776 * UInt8::to_field(bytes[25]) + 281474976710656 * UInt8::to_field(bytes[26]) + 72057594037927936 * UInt8::to_field(bytes[27]) + 18446744073709551616 * UInt8::to_field(bytes[28]) + 4722366482869645213696 * UInt8::to_field(bytes[29]);
    let a3 = 1 * UInt8::to_field(bytes[30]) + 256 * UInt8::to_field(bytes[31]);
    let raw = [a0, a1, a2, a3];
    let (difference, borrow) = hint::<([Field; 4], [Field; 4])>("kzg.fr.canonical", raw);
    BN254Fq::bound(difference);
    assert_eq!(borrow[0] * (borrow[0] - 1), 0, "KZG Fr borrow");
    assert_eq!(531584715432774185517056 - raw[0] - 0 + 1208925819614629174706176 * borrow[0], difference[0], "KZG Fr canonical subtraction");
    assert_eq!(borrow[1] * (borrow[1] - 1), 0, "KZG Fr borrow");
    assert_eq!(611571273565344341981625 - raw[1] - borrow[0] + 1208925819614629174706176 * borrow[1], difference[1], "KZG Fr canonical subtraction");
    assert_eq!(borrow[2] * (borrow[2] - 1), 0, "KZG Fr borrow");
    assert_eq!(370463741415268654532022 - raw[2] - borrow[1] + 1208925819614629174706176 * borrow[2], difference[2], "KZG Fr canonical subtraction");
    assert_eq!(borrow[3] * (borrow[3] - 1), 0, "KZG Fr borrow");
    assert_eq!(12388 - raw[3] - borrow[2] + 1208925819614629174706176 * borrow[3], difference[3], "KZG Fr canonical subtraction");
    assert_eq!(borrow[3], 0, "noncanonical KZG Fr encoding");
    1 * raw[0] + 1208925819614629174706176 * raw[1] + 1461501637330902918203684832716283019655932542976 * raw[2] + 1766847064778384329583297500742918515827483896875618958121606201292619776 * raw[3]
  }

  fn scalar_bytes(value: Field) -> [UInt8::U8; 32] {
    let bytes = Blake3::address_from_fields(hint::<[Field; 32]>("kzg.scalar_bytes", value));
    assert_eq!(scalar_from_bytes(bytes), value, "KZG Fr byte recomposition");
    bytes
  }

  fn scalar(input: Input) -> (Field, Input) {
    let (bytes, rest) = read32(input);
    (scalar_from_bytes(bytes), rest)
  }

  fn point(input: Input) -> (BN254G1::Point, Input) {
    let (bytes, rest) = read32(input);
    (BN254G1::from_bytes(Blake3::address_to_fields(bytes)), rest)
  }

  fn digest(input: Input) -> (Digest, Input) {
    let (bytes, rest) = read32(input);
    ([Blake3::pack_word(UInt32::from_bytes(bytes[0 .. 4])), Blake3::pack_word(UInt32::from_bytes(bytes[4 .. 8])), Blake3::pack_word(UInt32::from_bytes(bytes[8 .. 12])), Blake3::pack_word(UInt32::from_bytes(bytes[12 .. 16])), Blake3::pack_word(UInt32::from_bytes(bytes[16 .. 20])), Blake3::pack_word(UInt32::from_bytes(bytes[20 .. 24])), Blake3::pack_word(UInt32::from_bytes(bytes[24 .. 28])), Blake3::pack_word(UInt32::from_bytes(bytes[28 .. 32]))], rest)
  }

  inline fn digest_word(value: Field) -> UInt32::U32 {
    let word = UInt32::from_field(value);
    assert_eq!(Blake3::pack_word(word), value, "KZG digest word exceeds u32");
    word
  }

  inline fn digest_bytes(value: Digest) -> [UInt8::U8; 32] {
    Blake3::digest_bytes([digest_word(value[0]), digest_word(value[1]), digest_word(value[2]), digest_word(value[3]), digest_word(value[4]), digest_word(value[5]), digest_word(value[6]), digest_word(value[7])])
  }

  inline fn prepend4(bytes: [UInt8::U8;4], tail: Bytes::Stream) -> Bytes::Stream {
    &(Lists::Node::Cons(bytes[0],&(Lists::Node::Cons(bytes[1],&(Lists::Node::Cons(bytes[2],&(Lists::Node::Cons(bytes[3],tail))))))))
  }

  inline fn prepend8(bytes: [UInt8::U8; 8], tail: Bytes::Stream) -> Bytes::Stream {
    let tail = &(Lists::Node::Cons(bytes[7], tail));
    let tail = &(Lists::Node::Cons(bytes[6], tail));
    let tail = &(Lists::Node::Cons(bytes[5], tail));
    let tail = &(Lists::Node::Cons(bytes[4], tail));
    let tail = &(Lists::Node::Cons(bytes[3], tail));
    let tail = &(Lists::Node::Cons(bytes[2], tail));
    let tail = &(Lists::Node::Cons(bytes[1], tail));
    let tail = &(Lists::Node::Cons(bytes[0], tail));
    tail
  }

  inline fn prepend32(bytes: [UInt8::U8; 32], tail: Bytes::Stream) -> Bytes::Stream {
    let tail = &(Lists::Node::Cons(bytes[31], tail));
    let tail = &(Lists::Node::Cons(bytes[30], tail));
    let tail = &(Lists::Node::Cons(bytes[29], tail));
    let tail = &(Lists::Node::Cons(bytes[28], tail));
    let tail = &(Lists::Node::Cons(bytes[27], tail));
    let tail = &(Lists::Node::Cons(bytes[26], tail));
    let tail = &(Lists::Node::Cons(bytes[25], tail));
    let tail = &(Lists::Node::Cons(bytes[24], tail));
    let tail = &(Lists::Node::Cons(bytes[23], tail));
    let tail = &(Lists::Node::Cons(bytes[22], tail));
    let tail = &(Lists::Node::Cons(bytes[21], tail));
    let tail = &(Lists::Node::Cons(bytes[20], tail));
    let tail = &(Lists::Node::Cons(bytes[19], tail));
    let tail = &(Lists::Node::Cons(bytes[18], tail));
    let tail = &(Lists::Node::Cons(bytes[17], tail));
    let tail = &(Lists::Node::Cons(bytes[16], tail));
    let tail = &(Lists::Node::Cons(bytes[15], tail));
    let tail = &(Lists::Node::Cons(bytes[14], tail));
    let tail = &(Lists::Node::Cons(bytes[13], tail));
    let tail = &(Lists::Node::Cons(bytes[12], tail));
    let tail = &(Lists::Node::Cons(bytes[11], tail));
    let tail = &(Lists::Node::Cons(bytes[10], tail));
    let tail = &(Lists::Node::Cons(bytes[9], tail));
    let tail = &(Lists::Node::Cons(bytes[8], tail));
    let tail = &(Lists::Node::Cons(bytes[7], tail));
    let tail = &(Lists::Node::Cons(bytes[6], tail));
    let tail = &(Lists::Node::Cons(bytes[5], tail));
    let tail = &(Lists::Node::Cons(bytes[4], tail));
    let tail = &(Lists::Node::Cons(bytes[3], tail));
    let tail = &(Lists::Node::Cons(bytes[2], tail));
    let tail = &(Lists::Node::Cons(bytes[1], tail));
    let tail = &(Lists::Node::Cons(bytes[0], tail));
    tail
  }

  fn fields_to_bytes(values: Lists::List<Field>) -> Bytes::Stream {
    match *values {
      Lists::Node::Nil => &(Lists::Node::Nil),
      Lists::Node::Cons(value, rest) => &(Lists::Node::Cons(UInt8::from_field(value), fields_to_bytes(rest))),
    }
  }
}
⟧

end MultiStark.Source
