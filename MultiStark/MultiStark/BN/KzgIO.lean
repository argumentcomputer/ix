import Aiur.Modules.Frontend

/-! Strict canonical byte ingress for the BN254 verifier. Structural integers
are u32 little-endian; field values are canonical 32-byte little-endian Fr.
Advice never decides canonicality or performs proof verification. -/
namespace MultiStark.Source

def kzgIO : Aiur.Modules.Program Nat := aiur⟦
module KzgIO {
  type Digest = [Field; 8];

  fn read_stream(channel: Field, remaining: Field, offset: Field) -> Bytes::Stream {
    match remaining {
      0 => &(Lists::Node::Nil),
      _ => {
        let byte = UInt8::from_field(hint::<Field>("kzg.io.read1", (channel, offset)));
        &(Lists::Node::Cons(byte, read_stream(channel, remaining - 1, offset + 1)))
      },
    }
  }

  fn channel(channel: Field) -> Bytes::Stream {
    let length = hint::<Field>("kzg.io.length", channel);
    assert_eq!(UInt32::less_than_fields(length, 67108865), 1, "KZG input exceeds 64 MiB");
    read_stream(channel, length, 0)
  }

  fn byte(input: Bytes::Stream) -> (UInt8::U8, Bytes::Stream) {
    let Lists::Node::Cons(value, rest) = *input;
    (value, rest)
  }

  inline fn tag(input: Bytes::Stream) -> (Field, Bytes::Stream) {
    let (value, rest) = byte(input);
    (UInt8::to_field(value), rest)
  }

  fn u32(input: Bytes::Stream) -> (Field, Bytes::Stream) {
    let (a, input) = byte(input); let (b, input) = byte(input);
    let (c, input) = byte(input); let (d, input) = byte(input);
    (UInt8::to_field(a) + 256 * UInt8::to_field(b) + 65536 * UInt8::to_field(c) + 16777216 * UInt8::to_field(d), input)
  }

  fn read_bytes(input: Bytes::Stream, count: Field) -> (Bytes::Stream, Bytes::Stream) {
    match count {
      0 => (&(Lists::Node::Nil), input),
      _ => {
        let (head, input) = byte(input);
        let (tail, rest) = read_bytes(input, count - 1);
        (&(Lists::Node::Cons(head, tail)), rest)
      },
    }
  }

  fn blob(input: Bytes::Stream) -> (Bytes::Stream, Bytes::Stream) {
    let (count, input) = u32(input);
    read_bytes(input, count)
  }

  fn finish(input: Bytes::Stream) -> () { let Lists::Node::Nil = *input; () }

  fn equal_bytes(a: Bytes::Stream, b: Bytes::Stream) -> () {
    match (*a, *b) {
      (Lists::Node::Nil, Lists::Node::Nil) => (),
      (Lists::Node::Cons(x, xs), Lists::Node::Cons(y, ys)) => {
        assert_eq!(UInt8::to_field(x), UInt8::to_field(y), "KZG byte mismatch");
        equal_bytes(xs, ys)
      },
    }
  }

  fn magic(input: Bytes::Stream, expected: [Field; 8]) -> Bytes::Stream {
    let (b0, input) = tag(input);
    let (b1, input) = tag(input);
    let (b2, input) = tag(input);
    let (b3, input) = tag(input);
    let (b4, input) = tag(input);
    let (b5, input) = tag(input);
    let (b6, input) = tag(input);
    let (b7, input) = tag(input);
    assert_eq!([b0, b1, b2, b3, b4, b5, b6, b7], expected, "KZG wire version mismatch");
    input
  }

  fn read32(input: Bytes::Stream) -> ([UInt8::U8; 32], Bytes::Stream) {
    let (b0, input) = byte(input);
    let (b1, input) = byte(input);
    let (b2, input) = byte(input);
    let (b3, input) = byte(input);
    let (b4, input) = byte(input);
    let (b5, input) = byte(input);
    let (b6, input) = byte(input);
    let (b7, input) = byte(input);
    let (b8, input) = byte(input);
    let (b9, input) = byte(input);
    let (b10, input) = byte(input);
    let (b11, input) = byte(input);
    let (b12, input) = byte(input);
    let (b13, input) = byte(input);
    let (b14, input) = byte(input);
    let (b15, input) = byte(input);
    let (b16, input) = byte(input);
    let (b17, input) = byte(input);
    let (b18, input) = byte(input);
    let (b19, input) = byte(input);
    let (b20, input) = byte(input);
    let (b21, input) = byte(input);
    let (b22, input) = byte(input);
    let (b23, input) = byte(input);
    let (b24, input) = byte(input);
    let (b25, input) = byte(input);
    let (b26, input) = byte(input);
    let (b27, input) = byte(input);
    let (b28, input) = byte(input);
    let (b29, input) = byte(input);
    let (b30, input) = byte(input);
    let (b31, input) = byte(input);
    ([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31], input)
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

  fn scalar(input: Bytes::Stream) -> (Field, Bytes::Stream) {
    let (bytes, rest) = read32(input);
    (scalar_from_bytes(bytes), rest)
  }

  fn point(input: Bytes::Stream) -> (BN254G1::Point, Bytes::Stream) {
    let (bytes, rest) = read32(input);
    (BN254G1::from_bytes(Blake3::address_to_fields(bytes)), rest)
  }

  fn digest(input: Bytes::Stream) -> (Digest, Bytes::Stream) {
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
