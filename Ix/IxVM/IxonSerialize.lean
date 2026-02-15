import Ix.Aiur.Meta

namespace IxVM

def ixonSerialize := ⟦
  fn put_u64_le(bs: [G; 8], num_bytes: G) -> ByteStream {
    match num_bytes {
      0 => ByteStream.Nil,
      _ =>
        let [b1, b2, b3, b4, b5, b6, b7, b8] = bs;
        let rest = [b2, b3, b4, b5, b6, b7, b8, 0];
        ByteStream.Cons(b1, store(put_u64_le(rest, num_bytes - 1))),
    }
  }

  fn put_tag0(bs: [G; 8]) -> ByteStream {
    let byte_count = u64_byte_count(bs);
    let small = u8_less_than(bs[0], 128);
    match (byte_count, small) {
      (1, 1) => ByteStream.Cons(bs[0], store(ByteStream.Nil)),
      _ =>
        let head = 128 + (byte_count - 1);
        ByteStream.Cons(head, store(put_u64_le(bs, byte_count))),
    }
  }

  fn put_tag4(flag: G, bs: [G; 8]) -> ByteStream {
    let byte_count = u64_byte_count(bs);
    let small = u8_less_than(bs[0], 8);
    match (byte_count, small) {
      (1, 1) =>
        let head = flag * 16 + bs[0];
        ByteStream.Cons(head, store(ByteStream.Nil)),
      _ =>
        let head = flag * 16 + 8 + (byte_count - 1);
        let bs_bytes = put_u64_le(bs, byte_count);
        ByteStream.Cons(head, store(bs_bytes)),
    }
  }
⟧
end IxVM
