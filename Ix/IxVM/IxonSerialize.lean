import Ix.Aiur.Meta

namespace IxVM

set_option maxHeartbeats 2000000 in
def ixonSerialize := ⟦
  fn serialize(ixon: Ixon) -> ByteStream {
    let stream = ByteStream.Nil;
    match ixon {
      Ixon.NAnon => ByteStream.Cons(0x00, store(stream)),
      Ixon.NStr(Address.Bytes(a), Address.Bytes(b)) =>
        let tag = 0x01;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(b[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(a[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.NNum(Address.Bytes(a), Address.Bytes(b)) =>
        let tag = 0x02;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(b[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(a[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.UZero => ByteStream.Cons(0x03, store(stream)),
      Ixon.USucc(Address.Bytes(a)) =>
        let tag = 0x04;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(a[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.UMax(Address.Bytes(a), Address.Bytes(b)) =>
        let tag = 0x05;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(b[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(a[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.UIMax(Address.Bytes(a), Address.Bytes(b)) =>
        let tag = 0x06;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(b[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(a[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.ESort(Address.Bytes(a)) =>
        let tag = 0x80;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(a[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.EStr(Address.Bytes(n)) =>
        let tag = 0x81;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(n[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.ENat(Address.Bytes(a)) =>
        let tag = 0x82;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(a[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.EApp(Address.Bytes(a), Address.Bytes(b)) =>
        let tag = 0x83;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(b[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(a[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.ELam(Address.Bytes(a), Address.Bytes(b)) =>
        let tag = 0x84;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(b[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(a[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.EAll(Address.Bytes(a), Address.Bytes(b)) =>
        let tag = 0x85;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(b[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(a[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.ELet(bool, Address.Bytes(a), Address.Bytes(b), Address.Bytes(c)) =>
        let tag = 0x87 - bool;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(c[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(b[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(a[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.Eval(Address.Bytes(a), Address.Bytes(b), Address.Bytes(c), Address.Bytes(d)) =>
        let tag = 0xE1;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(d[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(c[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(b[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(a[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.Chck(Address.Bytes(a), Address.Bytes(b), Address.Bytes(c)) =>
        let tag = 0xE2;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(c[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(b[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(a[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.Comm(Address.Bytes(a), Address.Bytes(b)) =>
        let tag = 0xE3;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(b[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(a[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
      Ixon.Defn(def_kind, def_safety, Nat.Bytes(nat_bytes), Address.Bytes(addr1), Address.Bytes(addr2)) =>
        let tag = 0xA0;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(addr2[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(addr1[@i][@j], store(stream))));
        let nat_len = byte_stream_length(nat_bytes);
        let nat_flag = 0x9;
        let stream = byte_stream_concat(nat_bytes, stream);
        let (nat_tag, stream) = serialize_put_length(nat_flag, nat_len, stream);
        let stream = ByteStream.Cons(nat_tag, store(stream));
        let stream = serialize_put_def_safety(def_safety, stream);
        let stream = serialize_put_def_kind(def_kind, stream);
        ByteStream.Cons(tag, store(stream)),
      Ixon.Recr(k, is_unsafe, Nat.Bytes(nat_bytes1), Nat.Bytes(nat_bytes2), Nat.Bytes(nat_bytes3), Nat.Bytes(nat_bytes4), Nat.Bytes(nat_bytes5), Address.Bytes(addr), recursor_rules) =>
        let tag = 0xA1;
        let (rules_len, stream) = serialize_put_recursor_rules(recursor_rules, stream);
        let rules_flag = 0x9;
        let (rules_tag, stream) = serialize_put_length(rules_flag, rules_len, stream);
        let stream = ByteStream.Cons(rules_tag, store(stream));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(addr[@i][@j], store(stream))));
        let nat5_len = byte_stream_length(nat_bytes5);
        let nat_flag = 0x9;
        let stream = byte_stream_concat(nat_bytes5, stream);
        let (nat5_tag, stream) = serialize_put_length(nat_flag, nat5_len, stream);
        let stream = ByteStream.Cons(nat5_tag, store(stream));
        let nat4_len = byte_stream_length(nat_bytes4);
        let stream = byte_stream_concat(nat_bytes4, stream);
        let (nat4_tag, stream) = serialize_put_length(nat_flag, nat4_len, stream);
        let stream = ByteStream.Cons(nat4_tag, store(stream));
        let nat3_len = byte_stream_length(nat_bytes3);
        let stream = byte_stream_concat(nat_bytes3, stream);
        let (nat3_tag, stream) = serialize_put_length(nat_flag, nat3_len, stream);
        let stream = ByteStream.Cons(nat3_tag, store(stream));
        let nat2_len = byte_stream_length(nat_bytes2);
        let stream = byte_stream_concat(nat_bytes2, stream);
        let (nat2_tag, stream) = serialize_put_length(nat_flag, nat2_len, stream);
        let stream = ByteStream.Cons(nat2_tag, store(stream));
        let nat1_len = byte_stream_length(nat_bytes1);
        let stream = byte_stream_concat(nat_bytes1, stream);
        let (nat1_tag, stream) = serialize_put_length(nat_flag, nat1_len, stream);
        let stream = ByteStream.Cons(nat1_tag, store(stream));
        let packed_bools = pack_2_bools(k, is_unsafe);
        let stream = ByteStream.Cons(packed_bools, store(stream));
        ByteStream.Cons(tag, store(stream)),
      Ixon.Axio(is_unsafe, Nat.Bytes(nat_bytes), Address.Bytes(addr)) =>
        let tag = 0xA2;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(addr[@i][@j], store(stream))));
        let nat_len = byte_stream_length(nat_bytes);
        let nat_flag = 0x9;
        let stream = byte_stream_concat(nat_bytes, stream);
        let (nat_tag, stream) = serialize_put_length(nat_flag, nat_len, stream);
        let stream = ByteStream.Cons(nat_tag, store(stream));
        let stream = ByteStream.Cons(is_unsafe, store(stream));
        ByteStream.Cons(tag, store(stream)),
      Ixon.Quot(quot_kind, Nat.Bytes(nat_bytes), Address.Bytes(addr)) =>
        let tag = 0xA3;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(addr[@i][@j], store(stream))));
        let nat_len = byte_stream_length(nat_bytes);
        let nat_flag = 0x9;
        let stream = byte_stream_concat(nat_bytes, stream);
        let (nat_tag, stream) = serialize_put_length(nat_flag, nat_len, stream);
        let stream = ByteStream.Cons(nat_tag, store(stream));
        let stream = serialize_put_quot_kind(quot_kind, stream);
        ByteStream.Cons(tag, store(stream)),
      Ixon.CPrj(Nat.Bytes(nat_bytes1), Nat.Bytes(nat_bytes2), Address.Bytes(addr)) =>
        let tag = 0xA4;
        let nat_flag = 0x9;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(addr[@i][@j], store(stream))));
        let nat2_len = byte_stream_length(nat_bytes2);
        let stream = byte_stream_concat(nat_bytes2, stream);
        let (nat2_tag, stream) = serialize_put_length(nat_flag, nat2_len, stream);
        let stream = ByteStream.Cons(nat2_tag, store(stream));
        let nat1_len = byte_stream_length(nat_bytes1);
        let stream = byte_stream_concat(nat_bytes1, stream);
        let (nat1_tag, stream) = serialize_put_length(nat_flag, nat1_len, stream);
        let stream = ByteStream.Cons(nat1_tag, store(stream));
        ByteStream.Cons(tag, store(stream)),
      Ixon.RPrj(Nat.Bytes(nat_bytes), Address.Bytes(addr)) =>
        let tag = 0xA5;
        let nat_flag = 0x9;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(addr[@i][@j], store(stream))));
        let nat_len = byte_stream_length(nat_bytes);
        let stream = byte_stream_concat(nat_bytes, stream);
        let (nat_tag, stream) = serialize_put_length(nat_flag, nat_len, stream);
        let stream = ByteStream.Cons(nat_tag, store(stream));
        ByteStream.Cons(tag, store(stream)),
      Ixon.IPrj(Nat.Bytes(nat_bytes), Address.Bytes(addr)) =>
        let tag = 0xA6;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(addr[@i][@j], store(stream))));
        let nat_len = byte_stream_length(nat_bytes);
        let nat_flag = 0x9;
        let stream = byte_stream_concat(nat_bytes, stream);
        let (nat_tag, stream) = serialize_put_length(nat_flag, nat_len, stream);
        let stream = ByteStream.Cons(nat_tag, store(stream));
        ByteStream.Cons(tag, store(stream)),
      Ixon.DPrj(Nat.Bytes(nat_bytes), Address.Bytes(addr)) =>
        let tag = 0xA7;
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(addr[@i][@j], store(stream))));
        let nat_len = byte_stream_length(nat_bytes);
        let nat_flag = 0x9;
        let stream = byte_stream_concat(nat_bytes, stream);
        let (nat_tag, stream) = serialize_put_length(nat_flag, nat_len, stream);
        let stream = ByteStream.Cons(nat_tag, store(stream));
        ByteStream.Cons(tag, store(stream)),
      Ixon.Blob(bytes) =>
        let len = byte_stream_length(bytes);
        let flag = 0x9;
        let (tag, stream) = serialize_put_length(flag, len, bytes);
        ByteStream.Cons(tag, store(stream)),
      Ixon.UVar(Nat.Bytes(bytes)) =>
        let len = byte_stream_length(bytes);
        let flag = 0x1;
        let (tag, stream) = serialize_put_length(flag, len, bytes);
        ByteStream.Cons(tag, store(stream)),
      Ixon.EVar(Nat.Bytes(bytes)) =>
        let len: [G; 8] = byte_stream_length(bytes);
        let flag = 0x2;
        let (tag, stream) = serialize_put_length(flag, len, bytes);
        ByteStream.Cons(tag, store(stream)),
      Ixon.Muts(mut_consts) =>
        let (len, stream) = serialize_put_mut_consts(mut_consts, stream);
        let flag = 0xB;
        let (tag, stream) = serialize_put_length(flag, len, stream);
        ByteStream.Cons(tag, store(stream)),
      Ixon.ERef(Address.Bytes(a), addresses) =>
        let (len, stream) = serialize_put_addresses(addresses, stream);
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(a[@i][@j], store(stream))));
        let flag = 0x3;
        let (tag, stream) = serialize_put_length(flag, len, stream);
        ByteStream.Cons(tag, store(stream)),
      Ixon.ERec(Nat.Bytes(n), addresses) =>
        let flag = 0x4;
        let (address_len, stream) = serialize_put_addresses(addresses, stream);
        let (tag, stream) = serialize_put_length(flag, address_len, stream);
        let blob_len = byte_stream_length(n);
        let blob_flag = 0x9;
        let stream = byte_stream_concat(n, stream);
        let (blob_tag, stream) = serialize_put_length(blob_flag, blob_len, stream);
        let stream = ByteStream.Cons(blob_tag, store(stream));
        ByteStream.Cons(tag, store(stream)),
      Ixon.EPrj(Address.Bytes(a), Nat.Bytes(n), Address.Bytes(b)) =>
        let flag = 0x5;
        let len = byte_stream_length(n);
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(b[@i][@j], store(stream))));
        let stream = byte_stream_concat(n, stream);
        let (tag, stream) = serialize_put_length(flag, len, stream);
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(a[@i][@j], store(stream))));
        ByteStream.Cons(tag, store(stream)),
    }
  }

  fn serialize_put_addresses(addresses: AddressList, stream: ByteStream) -> ([G; 8], ByteStream) {
    match addresses {
      AddressList.Nil => ([0; 8], stream),
      AddressList.Cons(Address.Bytes(a), rest_ptr) =>
        let (len, stream) = serialize_put_addresses(load(rest_ptr), stream);
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(a[@i][@j], store(stream))));
        (relaxed_u64_succ(len), stream),
    }
  }

  fn serialize_put_length(flag: G, len: [G; 8], stream: ByteStream) -> (G, ByteStream) {
    match len {
      [b1, 0, 0, 0, 0, 0, 0, 0] =>
        -- 248 is minus 8 in u8
        let (_, large) = u8_add(b1, 248);
        match large {
          0 =>
            let tag = encode_tag_head(flag, 0, b1);
            (tag, stream),
          1 =>
            let tag = encode_tag_head(flag, 1, 0);
            (tag, ByteStream.Cons(b1, store(stream))),
        },
      [_, _, 0, 0, 0, 0, 0, 0] =>
        let tag = encode_tag_head(flag, 1, 1);
        (tag, fold(2..0, stream, |stream, @i| ByteStream.Cons(len[@i], store(stream)))),
      [_, _, _, 0, 0, 0, 0, 0] =>
        let tag = encode_tag_head(flag, 1, 2);
        (tag, fold(3..0, stream, |stream, @i| ByteStream.Cons(len[@i], store(stream)))),
      [_, _, _, _, 0, 0, 0, 0] =>
        let tag = encode_tag_head(flag, 1, 3);
        (tag, fold(4..0, stream, |stream, @i| ByteStream.Cons(len[@i], store(stream)))),
      [_, _, _, _, _, 0, 0, 0] =>
        let tag = encode_tag_head(flag, 1, 4);
        (tag, fold(5..0, stream, |stream, @i| ByteStream.Cons(len[@i], store(stream)))),
      [_, _, _, _, _, _, 0, 0] =>
        let tag = encode_tag_head(flag, 1, 5);
        (tag, fold(6..0, stream, |stream, @i| ByteStream.Cons(len[@i], store(stream)))),
      [_, _, _, _, _, _, _, 0] =>
        let tag = encode_tag_head(flag, 1, 6);
        (tag, fold(7..0, stream, |stream, @i| ByteStream.Cons(len[@i], store(stream)))),
      [_, _, _, _, _, _, _, _] =>
        let tag = encode_tag_head(flag, 1, 7);
        (tag, fold(8..0, stream, |stream, @i| ByteStream.Cons(len[@i], store(stream)))),
    }
  }

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

  fn pack_2_bools(a: G, b: G) -> G {
    match (a, b) {
      (0, 0) => 0,
      (1, 0) => 2,
      (0, 1) => 1,
      (1, 1) => 3,
    }
  }

  fn pack_3_bools(a: G, b: G, c: G) -> G {
    match (a, b, c) {
      (0, 0, 0) => 0,
      (1, 0, 0) => 2,
      (0, 1, 0) => 1,
      (1, 1, 0) => 3,
      (0, 0, 1) => 4,
      (1, 0, 1) => 5,
      (0, 1, 1) => 6,
      (1, 1, 1) => 7,
    }
  }

  fn serialize_put_def_kind(def_kind: DefKind, stream: ByteStream) -> ByteStream {
    match def_kind {
      DefKind.Definition => ByteStream.Cons(0, store(stream)),
      DefKind.Opaque => ByteStream.Cons(1, store(stream)),
      DefKind.Theorem => ByteStream.Cons(2, store(stream)),
    }
  }

  fn serialize_put_def_safety(def_safety: DefinitionSafety, stream: ByteStream) -> ByteStream {
    match def_safety {
      DefinitionSafety.Unsafe => ByteStream.Cons(0, store(stream)),
      DefinitionSafety.Safe => ByteStream.Cons(1, store(stream)),
      DefinitionSafety.Partial => ByteStream.Cons(2, store(stream)),
    }
  }

  fn serialize_put_quot_kind(quot_kind: QuotKind, stream: ByteStream) -> ByteStream {
    match quot_kind {
      QuotKind.Typ => ByteStream.Cons(0, store(stream)),
      QuotKind.Ctor => ByteStream.Cons(1, store(stream)),
      QuotKind.Lift => ByteStream.Cons(2, store(stream)),
      QuotKind.Ind => ByteStream.Cons(3, store(stream)),
    }
  }

  fn serialize_put_recursor_rules(rules: RecursorRuleList, stream: ByteStream) -> ([G; 8], ByteStream) {
    match rules {
      RecursorRuleList.Nil => ([0; 8], stream),
      RecursorRuleList.Cons(Nat.Bytes(nat_bytes), Address.Bytes(addr), rest_ptr) =>
        let (len, stream) = serialize_put_recursor_rules(load(rest_ptr), stream);
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(addr[@i][@j], store(stream))));
        let nat_len = byte_stream_length(nat_bytes);
        let nat_flag = 0x9;
        let stream = byte_stream_concat(nat_bytes, stream);
        let (nat_tag, stream) = serialize_put_length(nat_flag, nat_len, stream);
        let stream = ByteStream.Cons(nat_tag, store(stream));
        (relaxed_u64_succ(len), stream),
    }
  }

  fn serialize_put_constructors(constructors: ConstructorList, stream: ByteStream) -> ([G; 8], ByteStream) {
    match constructors {
      ConstructorList.Nil => ([0; 8], stream),
      ConstructorList.Cons(is_unsafe, Nat.Bytes(nat_bytes1), Nat.Bytes(nat_bytes2), Nat.Bytes(nat_bytes3), Nat.Bytes(nat_bytes4), Address.Bytes(addr), rest_ptr) =>
        let (len, stream) = serialize_put_constructors(load(rest_ptr), stream);
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(addr[@i][@j], store(stream))));
        let nat4_len = byte_stream_length(nat_bytes4);
        let nat_flag = 0x9;
        let stream = byte_stream_concat(nat_bytes4, stream);
        let (nat4_tag, stream) = serialize_put_length(nat_flag, nat4_len, stream);
        let stream = ByteStream.Cons(nat4_tag, store(stream));
        let nat3_len = byte_stream_length(nat_bytes3);
        let stream = byte_stream_concat(nat_bytes3, stream);
        let (nat3_tag, stream) = serialize_put_length(nat_flag, nat3_len, stream);
        let stream = ByteStream.Cons(nat3_tag, store(stream));
        let nat2_len = byte_stream_length(nat_bytes2);
        let stream = byte_stream_concat(nat_bytes2, stream);
        let (nat2_tag, stream) = serialize_put_length(nat_flag, nat2_len, stream);
        let stream = ByteStream.Cons(nat2_tag, store(stream));
        let nat1_len = byte_stream_length(nat_bytes1);
        let stream = byte_stream_concat(nat_bytes1, stream);
        let (nat1_tag, stream) = serialize_put_length(nat_flag, nat1_len, stream);
        let stream = ByteStream.Cons(nat1_tag, store(stream));
        let stream = ByteStream.Cons(is_unsafe, store(stream));
        (relaxed_u64_succ(len), stream),
    }
  }

  fn serialize_put_mut_consts(mut_consts: MutConstList, stream: ByteStream) -> ([G; 8], ByteStream) {
    match mut_consts {
      MutConstList.Nil => ([0; 8], stream),
      MutConstList.ConsDefn(def_kind, def_safety, Nat.Bytes(nat_bytes), Address.Bytes(addr1), Address.Bytes(addr2), rest_ptr) =>
        let (len, stream) = serialize_put_mut_consts(load(rest_ptr), stream);
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(addr2[@i][@j], store(stream))));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(addr1[@i][@j], store(stream))));
        let nat_len = byte_stream_length(nat_bytes);
        let nat_flag = 0x9;
        let stream = byte_stream_concat(nat_bytes, stream);
        let (nat_tag, stream) = serialize_put_length(nat_flag, nat_len, stream);
        let stream = ByteStream.Cons(nat_tag, store(stream));
        let stream = serialize_put_def_safety(def_safety, stream);
        let stream = serialize_put_def_kind(def_kind, stream);
        let stream = ByteStream.Cons(0, store(stream));
        (relaxed_u64_succ(len), stream),
      MutConstList.ConsIndc(recr, refl, is_unsafe, Nat.Bytes(nat_bytes1), Nat.Bytes(nat_bytes2), Nat.Bytes(nat_bytes3), Nat.Bytes(nat_bytes4), Address.Bytes(addr), constructors, rest_ptr) =>
        let (len, stream) = serialize_put_mut_consts(load(rest_ptr), stream);
        let (constructors_len, stream) = serialize_put_constructors(constructors, stream);
        let constructors_flag = 0x9;
        let (constructors_tag, stream) = serialize_put_length(constructors_flag, constructors_len, stream);
        let stream = ByteStream.Cons(constructors_tag, store(stream));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(addr[@i][@j], store(stream))));
        let nat4_len = byte_stream_length(nat_bytes4);
        let nat_flag = 0x9;
        let stream = byte_stream_concat(nat_bytes4, stream);
        let (nat4_tag, stream) = serialize_put_length(nat_flag, nat4_len, stream);
        let stream = ByteStream.Cons(nat4_tag, store(stream));
        let nat3_len = byte_stream_length(nat_bytes3);
        let stream = byte_stream_concat(nat_bytes3, stream);
        let (nat3_tag, stream) = serialize_put_length(nat_flag, nat3_len, stream);
        let stream = ByteStream.Cons(nat3_tag, store(stream));
        let nat2_len = byte_stream_length(nat_bytes2);
        let stream = byte_stream_concat(nat_bytes2, stream);
        let (nat2_tag, stream) = serialize_put_length(nat_flag, nat2_len, stream);
        let stream = ByteStream.Cons(nat2_tag, store(stream));
        let nat1_len = byte_stream_length(nat_bytes1);
        let stream = byte_stream_concat(nat_bytes1, stream);
        let (nat1_tag, stream) = serialize_put_length(nat_flag, nat1_len, stream);
        let stream = ByteStream.Cons(nat1_tag, store(stream));
        let packed_bools = pack_3_bools(recr, refl, is_unsafe);
        let stream = ByteStream.Cons(packed_bools, store(stream));
        let stream = ByteStream.Cons(1, store(stream));
        (relaxed_u64_succ(len), stream),
      MutConstList.ConsRecr(k, is_unsafe, Nat.Bytes(nat_bytes1), Nat.Bytes(nat_bytes2), Nat.Bytes(nat_bytes3), Nat.Bytes(nat_bytes4), Nat.Bytes(nat_bytes5), Address.Bytes(addr), recursor_rules, rest_ptr) =>
        let (len, stream) = serialize_put_mut_consts(load(rest_ptr), stream);
        let (rules_len, stream) = serialize_put_recursor_rules(recursor_rules, stream);
        let rules_flag = 0x9;
        let (rules_tag, stream) = serialize_put_length(rules_flag, rules_len, stream);
        let stream = ByteStream.Cons(rules_tag, store(stream));
        let stream = fold(8..0, stream, |stream, @i|
          fold(4..0, stream, |stream, @j| ByteStream.Cons(addr[@i][@j], store(stream))));
        let nat5_len = byte_stream_length(nat_bytes5);
        let nat_flag = 0x9;
        let stream = byte_stream_concat(nat_bytes5, stream);
        let (nat5_tag, stream) = serialize_put_length(nat_flag, nat5_len, stream);
        let stream = ByteStream.Cons(nat5_tag, store(stream));
        let nat4_len = byte_stream_length(nat_bytes4);
        let stream = byte_stream_concat(nat_bytes4, stream);
        let (nat4_tag, stream) = serialize_put_length(nat_flag, nat4_len, stream);
        let stream = ByteStream.Cons(nat4_tag, store(stream));
        let nat3_len = byte_stream_length(nat_bytes3);
        let stream = byte_stream_concat(nat_bytes3, stream);
        let (nat3_tag, stream) = serialize_put_length(nat_flag, nat3_len, stream);
        let stream = ByteStream.Cons(nat3_tag, store(stream));
        let nat2_len = byte_stream_length(nat_bytes2);
        let stream = byte_stream_concat(nat_bytes2, stream);
        let (nat2_tag, stream) = serialize_put_length(nat_flag, nat2_len, stream);
        let stream = ByteStream.Cons(nat2_tag, store(stream));
        let nat1_len = byte_stream_length(nat_bytes1);
        let stream = byte_stream_concat(nat_bytes1, stream);
        let (nat1_tag, stream) = serialize_put_length(nat_flag, nat1_len, stream);
        let stream = ByteStream.Cons(nat1_tag, store(stream));
        let packed_bools = pack_2_bools(k, is_unsafe);
        let stream = ByteStream.Cons(packed_bools, store(stream));
        let stream = ByteStream.Cons(2, store(stream));
        (relaxed_u64_succ(len), stream),
    }
  }
⟧

end IxVM
