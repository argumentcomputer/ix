import Ix.Aiur.Meta

namespace IxVM

set_option maxHeartbeats 2000000 in
def ixonDeserialize := ⟦
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
          Tag4.Mk(0x1, size) =>
            let (bytes, _) = deserialize_byte_stream(stream, [0; 8], size);
            Ixon.UVar(Nat.Bytes(bytes)),
          Tag4.Mk(0x2, size) =>
            let (bytes, _) = deserialize_byte_stream(stream, [0; 8], size);
            Ixon.EVar(Nat.Bytes(bytes)),
          Tag4.Mk(0x3, size) =>
            let (addr, tail) = deserialize_addr(stream, [[0; 4]; 8], 0);
            let (addresses, _) = deserialize_addr_list(tail, [0; 8], size);
            Ixon.ERef(Address.Bytes(addr), addresses),
          Tag4.Mk(0x4, size) =>
            let (nat_tag, tail) = deserialize_tag(stream);
            let Tag4.Mk(0x9, nat_size) = nat_tag;
            let (nat_bytes, tail) = deserialize_byte_stream(tail, [0; 8], nat_size);
            let (addresses, _) = deserialize_addr_list(tail, [0; 8], size);
            Ixon.ERec(Nat.Bytes(nat_bytes), addresses),
          Tag4.Mk(0x5, size) =>
            let (addr1, tail) = deserialize_addr(stream, [[0; 4]; 8], 0);
            let (nat_bytes, tail) = deserialize_byte_stream(tail, [0; 8], size);
            let (addr2, _) = deserialize_addr(tail, [[0; 4]; 8], 0);
            Ixon.EPrj(Address.Bytes(addr1), Nat.Bytes(nat_bytes), Address.Bytes(addr2)),
          Tag4.Mk(0x9, size) =>
            let (bytes, _) = deserialize_byte_stream(stream, [0; 8], size);
            Ixon.Blob(bytes),
        },
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
  fn deserialize_addr_list(stream: ByteStream, count: [G; 8], size: [G; 8]) -> (AddressList, ByteStream) {
    match (size[0]-count[0], size[1]-count[1], size[2]-count[2], size[3]-count[3],
           size[4]-count[4], size[5]-count[5], size[6]-count[6], size[7]-count[7]) {
      (0, 0, 0, 0, 0, 0, 0, 0) => (AddressList.Nil, stream),
      _ =>
        let (addr_bytes, tail) = deserialize_addr(stream, [[0; 4]; 8], 0);
        let (tail_de, tail) = deserialize_addr_list(
          tail,
          relaxed_u64_succ(count),
          size
        );
        let addr_head = Address.Bytes(addr_bytes);
        (AddressList.Cons(addr_head, store(tail_de)), tail),
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
      1 =>
        let ByteStream.Cons(b0, tail_ptr) = stream;
        (set(u64, 0, b0), load(tail_ptr)),
      2 =>
        let ByteStream.Cons(b0, tail_ptr) = stream;
        let ByteStream.Cons(b1, tail_ptr) = load(tail_ptr);
        let u64 = set(u64, 0, b0);
        (set(u64, 1, b1), load(tail_ptr)),
      3 =>
        let ByteStream.Cons(b0, tail_ptr) = stream;
        let ByteStream.Cons(b1, tail_ptr) = load(tail_ptr);
        let ByteStream.Cons(b2, tail_ptr) = load(tail_ptr);
        let u64 = set(u64, 0, b0);
        let u64 = set(u64, 1, b1);
        (set(u64, 2, b2), load(tail_ptr)),
      4 =>
        let ByteStream.Cons(b0, tail_ptr) = stream;
        let ByteStream.Cons(b1, tail_ptr) = load(tail_ptr);
        let ByteStream.Cons(b2, tail_ptr) = load(tail_ptr);
        let ByteStream.Cons(b3, tail_ptr) = load(tail_ptr);
        let u64 = set(u64, 0, b0);
        let u64 = set(u64, 1, b1);
        let u64 = set(u64, 2, b2);
        (set(u64, 3, b3), load(tail_ptr)),
      5 =>
        let ByteStream.Cons(b0, tail_ptr) = stream;
        let ByteStream.Cons(b1, tail_ptr) = load(tail_ptr);
        let ByteStream.Cons(b2, tail_ptr) = load(tail_ptr);
        let ByteStream.Cons(b3, tail_ptr) = load(tail_ptr);
        let ByteStream.Cons(b4, tail_ptr) = load(tail_ptr);
        let u64 = set(u64, 0, b0);
        let u64 = set(u64, 1, b1);
        let u64 = set(u64, 2, b2);
        let u64 = set(u64, 3, b3);
        (set(u64, 4, b4), load(tail_ptr)),
      6 =>
        let ByteStream.Cons(b0, tail_ptr) = stream;
        let ByteStream.Cons(b1, tail_ptr) = load(tail_ptr);
        let ByteStream.Cons(b2, tail_ptr) = load(tail_ptr);
        let ByteStream.Cons(b3, tail_ptr) = load(tail_ptr);
        let ByteStream.Cons(b4, tail_ptr) = load(tail_ptr);
        let ByteStream.Cons(b5, tail_ptr) = load(tail_ptr);
        let u64 = set(u64, 0, b0);
        let u64 = set(u64, 1, b1);
        let u64 = set(u64, 2, b2);
        let u64 = set(u64, 3, b3);
        let u64 = set(u64, 4, b4);
        (set(u64, 5, b5), load(tail_ptr)),
      7 =>
        let ByteStream.Cons(b0, tail_ptr) = stream;
        let ByteStream.Cons(b1, tail_ptr) = load(tail_ptr);
        let ByteStream.Cons(b2, tail_ptr) = load(tail_ptr);
        let ByteStream.Cons(b3, tail_ptr) = load(tail_ptr);
        let ByteStream.Cons(b4, tail_ptr) = load(tail_ptr);
        let ByteStream.Cons(b5, tail_ptr) = load(tail_ptr);
        let ByteStream.Cons(b6, tail_ptr) = load(tail_ptr);
        let u64 = set(u64, 0, b0);
        let u64 = set(u64, 1, b1);
        let u64 = set(u64, 2, b2);
        let u64 = set(u64, 3, b3);
        let u64 = set(u64, 4, b4);
        let u64 = set(u64, 5, b5);
        (set(u64, 6, b6), load(tail_ptr)),
      8 =>
        let ByteStream.Cons(b0, tail_ptr) = stream;
        let ByteStream.Cons(b1, tail_ptr) = load(tail_ptr);
        let ByteStream.Cons(b2, tail_ptr) = load(tail_ptr);
        let ByteStream.Cons(b3, tail_ptr) = load(tail_ptr);
        let ByteStream.Cons(b4, tail_ptr) = load(tail_ptr);
        let ByteStream.Cons(b5, tail_ptr) = load(tail_ptr);
        let ByteStream.Cons(b6, tail_ptr) = load(tail_ptr);
        let ByteStream.Cons(b7, tail_ptr) = load(tail_ptr);
        let u64 = set(u64, 0, b0);
        let u64 = set(u64, 1, b1);
        let u64 = set(u64, 2, b2);
        let u64 = set(u64, 3, b3);
        let u64 = set(u64, 4, b4);
        let u64 = set(u64, 5, b5);
        let u64 = set(u64, 6, b6);
        (set(u64, 7, b7), load(tail_ptr)),
    }
  }
⟧

end IxVM
