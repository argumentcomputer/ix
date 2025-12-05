import Ix.Aiur.Meta

namespace IxVM

def byteStream := ⟦
  enum ByteStream {
    Cons(G, &ByteStream),
    Nil
  }

  fn byte_stream_concat(as: ByteStream, bs: ByteStream) -> ByteStream {
    match as {
      ByteStream.Nil => bs,
      ByteStream.Cons(a, as_ptr) =>
        let concat = byte_stream_concat(load(as_ptr), bs);
        ByteStream.Cons(a, store(concat)),
    }
  }

  fn byte_stream_length(bytes: ByteStream) -> [G; 8] {
    match bytes {
      ByteStream.Nil => [0; 8],
      ByteStream.Cons(_, rest) => relaxed_u64_succ(byte_stream_length(load(rest))),
    }
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

end IxVM
