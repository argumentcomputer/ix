import Aiur.Modules.Frontend

/-! # MultiStark module `StarkIO`

Byte streams read from the host's IO channels.

Formal Aiur source, written as Lean syntax (`aiur⟦ … ⟧`). `MultiStark.recursionSource`
and `MultiStark.aggregateSource` (`MultiStark/MultiStark/Program.lean`) compose the modules. -/

namespace MultiStark.Source

def starkIO : Aiur.Modules.Program Nat := aiur⟦
module StarkIO {
  fn read_byte_stream(channel: Field, idx: Field, len: Field) -> Bytes::Stream {
      match len {
        0 => {  (&(Lists::Node::Nil)) } ,
        1 | 2 | 3 | 4 | 5 | 6 | 7 => {
          let [byte] = hint::<[Field; 1]>("stark.io.read1", (channel, idx));
          let tail = read_byte_stream(channel, idx + 1, len - 1);
          (&(Lists::Node::Cons(UInt8::from_field(byte), tail))) } ,
        _ => {
          let [b0, b1, b2, b3, b4, b5, b6, b7] = hint::<[Field; 8]>("stark.io.read8", (channel, idx));
          let (c0, c1) = UInt8::from_fields(b0, b1);
          let (c2, c3) = UInt8::from_fields(b2, b3);
          let (c4, c5) = UInt8::from_fields(b4, b5);
          let (c6, c7) = UInt8::from_fields(b6, b7);
          let tail = read_byte_stream(channel, idx + 8, len - 8);
          (&(Lists::Node::Cons(c0, (&(Lists::Node::Cons(c1, (&(Lists::Node::Cons(c2,
          (&(Lists::Node::Cons(c3, (&(Lists::Node::Cons(c4, (&(Lists::Node::Cons(c5,
          (&(Lists::Node::Cons(c6, (&(Lists::Node::Cons(c7, tail)))))))))))))))))))))))) } ,
      }
    }
}
⟧

end MultiStark.Source
