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
          _ => {
            let [byte] = hint::<[Field; 1]>("stark.io.read1", (channel, idx));
            let tail = read_byte_stream(channel, idx + 1, len - 1);
            (&(Lists::Node::Cons(UInt8::from_field(byte), tail))) } ,
        }
    }
}
⟧

end MultiStark.Source
