import Aiur.Modules.Frontend

/-! # IxVM module `IxByteStream`

Byte streams read from the host's IO channels.

Formal Aiur source, written as Lean syntax (`aiur⟦ … ⟧`). `IxVM.source`
(`IxVM/IxVM/Program.lean`) composes the modules. -/

namespace IxVM.Source

def ixByteStream : Aiur.Modules.Program Nat := aiur⟦
module IxByteStream {
  -- Port divergence: bytes are typed hints, checked as bytes by `UInt8::from_field`.
  fn read_byte_stream(channel: Field, idx: Field, len: Field) -> Bytes::Stream {

          match len {
            0 => {  (&(Lists::Node::Nil)) } ,
            _ => {  let byte = hint::<Field>("ixvm.io.read", (channel, idx));
                 let tail = read_byte_stream(channel, idx + 1, len - 1);
                 (&(Lists::Node::Cons(UInt8::from_field(byte), tail))) } ,
          }
    }

  fn read_finite_byte_stream(channel: Field, idx: Field, len: Field) -> Bytes::Stream {
      let bytes = read_byte_stream(channel, idx, len);
      WordLists::depth_checked(bytes);
      bytes
    }
}
⟧

end IxVM.Source
