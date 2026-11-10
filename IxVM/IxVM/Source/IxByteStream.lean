import Aiur.Modules.Function

/-! # IxVM module `IxByteStream`

Byte streams read from the host's IO channels.

Named Aiur declarations, elaborated together by `IxVM.Program`. -/

namespace IxVM

aiur_module IxByteStream where

  -- Port divergence: bytes are typed hints, checked as bytes by `UInt8::from_field`.
def read_byte_stream := aiur_fn⟦
  fn read_byte_stream(channel: Field, idx: Field, len: Field) -> Bytes::Stream {

          match len {
            0 => {  (&(Lists::Node::Nil)) } ,
            _ => {  let byte = hint::<Field>("ixvm.io.read", (channel, idx));
                 let tail = read_byte_stream(channel, idx + 1, len - 1);
                 (&(Lists::Node::Cons(UInt8::from_field(byte), tail))) } ,
          }
    }
⟧

def read_finite_byte_stream := aiur_fn⟦
  fn read_finite_byte_stream(channel: Field, idx: Field, len: Field) -> Bytes::Stream {
      let bytes = read_byte_stream(channel, idx, len);
      WordLists::depth_checked(bytes);
      bytes
    }
⟧

end

end IxVM
