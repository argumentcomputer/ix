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

  -- A stream of fewer than 2^32 bytes. `read_byte_stream` builds exactly `len` bytes by its own
  -- recursion, so the bound is a range check of `len` (the comparison checks both operands below
  -- 2^32). This replaces a walk of the stream (`WordLists::depth_checked`, one row per byte), which
  -- was needed while the stream was unconstrained advice that could be cyclic (#648); the formal
  -- program has no unconstrained calls.

def read_finite_byte_stream := aiur_fn⟦
  fn read_finite_byte_stream(channel: Field, idx: Field, len: Field) -> Bytes::Stream {
      match UInt32::less_than_fields(0, len) {
        0 => {  (&(Lists::Node::Nil)) } ,
        _ => {  read_byte_stream(channel, idx, len) } ,
      }
    }
⟧

end

end IxVM
