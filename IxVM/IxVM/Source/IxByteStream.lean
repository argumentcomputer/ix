import Aiur.Modules.Function

/-! # IxVM module `IxByteStream`

Byte streams read from the host's IO channels.

Named Aiur declarations, elaborated together by `IxVM.Program`. -/

namespace IxVM

aiur_module IxByteStream where

  -- Port divergence: bytes are typed hints, checked as bytes by `UInt8::from_field`, or two at a
  -- time by `UInt8::from_fields` (one lookup in the byte-pair table). Four bytes per row; the last
  -- 0 to 3 bytes of a stream take one row.
def read_byte_stream := aiur_fn⟦
  fn read_byte_stream(channel: Field, idx: Field, len: Field) -> Bytes::Stream {
      match len {
        0 => {  (&(Lists::Node::Nil)) } ,
        1 => {
          let b0 = hint::<Field>("ixvm.io.read", (channel, idx));
          (&(Lists::Node::Cons(UInt8::from_field(b0), (&(Lists::Node::Nil))))) } ,
        2 => {
          let b0 = hint::<Field>("ixvm.io.read", (channel, idx));
          let b1 = hint::<Field>("ixvm.io.read", (channel, idx + 1));
          let (u0, u1) = UInt8::from_fields(b0, b1);
          (&(Lists::Node::Cons(u0, (&(Lists::Node::Cons(u1, (&(Lists::Node::Nil)))))))) } ,
        3 => {
          let b0 = hint::<Field>("ixvm.io.read", (channel, idx));
          let b1 = hint::<Field>("ixvm.io.read", (channel, idx + 1));
          let b2 = hint::<Field>("ixvm.io.read", (channel, idx + 2));
          let (u0, u1) = UInt8::from_fields(b0, b1);
          (&(Lists::Node::Cons(u0, (&(Lists::Node::Cons(u1,
            (&(Lists::Node::Cons(UInt8::from_field(b2), (&(Lists::Node::Nil))))))))))) } ,
        _ => {
          let b0 = hint::<Field>("ixvm.io.read", (channel, idx));
          let b1 = hint::<Field>("ixvm.io.read", (channel, idx + 1));
          let b2 = hint::<Field>("ixvm.io.read", (channel, idx + 2));
          let b3 = hint::<Field>("ixvm.io.read", (channel, idx + 3));
          let (u0, u1) = UInt8::from_fields(b0, b1);
          let (u2, u3) = UInt8::from_fields(b2, b3);
          let tail = read_byte_stream(channel, idx + 4, len - 4);
          (&(Lists::Node::Cons(u0, (&(Lists::Node::Cons(u1,
            (&(Lists::Node::Cons(u2, (&(Lists::Node::Cons(u3, tail)))))))))))) } ,
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
