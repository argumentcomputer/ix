module
public import Ix.MultiStark.Verify.Codec.Wire

/-! Fixed-integer byte-format relations with explicit cursors and budgets.
Vector budgets are charged before any element is read/written. Every byte
step preserves the input/output metadata not named in its state update.
These relations describe bytes, integer digits, tags and ordered elements;
none calls a codec reader, writer, canonicalizer or acceptance bit. -/

public section
@[expose] section

namespace MultiStark.Verify.Protocol.Wire

open Codec.Wire (ReadState WriteState)

abbrev ReadRel (α : Type) := ReadState → α → ReadState → Prop
abbrev WriteRel (α : Type) := α → WriteState → WriteState → Prop

def LittleEndianBytes (width value : Nat) : Bytes :=
  (Array.range width).map (fun position => (value / 2 ^ (8 * position)).toUInt8)

def LittleEndianValue (bytes : List UInt8) : Nat :=
  bytes.foldr (fun byte tail => byte.toNat + 256 * tail) 0

def BytesRead (count : Nat) (state : ReadState) (bytes : Bytes) (final : ReadState) : Prop :=
  state.offset + count ≤ state.bytes.size ∧ state.bytes.extract state.offset (state.offset + count) = bytes ∧
    { state with offset := state.offset + count } = final

def ByteRead (state : ReadState) (byte : UInt8) (final : ReadState) : Prop :=
  state.bytes[state.offset]? = some byte ∧ { state with offset := state.offset + 1 } = final

def NatRead (width : Nat) (state : ReadState) (value : Nat) (final : ReadState) : Prop :=
  ∃ bytes, BytesRead width state bytes final ∧ LittleEndianValue bytes.toList = value

def BoolRead (state : ReadState) (value : Bool) (final : ReadState) : Prop :=
  ByteRead state (if value then 1 else 0) final

def FieldRead (state : ReadState) (value : Field) (final : ReadState) : Prop :=
  NatRead 8 state value.val final

def ExtRead (state : ReadState) (value : Ext) (final : ReadState) : Prop :=
  ∃ middle, FieldRead state value.c0 middle ∧ FieldRead middle value.c1 final

def DigestRead (state : ReadState) (value : Digest) (final : ReadState) : Prop :=
  BytesRead 32 state value.bytes final

def RepeatedRead {α : Type} (element : ReadRel α) : Nat → ReadRel (List α)
  | 0, state, [], final => state = final
  | count + 1, state, value :: values, final =>
    ∃ middle, element state value middle ∧ RepeatedRead element count middle values final
  | _, _, _, _ => False

def CountedRead {α : Type} (count : Nat) (element : ReadRel α) (state : ReadState) (values : Array α) (final : ReadState) : Prop :=
  count ≤ state.vectorLimit ∧ count ≤ state.items ∧
    RepeatedRead element count { state with items := state.items - count } values.toList final

def VectorRead {α : Type} (width : Nat) (element : ReadRel α) (state : ReadState) (values : Array α) (final : ReadState) : Prop :=
  ∃ count middle, NatRead width state count middle ∧ CountedRead count element middle values final

def OptionRead {α : Type} (element : ReadRel α) (state : ReadState) : Option α → ReadState → Prop
  | none, final => ByteRead state 0 final
  | some value, final => ∃ middle, ByteRead state 1 middle ∧ element middle value final

def Decoded {α : Type} (limits : DecodeLimits) (bytes : Bytes) (reader : ReadRel α) (value : α) : Prop :=
  bytes.size ≤ limits.bytes ∧ ∃ final,
    reader { bytes, vectorLimit := limits.vector, items := limits.items } value final ∧ final.offset = bytes.size

def BytesWritten (bytes : Bytes) (state final : WriteState) : Prop :=
  state.bytes.size + bytes.size ≤ state.limit ∧ { state with bytes := state.bytes ++ bytes } = final

def ByteWritten (byte : UInt8) (state final : WriteState) : Prop := BytesWritten #[byte] state final

def NatWritten (width value : Nat) (state final : WriteState) : Prop :=
  value < 2 ^ (8 * width) ∧ BytesWritten (LittleEndianBytes width value) state final

def BoolWritten (value : Bool) (state final : WriteState) : Prop :=
  ByteWritten (if value then 1 else 0) state final

def FieldWritten (value : Field) (state final : WriteState) : Prop := NatWritten 8 value.val state final

def ExtWritten (value : Ext) (state final : WriteState) : Prop :=
  ∃ middle, FieldWritten value.c0 state middle ∧ FieldWritten value.c1 middle final

def DigestWritten (value : Digest) (state final : WriteState) : Prop := BytesWritten value.bytes state final

def ListWritten {α : Type} (element : WriteRel α) : WriteRel (List α)
  | [], state, final => state = final
  | value :: values, state, final => ∃ middle, element value state middle ∧ ListWritten element values middle final

def CountedWritten {α : Type} (element : WriteRel α) (values : Array α) (state final : WriteState) : Prop :=
  values.size ≤ state.vectorLimit ∧ values.size ≤ state.items ∧
    ListWritten element values.toList { state with items := state.items - values.size } final

def VectorWritten {α : Type} (width : Nat) (element : WriteRel α) (values : Array α) (state final : WriteState) : Prop :=
  ∃ middle, NatWritten width values.size state middle ∧ CountedWritten element values middle final

def OptionWritten {α : Type} (element : WriteRel α) : WriteRel (Option α)
  | none, state, final => ByteWritten 0 state final
  | some value, state, final => ∃ middle, ByteWritten 1 state middle ∧ element value middle final

def Written (limits : DecodeLimits) (writer : WriteState → WriteState → Prop) (bytes : Bytes) : Prop :=
  ∃ final, writer { limit := limits.bytes, vectorLimit := limits.vector, items := limits.items } final ∧ final.bytes = bytes

end MultiStark.Verify.Protocol.Wire
