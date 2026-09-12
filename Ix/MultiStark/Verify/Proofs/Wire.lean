module
public import Ix.MultiStark.Verify.Protocol.Wire
public import Ix.MultiStark.Verify.Proofs.Basic

public section

namespace MultiStark.Verify.Proofs

open Codec.Wire (ReadState WriteState)

theorem littleEndian_refines (width value : Nat) :
    Codec.Wire.littleEndian width value = Protocol.Wire.LittleEndianBytes width value := by
  simp only [Codec.Wire.littleEndian, Protocol.Wire.LittleEndianBytes, Nat.shiftRight_eq_div_pow]

theorem fromLittleEndian_refines (bytes : Bytes) :
    Codec.Wire.fromLittleEndian bytes = Protocol.Wire.LittleEndianValue bytes.toList := rfl

theorem littleEndianValue_bounded (bytes : List UInt8) :
    Protocol.Wire.LittleEndianValue bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => simp [Protocol.Wire.LittleEndianValue]
  | cons byte bytes ih =>
    have byteBound := byte.toNat_lt
    simp only [Protocol.Wire.LittleEndianValue, List.foldr_cons, List.length_cons, Nat.pow_succ]
    change Protocol.Wire.LittleEndianValue bytes < 256 ^ bytes.length at ih
    change byte.toNat < 256 at byteBound
    change byte.toNat + 256 * Protocol.Wire.LittleEndianValue bytes < 256 ^ bytes.length * 256
    omega

theorem bytesRead_size (count : Nat) (state final : ReadState) (bytes : Bytes)
    (read : Protocol.Wire.BytesRead count state bytes final) : bytes.size = count := by
  obtain ⟨bound, rfl, _⟩ := read
  simp only [Array.size_extract, Nat.min_eq_left bound, Nat.add_sub_cancel_left]

theorem natRead_bounded (width : Nat) (state final : ReadState) (value : Nat)
    (read : Protocol.Wire.NatRead width state value final) : value < 2 ^ (8 * width) := by
  obtain ⟨bytes, read, rfl⟩ := read
  have bound := littleEndianValue_bounded bytes.toList
  simpa only [Array.length_toList, bytesRead_size width state final bytes read, Nat.pow_mul] using bound

theorem readBytes_refines (count : Nat) (state final : ReadState) (bytes : Bytes) :
    (Codec.Wire.readBytes count).run state = .ok (bytes, final) ↔ Protocol.Wire.BytesRead count state bytes final := by
  simp only [Codec.Wire.readBytes, StateT.run, bind_ok_iff, unit_exists_iff, ensure_ok_iff,
    decide_eq_true_eq, pure_ok_iff, Prod.mk.injEq, Protocol.Wire.BytesRead]

theorem readByte_refines (state final : ReadState) (byte : UInt8) :
    Codec.Wire.readByte.run state = .ok (byte, final) ↔ Protocol.Wire.ByteRead state byte final := by
  unfold Codec.Wire.readByte StateT.run Protocol.Wire.ByteRead
  cases lookup : state.bytes[state.offset]? <;> simp [lookup]

theorem readTag_refines (expected : UInt8) (state final : ReadState) :
    (Codec.Wire.readTag expected).run state = .ok ((), final) ↔ Protocol.Wire.ByteRead state expected final := by
  simp only [Codec.Wire.readTag, StateT.run, bind_ok_iff, Prod.exists, unit_exists_iff,
    ensure_ok_iff, beq_iff_eq, pure_ok_iff, Prod.mk.injEq, true_and]
  constructor
  · rintro ⟨actual, middle, read, rfl, rfl⟩
    exact (readByte_refines state middle actual).mp read
  · intro read
    exact ⟨expected, final, (readByte_refines state final expected).mpr read, rfl, rfl⟩

theorem readNat_refines (width : Nat) (state final : ReadState) (value : Nat) :
    (Codec.Wire.readNat width).run state = .ok (value, final) ↔ Protocol.Wire.NatRead width state value final := by
  simp only [Codec.Wire.readNat, action_bind_ok_iff, action_pure_ok_iff, readBytes_refines,
    fromLittleEndian_refines, Protocol.Wire.NatRead]
  constructor
  · rintro ⟨bytes, middle, read, equal, rfl⟩
    exact ⟨bytes, read, equal⟩
  · rintro ⟨bytes, read, equal⟩
    exact ⟨bytes, final, read, equal, rfl⟩

theorem readBool_refines (state final : ReadState) (value : Bool) :
    Codec.Wire.readBool.run state = .ok (value, final) ↔ Protocol.Wire.BoolRead state value final := by
  simp only [Codec.Wire.readBool, action_bind_ok_iff, readByte_refines, Protocol.Wire.BoolRead]
  constructor
  · rintro ⟨byte, middle, read, accepted⟩
    split at accepted
    · simp only [action_pure_ok_iff] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      exact read
    · simp only [action_pure_ok_iff] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      exact read
    · simp [action_throw_ok_iff] at accepted
  · intro read
    cases value <;> exact ⟨_, final, read, by rfl⟩

theorem readField_refines (state final : ReadState) (value : Field) :
    Codec.Wire.readField.run state = .ok (value, final) ↔ Protocol.Wire.FieldRead state value final := by
  simp only [Codec.Wire.readField, action_bind_ok_iff, readNat_refines, Protocol.Wire.FieldRead]
  constructor
  · rintro ⟨word, middle, read, accepted⟩
    split at accepted
    · simp only [action_pure_ok_iff] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      exact read
    · simp [action_throw_ok_iff] at accepted
  · intro read
    refine ⟨value.val, final, read, ?_⟩
    simp [value.isLt, pure_ok_iff]

theorem readExt_refines (state final : ReadState) (value : Ext) :
    Codec.Wire.readExt.run state = .ok (value, final) ↔ Protocol.Wire.ExtRead state value final := by
  cases value
  simp only [Codec.Wire.readExt, action_bind_ok_iff, action_pure_ok_iff, readField_refines,
    Ix.Ixby.ExtGoldilocks.mk.injEq, Protocol.Wire.ExtRead]
  constructor
  · rintro ⟨c0, middle, first, c1, last, second, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨middle, first, second⟩
  · rintro ⟨middle, first, second⟩
    exact ⟨_, middle, first, _, final, second, ⟨rfl, rfl⟩, rfl⟩

theorem readDigest_refines (state final : ReadState) (value : Digest) :
    Codec.Wire.readDigest.run state = .ok (value, final) ↔ Protocol.Wire.DigestRead state value final := by
  simp only [Codec.Wire.readDigest, action_bind_ok_iff, readBytes_refines, Protocol.Wire.DigestRead]
  constructor
  · rintro ⟨bytes, middle, read, accepted⟩
    split at accepted
    · simp only [action_pure_ok_iff] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      exact read
    · simp [action_throw_ok_iff] at accepted
  · intro read
    refine ⟨value.bytes, final, read, ?_⟩
    simp [value.size, pure_ok_iff]

theorem readRepeatedFrom_refines {α : Type} (element : Codec.Wire.Reader α) (spec : Protocol.Wire.ReadRel α)
    (refines : ∀ state value final, element.run state = .ok (value, final) ↔ spec state value final)
    (count : Nat) (reversed : List α) (state final : ReadState) (result : List α) :
    (Codec.Wire.readRepeatedFrom element count reversed).run state = .ok (result, final) ↔
      ∃ values, Protocol.Wire.RepeatedRead spec count state values final ∧ reversed.reverse ++ values = result := by
  induction count generalizing reversed state final result with
  | zero =>
    simp only [Codec.Wire.readRepeatedFrom, action_pure_ok_iff]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨[], rfl, by simp⟩
    · rintro ⟨values, read, same⟩
      cases values with
      | nil => exact ⟨by simpa using same, read⟩
      | cons _ _ => cases read
  | succ count ih =>
    simp only [Codec.Wire.readRepeatedFrom, action_bind_ok_iff, refines, ih]
    constructor
    · rintro ⟨value, middle, read, rest, tail, same⟩
      exact ⟨value :: rest, ⟨middle, read, tail⟩, by simpa using same⟩
    · rintro ⟨values, read, same⟩
      cases values with
      | nil => cases read
      | cons value rest =>
        obtain ⟨middle, read, tail⟩ := read
        exact ⟨value, middle, read, rest, tail, by simpa using same⟩

theorem readRepeated_refines {α : Type} (element : Codec.Wire.Reader α) (spec : Protocol.Wire.ReadRel α)
    (refines : ∀ state value final, element.run state = .ok (value, final) ↔ spec state value final)
    (count : Nat) (state final : ReadState) (values : List α) :
    (Codec.Wire.readRepeated element count).run state = .ok (values, final) ↔
      Protocol.Wire.RepeatedRead spec count state values final := by
  simpa only [Codec.Wire.readRepeated, List.reverse_nil, List.nil_append, exists_eq_right] using
    readRepeatedFrom_refines element spec refines count [] state final values

theorem readCounted_refines {α : Type} (element : Codec.Wire.Reader α) (spec : Protocol.Wire.ReadRel α)
    (refines : ∀ state value final, element.run state = .ok (value, final) ↔ spec state value final)
    (count : Nat) (state final : ReadState) (values : Array α) :
    (Codec.Wire.readCounted count element).run state = .ok (values, final) ↔
      Protocol.Wire.CountedRead count spec state values final := by
  simp only [Codec.Wire.readCounted, StateT.run, bind_ok_iff, unit_exists_iff, ensure_ok_iff,
    decide_eq_true_eq, Prod.exists,
    pure_ok_iff, Prod.mk.injEq, Protocol.Wire.CountedRead]
  constructor
  · rintro ⟨vectorBound, itemBound, list, last, read, rfl, rfl⟩
    exact ⟨vectorBound, itemBound, by simpa using (readRepeated_refines element spec refines count _ _ _).mp read⟩
  · rintro ⟨vectorBound, itemBound, read⟩
    exact ⟨vectorBound, itemBound, values.toList, final,
      (readRepeated_refines element spec refines count _ _ _).mpr read, by simp, rfl⟩

theorem readVectorWidth_refines {α : Type} (element : Codec.Wire.Reader α) (spec : Protocol.Wire.ReadRel α)
    (refines : ∀ state value final, element.run state = .ok (value, final) ↔ spec state value final)
    (width : Nat) (state final : ReadState) (values : Array α) :
    (Codec.Wire.readVectorWidth width element).run state = .ok (values, final) ↔
      Protocol.Wire.VectorRead width spec state values final := by
  simp only [Codec.Wire.readVectorWidth, action_bind_ok_iff, readNat_refines,
    readCounted_refines element spec refines, Protocol.Wire.VectorRead]

theorem readVector_refines {α : Type} (element : Codec.Wire.Reader α) (spec : Protocol.Wire.ReadRel α)
    (refines : ∀ state value final, element.run state = .ok (value, final) ↔ spec state value final)
    (state final : ReadState) (values : Array α) :
    (Codec.Wire.readVector element).run state = .ok (values, final) ↔
      Protocol.Wire.VectorRead 8 spec state values final :=
  readVectorWidth_refines element spec refines 8 state final values

theorem readOption_refines {α : Type} (element : Codec.Wire.Reader α) (spec : Protocol.Wire.ReadRel α)
    (refines : ∀ state value final, element.run state = .ok (value, final) ↔ spec state value final)
    (state final : ReadState) (value : Option α) :
    (Codec.Wire.readOption element).run state = .ok (value, final) ↔
      Protocol.Wire.OptionRead spec state value final := by
  simp only [Codec.Wire.readOption, action_bind_ok_iff, readByte_refines]
  constructor
  · rintro ⟨tag, middle, read, accepted⟩
    split at accepted
    · simp only [action_pure_ok_iff] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      exact read
    · simp only [action_bind_ok_iff, refines, action_pure_ok_iff] at accepted
      obtain ⟨original, last, readValue, rfl, rfl⟩ := accepted
      exact ⟨middle, read, readValue⟩
    · simp [action_throw_ok_iff] at accepted
  · cases value with
    | none => intro read; exact ⟨0, final, read, by rfl⟩
    | some value =>
      rintro ⟨middle, read, readValue⟩
      refine ⟨1, middle, read, ?_⟩
      change (do let value ← element; pure (some value)).run middle = .ok (some value, final)
      exact (action_bind_ok_iff _ _ _ _ _).mpr ⟨value, final, (refines _ _ _).mpr readValue,
        (action_pure_ok_iff _ _ _ _).mpr ⟨rfl, rfl⟩⟩

theorem wire_decode_refines {α : Type} (reader : Codec.Wire.Reader α) (spec : Protocol.Wire.ReadRel α)
    (refines : ∀ state value final, reader.run state = .ok (value, final) ↔ spec state value final)
    (limits : DecodeLimits) (bytes : Bytes) (value : α) :
    Codec.Wire.decode limits bytes reader = .ok value ↔ Protocol.Wire.Decoded limits bytes spec value := by
  simp only [Codec.Wire.decode, bind_ok_iff, unit_exists_iff, ensure_ok_iff, decide_eq_true_eq,
    Prod.exists, refines, beq_iff_eq, pure_ok_iff, Protocol.Wire.Decoded]
  constructor
  · rintro ⟨bounded, result, final, read, consumed, rfl⟩
    exact ⟨bounded, final, read, consumed⟩
  · rintro ⟨bounded, final, read, consumed⟩
    exact ⟨bounded, value, final, read, consumed, rfl⟩

theorem writeBytes_refines (bytes : Bytes) (state final : WriteState) :
    (Codec.Wire.writeBytes bytes).run state = .ok ((), final) ↔ Protocol.Wire.BytesWritten bytes state final := by
  simp only [Codec.Wire.writeBytes, StateT.run, bind_ok_iff, unit_exists_iff, ensure_ok_iff,
    decide_eq_true_eq, pure_ok_iff, Prod.mk.injEq, true_and, Protocol.Wire.BytesWritten]

theorem writeByte_refines (byte : UInt8) (state final : WriteState) :
    (Codec.Wire.writeByte byte).run state = .ok ((), final) ↔ Protocol.Wire.ByteWritten byte state final :=
  writeBytes_refines #[byte] state final

theorem writeNat_refines (width value : Nat) (state final : WriteState) :
    (Codec.Wire.writeNat width value).run state = .ok ((), final) ↔
      Protocol.Wire.NatWritten width value state final := by
  simp only [Codec.Wire.writeNat, StateT.run, bind_ok_iff, unit_exists_iff, ensure_ok_iff,
    decide_eq_true_eq, Protocol.Wire.NatWritten]
  apply and_congr_right
  intro _
  simpa only [littleEndian_refines, StateT.run] using writeBytes_refines (Codec.Wire.littleEndian width value) state final

theorem writeBool_refines (value : Bool) (state final : WriteState) :
    (Codec.Wire.writeBool value).run state = .ok ((), final) ↔ Protocol.Wire.BoolWritten value state final :=
  writeByte_refines (if value then 1 else 0) state final

theorem writeField_refines (value : Field) (state final : WriteState) :
    (Codec.Wire.writeField value).run state = .ok ((), final) ↔ Protocol.Wire.FieldWritten value state final :=
  writeNat_refines 8 value.val state final

theorem writeExt_refines (value : Ext) (state final : WriteState) :
    (Codec.Wire.writeExt value).run state = .ok ((), final) ↔ Protocol.Wire.ExtWritten value state final := by
  simp only [Codec.Wire.writeExt, action_bind_ok_iff, unit_exists_iff, writeField_refines, Protocol.Wire.ExtWritten]

theorem writeDigest_refines (value : Digest) (state final : WriteState) :
    (Codec.Wire.writeDigest value).run state = .ok ((), final) ↔ Protocol.Wire.DigestWritten value state final :=
  writeBytes_refines value.bytes state final

theorem writeList_refines {α : Type} (element : α → Codec.Wire.Writer Unit) (spec : Protocol.Wire.WriteRel α)
    (refines : ∀ value state final, (element value).run state = .ok ((), final) ↔ spec value state final)
    (values : List α) (state final : WriteState) :
    (Codec.Wire.writeList element values).run state = .ok ((), final) ↔ Protocol.Wire.ListWritten spec values state final := by
  induction values generalizing state with
  | nil => simp only [Codec.Wire.writeList, action_pure_ok_iff, true_and, Protocol.Wire.ListWritten]
  | cons value values ih =>
    simp only [Codec.Wire.writeList, action_bind_ok_iff, unit_exists_iff, refines, ih, Protocol.Wire.ListWritten]

theorem writeCounted_refines {α : Type} (element : α → Codec.Wire.Writer Unit) (spec : Protocol.Wire.WriteRel α)
    (refines : ∀ value state final, (element value).run state = .ok ((), final) ↔ spec value state final)
    (values : Array α) (state final : WriteState) :
    (Codec.Wire.writeCounted element values).run state = .ok ((), final) ↔ Protocol.Wire.CountedWritten spec values state final := by
  simp only [Codec.Wire.writeCounted, StateT.run, bind_ok_iff, unit_exists_iff, ensure_ok_iff,
    decide_eq_true_eq, Protocol.Wire.CountedWritten]
  exact and_congr_right (fun _ => and_congr_right (fun _ => writeList_refines element spec refines values.toList _ final))

theorem writeVectorWidth_refines {α : Type} (element : α → Codec.Wire.Writer Unit) (spec : Protocol.Wire.WriteRel α)
    (refines : ∀ value state final, (element value).run state = .ok ((), final) ↔ spec value state final)
    (width : Nat) (values : Array α) (state final : WriteState) :
    (Codec.Wire.writeVectorWidth width element values).run state = .ok ((), final) ↔
      Protocol.Wire.VectorWritten width spec values state final := by
  simp only [Codec.Wire.writeVectorWidth, action_bind_ok_iff, unit_exists_iff, writeNat_refines,
    writeCounted_refines element spec refines, Protocol.Wire.VectorWritten]

theorem writeVector_refines {α : Type} (element : α → Codec.Wire.Writer Unit) (spec : Protocol.Wire.WriteRel α)
    (refines : ∀ value state final, (element value).run state = .ok ((), final) ↔ spec value state final)
    (values : Array α) (state final : WriteState) :
    (Codec.Wire.writeVector element values).run state = .ok ((), final) ↔
      Protocol.Wire.VectorWritten 8 spec values state final :=
  writeVectorWidth_refines element spec refines 8 values state final

theorem writeOption_refines {α : Type} (element : α → Codec.Wire.Writer Unit) (spec : Protocol.Wire.WriteRel α)
    (refines : ∀ value state final, (element value).run state = .ok ((), final) ↔ spec value state final)
    (value : Option α) (state final : WriteState) :
    (Codec.Wire.writeOption element value).run state = .ok ((), final) ↔ Protocol.Wire.OptionWritten spec value state final := by
  cases value <;>
    simp only [Codec.Wire.writeOption, action_bind_ok_iff, unit_exists_iff, writeByte_refines,
      refines, Protocol.Wire.OptionWritten]

theorem wire_encode_refines (writer : Codec.Wire.Writer Unit) (spec : WriteState → WriteState → Prop)
    (refines : ∀ state final, writer.run state = .ok ((), final) ↔ spec state final)
    (limits : DecodeLimits) (bytes : Bytes) :
    Codec.Wire.encode limits writer = .ok bytes ↔ Protocol.Wire.Written limits spec bytes := by
  simp only [Codec.Wire.encode, bind_ok_iff, Prod.exists, unit_exists_iff, refines,
    pure_ok_iff, Protocol.Wire.Written]

/-- The dependent output already carries its exact encoder equality. The
canonicalizer returns that output precisely when its value is the input. -/
theorem canonicalize_value_iff {α : Type} (encode : α → Except DecodeError Bytes) (bytes : Bytes)
    (value : α) (result : Codec.Canonical encode bytes) :
    Codec.Wire.canonicalize encode bytes value = .ok result ↔ value = result.value := by
  constructor
  · intro accepted
    unfold Codec.Wire.canonicalize at accepted
    split at accepted
    · cases accepted
    · split at accepted
      · cases Except.ok.inj accepted
        rfl
      · cases accepted
  · intro equal
    cases result with
    | mk original encoded =>
      cases equal
      unfold Codec.Wire.canonicalize
      split
      next error failed =>
        have impossible : (Except.error error : Except DecodeError Bytes) = .ok bytes := failed.symm.trans encoded
        cases impossible
      next actual produced =>
        have same : actual = bytes := Except.ok.inj (produced.symm.trans encoded)
        subst actual
        split
        · rfl
        · rename_i impossible
          exact False.elim (impossible rfl)

end MultiStark.Verify.Proofs
