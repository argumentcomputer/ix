module
public import Ix.MultiStark.Verify.Protocol.CodecKey
public import Ix.MultiStark.Verify.Proofs.Wire

public section

namespace MultiStark.Verify.Proofs

open Codec.Wire (ReadState WriteState)

theorem readParameters_refines (state final : ReadState) (value : Parameters) :
    Codec.KeyWire.readParameters.run state = .ok (value, final) ↔ Protocol.Wire.ParametersRead state value final := by
  cases value
  simp only [Codec.KeyWire.readParameters, action_bind_ok_iff, action_pure_ok_iff, readNat_refines,
    Parameters.mk.injEq, Protocol.Wire.ParametersRead]
  constructor
  · rintro ⟨_, s1, h1, _, s2, h2, _, s3, h3, _, s4, h4, _, s5, h5, _, s6, h6,
      _, last, h7, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
    exact ⟨s1, s2, s3, s4, s5, s6, h1, h2, h3, h4, h5, h6, h7⟩
  · rintro ⟨s1, s2, s3, s4, s5, s6, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨_, s1, h1, _, s2, h2, _, s3, h3, _, s4, h4, _, s5, h5, _, s6, h6,
      _, final, h7, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem readNode_refines (state final : ReadState) (value : Node) :
    Codec.KeyWire.readNode.run state = .ok (value, final) ↔ Protocol.Wire.NodeRead state value final := by
  simp only [Codec.KeyWire.readNode, action_bind_ok_iff, readByte_refines, Protocol.Wire.NodeRead]
  apply exists_congr
  intro tag
  apply exists_congr
  intro middle
  apply and_congr_right
  intro _
  unfold Protocol.Wire.NodeBodyRead
  split <;>
    simp only [action_bind_ok_iff, action_pure_ok_iff, action_throw_ok_iff, readNat_refines, readField_refines]
  all_goals
    constructor
    · intro parsed
      rcases parsed with ⟨first, s1, h1, rest⟩
      first
      | (obtain ⟨same, rfl⟩ := rest; exact ⟨first, h1, same⟩)
      | (obtain ⟨second, last, h2, same, rfl⟩ := rest; exact ⟨first, s1, second, h1, h2, same⟩)
    · intro parsed
      first
      | (obtain ⟨first, h1, same⟩ := parsed; exact ⟨first, final, h1, same, rfl⟩)
      | (obtain ⟨first, s1, second, h1, h2, same⟩ := parsed; exact ⟨first, s1, h1, second, final, h2, same, rfl⟩)

theorem readLookup_refines (state final : ReadState) (value : Lookup) :
    Codec.KeyWire.readLookup.run state = .ok (value, final) ↔ Protocol.Wire.LookupRead state value final := by
  cases value
  simp only [Codec.KeyWire.readLookup, action_bind_ok_iff, action_pure_ok_iff, readNat_refines,
    readVectorWidth_refines _ _ (fun state value final => readNat_refines 2 state final value),
    Lookup.mk.injEq, Protocol.Wire.LookupRead]
  constructor
  · rintro ⟨_, middle, first, _, last, rest, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨middle, first, rest⟩
  · rintro ⟨middle, first, rest⟩
    exact ⟨_, middle, first, _, final, rest, ⟨rfl, rfl⟩, rfl⟩

theorem readCircuit_refines (state final : ReadState) (value : Circuit) :
    Codec.KeyWire.readCircuit.run state = .ok (value, final) ↔ Protocol.Wire.CircuitRead state value final := by
  cases value
  simp only [Codec.KeyWire.readCircuit, action_bind_ok_iff, action_pure_ok_iff, readNat_refines,
    readVectorWidth_refines _ _ (fun state value final => readNode_refines state final value),
    readVectorWidth_refines _ _ (fun state value final => readNat_refines 2 state final value),
    readVectorWidth_refines _ _ (fun state value final => readLookup_refines state final value),
    Circuit.mk.injEq, Protocol.Wire.CircuitRead]
  constructor
  · rintro ⟨_, s1, h1, _, s2, h2, _, s3, h3, _, s4, h4, _, s5, h5, _, s6, h6, _, s7, h7,
      _, last, h8, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
    exact ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · rintro ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨_, s1, h1, _, s2, h2, _, s3, h3, _, s4, h4, _, s5, h5, _, s6, h6, _, s7, h7,
      _, final, h8, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem readIndex_refines (state final : ReadState) (value : Option Nat) :
    Codec.KeyWire.readIndex.run state = .ok (value, final) ↔ Protocol.Wire.IndexRead state value final := by
  simp only [Codec.KeyWire.readIndex, action_bind_ok_iff, action_pure_ok_iff, readNat_refines,
    beq_iff_eq, Protocol.Wire.IndexRead]
  constructor
  · rintro ⟨word, middle, read, same, rfl⟩
    exact ⟨word, read, same⟩
  · rintro ⟨word, read, same⟩
    exact ⟨word, final, read, same, rfl⟩

theorem readKey_refines (state final : ReadState) (value : Key) :
    Codec.KeyWire.read.run state = .ok (value, final) ↔ Protocol.Wire.KeyRead state value final := by
  cases value
  simp only [Codec.KeyWire.read, action_bind_ok_iff, action_pure_ok_iff, readParameters_refines,
    readVectorWidth_refines _ _ (fun state value final => readCircuit_refines state final value),
    readOption_refines _ _ (fun state value final => readVectorWidth_refines _ _
      (fun state value final => readDigest_refines state final value) 2 state final value),
    readCounted_refines _ _ (fun state value final => readIndex_refines state final value),
    Key.mk.injEq, Protocol.Wire.KeyRead]
  constructor
  · rintro ⟨_, s1, h1, _, s2, h2, _, s3, h3, _, last, h4, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
    exact ⟨s1, s2, s3, h1, h2, h3, h4⟩
  · rintro ⟨s1, s2, s3, h1, h2, h3, h4⟩
    exact ⟨_, s1, h1, _, s2, h2, _, s3, h3, _, final, h4, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩

theorem writeParameters_refines (value : Parameters) (state final : WriteState) :
    (Codec.KeyWire.writeParameters value).run state = .ok ((), final) ↔
      Protocol.Wire.ParametersWritten value state final :=
  writeList_refines (Codec.Wire.writeNat 2) (Protocol.Wire.NatWritten 2) (writeNat_refines 2) value.words.toList state final

theorem writeNode_refines (value : Node) (state final : WriteState) :
    (Codec.KeyWire.writeNode value).run state = .ok ((), final) ↔ Protocol.Wire.NodeWritten value state final := by
  cases value with
  | const value =>
    by_cases small : value.val < 65536 <;>
      simp only [Codec.KeyWire.writeNode, Protocol.Wire.NodeWritten, small, ↓reduceIte,
        action_bind_ok_iff, unit_exists_iff, writeByte_refines, writeNat_refines, writeField_refines]
  | var source next column =>
    cases source <;> cases next <;>
      simp only [Codec.KeyWire.writeNode, Protocol.Wire.NodeWritten, Bool.false_eq_true, ↓reduceIte,
        action_bind_ok_iff, unit_exists_iff, writeByte_refines, writeNat_refines] <;> rfl
  | _ =>
    simp only [Codec.KeyWire.writeNode, Protocol.Wire.NodeWritten, action_bind_ok_iff, unit_exists_iff,
      writeByte_refines, writeNat_refines, exists_and_left]

theorem writeLookup_refines (value : Lookup) (state final : WriteState) :
    (Codec.KeyWire.writeLookup value).run state = .ok ((), final) ↔ Protocol.Wire.LookupWritten value state final := by
  simp only [Codec.KeyWire.writeLookup, action_bind_ok_iff, unit_exists_iff, writeNat_refines,
    writeVectorWidth_refines _ _ (writeNat_refines 2), Protocol.Wire.LookupWritten]

theorem writeCircuit_refines (value : Circuit) (state final : WriteState) :
    (Codec.KeyWire.writeCircuit value).run state = .ok ((), final) ↔ Protocol.Wire.CircuitWritten value state final := by
  simp only [Codec.KeyWire.writeCircuit, action_bind_ok_iff, unit_exists_iff, writeNat_refines,
    writeVectorWidth_refines _ _ writeNode_refines, writeVectorWidth_refines _ _ (writeNat_refines 2),
    writeVectorWidth_refines _ _ writeLookup_refines, Protocol.Wire.CircuitWritten, exists_and_left]

theorem writeIndex_refines (value : Option Nat) (state final : WriteState) :
    (Codec.KeyWire.writeIndex value).run state = .ok ((), final) ↔ Protocol.Wire.IndexWritten value state final := by
  cases value with
  | none => exact writeNat_refines 2 65535 state final
  | some index =>
    by_cases bound : index < 65535
    · simp [Codec.KeyWire.writeIndex, Protocol.Wire.IndexWritten, bound, Nat.not_le.mpr bound,
        writeNat_refines]
    · simp only [Codec.KeyWire.writeIndex, Protocol.Wire.IndexWritten, bound, Nat.le_of_not_gt bound,
        ↓reduceIte, action_bind_ok_iff, action_throw_ok_iff, false_and]
      simp

theorem writeKey_refines (value : Key) (state final : WriteState) :
    (Codec.KeyWire.write value).run state = .ok ((), final) ↔ Protocol.Wire.KeyWritten value state final := by
  by_cases same : value.preprocessedIndices.size = value.circuits.size
  · simp only [Codec.KeyWire.write, same, beq_self_eq_true, ↓reduceIte,
      action_bind_ok_iff, unit_exists_iff, writeParameters_refines,
      writeVectorWidth_refines _ _ writeCircuit_refines,
      writeOption_refines _ _ (fun value state final => writeVectorWidth_refines _ _ writeDigest_refines 2 value state final),
      writeCounted_refines _ _ writeIndex_refines, Protocol.Wire.KeyWritten, true_and, exists_and_left]
  · simp only [Codec.KeyWire.write, beq_iff_eq, same, ↓reduceIte, Protocol.Wire.KeyWritten,
      action_bind_ok_iff, action_throw_ok_iff, false_and]
    simp

theorem encodeKey_refines (limits : DecodeLimits) (value : Key) (bytes : Bytes) :
    Codec.encodeKey limits value = .ok bytes ↔ Protocol.Wire.Written limits (Protocol.Wire.KeyWritten value) bytes :=
  wire_encode_refines (Codec.KeyWire.write value) (Protocol.Wire.KeyWritten value) (writeKey_refines value) limits bytes

theorem decodeKey_refines (limits : DecodeLimits) (bytes : Bytes)
    (result : Codec.Canonical (Codec.encodeKey limits) bytes) :
    Codec.decodeKey limits bytes = .ok result ↔ Protocol.Wire.CanonicalKey limits bytes result.value := by
  simp only [Codec.decodeKey, bind_ok_iff, canonicalize_value_iff,
    wire_decode_refines _ _ (fun state value final => readKey_refines state final value),
    exists_eq_right, Protocol.Wire.CanonicalKey]
  constructor
  · intro read
    exact ⟨read, (encodeKey_refines limits result.value bytes).mp result.encoded⟩
  · exact And.left

theorem decodeKey_exists_iff (limits : DecodeLimits) (bytes : Bytes) (value : Key) :
    (∃ result, Codec.decodeKey limits bytes = .ok result ∧ result.value = value) ↔
      Protocol.Wire.CanonicalKey limits bytes value := by
  constructor
  · rintro ⟨result, decoded, rfl⟩
    exact (decodeKey_refines limits bytes result).mp decoded
  · intro canonical
    let result : Codec.Canonical (Codec.encodeKey limits) bytes :=
      ⟨value, (encodeKey_refines limits value bytes).mpr canonical.2⟩
    exact ⟨result, (decodeKey_refines limits bytes result).mpr canonical, rfl⟩

end MultiStark.Verify.Proofs
