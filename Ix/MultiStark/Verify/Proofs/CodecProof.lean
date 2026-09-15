module
public import Ix.MultiStark.Verify.Protocol.CodecProof
public import Ix.MultiStark.Verify.Proofs.Wire

public section

namespace MultiStark.Verify.Proofs

open Codec.Wire (ReadState WriteState)

theorem readCap_refines (state final : ReadState) (value : MerkleCap) :
    Codec.Wire.readCap.run state = .ok (value, final) ↔ Protocol.Wire.CapRead state value final := by
  apply readVector_refines
  exact fun state value final => readDigest_refines state final value

theorem readRound_refines (state final : ReadState) (value : OpenedRound) :
    Codec.Wire.readRound.run state = .ok (value, final) ↔ Protocol.Wire.RoundRead state value final := by
  apply readVector_refines
  intro state value final
  apply readVector_refines
  intro state value final
  apply readVector_refines
  exact fun state value final => readExt_refines state final value

theorem readBatchValues_refines (state final : ReadState) (value : Array (Array (Array Field))) :
    (Codec.Wire.readVector (Codec.Wire.readVector (Codec.Wire.readVector Codec.Wire.readField))).run state = .ok (value, final) ↔
      Protocol.Wire.BatchValuesRead state value final := by
  apply readVector_refines
  intro state value final
  apply readVector_refines
  intro state value final
  apply readVector_refines
  exact fun state value final => readField_refines state final value

theorem readSiblings_refines (state final : ReadState) (value : Array (Array Ext)) :
    (Codec.Wire.readVector (Codec.Wire.readVector Codec.Wire.readExt)).run state = .ok (value, final) ↔
      Protocol.Wire.SiblingsRead state value final := by
  apply readVector_refines
  intro state value final
  apply readVector_refines
  exact fun state value final => readExt_refines state final value

theorem readCommitments_refines (state final : ReadState) (value : Commitments) :
    Codec.Wire.readCommitments.run state = .ok (value, final) ↔ Protocol.Wire.CommitmentsRead state value final := by
  cases value
  simp only [Codec.Wire.readCommitments, action_bind_ok_iff, action_pure_ok_iff, readCap_refines,
    Commitments.mk.injEq, Protocol.Wire.CommitmentsRead]
  constructor
  · rintro ⟨_, s1, h1, _, s2, h2, _, last, h3, ⟨rfl, rfl, rfl⟩, rfl⟩
    exact ⟨s1, s2, h1, h2, h3⟩
  · rintro ⟨s1, s2, h1, h2, h3⟩
    exact ⟨_, s1, h1, _, s2, h2, _, final, h3, ⟨rfl, rfl, rfl⟩, rfl⟩

theorem readBatchOpening_refines (state final : ReadState) (value : BatchOpening) :
    Codec.Wire.readBatchOpening.run state = .ok (value, final) ↔ Protocol.Wire.BatchOpeningRead state value final := by
  cases value
  simp only [Codec.Wire.readBatchOpening, action_bind_ok_iff, action_pure_ok_iff, readBatchValues_refines,
    readVector_refines _ _ (fun state value final => readDigest_refines state final value),
    BatchOpening.mk.injEq, Protocol.Wire.BatchOpeningRead]
  constructor
  · rintro ⟨_, middle, values, _, last, frontier, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨middle, values, frontier⟩
  · rintro ⟨middle, values, frontier⟩
    exact ⟨_, middle, values, _, final, frontier, ⟨rfl, rfl⟩, rfl⟩

theorem readCommitPhaseStep_refines (state final : ReadState) (value : CommitPhaseStep) :
    Codec.Wire.readCommitPhaseStep.run state = .ok (value, final) ↔ Protocol.Wire.CommitPhaseStepRead state value final := by
  cases value
  simp only [Codec.Wire.readCommitPhaseStep, action_bind_ok_iff, action_pure_ok_iff, readByte_refines,
    readSiblings_refines, readVector_refines _ _ (fun state value final => readDigest_refines state final value),
    CommitPhaseStep.mk.injEq, Protocol.Wire.CommitPhaseStepRead]
  constructor
  · rintro ⟨_, s1, h1, _, s2, h2, _, last, h3, ⟨rfl, rfl, rfl⟩, rfl⟩
    exact ⟨s1, s2, h1, h2, h3⟩
  · rintro ⟨s1, s2, h1, h2, h3⟩
    exact ⟨_, s1, h1, _, s2, h2, _, final, h3, ⟨rfl, rfl, rfl⟩, rfl⟩

theorem readFri_refines (state final : ReadState) (value : FriProof) :
    Codec.Wire.readFri.run state = .ok (value, final) ↔ Protocol.Wire.FriRead state value final := by
  cases value
  simp only [Codec.Wire.readFri, action_bind_ok_iff, action_pure_ok_iff,
    readVector_refines _ _ (fun state value final => readCap_refines state final value),
    readVector_refines _ _ (fun state value final => readField_refines state final value),
    readVector_refines _ _ (fun state value final => readBatchOpening_refines state final value),
    readVector_refines _ _ (fun state value final => readCommitPhaseStep_refines state final value),
    readVector_refines _ _ (fun state value final => readExt_refines state final value),
    readField_refines, FriProof.mk.injEq, Protocol.Wire.FriRead]
  constructor
  · rintro ⟨_, s1, h1, _, s2, h2, _, s3, h3, _, s4, h4, _, s5, h5, _, last, h6,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
    exact ⟨s1, s2, s3, s4, s5, h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨s1, s2, s3, s4, s5, h1, h2, h3, h4, h5, h6⟩
    exact ⟨_, s1, h1, _, s2, h2, _, s3, h3, _, s4, h4, _, s5, h5, _, final, h6,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem readProof_refines (state final : ReadState) (value : Proof) :
    Codec.Wire.readProof.run state = .ok (value, final) ↔ Protocol.Wire.ProofRead state value final := by
  cases value
  simp only [Codec.Wire.readProof, action_bind_ok_iff, action_pure_ok_iff,
    readVector_refines _ _ (fun state value final => readBool_refines state final value),
    readVector_refines _ _ (fun state value final => readExt_refines state final value),
    readVector_refines _ _ (fun state value final => readByte_refines state final value),
    readOption_refines _ _ (fun state value final => readRound_refines state final value),
    readCommitments_refines, readFri_refines, readRound_refines, Proof.mk.injEq, Protocol.Wire.ProofRead]
  constructor
  · rintro ⟨_, s1, h1, _, s2, h2, _, s3, h3, _, s4, h4, _, s5, h5, _, s6, h6, _, s7, h7,
      _, s8, h8, _, last, h9, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
    exact ⟨s1, s2, s3, s4, s5, s6, s7, s8, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · rintro ⟨s1, s2, s3, s4, s5, s6, s7, s8, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨_, s1, h1, _, s2, h2, _, s3, h3, _, s4, h4, _, s5, h5, _, s6, h6, _, s7, h7,
      _, s8, h8, _, final, h9, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem writeCap_refines (value : MerkleCap) (state final : WriteState) :
    (Codec.Wire.writeCap value).run state = .ok ((), final) ↔ Protocol.Wire.CapWritten value state final := by
  apply writeVector_refines
  exact writeDigest_refines

theorem writeRound_refines (value : OpenedRound) (state final : WriteState) :
    (Codec.Wire.writeRound value).run state = .ok ((), final) ↔ Protocol.Wire.RoundWritten value state final := by
  apply writeVector_refines
  intro value state final
  apply writeVector_refines
  intro value state final
  apply writeVector_refines
  exact writeExt_refines

theorem writeBatchValues_refines (value : Array (Array (Array Field))) (state final : WriteState) :
    (Codec.Wire.writeVector (Codec.Wire.writeVector (Codec.Wire.writeVector Codec.Wire.writeField)) value).run state = .ok ((), final) ↔
      Protocol.Wire.BatchValuesWritten value state final := by
  apply writeVector_refines
  intro value state final
  apply writeVector_refines
  intro value state final
  apply writeVector_refines
  exact writeField_refines

theorem writeSiblings_refines (value : Array (Array Ext)) (state final : WriteState) :
    (Codec.Wire.writeVector (Codec.Wire.writeVector Codec.Wire.writeExt) value).run state = .ok ((), final) ↔
      Protocol.Wire.SiblingsWritten value state final := by
  apply writeVector_refines
  intro value state final
  apply writeVector_refines
  exact writeExt_refines

theorem writeCommitments_refines (value : Commitments) (state final : WriteState) :
    (Codec.Wire.writeCommitments value).run state = .ok ((), final) ↔ Protocol.Wire.CommitmentsWritten value state final := by
  simp only [Codec.Wire.writeCommitments, action_bind_ok_iff, unit_exists_iff, writeCap_refines,
    Protocol.Wire.CommitmentsWritten, exists_and_left]

theorem writeBatchOpening_refines (value : BatchOpening) (state final : WriteState) :
    (Codec.Wire.writeBatchOpening value).run state = .ok ((), final) ↔ Protocol.Wire.BatchOpeningWritten value state final := by
  simp only [Codec.Wire.writeBatchOpening, action_bind_ok_iff, unit_exists_iff, writeBatchValues_refines,
    writeVector_refines _ _ writeDigest_refines, Protocol.Wire.BatchOpeningWritten, Protocol.Wire.CapWritten]

theorem writeCommitPhaseStep_refines (value : CommitPhaseStep) (state final : WriteState) :
    (Codec.Wire.writeCommitPhaseStep value).run state = .ok ((), final) ↔ Protocol.Wire.CommitPhaseStepWritten value state final := by
  simp only [Codec.Wire.writeCommitPhaseStep, action_bind_ok_iff, unit_exists_iff, writeByte_refines,
    writeSiblings_refines, writeVector_refines _ _ writeDigest_refines, Protocol.Wire.CommitPhaseStepWritten,
    Protocol.Wire.CapWritten, exists_and_left]

theorem writeFri_refines (value : FriProof) (state final : WriteState) :
    (Codec.Wire.writeFri value).run state = .ok ((), final) ↔ Protocol.Wire.FriWritten value state final := by
  simp only [Codec.Wire.writeFri, action_bind_ok_iff, unit_exists_iff,
    writeVector_refines _ _ writeCap_refines, writeVector_refines _ _ writeField_refines,
    writeVector_refines _ _ writeBatchOpening_refines, writeVector_refines _ _ writeCommitPhaseStep_refines,
    writeVector_refines _ _ writeExt_refines, writeField_refines, Protocol.Wire.FriWritten, exists_and_left]

theorem writeProof_refines (value : Proof) (state final : WriteState) :
    (Codec.Wire.writeProof value).run state = .ok ((), final) ↔ Protocol.Wire.ProofWritten value state final := by
  simp only [Codec.Wire.writeProof, action_bind_ok_iff, unit_exists_iff,
    writeVector_refines _ _ writeBool_refines, writeVector_refines _ _ writeExt_refines,
    writeVector_refines _ _ writeByte_refines, writeOption_refines _ _ writeRound_refines,
    writeCommitments_refines, writeFri_refines, writeRound_refines, Protocol.Wire.ProofWritten, exists_and_left]

theorem encodeProof_refines (limits : DecodeLimits) (value : Proof) (bytes : Bytes) :
    Codec.encodeProof limits value = .ok bytes ↔ Protocol.Wire.Written limits (Protocol.Wire.ProofWritten value) bytes :=
  wire_encode_refines (Codec.Wire.writeProof value) (Protocol.Wire.ProofWritten value) (writeProof_refines value) limits bytes

theorem decodeProof_refines (limits : DecodeLimits) (bytes : Bytes)
    (result : Codec.Canonical (Codec.encodeProof limits) bytes) :
    Codec.decodeProof limits bytes = .ok result ↔ Protocol.Wire.CanonicalProof limits bytes result.value := by
  simp only [Codec.decodeProof, bind_ok_iff, canonicalize_value_iff,
    wire_decode_refines _ _ (fun state value final => readProof_refines state final value),
    exists_eq_right, Protocol.Wire.CanonicalProof]
  constructor
  · intro read
    exact ⟨read, (encodeProof_refines limits result.value bytes).mp result.encoded⟩
  · exact And.left

theorem decodeProof_exists_iff (limits : DecodeLimits) (bytes : Bytes) (value : Proof) :
    (∃ result, Codec.decodeProof limits bytes = .ok result ∧ result.value = value) ↔
      Protocol.Wire.CanonicalProof limits bytes value := by
  constructor
  · rintro ⟨result, decoded, rfl⟩
    exact (decodeProof_refines limits bytes result).mp decoded
  · intro canonical
    let result : Codec.Canonical (Codec.encodeProof limits) bytes :=
      ⟨value, (encodeProof_refines limits value bytes).mpr canonical.2⟩
    exact ⟨result, (decodeProof_refines limits bytes result).mpr canonical, rfl⟩

end MultiStark.Verify.Proofs
