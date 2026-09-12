module
public import Ix.MultiStark.Verify.Protocol.Source
public import Ix.MultiStark.Verify.Proofs.Check
public import Ix.MultiStark.Verify.Proofs.CodecKey
public import Ix.MultiStark.Verify.Proofs.CodecProof
public import Ix.MultiStark.Verify.Proofs.Claim

public section

namespace MultiStark.Verify.Proofs

theorem checkClaim_refines (config : SourceConfig) (claim : ClosedCheckEnv) (proofBytes : Bytes) :
    checkClaim config claim proofBytes = .ok () ↔ Protocol.Stage2ProtocolAcceptsClaim config claim proofBytes := by
  simp only [checkClaim, bind_ok_iff, unit_exists_iff, mapError_ok_iff,
    validateKey_refines, checkTyped_refines, expectedClaim_refines, Protocol.Stage2ProtocolAcceptsClaim]
  constructor
  · rintro ⟨key, keyDecoded, admitted, proof, proofDecoded, accepted⟩
    exact ⟨key.value, proof.value, (decodeKey_refines _ _ _).mp keyDecoded, admitted,
      (decodeProof_refines _ _ _).mp proofDecoded, accepted⟩
  · rintro ⟨key, proof, keyCanonical, admitted, proofCanonical, accepted⟩
    obtain ⟨checkedKey, keyDecoded, rfl⟩ := (decodeKey_exists_iff _ _ _).mpr keyCanonical
    obtain ⟨checkedProof, proofDecoded, rfl⟩ := (decodeProof_exists_iff _ _ _).mpr proofCanonical
    exact ⟨checkedKey, keyDecoded, admitted, checkedProof, proofDecoded, accepted⟩

theorem stage2Verify_refines (config : SourceConfig) (claim : ClosedCheckEnv) (proofBytes : Bytes) :
    stage2Verify config claim proofBytes = true ↔ Protocol.Stage2ProtocolAcceptsClaim config claim proofBytes :=
  (stage2Verify_iff config claim proofBytes).trans (checkClaim_refines config claim proofBytes)

/-- End-to-end deterministic source correctness, including canonical key/
proof bytes and the exact public-claim adapter. Cryptographic soundness and
configuration approval are NOT inferred from this theorem. -/
theorem stage2Verify_sound (config : SourceConfig) (claim : ClosedCheckEnv) (proofBytes : Bytes)
    (accepted : stage2Verify config claim proofBytes = true) : Protocol.Stage2ProtocolAcceptsClaim config claim proofBytes :=
  (stage2Verify_refines config claim proofBytes).mp accepted

/-- Complete on the explicitly supported canonical, bounded input class. -/
theorem stage2Verify_complete (config : SourceConfig) (claim : ClosedCheckEnv) (proofBytes : Bytes)
    (supported : Protocol.Stage2ProtocolAcceptsClaim config claim proofBytes) : stage2Verify config claim proofBytes = true :=
  (stage2Verify_refines config claim proofBytes).mpr supported

theorem claimWrapper_refines (config : SourceConfig) (claim output : ClosedCheckEnv) (proofBytes : Bytes) :
    claimWrapper config claim proofBytes = some output ↔
      output = claim ∧ Protocol.Stage2ProtocolAcceptsClaim config claim proofBytes := by
  rw [claimWrapper_some_iff, stage2Verify_refines]

theorem stage2VerifyBytes_refines (config : SourceConfig) (publicClaim proofBytes : Bytes) :
    stage2VerifyBytes config publicClaim proofBytes = true ↔ Protocol.Stage2ProtocolAcceptsBytes config publicClaim proofBytes := by
  have decoded_iff : stage2VerifyBytes config publicClaim proofBytes = true ↔
      ∃ checked, decodeClosedCheckEnv publicClaim = .ok checked ∧ stage2Verify config checked.value proofBytes = true := by
    cases decoded : decodeClosedCheckEnv publicClaim <;> simp [stage2VerifyBytes, decoded]
  rw [decoded_iff]
  constructor
  · rintro ⟨checked, decoded, accepted⟩
    exact ⟨checked.value, (decodeClosedCheckEnv_refines _ _).mp decoded,
      (stage2Verify_refines _ _ _).mp accepted⟩
  · rintro ⟨claim, canonical, accepted⟩
    obtain ⟨checked, decoded, rfl⟩ := (decodeClosedCheckEnv_exists_iff _ _).mpr canonical
    exact ⟨checked, decoded, (stage2Verify_refines _ _ _).mpr accepted⟩

theorem stage2VerifyBytes_sound (config : SourceConfig) (publicClaim proofBytes : Bytes)
    (accepted : stage2VerifyBytes config publicClaim proofBytes = true) :
    Protocol.Stage2ProtocolAcceptsBytes config publicClaim proofBytes :=
  (stage2VerifyBytes_refines config publicClaim proofBytes).mp accepted

theorem stage2VerifyBytes_complete (config : SourceConfig) (publicClaim proofBytes : Bytes)
    (supported : Protocol.Stage2ProtocolAcceptsBytes config publicClaim proofBytes) :
    stage2VerifyBytes config publicClaim proofBytes = true :=
  (stage2VerifyBytes_refines config publicClaim proofBytes).mpr supported

theorem claimBytesWrapper_refines (config : SourceConfig) (publicClaim output proofBytes : Bytes) :
    claimBytesWrapper config publicClaim proofBytes = some output ↔
      output = publicClaim ∧ Protocol.Stage2ProtocolAcceptsBytes config publicClaim proofBytes := by
  rw [claimBytesWrapper_some_iff, stage2VerifyBytes_refines]

end MultiStark.Verify.Proofs
