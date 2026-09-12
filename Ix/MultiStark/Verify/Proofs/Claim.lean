module
public import Ix.MultiStark.Verify.Protocol.Claim
public import Ix.MultiStark.Verify.Proofs.Wire

public section

namespace MultiStark.Verify.Proofs

open Codec.Wire (ReadState WriteState)

theorem closedClaimBytes_refines (claim : ClosedCheckEnv) : claim.bytes = Protocol.ClosedClaimBytes claim := rfl

theorem allowedIdentity_refines (config : AggregateConfig) : config.allowedIdentity = Protocol.AllowedIdentityBytes config := by
  simp only [AggregateConfig.allowedIdentity, hash, littleEndian_refines, Protocol.AllowedIdentityBytes]

theorem packDigest_refines (digest : Digest) : packDigest digest = Protocol.DigestWords digest := by
  simp only [packDigest, fromLittleEndian_refines, Protocol.DigestWords]

/-- Every digest chunk fits in 32 bits, so packing it into a canonical
Goldilocks word cannot discard high digest bits by field reduction. -/
theorem digestWord_bounded (digest : Digest) (index : Nat) (bound : index < 8) :
    Protocol.Wire.LittleEndianValue (digest.bytes.extract (4 * index) (4 * index + 4)).toList < 2 ^ 32 := by
  have size : (digest.bytes.extract (4 * index) (4 * index + 4)).size = 4 := by
    simp only [Array.size_extract, digest.size, Nat.min_eq_left (show 4 * index + 4 ≤ 32 by omega)]
    omega
  simpa only [Array.length_toList, size] using littleEndianValue_bounded
    (digest.bytes.extract (4 * index) (4 * index + 4)).toList

theorem expectedClaim_refines (config : AggregateConfig) (claim : ClosedCheckEnv) :
    config.expectedClaim claim = Protocol.NativeAggregateClaim config claim := by
  simp only [AggregateConfig.expectedClaim, packDigest_refines, hash,
    allowedIdentity_refines, closedClaimBytes_refines, Protocol.NativeAggregateClaim]

theorem readClosedCheckEnv_refines (state final : ReadState) (value : ClosedCheckEnv) :
    readClosedCheckEnv.run state = .ok (value, final) ↔ Protocol.Wire.ClosedClaimRead state value final := by
  cases value
  simp only [readClosedCheckEnv, action_bind_ok_iff, unit_exists_iff, action_pure_ok_iff,
    readTag_refines, readDigest_refines, ClosedCheckEnv.mk.injEq, Protocol.Wire.ClosedClaimRead]
  constructor
  · rintro ⟨first, h1, _, second, h2, last, h3, rfl, rfl⟩
    exact ⟨first, second, h1, h2, h3⟩
  · rintro ⟨first, second, h1, h2, h3⟩
    exact ⟨first, h1, _, second, h2, final, h3, rfl, rfl⟩

theorem decodeClosedCheckEnv_refines (bytes : Bytes)
    (result : Codec.Canonical (fun claim : ClosedCheckEnv => .ok claim.bytes) bytes) :
    decodeClosedCheckEnv bytes = .ok result ↔ Protocol.Wire.CanonicalClosedClaim bytes result.value := by
  simp only [decodeClosedCheckEnv, bind_ok_iff, canonicalize_value_iff,
    wire_decode_refines _ _ (fun state value final => readClosedCheckEnv_refines state final value),
    exists_eq_right, Protocol.Wire.CanonicalClosedClaim]
  constructor
  · intro read
    exact ⟨read, (closedClaimBytes_refines result.value).symm.trans (Except.ok.inj result.encoded)⟩
  · exact And.left

theorem decodeClosedCheckEnv_exists_iff (bytes : Bytes) (value : ClosedCheckEnv) :
    (∃ result, decodeClosedCheckEnv bytes = .ok result ∧ result.value = value) ↔
      Protocol.Wire.CanonicalClosedClaim bytes value := by
  constructor
  · rintro ⟨result, decoded, rfl⟩
    exact (decodeClosedCheckEnv_refines bytes result).mp decoded
  · intro canonical
    let result : Codec.Canonical (fun claim : ClosedCheckEnv => .ok claim.bytes) bytes :=
      ⟨value, congrArg Except.ok ((closedClaimBytes_refines value).trans canonical.2)⟩
    exact ⟨result, (decodeClosedCheckEnv_refines bytes result).mpr canonical, rfl⟩

theorem readClaims_refines (state final : ReadState) (value : Array (Array Field)) :
    (Codec.Wire.readVector (Codec.Wire.readVector Codec.Wire.readField)).run state = .ok (value, final) ↔
      Protocol.Wire.ClaimsRead state value final := by
  apply readVector_refines
  intro state value final
  apply readVector_refines
  exact fun state value final => readField_refines state final value

theorem writeClaims_refines (value : Array (Array Field)) (state final : WriteState) :
    (Codec.Wire.writeVector (Codec.Wire.writeVector Codec.Wire.writeField) value).run state = .ok ((), final) ↔
      Protocol.Wire.ClaimsWritten value state final := by
  apply writeVector_refines
  intro value state final
  apply writeVector_refines
  exact writeField_refines

theorem encodeClaims_refines (limits : DecodeLimits) (value : Array (Array Field)) (bytes : Bytes) :
    Codec.encodeClaims limits value = .ok bytes ↔ Protocol.Wire.Written limits (Protocol.Wire.ClaimsWritten value) bytes :=
  wire_encode_refines _ _ (writeClaims_refines value) limits bytes

theorem decodeClaims_refines (limits : DecodeLimits) (bytes : Bytes)
    (result : Codec.Canonical (Codec.encodeClaims limits) bytes) :
    Codec.decodeClaims limits bytes = .ok result ↔ Protocol.Wire.CanonicalClaims limits bytes result.value := by
  simp only [Codec.decodeClaims, bind_ok_iff, canonicalize_value_iff,
    wire_decode_refines _ _ (fun state value final => readClaims_refines state final value),
    exists_eq_right, Protocol.Wire.CanonicalClaims]
  constructor
  · intro read
    exact ⟨read, (encodeClaims_refines limits result.value bytes).mp result.encoded⟩
  · exact And.left

theorem decodeClaims_exists_iff (limits : DecodeLimits) (bytes : Bytes) (value : Array (Array Field)) :
    (∃ result, Codec.decodeClaims limits bytes = .ok result ∧ result.value = value) ↔
      Protocol.Wire.CanonicalClaims limits bytes value := by
  constructor
  · rintro ⟨result, decoded, rfl⟩
    exact (decodeClaims_refines limits bytes result).mp decoded
  · intro canonical
    let result : Codec.Canonical (Codec.encodeClaims limits) bytes :=
      ⟨value, (encodeClaims_refines limits value bytes).mpr canonical.2⟩
    exact ⟨result, (decodeClaims_refines limits bytes result).mpr canonical, rfl⟩

end MultiStark.Verify.Proofs
