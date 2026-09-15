module
import Tests.Ixby.Common
import Ix.MultiStark.Verify.Claim
import Ix.Aggr

namespace Tests.MultiStark.Verify.Claim

open _root_.MultiStark.Verify
open Tests.Ixby (Check runChecks)

private def root : Digest := ⟨(Array.range 32).map Nat.toUInt8, by simp⟩
private def claim : ClosedCheckEnv := ⟨root⟩
private def config : AggregateConfig := ⟨#[1, 2, 3, 4], 7, #[5, 6, 7, 8], 11⟩

private def checks : IO (List Check) := do
  let nativeClaim : Ix.Claim := .checkEnv ⟨⟨root.bytes⟩⟩ none
  let nativeAllowed := Aggr.allowedBlob ⟨config.ixvmKey⟩ config.verifyClaimEntry.val
    ⟨config.aggregateKey⟩ config.aggregateEntry.val
  let nativeStatement := Aiur.buildClaim config.aggregateEntry.val
    (Aggr.pubInput nativeAllowed (Ix.Claim.ser nativeClaim)) #[]
  return [
    ("pure closed-root bytes equal production Ixon serialization", claim.bytes ==
      (Ix.Claim.ser nativeClaim).data),
    ("pure closed-root decoder round trip", match decodeClosedCheckEnv claim.bytes with
      | .ok checked => checked.value == claim | .error _ => false),
    ("conditional root is not accepted as closed", !(decodeClosedCheckEnv
      (Ix.Claim.ser (.checkEnv ⟨⟨root.bytes⟩⟩ (some ⟨⟨root.bytes⟩⟩))).data).isOk),
    ("different claim kind is not accepted as CheckEnv", !(decodeClosedCheckEnv
      (Ix.Claim.ser (.check ⟨⟨root.bytes⟩⟩ none)).data).isOk),
    ("every public-claim prefix rejected", (List.range 34).all (fun size =>
      !(decodeClosedCheckEnv (claim.bytes.extract 0 size)).isOk)),
    ("trailing claim bytes rejected", !(decodeClosedCheckEnv (claim.bytes.push 0)).isOk),
    ("pure allowed identity equals host reference", config.allowedIdentity == nativeAllowed.data),
    ("pure aggregate claim equals host reference", (config.expectedClaim claim).map (·.val) ==
      nativeStatement.map (·.n)),
    ("IxVM key is bound", { config with ixvmKey := #[9] }.allowedIdentity != config.allowedIdentity),
    ("aggregate key is bound", { config with aggregateKey := #[9] }.allowedIdentity != config.allowedIdentity),
    ("IxVM entry is bound", { config with verifyClaimEntry := 8 }.allowedIdentity != config.allowedIdentity),
    ("aggregate entry is bound", { config with aggregateEntry := 12 }.allowedIdentity != config.allowedIdentity),
    ("changed public C changes native expected claim", config.expectedClaim
      ⟨⟨Array.replicate 32 9, by simp⟩⟩ != config.expectedClaim claim),
    ("digest uses eight ordered little-endian u32 limbs", (packDigest root).map (·.val) ==
      #[0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c,
        0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c])
  ]

public def suite : IO UInt32 := runChecks "stage2-claim" checks

end Tests.MultiStark.Verify.Claim
