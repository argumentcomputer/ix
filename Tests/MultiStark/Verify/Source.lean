module
import Tests.Ixby.Common
import Ix.MultiStark.Stage2

namespace Tests.MultiStark.Verify.Source

open _root_.MultiStark.Verify
open Tests.Ixby (Check runChecks)

private def root : Digest := ⟨Array.replicate 32 7, by simp⟩
private def claim : ClosedCheckEnv := ⟨root⟩
private def config : SourceConfig := { aggregate := ⟨#[], 0, #[], 0⟩ }

private def checks : IO (List Check) := do
  let typed : Ix.Claim := .checkEnv ⟨⟨root.bytes⟩⟩ none
  let conditional : Ix.Claim := .checkEnv ⟨⟨root.bytes⟩⟩ (some ⟨⟨root.bytes⟩⟩)
  let alias : Ix.Claim := .checkEnv ⟨⟨Array.replicate 31 7⟩⟩ (some ⟨⟨#[0]⟩⟩)
  return [
    ("empty aggregate key rejects before proof verification", match checkClaim config claim #[] with
      | .error (.keyDecode _) => true | _ => false),
    ("typed source verifier rejects invalid key/proof", !stage2Verify config claim #[]),
    ("failed typed verification does not return a claim", (claimWrapper config claim #[]).isNone),
    ("failed byte verification does not return claim bytes", (claimBytesWrapper config claim.bytes #[]).isNone),
    ("byte verifier rejects every truncated claim", (List.range 34).all fun size =>
      !stage2VerifyBytes config (claim.bytes.extract 0 size) #[]),
    ("byte verifier rejects a trailing public byte", !stage2VerifyBytes config (claim.bytes.push 0) #[]),
    ("byte verifier rejects a conditional claim", !stage2VerifyBytes config (Ix.Claim.ser conditional).data #[]),
    ("byte verifier rejects another claim kind", !stage2VerifyBytes config
      (Ix.Claim.ser (.check ⟨⟨root.bytes⟩⟩ none)).data #[]),
    ("typed public adapter rejects failed protocol verification", !_root_.MultiStark.Stage2.stage2Verify config typed ⟨#[]⟩),
    ("typed public adapter never drops assumptions", !_root_.MultiStark.Stage2.stage2Verify config conditional ⟨#[]⟩),
    ("malformed conditional addresses can alias a closed byte envelope", (decodeClosedCheckEnv (Ix.Claim.ser alias).data).isOk),
    ("typed public adapter rejects the original malformed conditional value", !_root_.MultiStark.Stage2.stage2Verify config alias ⟨#[]⟩)
  ]

public def suite : IO UInt32 := runChecks "stage2-source" checks

end Tests.MultiStark.Verify.Source
