import Ix.MultiStark.Verify.Source
import Compilatrix.Tools.Check
import Compilatrix.Ixon.Hash

open Compilatrix Compilatrix.Tools.Check MultiStark.Verify

private def fixedConfig (directory : System.FilePath) : IO SourceConfig := do
  let ixvm ← IO.FS.readBinFile (directory / "ixvm.vk")
  let aggregate ← IO.FS.readBinFile (directory / "aggr.vk")
  need (ixvm.size == 744159 && (Ixon.Address.blake3 ixvm).toHex ==
    "3983867e9f70a82d990ea65e15265da105617317b95b4b1482e7a7b854ca8063")
    "fixed IxVM key differs"
  need (aggregate.size == 181630 && (Ixon.Address.blake3 aggregate).toHex ==
    "75452941bc0dbe4a861c88c792067f34d7864f0460f305858a0a004ec409406e")
    "fixed aggregate key differs"
  return {
    aggregate := {
      ixvmKey := ixvm.data, aggregateKey := aggregate.data
      verifyClaimEntry := Ix.Ixby.Goldilocks.reduce 755
      aggregateEntry := Ix.Ixby.Goldilocks.reduce 243 }
    decode := { bytes := 16777216, vector := 1048576, items := 2097152 }
    verifier := {
      queries := 1024, foldArity := 256
      transcript := { observationBytes := 16777216, sampleAttempts := 64 } } }

/-- Native execution of the unchanged source reference. This program is a
test oracle; it neither compiles nor executes an Ixby guest. Key loading and
fixture decompression belong to this test process, not the guest definition. -/
def main (args : List String) : IO UInt32 := cli "stage2-source-run" do
  let [directory, name] := args |
    throw (IO.userError "usage: stage2-source-run <fixture-directory> <case>")
  let directory : System.FilePath := directory
  need (["valid", "claim-mismatch", "empty-proof", "truncated-proof",
    "trailing-public", "trailing-proof", "wrong-claim-kind", "malformed-proof"].contains name)
    "unknown source test case"
  let config ← fixedConfig directory
  let publicClaim ← IO.FS.readBinFile (directory / "smoke-public.claim")
  let expectedClaim ← checked (unhex
    "e571cbf135649af05f7cce8ba201a48e46556de51483f690cc6ec500a65530059c00")
  need (publicClaim.size == 34 && publicClaim == expectedClaim)
    "source smoke claim differs"
  IO.FS.withTempDir fun temporary => do
    let archive := temporary / "proof.bin.gz"
    IO.FS.writeBinFile archive (← IO.FS.readBinFile (directory / "smoke-native-proof.bin.gz"))
    let _ ← run "gzip" #["-d", archive.toString]
    let proofFile := temporary / "proof.bin"
    let digest := (words (← run "sha256sum" #[proofFile.toString])).headD ""
    need (digest == "c495ab47db90bdb3b245391c18967e7c264ffb8d51c4c39605ee6f47cd0e7bb9")
      "source smoke proof differs"
    let proof ← IO.FS.readBinFile proofFile
    need (proof.size == 8555808) "source smoke proof length differs"
    let claim := match name with
      | "claim-mismatch" => publicClaim.data.set! 1 (publicClaim.data[1]! ^^^ 1)
      | "trailing-public" => publicClaim.data.push 0
      | "wrong-claim-kind" => publicClaim.data.set! 0 0xe4
      | _ => publicClaim.data
    let input := match name with
      | "empty-proof" => #[]
      | "truncated-proof" => proof.data.extract 0 (proof.size - 1)
      | "trailing-proof" => proof.data.push 0
      | "malformed-proof" => #[0xff, 0xff]
      | _ => proof.data
    let expected := if name == "valid" then some publicClaim.data else none
    let result := claimBytesWrapper config claim input
    need (result == expected) s!"source behavior changed in {name}: {reprStr result}"
    IO.println s!"stage2-source-run ok: {name}; {if result.isSome then "exact 34-byte claim" else "none"}; source reference only"
