/-
`ix flock-leaf PROOF_ADDRESS` profiles or proves the Flock verifier relation
for one persisted raw IxVM proof. It is a development command: the complete
relation verifies the exact ten-word P3 statement but does not yet fold the
`CheckEnv` preimage or emit a recursive Stage 2 artifact.
-/
module
public import Cli
public import Ix.Address
public import Ix.Aiur.Protocol
public import Ix.Cli.VerifyCmd
public import Ix.IxVM.ClaimHarness
public import Ix.Ixon
public import Ix.Store
public import Ix.Unsigned

public section

namespace Ix.Cli.FlockLeafCmd

structure IxvmLeafInputs where
  proofAddress : Address
  bundledClaim : Ix.Claim
  verifyingKey : ByteArray
  p3Claim : ByteArray
  proof : ByteArray
  fri : Aiur.FriParameters
  verifyClaimIndex : Nat

private def claimBytes (claim : Array Aiur.G) : ByteArray :=
  claim.foldl (init := .empty) fun bytes value =>
    bytes ++ value.val.toLEBytes

def prepareIxvmLeafInputs (proofHex : String) : IO (Except String IxvmLeafInputs) := do
  let some proofAddress := Address.fromString proofHex
    | return .error s!"IxVM proof: expected 64-char hex (32-byte address), \
        got {proofHex.length}-char {proofHex}"
  let wrapper ← match Ixon.Proof.de (← StoreIO.toIO (Store.read proofAddress)) with
    | .ok wrapper => pure wrapper
    | .error error =>
      return .error s!"IxVM proof wrapper {proofAddress} does not decode: {error}"
  let (system, compiled) ← match ← Ix.Cli.VerifyCmd.buildBackend with
    | .ok backend => pure backend
    | .error error => return .error error
  let verifyClaimIndex ← match compiled.getFuncIdx `verify_claim with
    | some index => pure index
    | none => return .error "`verify_claim` is missing from the IxVM system"
  let claimDigest := Address.blake3 (Ix.Claim.ser wrapper.claim)
  let input := IxVM.ClaimHarness.packedDigestKey claimDigest
  let p3ClaimWords := Aiur.buildClaim verifyClaimIndex input #[]
  if p3ClaimWords.size != 10 then
    return .error s!"internal IxVM claim width is {p3ClaimWords.size}, expected 10"
  return .ok {
    proofAddress
    bundledClaim := wrapper.claim
    verifyingKey := system.vkBytes
    p3Claim := claimBytes p3ClaimWords
    proof := wrapper.proof
    fri := Aiur.defaultFriParameters
    verifyClaimIndex
  }

def runFlockLeafCmd (p : Cli.Parsed) : IO UInt32 := do
  let proofs := (p.variableArgsAs! String).toList
  let proofHex ← match proofs with
    | [proof] => pure proof
    | [] => p.printError "error: expected one raw IxVM proof address"; return 1
    | _ => p.printError "error: expected exactly one raw IxVM proof address"; return 1
  let mode := (p.flag? "mode").map (·.as! String) |>.getD "preflight"
  if mode != "profile" && mode != "pcs-size" && mode != "size" &&
      mode != "pcs" && mode != "preflight" && mode != "prove" then
    IO.eprintln s!"error: unknown Flock leaf mode `{mode}` \
      (expected profile|pcs-size|size|pcs|preflight|prove)"
    return 1
  let queries? := (p.flag? "queries").map (·.as! Nat)
  let queryCount := queries?.getD 1
  if queryCount == 0 then
    IO.eprintln "error: --queries must be at least one"
    return 1
  if mode != "pcs" && mode != "pcs-size" && queries?.isSome then
    IO.eprintln "error: --queries is only valid with --mode pcs or pcs-size"
    return 1
  let inputs ← match ← prepareIxvmLeafInputs proofHex with
    | .ok inputs => pure inputs
    | .error error => IO.eprintln s!"error: {error}"; return 1
  IO.println s!"Flock Stage 2 {mode}: raw IxVM proof {inputs.proofAddress}"
  IO.println s!"  bundled claim: {inputs.bundledClaim}"
  IO.println s!"  IxVM vk: {Address.blake3 inputs.verifyingKey}"
  IO.println s!"  compact proof: {inputs.proof.size} bytes"
  (← IO.getStdout).flush
  match Aiur.flockStage2IxvmLeaf inputs.verifyingKey inputs.p3Claim
      inputs.proof inputs.fri inputs.verifyClaimIndex queryCount mode with
  | .ok () =>
    IO.println s!"ok: Flock Stage 2 {mode} accepted IxVM proof {inputs.proofAddress}"
    return 0
  | .error error =>
    IO.eprintln s!"error: Flock Stage 2 {mode} failed: {error}"
    return 1

end Ix.Cli.FlockLeafCmd

open Ix.Cli.FlockLeafCmd in
def flockLeafCmd : Cli.Cmd := `[Cli|
  "flock-leaf" VIA runFlockLeafCmd;
  "Preflight or prove one raw IxVM P3 proof with Flock Stage 2 (build with IX_FLOCK=1)"

  FLAGS:
    "mode" : String; "Stage 2 leaf action: profile | pcs-size | size | pcs | preflight | prove (default: preflight)."
    "queries" : Nat; "PCS/FRI query-prefix length for --mode pcs or pcs-size (default: 1)."

  ARGS:
    ...proof : String; "Exactly one persisted raw IxVM proof-wrapper address."
]

end
