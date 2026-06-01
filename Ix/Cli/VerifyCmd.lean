/-
  `ix verify <proof-hex>`: read a persisted `Ixon.Proof` wrapper from
  the content-addressed store, extract the inner claim + opaque ZK
  proof bytes, reconstruct the Aiur-level public input, and run the
  Aiur backend's `verify`. Exits 0 on success, 1 with an error
  message otherwise.

  The wrapper carries the claim, so this command takes only the proof
  hex — no separate claim arg.
-/
module
public import Cli
public import Ix.Address
public import Ix.Aiur.Compiler
public import Ix.Aiur.Protocol
public import Ix.Claim
public import Ix.Common
public import Ix.IxVM
public import Ix.IxVM.ClaimHarness
public import Ix.Store

public section

open System (FilePath)

namespace Ix.Cli.VerifyCmd

private def addrOfHex! (label : String) (s : String) : IO Address := do
  match Address.fromString s with
  | some a => pure a
  | none =>
    throw <| IO.userError
      s!"error: {label}: expected 64-char hex (32-byte address), got {s.length}-char {s}"

/-- Same parameters as `ix prove`. Mismatch makes verification fail
    silently with no useful diagnostic, so these MUST match the
    proving side until they migrate into the proof header. -/
private def commitmentParameters : Aiur.CommitmentParameters :=
  { logBlowup := 1, capHeight := 0 }

private def friParameters : Aiur.FriParameters := {
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 100
  commitProofOfWorkBits := 20
  queryProofOfWorkBits := 0
}

def runVerifyCmd (p : Cli.Parsed) : IO UInt32 := do
  let some proofArg := p.positionalArg? "proof"
    | p.printError "error: must specify <proof-hex>"; return 1
  let proofAddr ← addrOfHex! "proof" (proofArg.as! String)

  -- 1. Load + decode the wrapper from the store.
  let bytes ← StoreIO.toIO (Store.read proofAddr)
  let wrapper ← IO.ofExcept (Ixon.Proof.de bytes)

  -- 2. Recover the Aiur Proof object from the opaque bytes.
  let proof := Aiur.Proof.ofBytes wrapper.proof

  -- 3. Rebuild the Aiur backend (must match the proving side).
  let toplevel ← match IxVM.ixVM with
    | .error e => IO.eprintln s!"toplevel merging failed: {e}"; return 1
    | .ok t => pure t
  let compiled ← match toplevel.compile with
    | .error e => IO.eprintln s!"compilation failed: {e}"; return 1
    | .ok c => pure c
  let aiurSystem := Aiur.AiurSystem.build compiled.bytecode commitmentParameters

  -- 4. Reconstruct the Aiur-level public input from the wrapper's
  -- claim. `verify_claim` takes a 32-G blake3 digest of the
  -- serialized claim bytes (see `IxVM.ClaimHarness.buildClaimWitness`).
  let claimDigest := Address.blake3 (Ix.Claim.ser wrapper.claim)
  let funIdx ← match compiled.getFuncIdx `verify_claim with
    | some i => pure i
    | none =>
      IO.eprintln "error: `verify_claim` entrypoint missing from compiled toplevel"
      return 1
  let input : Array Aiur.G := claimDigest.hash.data.map .ofUInt8
  let aiurClaim := Aiur.buildClaim funIdx input #[]

  -- 5. Verify.
  match aiurSystem.verify friParameters aiurClaim proof with
  | .ok () =>
    IO.println s!"ok: proof {proofAddr} verifies claim {claimDigest}"
    return 0
  | .error e =>
    IO.eprintln s!"error: verification failed: {e}"
    return 1

end Ix.Cli.VerifyCmd

open Ix.Cli.VerifyCmd in
def verifyCmd : Cli.Cmd := `[Cli|
  verify VIA runVerifyCmd;
  "Verify a STARK proof against its bundled claim"

  ARGS:
    proof : String; "32-byte hex address of the persisted `Ixon.Proof` wrapper in `~/.ix/store/`."
]

end
