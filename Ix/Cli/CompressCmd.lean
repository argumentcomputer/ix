/-
  `ix compress <proof-hex>`: read a persisted `Ixon.Proof` wrapper from the
  content-addressed store and re-verify it inside the SP1 zkVM, producing a
  recursive SP1 proof of that verification — a constant-size compression of
  the (multi-MB) Aiur multi-STARK proof. See `sp1-compress/README.md`.

  The SP1 proof's public values bind `blake3(vk) || fri params || claim`;
  a downstream consumer must check those against known-good values plus the
  SP1 verifying key of the `sp1-compress-guest` program.

  Requires an `IX_SP1=1 lake build` binary; otherwise the FFI stub reports
  that SP1 support is compiled out.
-/
module
public import Cli
public import Ix.Address
public import Ix.Aiur.Compiler
public import Ix.Aiur.Protocol
public import Ix.Claim
public import Ix.Common
public import Ix.IxVM
public import Ix.Ixon
public import Ix.Store
public import Ix.Unsigned
public import Ix.Cli.VerifyCmd

public section

namespace Ix.Cli.CompressCmd

private def addrOfHex! (label : String) (s : String) : IO Address := do
  match Address.fromString s with
  | some a => pure a
  | none =>
    throw <| IO.userError
      s!"error: {label}: expected 64-char hex (32-byte address), got {s.length}-char {s}"

/-- Same parameters as `ix prove` / `ix verify`. The SP1 guest re-runs the
    Aiur verifier with these, so a mismatch fails in-circuit. MUST stay in
    sync until they migrate into the proof header. -/
private def friParameters : Aiur.FriParameters := {
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 100
  commitProofOfWorkBits := 20
  queryProofOfWorkBits := 0
}

/-- Aiur claim → guest wire format: one canonical u64 LE per element. -/
private def claimToLEBytes (claim : Array Aiur.G) : ByteArray :=
  claim.foldl (init := .empty) fun acc g => acc ++ g.val.toLEBytes

def runCompressCmd (p : Cli.Parsed) : IO UInt32 := do
  let some proofArg := p.positionalArg? "proof"
    | p.printError "error: must specify <proof-hex>"; return 1
  let mode := (p.flag? "mode").map (·.as! String) |>.getD "compressed"
  let output := (p.flag? "output").map (·.as! String) |>.getD ""
  let proofAddr ← addrOfHex! "proof" (proofArg.as! String)
  let bytes ← StoreIO.toIO (Store.read proofAddr)
  let wrapper ← IO.ofExcept (Ixon.Proof.de bytes)
  let (aiurSystem, compiled) ← match (← Ix.Cli.VerifyCmd.buildBackend) with
    | .error e => IO.eprintln e; return 1
    | .ok b => pure b
  let funIdx ← match compiled.getFuncIdx `verify_claim with
    | some i => pure i
    | none =>
      IO.eprintln "error: `verify_claim` entrypoint missing from compiled toplevel"
      return 1
  -- Same public-input reconstruction as `ix verify`: `verify_claim` takes
  -- the 32-G blake3 digest of the serialized claim.
  let claimDigest := Address.blake3 (Ix.Claim.ser wrapper.claim)
  let input : Array Aiur.G := claimDigest.hash.data.map .ofUInt8
  let aiurClaim := Aiur.buildClaim funIdx input #[]
  IO.println s!"Compressing proof {proofAddr} (claim {claimDigest}) in SP1, mode={mode}"
  (← IO.getStdout).flush
  match Aiur.sp1CompressAiurProof aiurSystem.vkBytes (claimToLEBytes aiurClaim)
      wrapper.proof friParameters mode output with
  | .ok () =>
    IO.println s!"ok: SP1 ({mode}) accepted proof {proofAddr} for claim {claimDigest}"
    return 0
  | .error e =>
    IO.eprintln s!"error: SP1 compress failed: {e}"
    return 1

end Ix.Cli.CompressCmd

open Ix.Cli.CompressCmd in
def compressCmd : Cli.Cmd := `[Cli|
  compress VIA runCompressCmd;
  "Compress a persisted STARK proof by re-verifying it inside the SP1 zkVM (needs an `IX_SP1=1` build)"

  FLAGS:
    "mode" : String;   "SP1 stage: execute | core | compressed | groth16 | plonk (default: compressed). `execute` only emulates and prints cycle counts; groth16/plonk need Docker for the gnark wrapper."
    "output" : String; "Path to save the SP1 proof to (the SDK's `.save()` bincode format)."

  ARGS:
    proof : String; "32-byte hex address of a persisted `Ixon.Proof` wrapper in `~/.ix/store/`."
]

end
