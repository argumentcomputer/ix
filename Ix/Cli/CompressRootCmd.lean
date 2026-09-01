/-
`ix compress-root ROOT_ADDRESS` turns one closed, persisted `ix_aggr` root
into an SP1 proof and, by default, a final Groth16 SNARK.

The command rebuilds the deterministic recursion backend, reconstructs the
uniform 18-word outer claim from the wrapper's `CheckEnv`, and passes exactly
that key/claim/proof triple to the SP1 guest. Open roots are rejected for every
proof-producing mode. Execute-only profiling may opt into one with
`--allow-open-root` so a small retained-subtree fixture can exercise the guest.
-/
module
public import Cli
public import Ix.Address
public import Ix.Aiur.Protocol
public import Ix.Aggr
public import Ix.Cli.AggregateCmd
public import Ix.Cli.VerifyCmd
public import Ix.Ixon
public import Ix.MultiStark
public import Ix.Store
public import Ix.Unsigned

public section

namespace Ix.Cli.CompressRootCmd

/-- Canonical guest claim encoding: one little-endian u64 per Goldilocks word. -/
def outerClaimBytes (claim : Array Aiur.G) : ByteArray :=
  claim.foldl (init := .empty) fun bytes value => bytes ++ value.val.toLEBytes

/-- Canonical terminal-backend transport reconstructed from a persisted
aggregate wrapper. SP1 and Flock share this adapter so they cannot drift on the
recursion key, outer claim, proof bytes, or FRI parameters. -/
structure AggregateRootInputs where
  rootAddress : Address
  bundledClaim : Ix.Claim
  verifyingKey : ByteArray
  outerClaim : ByteArray
  proof : ByteArray
  fri : Aiur.FriParameters

def prepareAggregateRootInputs (rootHex : String) : IO (Except String AggregateRootInputs) := do
  let some rootAddress := Address.fromString rootHex
    | return .error s!"aggregate root: expected 64-char hex (32-byte address), \
        got {rootHex.length}-char {rootHex}"
  let wrapper ← match Ixon.Proof.de (← StoreIO.toIO (Store.read rootAddress)) with
    | .ok wrapper => pure wrapper
    | .error error =>
      return .error s!"aggregate wrapper {rootAddress} does not decode: {error}"
  let recursionParameters := MultiStark.defaultRecursionParameters
  let backend ← match ← Ix.Cli.VerifyCmd.buildAggregateBackend recursionParameters with
    | .ok backend => pure backend
    | .error error => return .error error
  let outerClaim := Ix.Cli.AggregateCmd.aggregateOuterClaim
    backend.allowed backend.aggrIdx wrapper.claim
  if outerClaim.size != 18 then
    return .error s!"internal ix_aggr claim width is {outerClaim.size}, expected 18"
  return .ok {
    rootAddress
    bundledClaim := wrapper.claim
    verifyingKey := backend.system.vkBytes
    outerClaim := outerClaimBytes outerClaim
    proof := wrapper.proof
    fri := recursionParameters.fri
  }

/-- Final compression accepts only closed `CheckEnv` roots. The explicit open
escape hatch is intentionally execute-only: it exists for cycle profiling and
cannot produce a misleading terminal proof. -/
def validateBundledClaim (claim : Ix.Claim) (mode : String)
    (allowOpenRoot : Bool) : Except String Unit := do
  let .checkEnv _ assumptions := claim
    | throw "aggregate root wrapper does not contain a CheckEnv claim"
  if assumptions.isSome then
    if mode == "execute" && allowOpenRoot then pure ()
    else throw "aggregate root retains assumptions; final compression requires a closed root"
  else if allowOpenRoot && mode != "execute" then
    throw "--allow-open-root is restricted to --mode execute"

def runCompressRootCmd (p : Cli.Parsed) : IO UInt32 := do
  let roots := (p.variableArgsAs! String).toList
  let rootHex ← match roots with
    | [root] => pure root
    | [] => p.printError "error: expected one aggregate root address"; return 1
    | _ => p.printError "error: expected exactly one aggregate root address"; return 1
  let mode := (p.flag? "mode").map (·.as! String) |>.getD "groth16"
  let allowOpenRoot := p.hasFlag "allow-open-root"
  let output := (p.flag? "output").map (·.as! String) |>.getD ""
  let onchainOutput := (p.flag? "onchain-output").map (·.as! String) |>.getD ""
  let inputs ← match ← prepareAggregateRootInputs rootHex with
    | .ok inputs => pure inputs
    | .error error => IO.eprintln s!"error: {error}"; return 1
  match validateBundledClaim inputs.bundledClaim mode allowOpenRoot with
  | .ok () => pure ()
  | .error error => IO.eprintln s!"error: {error}"; return 1

  IO.println s!"Compressing aggregate root {inputs.rootAddress} with SP1 ({mode})"
  IO.println s!"  bundled claim: {inputs.bundledClaim}"
  IO.println s!"  recursion vk: {Address.blake3 inputs.verifyingKey}"
  (← IO.getStdout).flush
  match Aiur.sp1CompressAggregateRoot inputs.verifyingKey
      inputs.outerClaim inputs.proof inputs.fri
      mode output onchainOutput with
  | .ok () =>
    IO.println s!"ok: SP1 {mode} accepted aggregate root {inputs.rootAddress}"
    return 0
  | .error error =>
    IO.eprintln s!"error: SP1 root compression failed: {error}"
    return 1

end Ix.Cli.CompressRootCmd

open Ix.Cli.CompressRootCmd in
def compressRootCmd : Cli.Cmd := `[Cli|
  "compress-root" VIA runCompressRootCmd;
  "Compress one closed ix_aggr root through SP1 to a final SNARK (build with IX_SP1=1)"

  FLAGS:
    "mode" : String;           "SP1 stage: execute | core | compressed | groth16 | plonk (default: groth16)."
    "output" : String;         "Save the verified SP1 SDK proof container at this path."
    "onchain-output" : String; "For groth16/plonk, save the raw onchain proof bytes at this path."
    "allow-open-root";         "Allow a root retaining assumptions for execute-only guest profiling; never permits proof generation."

  ARGS:
    ...root : String; "Exactly one 32-byte store address of a persisted aggregate root."
]

end
