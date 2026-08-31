/-
`ix flock-root ROOT_ADDRESS` consumes the same canonical aggregate-root
transport as `ix compress-root`, then either compiles/evaluates the complete
Stage 3 relation (`preflight`) or emits a verified Flock artifact (`prove`).

Preflight deliberately stops before the cryptographic prover. It is the cheap
compatibility and capacity gate for a production-sized Stage 2 aggregate.
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

namespace Ix.Cli.FlockRootCmd

/-- Canonical terminal claim encoding: one little-endian u64 per Goldilocks
word. -/
def outerClaimBytes (claim : Array Aiur.G) : ByteArray :=
  claim.foldl (init := .empty) fun bytes value => bytes ++ value.val.toLEBytes

/-- Canonical Flock transport reconstructed from a persisted aggregate
wrapper. -/
structure AggregateRootInputs where
  rootAddress : Address
  bundledClaim : Ix.Claim
  verifyingKey : ByteArray
  outerClaim : ByteArray
  proof : ByteArray
  fri : Aiur.FriParameters

def prepareAggregateRootInputs
    (rootHex : String) : IO (Except String AggregateRootInputs) := do
  let some rootAddress := Address.fromString rootHex
    | return .error s!"aggregate root: expected 64-char hex (32-byte address), \
        got {rootHex.length}-char {rootHex}"
  let wrapper ← match Ixon.Proof.de (← StoreIO.toIO (Store.read rootAddress)) with
    | .ok wrapper => pure wrapper
    | .error error =>
      return .error s!"aggregate wrapper {rootAddress} does not decode: {error}"
  let recursionParameters := MultiStark.defaultRecursionParameters
  let backend ←
    match ← Ix.Cli.VerifyCmd.buildAggregateBackend recursionParameters with
    | .ok backend => pure backend
    | .error error => return .error error
  let outerClaim := Ix.Cli.AggregateCmd.aggregateOuterClaim
    backend.allowed backend.aggrIdx wrapper.claim
  if outerClaim.size != 18 then
    return .error
      s!"internal ix_aggr claim width is {outerClaim.size}, expected 18"
  return .ok {
    rootAddress
    bundledClaim := wrapper.claim
    verifyingKey := backend.system.vkBytes
    outerClaim := outerClaimBytes outerClaim
    proof := wrapper.proof
    fri := recursionParameters.fri
  }

/-- Flock Stage 3 accepts only closed aggregate roots. -/
def validateBundledClaim (claim : Ix.Claim) : Except String Unit := do
  let .checkEnv _ assumptions := claim
    | throw "aggregate root wrapper does not contain a CheckEnv claim"
  if assumptions.isSome then
    throw "aggregate root retains assumptions; Flock Stage 3 requires a closed root"

def runFlockRootCmd (p : Cli.Parsed) : IO UInt32 := do
  let roots := (p.variableArgsAs! String).toList
  let rootHex ← match roots with
    | [root] => pure root
    | [] => p.printError "error: expected one aggregate root address"; return 1
    | _ => p.printError "error: expected exactly one aggregate root address"; return 1
  let mode := (p.flag? "mode").map (·.as! String) |>.getD "preflight"
  if mode != "preflight" && mode != "prove" then
    IO.eprintln s!"error: unknown Flock mode `{mode}` (expected preflight|prove)"
    return 1
  let output := (p.flag? "output").map (·.as! String) |>.getD ""
  if mode == "preflight" && !output.isEmpty then
    IO.eprintln "error: --output is only valid with --mode prove"
    return 1
  if mode == "prove" && output.isEmpty then
    IO.eprintln "error: Flock proving requires --output"
    return 1

  let inputs ← match ← prepareAggregateRootInputs rootHex with
    | .ok inputs => pure inputs
    | .error error => IO.eprintln s!"error: {error}"; return 1
  match validateBundledClaim inputs.bundledClaim with
  | .ok () => pure ()
  | .error error => IO.eprintln s!"error: {error}"; return 1

  IO.println s!"Flock Stage 3 {mode}: aggregate root {inputs.rootAddress}"
  IO.println s!"  bundled claim: {inputs.bundledClaim}"
  IO.println s!"  recursion vk: {Address.blake3 inputs.verifyingKey}"
  (← IO.getStdout).flush
  match Aiur.flockStage3AggregateRoot inputs.verifyingKey inputs.outerClaim
      inputs.proof inputs.fri mode output with
  | .ok () =>
    IO.println s!"ok: Flock Stage 3 {mode} accepted aggregate root {inputs.rootAddress}"
    return 0
  | .error error =>
    IO.eprintln s!"error: Flock Stage 3 {mode} failed: {error}"
    return 1

end Ix.Cli.FlockRootCmd

open Ix.Cli.FlockRootCmd in
def flockRootCmd : Cli.Cmd := `[Cli|
  "flock-root" VIA runFlockRootCmd;
  "Preflight or prove one closed ix_aggr root with Flock Stage 3 (build with IX_FLOCK=1)"

  FLAGS:
    "mode" : String;   "Stage 3 action: preflight | prove (default: preflight)."
    "output" : String; "Atomically save the verified Stage3ArtifactV1 (required for prove)."

  ARGS:
    ...root : String; "Exactly one 32-byte store address of a persisted aggregate root."
]

end
