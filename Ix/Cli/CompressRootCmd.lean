/-
`ix compress-root ROOT_ADDRESS` turns one closed, persisted `ix_aggr` root
into an SP1 proof and, by default, a final Groth16 SNARK.

The default protocol rebuilds the deterministic recursion backend,
reconstructs the uniform 18-word outer claim from the wrapper's `CheckEnv`,
and passes exactly that key/claim/proof triple to the current SP1 guest. A
separate, explicitly selected compatibility protocol accepts only the audited
2026-09-03 Mathlib artifact and uses its version-pinned verifier guest.

Open roots are rejected for every proof-producing mode. Execute-only profiling
may opt into one with `--allow-open-root` so a small retained-subtree fixture
can exercise the current guest.
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

inductive Protocol where
  | current
  | mathlib20260903
  deriving BEq, DecidableEq, Repr

def Protocol.label : Protocol → String
  | .current => "current"
  | .mathlib20260903 => "mathlib-2026-09-03"

def parseProtocol : String → Except String Protocol
  | "current" => pure .current
  | "mathlib-2026-09-03" => pure .mathlib20260903
  | other => throw s!"unknown aggregate protocol `{other}` \
(current|mathlib-2026-09-03)"

def mathlib20260903AggregateAddress : Address :=
  (Address.fromString
    "c2fdce660eb66899efa303b41d4ca1611a62a688ef20684fdc327739d38bd67f").get!

def mathlib20260903RootAddress : Address :=
  (Address.fromString
    "3211abb340539c10220990fb095f8763cb3a364e111ebe57fb518992d42d7382").get!

/-- The legacy guest is an artifact-specific protocol, not a general old
verifier and never an automatic fallback from the current verifier. -/
def validateProtocolRoot (protocol : Protocol) (address : Address)
    (claim : Ix.Claim) : Except String Unit := do
  match protocol with
  | .current => pure ()
  | .mathlib20260903 =>
    if address != mathlib20260903AggregateAddress then
      throw s!"protocol mathlib-2026-09-03 accepts only aggregate root \
{mathlib20260903AggregateAddress}"
    if claim != .checkEnv mathlib20260903RootAddress none then
      throw s!"protocol mathlib-2026-09-03 requires the pinned closed claim \
CheckEnv({mathlib20260903RootAddress}, none)"

private def addrOfHex! (label : String) (s : String) : IO Address := do
  match Address.fromString s with
  | some a => pure a
  | none =>
    throw <| IO.userError
      s!"error: {label}: expected 64-char hex (32-byte address), got {s.length}-char {s}"

/-- Canonical guest claim encoding: one little-endian u64 per Goldilocks word. -/
def outerClaimBytes (claim : Array Aiur.G) : ByteArray :=
  claim.foldl (init := .empty) fun bytes value => bytes ++ value.val.toLEBytes

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
  let protocolName :=
    (p.flag? "protocol").map (·.as! String) |>.getD "current"
  let protocol ← match parseProtocol protocolName with
    | .ok protocol => pure protocol
    | .error error => IO.eprintln s!"error: {error}"; return 1
  let allowOpenRoot := p.hasFlag "allow-open-root"
  let output := (p.flag? "output").map (·.as! String) |>.getD ""
  let onchainOutput := (p.flag? "onchain-output").map (·.as! String) |>.getD ""
  let rootAddress ← addrOfHex! "aggregate root" rootHex
  let wrapper ← match Ixon.Proof.de (← StoreIO.toIO (Store.read rootAddress)) with
    | .ok wrapper => pure wrapper
    | .error error =>
      IO.eprintln s!"error: aggregate wrapper {rootAddress} does not decode: {error}"
      return 1
  match validateBundledClaim wrapper.claim mode allowOpenRoot with
  | .ok () => pure ()
  | .error error => IO.eprintln s!"error: {error}"; return 1
  match validateProtocolRoot protocol rootAddress wrapper.claim with
  | .ok () => pure ()
  | .error error => IO.eprintln s!"error: {error}"; return 1
  if protocol == .mathlib20260903 && allowOpenRoot then
    IO.eprintln "error: --allow-open-root applies only to the current protocol"
    return 1

  IO.println s!"Compressing aggregate root {rootAddress} with SP1 ({mode})"
  IO.println s!"  protocol: {protocol.label}"
  IO.println s!"  bundled claim: {wrapper.claim}"
  let result ← match protocol with
    | .current => do
      let recursionParameters := MultiStark.defaultRecursionParameters
      let backend ← match ← Ix.Cli.VerifyCmd.buildAggregateBackend recursionParameters with
        | .ok backend => pure backend
        | .error error => IO.eprintln s!"error: {error}"; return 1
      let outerClaim := Ix.Cli.AggregateCmd.aggregateOuterClaim
        backend.allowed backend.aggrIdx wrapper.claim
      if outerClaim.size != 18 then
        IO.eprintln s!"error: internal ix_aggr claim width is {outerClaim.size}, expected 18"
        return 1
      IO.println s!"  recursion vk: {Address.blake3 backend.system.vkBytes}"
      (← IO.getStdout).flush
      pure <| Aiur.sp1CompressAggregateRoot backend.system.vkBytes
        (outerClaimBytes outerClaim) wrapper.proof recursionParameters.fri
        mode output onchainOutput
    | .mathlib20260903 => do
      IO.println "  multi-stark: 2892243e674f9a0b3aca9004a8d00c79a23beec1"
      IO.println "  recursion vk: be6f790a7a978336ab513cb77c9e208a606df72f9167e4a264778da641749768"
      (← IO.getStdout).flush
      pure <| Aiur.sp1CompressMathlib20260903 wrapper.proof mode output onchainOutput
  match result with
  | .ok () =>
    IO.println s!"ok: SP1 {mode} accepted aggregate root {rootAddress} \
under protocol {protocol.label}"
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
    "protocol" : String;       "Verifier protocol: current | mathlib-2026-09-03 (default: current)."
    "output" : String;         "Save the verified SP1 SDK proof container at this path."
    "onchain-output" : String; "For groth16/plonk, save the raw onchain proof bytes at this path."
    "allow-open-root";         "Allow a root retaining assumptions for execute-only guest profiling; never permits proof generation."

  ARGS:
    ...root : String; "Exactly one 32-byte store address of a persisted aggregate root."
]

end
