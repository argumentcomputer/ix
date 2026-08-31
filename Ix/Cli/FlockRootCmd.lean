/-
`ix flock-root ROOT_ADDRESS` consumes the same canonical aggregate-root
transport as `ix compress-root`, then either compiles/evaluates the complete
Stage 3 relation (`preflight`) or emits a verified Flock artifact (`prove`).

Preflight deliberately stops before the cryptographic prover. It is the cheap
compatibility and capacity gate for a production-sized Stage 2 aggregate.
-/
module
public import Cli
public import Ix.Cli.CompressRootCmd

public section

namespace Ix.Cli.FlockRootCmd

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

  let inputs ← match ← Ix.Cli.CompressRootCmd.prepareAggregateRootInputs rootHex with
    | .ok inputs => pure inputs
    | .error error => IO.eprintln s!"error: {error}"; return 1
  match Ix.Cli.CompressRootCmd.validateBundledClaim
      inputs.bundledClaim mode false with
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
