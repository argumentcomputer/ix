/-
  `ix prove`: generate a STARK proof against an `Ix.Claim`. Mirrors
  the CLI shape of `ix check`:

      ix prove Nat.add_comm                            # compiled-in Lean env
      ix prove --ixe arena.ixe Foo.bar                 # from .ixe, named target
      ix prove --ixe arena.ixe                         # iterate every named const
      ix prove --ixe arena.ixe --claim <hex>           # against a persisted claim

  Each invocation runs the same `verify_claim` Aiur witness that
  `ix check` does, then drives Aiur's `prove` over it and persists
  the result as an `Ixon.Proof` wrapper (claim + opaque proof
  bytes). Prints the resulting proof blake3 hex on stdout — feed
  that to `ix verify <proof-hex>`.

  Per-claim mode (`--claim`) loads the claim from the store and
  resolves every referenced assumption / env / contains tree
  (build trees with `ix tree canonical` / `ix tree env`).

  Per-name mode builds a default `Claim.check addr none` and
  persists the claim alongside the proof so `ix verify` can stand
  alone with just the proof hex.

  Driven by the shared `Ix.Cli.CheckCmd.forEachClaim`: the only
  prove-specific surface is `runOne = proveOne aiurSystem compiled`.
-/
module
public import Cli
public import Std.Internal.UV.System
public import Ix.Aiur.Compiler
public import Ix.Aiur.Protocol
public import Ix.Claim
public import Ix.Cli.CheckCmd
public import Ix.Common
public import Ix.IxVM
public import Ix.IxVM.ClaimHarness
public import Ix.Ixon
public import Ix.Store

public section

open IxVM.ClaimHarness

namespace Ix.Cli.ProveCmd

/-- Canonical aiur params shared between prove and verify. Matches
    `Tests.Aiur.Common`. Until these become flags / commit to the
    proof header, they MUST stay in sync between `prove` and
    `verify`. -/
private def commitmentParameters : Aiur.CommitmentParameters :=
  { logBlowup := 1, capHeight := 0 }

private def friParameters : Aiur.FriParameters := {
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 100
  commitProofOfWorkBits := 20
  queryProofOfWorkBits := 0
}

/-- Run Aiur prove for one (claim, witness) pair, wrap into an
    `Ixon.Proof`, persist claim + wrapper, and print the resulting
    proof hex. Plugs into `Ix.Cli.CheckCmd.forEachClaim`. -/
def proveOne (aiurSystem : Aiur.AiurSystem)
    (compiled : Aiur.CompiledToplevel)
    (claim : Ix.Claim)
    (witness : IxVM.ClaimHarness.ClaimWitness)
    (label : String) : IO UInt32 := do
  IO.println s!"Proving {label}"
  (← IO.getStdout).flush
  let funIdx ← match compiled.getFuncIdx witness.funcName with
    | some i => pure i
    | none =>
      IO.eprintln s!"{label}: entrypoint `{witness.funcName}` missing from compiled toplevel"
      return 1
  let _ ← StoreIO.toIO (Store.write (Ix.Claim.ser claim))
  let (_aiurClaim, proof, _outIO) :=
    aiurSystem.prove friParameters funIdx witness.input witness.inputIOBuffer
  let wrapper : Ixon.Proof := { claim, proof := proof.toBytes }
  let proofAddr ← StoreIO.toIO (Store.write (Ixon.Proof.ser wrapper))
  IO.println (toString proofAddr)
  return 0

def runProveCmd (p : Cli.Parsed) : IO UInt32 := do
  Std.Internal.UV.System.osSetenv "IX_QUIET" "1"
  let keepGoing := p.hasFlag "keep-going"
  let ixePath : Option String := (p.flag? "ixe").map (·.as! String)
  let claimHex : Option String := (p.flag? "claim").map (·.as! String)
  let names := (p.variableArgsAs! String).toList
  let toplevel ← match IxVM.ixVM with
    | .error e => IO.eprintln s!"toplevel merging failed: {e}"; return 1
    | .ok t => pure t
  let compiled ← match toplevel.compile with
    | .error e => IO.eprintln s!"compilation failed: {e}"; return 1
    | .ok c => pure c
  let aiurSystem := Aiur.AiurSystem.build compiled.bytecode commitmentParameters
  Ix.Cli.CheckCmd.forEachClaim ixePath claimHex names keepGoing "prove"
    (proveOne aiurSystem compiled)

end Ix.Cli.ProveCmd

open Ix.Cli.ProveCmd in
def proveCmd : Cli.Cmd := `[Cli|
  prove VIA runProveCmd;
  "Generate a STARK proof for an `Ix.Claim` (mirrors `ix check`'s CLI shape)"

  FLAGS:
    "keep-going";       "Continue past failures and report them at the end instead of halting on the first."
    "ixe"   : String;   "Path to a serialized `.ixe` env. When set, the binary reads the env from disk instead of using the compiled-in Lean env."
    "claim" : String;   "32-byte hex address of a persisted `Ix.Claim` in `~/.ix/store/`. When set, proves the persisted claim against the `--ixe` env (single proof, skips per-const iteration)."

  ARGS:
    ...names : String; "Fully-qualified Lean.Name(s) to prove. With none, iterate every named constant in the env (sorted)."
]

end
