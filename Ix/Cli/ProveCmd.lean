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

def proveOne (aiurSystem : Aiur.AiurSystem)
    (compiled : Aiur.CompiledToplevel)
    (claim : Ix.Claim)
    (src : Ix.Cli.CheckCmd.WitnessSource)
    (label : String) : IO UInt32 := do
  IO.println s!"Proving {label}"
  (← IO.getStdout).flush
  let funIdx ← match compiled.getFuncIdx `verify_claim with
    | some i => pure i
    | none =>
      IO.eprintln s!"{label}: entrypoint `verify_claim` missing from compiled toplevel"
      return 1
  let _ ← StoreIO.toIO (Store.write (Ix.Claim.ser claim))
  -- Native IxVM path: routes execution through the codegen'd Rust
  -- kernel (`execute_generated`). For `Claim.check addr none` via
  -- `--ixe`, witness + execute + STARK prove run end-to-end in
  -- Rust (`proveAddrIxVM`) — no Lean-side per-byte boxing into
  -- `Aiur.G`. The Lean fallback path consumes a pre-built
  -- `ClaimWitness` (compiled-Lean-env, or a non-`check` persisted
  -- claim).
  let proof : Aiur.Proof ← match src with
    | .native ixe addr =>
      match aiurSystem.proveAddrIxVM friParameters funIdx
              ixe.toUTF8 addr.hash with
      | .error e =>
        IO.eprintln s!"{label}: proveAddrIxVM error: {e}"
        return 1
      | .ok (_aiurClaim, proof, _outIO) => pure proof
    | .nativeBytes envBytes addr =>
      match aiurSystem.proveEnvBytesIxVM friParameters funIdx envBytes addr.hash with
      | .error e =>
        IO.eprintln s!"{label}: proveEnvBytesIxVM error: {e}"
        return 1
      | .ok (_aiurClaim, proof, _outIO) => pure proof
    | .lean witness =>
      let (_aiurClaim, proof, _outIO) :=
        aiurSystem.proveIxVM friParameters funIdx witness.input witness.inputIOBuffer
      pure proof
  let wrapper : Ixon.Proof := { claim, proof := proof.toBytes }
  let proofAddr ← StoreIO.toIO (Store.write (Ixon.Proof.ser wrapper))
  IO.println (toString proofAddr)
  return 0

/-- Per-shard prove via the end-to-end Rust path
    (`shardProveIxVM`): witness build, `execute_ixvm`, and STARK
    prove run in one FFI trip with the parallel Rust witness
    builder. -/
def runShardProveNative (manifestPath ixePath : String) (shardK : Nat)
    (aiurSystem : Aiur.AiurSystem) (compiled : Aiur.CompiledToplevel)
    (printStats : Bool) : IO UInt32 := do
  match (← Ix.Cli.CheckCmd.loadEnvAndShards manifestPath ixePath) with
  | .error e => IO.eprintln e; return 1
  | .ok (ixonEnv, shards) =>
    match shards[shardK]? with
    | none => IO.eprintln s!"shard {shardK} out of range (0..{shards.size})"; return 1
    | some blocks => do
      let owned := Ix.Cli.CheckCmd.ownedConstsForBlocks ixonEnv blocks
      let mut blob := ByteArray.empty
      for a in owned do
        blob := blob ++ a.hash
      let label := s!"shard {shardK}"
      IO.println s!"Proving {label}"
      (← IO.getStdout).flush
      let funIdx := compiled.getFuncIdx `verify_claim |>.get!
      match aiurSystem.shardProveIxVM friParameters funIdx
              ixePath.toUTF8 blob with
      | .error e =>
        IO.eprintln s!"{label}: shardProveIxVM error: {e}"
        return 1
      | .ok (_aiurClaim, proof, _outIO) =>
        -- Reconstruct the shard's CheckEnv claim from the owned
        -- blocks so we can persist (claim, proof) like proveOne.
        match IxVM.ClaimHarness.shardCheckEnvClaim ixonEnv owned with
        | .error e =>
          IO.eprintln s!"{label}: claim reconstruct failed: {e}"
          return 1
        | .ok (claim, _closure, _trees) => do
          let _ ← StoreIO.toIO (Store.write (Ix.Claim.ser claim))
          let wrapper : Ixon.Proof := { claim, proof := proof.toBytes }
          let proofAddr ← StoreIO.toIO (Store.write (Ixon.Proof.ser wrapper))
          IO.println (toString proofAddr)
          if printStats then pure ()  -- TODO: surface query-counts if needed
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
  let runOne := proveOne aiurSystem compiled
  match ixePath, (p.flag? "ixes").map (·.as! String), (p.flag? "shard").map (·.as! Nat) with
  | some ixe, some manifest, some k =>
    -- IxVM-native shard prove: witness + execute + STARK prove all
    -- in Rust via `shardProveIxVM`.
    runShardProveNative manifest ixe k aiurSystem compiled false
  | some ixe, some manifest, none =>
    match (← Ix.Cli.CheckCmd.loadEnvAndShards manifest ixe) with
    | .error e => IO.eprintln e; return 1
    | .ok (_, shards) =>
      let mut rc : UInt32 := 0
      for k in [0 : shards.size] do
        if (← runShardProveNative manifest ixe k aiurSystem compiled false) != 0 then
          rc := 1
      pure rc
  | _, _, _ =>
    Ix.Cli.CheckCmd.forEachClaim ixePath claimHex names keepGoing "prove" runOne

end Ix.Cli.ProveCmd

open Ix.Cli.ProveCmd in
def proveCmd : Cli.Cmd := `[Cli|
  prove VIA runProveCmd;
  "Generate a STARK proof for an `Ix.Claim` (mirrors `ix check`'s CLI shape)"

  FLAGS:
    "keep-going";       "Continue past failures and report them at the end instead of halting on the first."
    "ixe"   : String;   "Path to a serialized `.ixe` env. When set, the binary reads the env from disk instead of using the compiled-in Lean env."
    "claim" : String;   "32-byte hex address of a persisted `Ix.Claim` in `~/.ix/store/`. When set, proves the persisted claim against the `--ixe` env (single proof, skips per-const iteration)."
    "ixes"  : String;   "Path to a `.ixes` shard manifest (with --ixe). With --shard K: prove shard K. Without --shard: prove every shard in the partition."
    "shard" : Nat;      "0-based shard index K (with --ixes and --ixe): prove that one shard's CheckEnv claim."

  ARGS:
    ...names : String; "Fully-qualified Lean.Name(s) to prove. With none, iterate every named constant in the env (sorted)."
]

end
