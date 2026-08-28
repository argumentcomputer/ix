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
public import Ix.Aiur.Compiler
public import Ix.Aiur.Protocol
public import Ix.Claim
public import Ix.Cli.CheckCmd
public import Ix.Common
public import Ix.IxVM
public import Ix.IxVM.Toplevel
public import Ix.IxVM.ClaimHarness
public import Ix.Ixon
public import Ix.Store

public section

open IxVM.ClaimHarness

namespace Ix.Cli.ProveCmd

/-- Canonical aiur params shared between prove and verify (the shared
    defaults in `Ix.Aiur.Protocol`). Matches `Tests.Aiur.Common`. Until
    these become flags / commit to the proof header, they MUST stay in
    sync between `prove` and `verify`. -/
private def commitmentParameters : Aiur.CommitmentParameters :=
  Aiur.defaultCommitmentParameters

private def friParameters : Aiur.FriParameters :=
  Aiur.defaultFriParameters

def proveOne (aiurSystem : Aiur.AiurSystem)
    (compiled : Aiur.CompiledToplevel)
    (claim : Ix.Claim)
    (envHandle? : Option Aiur.EnvHandle)
    (target : Ix.Cli.CheckCmd.Target)
    (label : String) : IO UInt32 := do
  IO.println s!"Proving {label}"
  (← IO.getStdout).flush
  let funIdx ← match compiled.getFuncIdx `verify_claim with
    | some i => pure i
    | none =>
      IO.eprintln s!"{label}: entrypoint `verify_claim` missing from compiled toplevel"
      return 1
  let _ ← StoreIO.toIO (Store.write (Ix.Claim.ser claim))
  -- Native IxVM path: routes execution + STARK prove through the
  -- codegen'd Rust kernel. `.addr` / `.shard` go through the
  -- envHandle-based prove FFIs (witness + execute + prove all in
  -- one Rust trip). `.leanW` consumes a pre-built `ClaimWitness`
  -- via `proveIxVM` (used for non-`check addr none` `--claim hex`).
  let proof : Aiur.Proof ← match target, envHandle? with
    | .addr a, some envHandle =>
      match aiurSystem.proveAddrWithEnv funIdx envHandle a.hash with
      | .error e =>
        IO.eprintln s!"{label}: proveAddrWithEnv error: {e}"
        return 1
      | .ok (_claimBytes, proof, _outIO) => pure proof
    | .shard owned, some envHandle =>
      let mut blob := ByteArray.empty
      for x in owned do blob := blob ++ x.hash
      match aiurSystem.shardProveWithEnv funIdx envHandle blob with
      | .error e =>
        IO.eprintln s!"{label}: shardProveWithEnv error: {e}"
        return 1
      | .ok r => match r.proof with
        | some proof => pure proof
        | none =>
          IO.eprintln s!"{label}: projected prover peak {r.peakBytes} bytes \
            exceeds the budget; this target is not a manifest shard, so it \
            cannot be split — raise --max-ram"
          return 1
    | .leanW witness, _ =>
      let (_aiurClaim, proof, _outIO) :=
        aiurSystem.proveIxVM funIdx witness.input witness.inputIOBuffer
      pure proof
    | _, none =>
      IO.eprintln s!"{label}: internal: addr/shard target with no envHandle"
      return 1
  let wrapper : Ixon.Proof := { claim, proof := proof.toBytes }
  let proofAddr ← StoreIO.toIO (Store.write (Ixon.Proof.ser wrapper))
  IO.println (toString proofAddr)
  return 0

/-- Prove the constants owned by `blocks` as ONE shard, splitting and
    recursing whenever the executed record's projected prover peak
    exceeds the budget.

    A shard is only a plan, never part of a statement: its claim is
    `checkEnv(ownedRoot, asmRoot)`, a pure function of `(env, owned)`
    with the frontier recomputed from the owned set. So halving `blocks`
    yields two claims exactly as valid as the parent's — each half's
    grown frontier is discharged by its sibling — and the split costs
    only the parent's execution, the cheap half of the run. Splitting on
    BLOCKS rather than constants is what keeps mutual-recursion groups
    intact, since every constant maps to exactly one block.

    Returns the block sets actually proven, in proof order: the parent's
    own when it fit, otherwise its descendants'. That is the partition
    the run really produced, which is what an updated manifest has to
    describe once the whole pipeline is done. -/
partial def proveBlocksWithinBudget (envHandle : Aiur.EnvHandle)
    (ixonEnv : Ixon.Env) (aiurSystem : Aiur.AiurSystem)
    (funIdx : Aiur.Bytecode.FunIdx) (maxRamBytes : Nat) (label : String)
    (blocks : Array Address) : IO (Except String (Array (Array Address))) := do
  let owned := Ix.Cli.CheckCmd.ownedConstsForBlocks ixonEnv blocks
  let mut blob := ByteArray.empty
  for a in owned do
    blob := blob ++ a.hash
  IO.println s!"Proving {label} ({blocks.size} blocks, {owned.size} consts)"
  (← IO.getStdout).flush
  match aiurSystem.shardProveWithEnv funIdx envHandle blob maxRamBytes with
  | .error e => return .error s!"{label}: shardProveWithEnv error: {e}"
  | .ok { claimBytes, proof, peakBytes } =>
    let gib := Float.ofNat peakBytes / 1073741824.0
    match proof with
    | none =>
      -- A single block is the atom the kernel checks together; there is
      -- no smaller shard to fall back to.
      if blocks.size <= 1 then
        return .error s!"{label}: projected prover peak {gib} GiB exceeds \
          the budget and the shard is a single block — raise --max-ram"
      let mid := blocks.size / 2
      IO.println s!"[{label}] peak {gib} GiB over budget — splitting \
        {blocks.size} blocks into {mid} + {blocks.size - mid}"
      match ← proveBlocksWithinBudget envHandle ixonEnv aiurSystem funIdx
          maxRamBytes s!"{label}.0" (blocks.extract 0 mid) with
      | .error e => return .error e
      | .ok lo =>
        match ← proveBlocksWithinBudget envHandle ixonEnv aiurSystem funIdx
            maxRamBytes s!"{label}.1" (blocks.extract mid blocks.size) with
        | .error e => return .error e
        | .ok hi => return .ok (lo ++ hi)
    | some proof =>
      IO.println s!"[{label}] prover peak {gib} GiB"
      -- Rust returns the canonical CheckEnv claim's wire bytes; deserialize
      -- back to `Ix.Claim` to persist alongside the proof. Avoids
      -- recomputing the closure walk + canonical AssumptionTree Lean-side.
      match Ixon.runGet Ix.Claim.get claimBytes with
      | .error e => return .error s!"{label}: Claim wire-decode failed: {e}"
      | .ok claim => do
        let _ ← StoreIO.toIO (Store.write (Ix.Claim.ser claim))
        let wrapper : Ixon.Proof := { claim, proof := proof.toBytes }
        let proofAddr ← StoreIO.toIO (Store.write (Ixon.Proof.ser wrapper))
        IO.println (toString proofAddr)
        return .ok #[blocks]

/-- Prove shard `shardK` of the partition, splitting it as needed.
    Returns the block sets actually proven for that shard. -/
def runShardProveNative (envHandle : Aiur.EnvHandle) (ixonEnv : Ixon.Env)
    (shards : Array (Array Address)) (shardK : Nat)
    (aiurSystem : Aiur.AiurSystem) (compiled : Aiur.CompiledToplevel)
    (maxRamBytes : Nat) : IO (Except String (Array (Array Address))) := do
  match shards[shardK]? with
  | none => return .error s!"shard {shardK} out of range (0..{shards.size})"
  | some blocks =>
    let funIdx := compiled.getFuncIdx `verify_claim |>.get!
    proveBlocksWithinBudget envHandle ixonEnv aiurSystem funIdx maxRamBytes
      s!"shard {shardK}" blocks

/-- Report the partition a prove run actually produced against the one
    its manifest planned. They differ exactly when a shard was split. -/
def reportPartition (proven : Array (Array Address)) (planned : Nat) : IO Unit := do
  if proven.size == planned then
    IO.println s!"[prove] {proven.size} shard(s) proven, partition unchanged"
  else
    IO.println s!"[prove] {proven.size} shard(s) proven from {planned} planned \
      ({proven.size - planned} from splits) — re-shard with this partition to \
      skip the splits next run"

def runProveCmd (p : Cli.Parsed) : IO UInt32 := do
  let keepGoing := p.hasFlag "keep-going"
  -- Same units as `ix shard --max-ram`: the per-shard prover budget the
  -- partition was sized against, re-checked here against each shard's
  -- measured peak. 0 = unchecked.
  let maxRamBytes := ((p.flag? "max-ram").map (·.as! Nat)).getD 0 * 1073741824
  let ixePath : Option String := (p.flag? "ixe").map (·.as! String)
  let claimHex : Option String := (p.flag? "claim").map (·.as! String)
  let names := (p.variableArgsAs! String).toList
  let toplevel ← match IxVM.ixVM with
    | .error e => IO.eprintln s!"toplevel merging failed: {e}"; return 1
    | .ok t => pure t
  let compiled ← match toplevel.compile with
    | .error e => IO.eprintln s!"compilation failed: {e}"; return 1
    | .ok c => pure c
  let aiurSystem := Aiur.AiurSystem.build compiled.bytecode commitmentParameters friParameters
  let runOne := proveOne aiurSystem compiled
  match ixePath, (p.flag? "ixes").map (·.as! String), (p.flag? "shard").map (·.as! Nat) with
  | some ixe, some manifest, some k =>
    -- IxVM-native shard prove. Build the envHandle once + share it
    -- with the shard prove FFI.
    match (← Ix.Cli.CheckCmd.loadEnvAndShards manifest ixe) with
    | .error e => IO.eprintln e; return 1
    | .ok (ixonEnv, shards) =>
      let envHandle ← match Aiur.EnvHandle.fromIxe ixe with
        | .error e => IO.eprintln s!"EnvHandle.fromIxe {ixe}: {e}"; return 1
        | .ok h => pure h
      match ← runShardProveNative envHandle ixonEnv shards k aiurSystem
          compiled maxRamBytes with
      | .error e => IO.eprintln e; return 1
      | .ok parts =>
        reportPartition parts shards.size
        return 0
  | some ixe, some manifest, none =>
    -- IxVM-native all-shards prove. Same envHandle reused across
    -- every shard.
    match (← Ix.Cli.CheckCmd.loadEnvAndShards manifest ixe) with
    | .error e => IO.eprintln e; return 1
    | .ok (ixonEnv, shards) =>
      let envHandle ← match Aiur.EnvHandle.fromIxe ixe with
        | .error e => IO.eprintln s!"EnvHandle.fromIxe {ixe}: {e}"; return 1
        | .ok h => pure h
      -- Accumulate the partition the run actually produced. Splits stay
      -- in this process, so the manifest describing them is written
      -- once at the end rather than rewritten per split.
      let mut proven : Array (Array Address) := #[]
      let mut rc : UInt32 := 0
      for k in [0 : shards.size] do
        match ← runShardProveNative envHandle ixonEnv shards k aiurSystem
            compiled maxRamBytes with
        | .error e => IO.eprintln e; rc := 1
        | .ok parts => proven := proven ++ parts
      if rc == 0 then reportPartition proven shards.size
      let _ := manifest
      pure rc
  | _, _, _ =>
    Ix.Cli.CheckCmd.forEachClaim ixePath claimHex names keepGoing "prove" false runOne

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
    "max-ram" : Nat;    "Per-shard prover-RAM budget, GiB — normally the same value the partition was sized with (`ix shard --max-ram`). Each shard is executed, its projected prover peak measured on the resulting record, and the proof attempted only if it fits; an over-budget shard is reported (split it and re-run) instead of being taken into the FFT phases that would exhaust the box. Omit to prove unconditionally."

  ARGS:
    ...names : String; "Fully-qualified Lean.Name(s) to prove. With none, iterate every named constant in the env (sorted)."
]

end
