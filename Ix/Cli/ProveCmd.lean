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

/-- Prove the constants owned by `blocks` as ONE shard, cutting it into
    the peak model's suggested part count whenever the executed record's
    projected prover peak exceeds the budget, and recursing on any part
    that still misses.

    Cuts are contiguous equal-block-count runs: rows are what the RAM
    model responds to, and equal-cumulative-vspan cuts measured worse
    on every axis (parts, depth, executions) across a synthetic
    fixture, init, and lean — vspan tracks time, not rows.

    A shard is only a plan, never part of a statement: its claim is
    `checkEnv(ownedRoot, asmRoot)`, a pure function of `(env, owned)`
    with the frontier recomputed from the owned set. So cutting `blocks`
    yields claims exactly as valid as the parent's — each part's grown
    frontier is discharged by its siblings — and the cut costs only the
    parent's execution, the cheap half of the run. Splitting on BLOCKS
    rather than constants is what keeps mutual-recursion groups intact,
    since every constant maps to exactly one block.

    The suggested count is optimistic — parts re-execute dependencies
    shared across the cut, and equal block counts are not equal row
    counts — so each part is gated on its own executed record and
    re-cut if it misses. That bias is deliberate: an under-cut costs
    one cheap re-execution, an over-cut pays the per-proof floor on
    every extra part for the life of the partition.

    Returns the parts actually proven, in proof order, each with its
    measured projected prover peak: the parent's own when it fit,
    otherwise its descendants'. That is the partition the run really
    produced — what the corrected manifest describes, peaks included. -/
partial def proveBlocksWithinBudget (envHandle : Aiur.EnvHandle)
    (ixonEnv : Ixon.Env) (aiurSystem : Aiur.AiurSystem)
    (funIdx : Aiur.Bytecode.FunIdx) (maxRamBytes : Nat)
    (execOnly : Bool) (label : String)
    (blocks : Array Address) :
    IO (Except String (Array (Array Address × Nat))) := do
  let owned := Ix.Cli.CheckCmd.ownedConstsForBlocks ixonEnv blocks
  let mut blob := ByteArray.empty
  for a in owned do
    blob := blob ++ a.hash
  IO.println s!"Proving {label} ({blocks.size} blocks, {owned.size} consts)"
  (← IO.getStdout).flush
  match aiurSystem.shardProveWithEnv funIdx envHandle blob maxRamBytes
      execOnly with
  | .error e => return .error s!"{label}: shardProveWithEnv error: {e}"
  | .ok { claimBytes, proof, peakBytes, suggestedParts } =>
    let gib := Float.ofNat peakBytes / 1073741824.0
    match proof with
    | none =>
      -- Exec-only leaf: the peak fit (parts = 1), there is just no
      -- STARK behind it. The partition bookkeeping is identical.
      if execOnly && suggestedParts <= 1 then
        IO.println s!"[{label}] prover peak {gib} GiB (exec-only)"
        return .ok #[(blocks, peakBytes)]
      -- A single block is the atom the kernel checks together; there is
      -- no smaller shard to fall back to.
      if blocks.size <= 1 then
        return .error s!"{label}: projected prover peak {gib} GiB exceeds \
          the budget and the shard is a single block — raise --max-ram"
      let cut := Ix.Cli.CheckCmd.cutBlocks blocks suggestedParts
      IO.println s!"[{label}] peak {gib} GiB over budget — cutting \
        {blocks.size} blocks into {cut.size} parts"
      let mut proven : Array (Array Address × Nat) := #[]
      for i in [0 : cut.size] do
        match ← proveBlocksWithinBudget envHandle ixonEnv aiurSystem funIdx
            maxRamBytes execOnly s!"{label}.{i}" cut[i]! with
        | .error e => return .error e
        | .ok parts => proven := proven ++ parts
      return .ok proven
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
        return .ok #[(blocks, peakBytes)]

/-- Prove shard `shardK` of the partition, splitting it as needed.
    Returns the block sets actually proven for that shard. -/
def runShardProveNative (envHandle : Aiur.EnvHandle) (ixonEnv : Ixon.Env)
    (shards : Array (Array Address)) (shardK : Nat)
    (aiurSystem : Aiur.AiurSystem) (compiled : Aiur.CompiledToplevel)
    (maxRamBytes : Nat) (execOnly : Bool) :
    IO (Except String (Array (Array Address × Nat))) := do
  match shards[shardK]? with
  | none => return .error s!"shard {shardK} out of range (0..{shards.size})"
  | some blocks =>
    let funIdx := compiled.getFuncIdx `verify_claim |>.get!
    proveBlocksWithinBudget envHandle ixonEnv aiurSystem funIdx maxRamBytes
      execOnly s!"shard {shardK}" blocks

/-- Report the partition a prove run actually produced against the one
    its manifest planned. They differ exactly when a shard was split. -/
def reportPartition (proven : Array (Array Address × Nat)) (planned : Nat) : IO Unit := do
  if proven.size == planned then
    IO.println s!"[prove] {proven.size} shard(s) proven, partition unchanged"
  else
    IO.println s!"[prove] {proven.size} shard(s) proven from {planned} planned \
      ({proven.size - planned} from splits) — re-shard with this partition to \
      skip the splits next run"

def runProveCmd (p : Cli.Parsed) : IO UInt32 := do
  -- Streamed `[texray] <span>: <dur> ── RAM Δ/peak` lines on stderr as
  -- each `aiur/` / `stark/` span closes: the per-phase wall + RSS
  -- breakdown (execute vs witness vs STARK) of every prove in the run.
  if p.hasFlag "texray" then TracingTexray.init {}
  let keepGoing := p.hasFlag "keep-going"
  -- Same units as `ix shard --max-ram`: the per-shard prover budget the
  -- partition was sized against, re-checked here against each shard's
  -- measured peak. 0 = detect (85% of `MemAvailable`, the check batch's
  -- gate policy — see `shardProveWithEnv`).
  let maxRamBytes := ((p.flag? "max-ram").map (·.as! Nat)).getD 0 * 1073741824
  let execOnly := p.hasFlag "exec-only"
  let outIxes := (p.flag? "out-ixes").map (·.as! String)
  -- Both `--ixes` branches end the same way: the partition the run
  -- actually proved, written as the manifest to start the next run from.
  let emitCorrected (ixe : String) (partition : Array (Array Address × Nat)) :
      IO Unit := do
    if let some out := outIxes then
      Ix.KernelCheck.rsShardManifestFromPartitionFFI ixe
        (Ix.Cli.CheckCmd.addrListsBlob (partition.map (·.1)))
        (Ix.Cli.CheckCmd.peaksBlob (partition.map (·.2))) out
      IO.println s!"[prove] corrected manifest → {out}"
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
          compiled maxRamBytes execOnly with
      | .error e => IO.eprintln e; return 1
      | .ok parts =>
        -- A single-shard run plans exactly one shard, not the whole
        -- partition.
        reportPartition parts 1
        -- The corrected whole partition: the plan with shard k replaced
        -- by the parts this run actually proved.
        emitCorrected ixe
          ((shards.extract 0 k).map (·, 0) ++ parts
            ++ (shards.extract (k + 1) shards.size).map (·, 0))
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
      let mut proven : Array (Array Address × Nat) := #[]
      let mut failed : Array (Nat × String) := #[]
      for k in [0 : shards.size] do
        match ← runShardProveNative envHandle ixonEnv shards k aiurSystem
            compiled maxRamBytes execOnly with
        | .error e => IO.eprintln e; failed := failed.push (k, e)
        | .ok parts => proven := proven ++ parts
      if failed.isEmpty then
        reportPartition proven shards.size
        emitCorrected ixe proven
        return 0
      IO.eprintln s!"[prove] {failed.size} of {shards.size} shard(s) FAILED:"
      for (k, e) in failed do
        IO.eprintln s!"  shard {k}: {e}"
      if let some out := outIxes then
        IO.eprintln s!"--out-ixes {out} skipped: {failed.size} failure(s)"
      return 1
  | _, _, _ =>
    Ix.Cli.CheckCmd.forEachClaim ixePath claimHex names keepGoing "prove" false runOne

end Ix.Cli.ProveCmd

open Ix.Cli.ProveCmd in
def proveCmd : Cli.Cmd := `[Cli|
  prove VIA runProveCmd;
  "Generate a STARK proof for an `Ix.Claim` (mirrors `ix check`'s CLI shape)"

  FLAGS:
    "keep-going";       "Continue past failures and report them at the end instead of halting on the first."
    "texray";           "Stream per-phase `[texray]` timing/RSS lines (execute, witness, STARK stages) to stderr as each span closes."
    "ixe"   : String;   "Path to a serialized `.ixe` env. When set, the binary reads the env from disk instead of using the compiled-in Lean env."
    "claim" : String;   "32-byte hex address of a persisted `Ix.Claim` in `~/.ix/store/`. When set, proves the persisted claim against the `--ixe` env (single proof, skips per-const iteration)."
    "ixes"  : String;   "Path to a `.ixes` shard manifest (with --ixe). With --shard K: prove shard K. Without --shard: prove every shard in the partition."
    "shard" : Nat;      "0-based shard index K (with --ixes and --ixe): prove that one shard's CheckEnv claim."
    "out-ixes" : String; "Write the partition this run actually proved — splits included — as a `.ixes` manifest to this path: the manifest `ix verify --ixes` checks these proofs against, and the one the next run of this env should start from. Skipped if any shard failed."
    "exec-only";        "Execute each shard and measure its projected prover peak, splitting over-budget shards as usual, but never start a STARK. The cheap way to audit a partition's split behavior at scale."
    "max-ram" : Nat;    "Per-shard prover-RAM budget, GiB — normally the same value the partition was sized with (`ix shard --max-ram`). Each shard is executed, its projected prover peak measured on the resulting record, and the proof attempted only if it fits; an over-budget shard is cut into the part count the peak model projects will fit, and each part re-gated, instead of being taken into the FFT phases that would exhaust the box. Omit to detect: 85% of the machine's available RAM."

  ARGS:
    ...names : String; "Fully-qualified Lean.Name(s) to prove. With none, iterate every named constant in the env (sorted)."
]

end
