/-
  `ix prove`: the proving surface. `ix check` executes and verifies;
  everything that generates a STARK lives here.

      ix prove --env arena.ixe --shards plan.ixes            # cluster shards, all
      ix prove --env arena.ixe --shards plan.ixes --shard 3  # one work unit
      ix prove --env arena.ixe                               # whole env, span proofs
      ix prove --env arena.ixe --dry-run                     # stop at witness gen
      ix prove Nat.add_comm                                  # compiled-in env, one claim
      ix prove --env arena.ixe --claim <hex>                 # against a persisted claim

  Shard mode is the CLUSTER path: each `.ixes` shard of the static
  min-cut plan (`ix shard`) is an immutable work unit a box runs
  whole — execute the shard's owned blocks warm into one record, seal
  the shard's canonical `Claim.checkEnv` (owned-set root +
  thin-frontier assumption root), derive multiplicities, measure the
  witness EXACTLY against this box's budget (IX_SCAN_RAM_GIB
  overrides), and prove behind that gate. A shard measuring over
  budget fails with the stable code AIUR_SHARD_OVER_BUDGET so a
  scheduler can re-partition it statically — claim composition makes
  any re-split sound — and the box never splits, probes, or heals.

  Whole-env mode runs the same engine over retained-bytes execution
  spans sized so each span is one proof, sealed and gated the same
  way. `--dry-run` stops at witness generation in both modes: seals,
  derivation, and each unit's exact measured peak, with no STARKs.

  Every proven unit — shard, whole-env span, or per-name / per-claim
  witness alike — is persisted as an `Ixon.Proof` wrapper (canonical
  claim + opaque proof bytes) in the content-addressed store, and its
  blake3 hex reported: the artifact a box ships for aggregation, and
  what `ix verify <proof-hex>` consumes. `--claim` loads the claim from the store
  and resolves every referenced assumption / env / contains tree
  (build trees with `ix tree canonical` / `ix tree env`). Driven by
  the shared `Ix.Cli.CheckCmd.forEachClaim`.
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
  -- codegen'd Rust kernel. `.addr` goes through the envHandle-based
  -- prove FFI (witness + execute + prove in one Rust trip); `.leanW`
  -- consumes a pre-built `ClaimWitness` via `proveIxVM` (used for
  -- non-`check addr none` `--claim hex`).
  let proof : Aiur.Proof ← match target, envHandle? with
    | .addr a, some envHandle =>
      match aiurSystem.proveAddrWithEnv funIdx envHandle a.hash with
      | .error e =>
        IO.eprintln s!"{label}: proveAddrWithEnv error: {e}"
        return 1
      | .ok (_claimBytes, proof, _outIO) => pure proof
    | .leanW witness, _ =>
      let (_aiurClaim, proof, _outIO) :=
        aiurSystem.proveIxVM funIdx witness.input witness.inputIOBuffer
      pure proof
    | _, none =>
      IO.eprintln s!"{label}: internal: addr target with no envHandle"
      return 1
  let wrapper : Ixon.Proof := { claim, proof := proof.toBytes }
  let proofAddr ← StoreIO.toIO (Store.write (Ixon.Proof.ser wrapper))
  IO.println (toString proofAddr)
  return 0


def runProveCmd (p : Cli.Parsed) : IO UInt32 := do
  let keepGoing := p.hasFlag "keep-going"
  let ixePath : Option String := (p.flag? "env").map (·.as! String)
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
  let engineIdxs : Except String (Nat × Nat) := do
    let some seg := compiled.getFuncIdx `verify_claim
      | throw "verify_claim missing from compiled toplevel"
    let some blk := compiled.getFuncIdx `verify_block
      | throw "verify_block missing from compiled toplevel"
    pure (seg, blk)
  let workers := ((p.flag? "jobs").map (·.as! Nat)).getD 0
  match ixePath, (p.flag? "shards").map (·.as! String), (p.flag? "shard").map (·.as! Nat) with
  | some ixe, some manifest, k? =>
    -- Cluster-shard prove: each manifest shard is an immutable work
    -- unit — execute owned blocks, seal, derive, measure exactly,
    -- prove behind the gate. Over-budget shards fail with
    -- AIUR_SHARD_OVER_BUDGET for the scheduler to re-partition.
    let (segIdx, blkIdx) ← match engineIdxs with
      | .error e => IO.eprintln s!"error: {e}"; return 1
      | .ok v => pure v
    let envHandle ← match Aiur.EnvHandle.fromIxe ixe with
      | .error e => IO.eprintln s!"EnvHandle.fromIxe {ixe}: {e}"; return 1
      | .ok h => pure h
    match aiurSystem.executeShardsProveWithEnv segIdx blkIdx envHandle
        (toString workers) manifest ((k?.map toString).getD "")
        (if p.hasFlag "dry-run" then "1" else "0") with
    | .error e => IO.eprintln s!"prove failed: {e}"; return 1
    | .ok () => IO.println "prove: OK"; return 0
  | some ixe, none, none =>
    if names.isEmpty && claimHex.isNone then
      -- Whole-env prove through the engine: retained-cut spans, each
      -- one sealed claim proceeding straight to a verified STARK
      -- (or, with --dry-run, to its exact measured peak report).
      let (segIdx, blkIdx) ← match engineIdxs with
        | .error e => IO.eprintln s!"error: {e}"; return 1
        | .ok v => pure v
      let envHandle ← match Aiur.EnvHandle.fromIxe ixe with
        | .error e => IO.eprintln s!"EnvHandle.fromIxe {ixe}: {e}"; return 1
        | .ok h => pure h
      match aiurSystem.executeEnvProveWithEnv segIdx blkIdx envHandle
          (toString workers) (if keepGoing then "0" else "1")
          (if p.hasFlag "dry-run" then "1" else "0") with
      | .error e => IO.eprintln s!"prove failed: {e}"; return 1
      | .ok () => IO.println "prove: OK"; return 0
    else
      Ix.Cli.CheckCmd.forEachClaim ixePath claimHex names keepGoing "prove" false runOne
  | some _, none, some _ =>
    IO.eprintln "error: --shard requires --shards"; return 1
  | none, some _, _ =>
    IO.eprintln "error: --shards requires --env"; return 1
  | none, none, _ =>
    Ix.Cli.CheckCmd.forEachClaim ixePath claimHex names keepGoing "prove" false runOne

end Ix.Cli.ProveCmd

open Ix.Cli.ProveCmd in
def proveCmd : Cli.Cmd := `[Cli|
  prove VIA runProveCmd;
  "Generate STARK proofs: `.ixes` cluster shards as immutable work units, whole envs as one proof per span (both sealed with CheckEnv claims and gated on their EXACT measured witness peak), or single `Ix.Claim`s persisted to the store"

  FLAGS:
    "keep-going";       "Continue past failures and report them at the end instead of halting on the first (whole-env engine mode and per-name iteration)."
    "env"   : String;   "Path to a serialized `.ixe` env. Alone (no names, no --claim): whole-env engine prove — retained-bytes execution spans, one CheckEnv claim per span, each measured EXACTLY and proven behind the gate. With --shards: the env the manifest partitions. With names or --claim: the env the claims prove against."
    "claim" : String;   "32-byte hex address of a persisted `Ix.Claim` in `~/.ix/store/`. When set, proves the persisted claim against the `--env` env (single proof, skips per-const iteration)."
    "shards" : String;  "Path to a `.ixes` manifest from `ix shard` (with --env). Each shard is an immutable work unit: execute its owned blocks, seal its CheckEnv claim, derive, measure EXACTLY, prove behind the gate. Over-budget shards fail with AIUR_SHARD_OVER_BUDGET (shard=/blocks=/peak_bytes=/budget_bytes=) for the scheduler to re-partition. All-shards runs first check exact cover of the env schedule."
    "shard" : Nat;      "0-based shard index K (with --shards): run only shard K (stamped PARTIAL — no coverage claim)."
    "dry-run";          "Stop at witness generation (both engine modes): warm execution, CheckEnv seal, derived multiplicities (the sealed record IS the witness), and each unit's exact measured peak-prove-RAM report. No STARKs."
    "jobs"  : Nat;      "Worker threads for the engine modes (default 0 = autoscale)."

  ARGS:
    ...names : String; "Fully-qualified Lean.Name(s) to prove as individual `verify_claim` proofs persisted to the store. With none and no --env, iterate every named constant of the compiled-in env."
]

end
