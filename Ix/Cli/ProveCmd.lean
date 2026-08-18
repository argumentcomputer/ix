/-
  `ix prove`: the proving surface. `ix check` executes and verifies;
  everything that generates a STARK lives here.

      ix prove --env arena.ixe                         # whole env, cut-mode segments
      ix prove --env arena.ixe --shards plan.ixes      # manifest: gate + self-heal
      ix prove --env arena.ixe --shards plan.ixes --shard 3
      ix prove Nat.add_comm                            # compiled-in Lean env, one claim
      ix prove --env arena.ixe Foo.bar                 # named claim from .ixe
      ix prove --env arena.ixe --claim <hex>           # against a persisted claim

  Whole-env and manifest modes run the shared-record engine: parallel
  warm block execution, canonical CheckEnv seal claim with derived
  multiplicities, the EXACT measured RAM gate before every STARK, and
  in manifest mode self-healing splits of over-budget shards. Each
  seal is the span's canonical `Claim.checkEnv` (owned-set root +
  thin-frontier assumption root — the digest `ix verify` binds shard
  proofs to); engine proofs are verified in-run.

  Per-name / per-claim modes prove one `verify_claim` witness and
  persist the result as an `Ixon.Proof` wrapper (claim + opaque proof
  bytes), printing the proof blake3 hex — feed that to
  `ix verify <proof-hex>`. `--claim` loads the claim from the store
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
    -- Manifest prove through the shared-record engine: each shard
    -- executes warm into its own record, seals (canonical CheckEnv
    -- claim, derived multiplicities), is gated on its measured peak,
    -- and proves; a shard that measures over budget self-heals by
    -- splitting. Exit status carries any rejection or unproven unit.
    let (segIdx, blkIdx) ← match engineIdxs with
      | .error e => IO.eprintln s!"error: {e}"; return 1
      | .ok v => pure v
    let envHandle ← match Aiur.EnvHandle.fromIxe ixe with
      | .error e => IO.eprintln s!"EnvHandle.fromIxe {ixe}: {e}"; return 1
      | .ok h => pure h
    match aiurSystem.executeManifestProveWithEnv segIdx blkIdx envHandle
        (toString workers) manifest ((k?.map toString).getD "") "0" "" with
    | .error e => IO.eprintln s!"prove failed: {e}"; return 1
    | .ok () => IO.println "prove: OK"; return 0
  | some ixe, none, none =>
    if names.isEmpty && claimHex.isNone then
      -- Whole-env prove through the engine: cut-mode segments, each
      -- sealed record proceeding straight to a verified STARK.
      let (segIdx, blkIdx) ← match engineIdxs with
        | .error e => IO.eprintln s!"error: {e}"; return 1
        | .ok v => pure v
      let envHandle ← match Aiur.EnvHandle.fromIxe ixe with
        | .error e => IO.eprintln s!"EnvHandle.fromIxe {ixe}: {e}"; return 1
        | .ok h => pure h
      match aiurSystem.executeEnvProveWithEnv segIdx blkIdx envHandle
          (toString workers) (if keepGoing then "0" else "1") "0" "" with
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
  "Generate STARK proofs: whole env or `.ixes` manifest through the shared-record engine (exact RAM gate, self-healing shards), or single `Ix.Claim`s persisted to the store"

  FLAGS:
    "keep-going";       "Continue past failures and report them at the end instead of halting on the first (whole-env engine mode and per-name iteration)."
    "env"   : String;   "Path to a serialized `.ixe` env. Alone (no names, no --claim): whole-env engine prove — every block's claim executes into a shared record, prove-sized segments are cut at the RAM model's budget line, and each sealed segment proceeds straight to a verified multi-claim STARK. With names or --claim: the env the claims prove against."
    "claim" : String;   "32-byte hex address of a persisted `Ix.Claim` in `~/.ix/store/`. When set, proves the persisted claim against the `--env` env (single proof, skips per-const iteration)."
    "shards" : String;  "Path to a `.ixes` shard manifest (with --env), e.g. from `ix shard`. Prove the manifest through the engine: each shard executes into its own record, seals, is gated on its EXACT measured peak, and proves; over-budget shards self-heal by splitting. Requires exact cover of the env schedule when run without --shard."
    "shard" : Nat;      "0-based shard index K (with --shards): prove only shard K (stamped PARTIAL — no coverage claim)."
    "jobs"  : Nat;      "Worker threads for the engine modes (default 0 = autoscale)."

  ARGS:
    ...names : String; "Fully-qualified Lean.Name(s) to prove as individual `verify_claim` proofs persisted to the store. With none and no --env, iterate every named constant of the compiled-in env."
]

end
