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
public import Ix.Cli.VerifyCmd
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
  { logBlowup := 2, capHeight := 0 }

private def friParameters : Aiur.FriParameters := {
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 100
  commitProofOfWorkBits := 0
  queryProofOfWorkBits := 20
}

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
    | .shard owned foreign stubbed, some envHandle =>
      let blobOf (xs : Array Address) : ByteArray := Id.run do
        let mut b := ByteArray.empty
        for x in xs do b := b ++ x.hash
        pure b
      match aiurSystem.shardProveWithEnv funIdx envHandle
        (blobOf owned) (blobOf foreign) (blobOf stubbed) with
      | .error e =>
        IO.eprintln s!"{label}: shardProveWithEnv error: {e}"
        return 1
      | .ok (_claimBytes, proof, _outIO) => pure proof
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

/-- Per-shard prove via the end-to-end Rust path
    (`shardProveIxVM`): witness build, `execute_ixvm`, and STARK
    prove run in one FFI trip with the parallel Rust witness
    builder. -/
def runShardProveNative (manifestPath : String) (envHandle : Aiur.EnvHandle)
    (ixonEnv : Ixon.Env) (shards : Array (Array Address × Array Address × Array Address))
    (shardK : Nat)
    (aiurSystem : Aiur.AiurSystem) (compiled : Aiur.CompiledToplevel)
    (_printStats : Bool) : IO UInt32 := do
  match shards[shardK]? with
  | none => IO.eprintln s!"shard {shardK} out of range (0..{shards.size})"; return 1
  | some (blocks, foreign, stubbed) => do
    let blobOf (bs : Array Address) : ByteArray := Id.run do
      let mut b := ByteArray.empty
      for a in Ix.Cli.CheckCmd.ownedConstsForBlocks ixonEnv bs do
        b := b ++ a.hash
      pure b
    let label := s!"shard {shardK}"
    IO.println s!"Proving {label}"
    (← IO.getStdout).flush
    let funIdx := compiled.getFuncIdx `verify_claim |>.get!
    match aiurSystem.shardProveWithEnv funIdx envHandle
      (blobOf blocks) (blobOf foreign) (blobOf stubbed)
      (manifestPath ++ ".ghosts.csv") with
    | .error e =>
      IO.eprintln s!"{label}: shardProveWithEnv error: {e}"
      return 1
    | .ok (claimBytes, proof, _outIO) =>
      -- Rust returns the canonical CheckEnv claim's wire bytes; deserialize
      -- back to `Ix.Claim` to persist alongside the proof. Avoids
      -- recomputing the closure walk + canonical AssumptionTree Lean-side.
      match Ixon.runGet Ix.Claim.get claimBytes with
      | .error e =>
        IO.eprintln s!"{label}: Claim wire-decode failed: {e}"
        return 1
      | .ok claim => do
        let _ ← StoreIO.toIO (Store.write (Ix.Claim.ser claim))
        let wrapper : Ixon.Proof := { claim, proof := proof.toBytes }
        let proofAddr ← StoreIO.toIO (Store.write (Ixon.Proof.ser wrapper))
        IO.println (toString proofAddr)
        let _ := manifestPath  -- kept for parity with previous signature
        return 0

/-- One row of the batch-prove sidecar (`<manifest>.proofs.csv`):
    a shard proven, verified, and bound to its reconstructed claim. -/
structure ProofRow where
  shard : Nat
  claimDigest : Address
  proofAddr : Address

/-- Batched, resumable all-shards prove — the whole-partition behavior of
    `prove --ixes` with no `--shard`.

    One `EnvHandle`, one compiled toplevel, and one `AiurSystem` are shared
    across every shard (the per-invocation setup is paid once). Progress
    persists in `<manifest>.proofs.csv` (`shard,claim_digest,proof_addr`):
    a row is appended only after the shard's proof both VERIFIES and binds
    to the shard's reconstructed `CheckEnv` claim digest, so a crash,
    OOM, or interrupt costs only the in-flight shard and re-running the
    same command resumes. Rows whose digest no longer matches the current
    manifest (e.g. after a repair escalation changed the shard's ingress
    sets) are discarded and the shard re-proven.

    `jobs` shards prove concurrently (default 1: each prove peaks at the
    shard's full predicted RAM, so concurrency is a big-box knob).

    Ends with the composed verdict: disjoint cover + every shard bound to
    a verified proof — the same statement `ix verify --ixe --ixes <proofs…>`
    checks after the fact. -/
def runShardProveAllNative (manifestPath : String) (envHandle : Aiur.EnvHandle)
    (ixonEnv : Ixon.Env)
    (shards : Array (Array Address × Array Address × Array Address))
    (aiurSystem : Aiur.AiurSystem) (compiled : Aiur.CompiledToplevel)
    (jobs : Nat) : IO UInt32 := do
  if !(← Ix.Cli.CheckCmd.shardsCover ixonEnv shards) then return 1
  -- Reconstructed claim digest per shard: the binding target for proofs
  -- and the staleness test for sidecar rows.
  let mut digests : Array Address := #[]
  for (blocks, foreign, stubbed) in shards do
    match Ix.Cli.CheckCmd.shardClaimDigest ixonEnv blocks foreign stubbed with
    | .error e => IO.eprintln s!"reconstruct shard {digests.size} claim failed: {e}"; return 1
    | .ok d => digests := digests.push d
  -- Resume: keep sidecar rows whose digest still matches this manifest
  -- AND whose proof still verifies — a digest match alone would count a
  -- proof made under a different circuit version (any kernel change
  -- between sessions regenerates the codegen and the verifying key).
  let sidecar := manifestPath ++ ".proofs.csv"
  let mut done : Std.HashMap Nat Address := {}
  if ← System.FilePath.pathExists sidecar then
    for line in (← IO.FS.readFile sidecar).splitOn "\n" do
      match line.splitOn "," with
      | [k, d, pa] =>
        match k.toNat?, Address.fromString d, Address.fromString pa with
        | some k, some d, some pa =>
          if digests[k]? == some d && !done.contains k then
            if (← Ix.Cli.VerifyCmd.verifyOneProof aiurSystem compiled pa) == 0 then
              done := done.insert k pa
            else
              IO.println s!"[prove] shard {k}: sidecar proof {pa} no longer \
                verifies (circuit changed?) — re-proving"
        | _, _, _ => pure ()
      | _ => pure ()
  let pending := (List.range shards.size).filter (fun k => !done.contains k)
  -- Largest-predicted-RAM first. The RAM model carries a content residual
  -- it cannot see (the klimbs blind spot), so if any shard is going to
  -- breach the watchdog it is one of the heaviest — proving those first
  -- surfaces a failure in the opening minutes instead of hours in, and
  -- everything after the heavy head is strictly safer than what already
  -- passed. Predictions come from the packer's costs sidecar; without
  -- one, manifest order stands.
  let pending : List Nat ← do
    let costs := manifestPath ++ ".costs.csv"
    if !(← System.FilePath.pathExists costs) then
      IO.println s!"[prove] no costs sidecar ({costs}); proving in manifest order"
      pure pending
    else
      -- `pred_ram_gib` is printed with two decimals, so dropping the dot
      -- yields centi-GiB as a Nat sort key.
      let mut ram : Std.HashMap Nat Nat := {}
      for line in (← IO.FS.readFile costs).splitOn "\n" do
        match line.splitOn "," with
        | [k, _, _, _, pr, _] =>
          match k.toNat?, ((pr.replace "." "").toNat?) with
          | some k, some centi => ram := ram.insert k centi
          | _, _ => pure ()
        | _ => pure ()
      pure <| pending.mergeSort (fun a b =>
        (ram.get? a).getD 0 ≥ (ram.get? b).getD 0)
  IO.println s!"[prove] {shards.size} shards: {done.size} already proven \
    (sidecar {sidecar}), {pending.length} pending (heaviest first)"
  let appendRow (r : ProofRow) : IO Unit := do
    let h ← IO.FS.Handle.mk sidecar .append
    h.putStr s!"{r.shard},{r.claimDigest},{r.proofAddr}\n"
    h.flush
  let funIdx := compiled.getFuncIdx `verify_claim |>.get!
  let proveOneShard (k : Nat) : IO (Except String ProofRow) := do
    let (blocks, foreign, stubbed) := shards[k]!
    let blobOf (bs : Array Address) : ByteArray := Id.run do
      let mut b := ByteArray.empty
      for a in Ix.Cli.CheckCmd.ownedConstsForBlocks ixonEnv bs do
        b := b ++ a.hash
      pure b
    IO.println s!"Proving shard {k}"
    (← IO.getStdout).flush
    match aiurSystem.shardProveWithEnv funIdx envHandle
      (blobOf blocks) (blobOf foreign) (blobOf stubbed)
      (manifestPath ++ ".ghosts.csv") with
    | .error e => return .error s!"shardProveWithEnv: {e}"
    | .ok (claimBytes, proof, _outIO) =>
      match Ixon.runGet Ix.Claim.get claimBytes with
      | .error e => return .error s!"claim wire-decode failed: {e}"
      | .ok claim =>
        let d := Address.blake3 (Ix.Claim.ser claim)
        if digests[k]? != some d then
          return .error s!"proved claim {d} does not match reconstructed \
            digest {digests[k]!} — witness and reconstruction disagree"
        let _ ← StoreIO.toIO (Store.write (Ix.Claim.ser claim))
        let wrapper : Ixon.Proof := { claim, proof := proof.toBytes }
        let proofAddr ← StoreIO.toIO (Store.write (Ixon.Proof.ser wrapper))
        if (← Ix.Cli.VerifyCmd.verifyOneProof aiurSystem compiled proofAddr) != 0 then
          return .error s!"proof {proofAddr} failed verification"
        return .ok { shard := k, claimDigest := d, proofAddr }
  let mut failures : List (Nat × String) := []
  for chunk in pending.toChunks (max 1 jobs) do
    let tasks ← chunk.mapM fun k =>
      IO.asTask (prio := .dedicated) do pure (k, ← proveOneShard k)
    for t in tasks do
      match t.get with
      | .ok (k, .ok row) =>
        appendRow row
        done := done.insert k row.proofAddr
        IO.println s!"[prove] shard {k}: proof {row.proofAddr} verified \
          ({done.size}/{shards.size})"
      | .ok (k, .error e) =>
        IO.eprintln s!"[prove] shard {k} FAILED: {e}"
        failures := (k, e) :: failures
      | .error e =>
        IO.eprintln s!"[prove] task crashed: {e}"
        failures := (shards.size, toString e) :: failures
  if !failures.isEmpty then
    IO.eprintln s!"[prove] {failures.length} shard(s) failed: \
      {failures.map (·.1)}; re-run the same command to resume"
    return 1
  IO.println s!"[prove] OK: composed verdict — all {shards.size} shards \
    proven + verified + bound, disjoint cover ({sidecar})"
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
      runShardProveNative manifest envHandle ixonEnv shards k aiurSystem compiled false
  | some ixe, some manifest, none =>
    -- Batched, resumable all-shards prove (one env handle + one Aiur
    -- system across every shard; progress in <manifest>.proofs.csv).
    match (← Ix.Cli.CheckCmd.loadEnvAndShards manifest ixe) with
    | .error e => IO.eprintln e; return 1
    | .ok (ixonEnv, shards) =>
      let envHandle ← match Aiur.EnvHandle.fromIxe ixe with
        | .error e => IO.eprintln s!"EnvHandle.fromIxe {ixe}: {e}"; return 1
        | .ok h => pure h
      runShardProveAllNative manifest envHandle ixonEnv shards aiurSystem
        compiled (((p.flag? "jobs").map (·.as! Nat)).getD 1)
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
    "jobs"  : Nat;      "Shards to prove concurrently in the all-shards batch (default 1). Each prove peaks at the shard's full predicted RAM, so raise this only when the box fits several shards at once."

  ARGS:
    ...names : String; "Fully-qualified Lean.Name(s) to prove. With none, iterate every named constant in the env (sorted)."
]

end
