module
public import Ix.Check
public import Ix.Shard.Environment
public import Ix.Benchmark.Results
public import Ix.TracingTexray
public import Ix.Unsigned

/-! Manifest-driven IxVM execution helpers and shard refinement. -/

public section
namespace Ix.Shard.Check
open Ix.Check Ix.Shard IxVM.ClaimHarness

/-- Run the shard operation for one shard, given the already-loaded env and the
    shard's owned `blocks`: build the `CheckEnv` witness over the owned consts
    (ingress their closure, skip the frontier) and dispatch `runOne`. -/
def runShardOwned (ixonEnv : Ixon.Env) (blocks : Array Address) (shardK : Nat)
    (runOne : Ix.Claim → IxVM.ClaimHarness.ClaimWitness → String → IO UInt32) : IO UInt32 := do
  let owned := ownedConstsForBlocks ixonEnv blocks
  IO.println s!"[shard] shard {shardK}: {blocks.size} owned blocks → \
    {owned.size}/{ixonEnv.consts.size} owned consts"
  if owned.isEmpty then
    -- every block of the shard is outside Lean's logic (`ownedConstsPer`)
    IO.println s!"[shard] shard {shardK}: owns no constant in Lean's logic, so no claim"
    return 0
  match IxVM.ClaimHarness.buildShardCheckEnvWitness ixonEnv owned with
  | .error e => IO.eprintln s!"shard witness build failed: {e}"; return 1
  | .ok (claim, witness) => runOne claim witness s!"shard {shardK}"

/-- Manifest-driven check/prove of one shard `shardK` of the partition. -/
def runShardCheckManifest (manifestPath ixePath : String) (shardK : Nat)
    (runOne : Ix.Claim → IxVM.ClaimHarness.ClaimWitness → String → IO UInt32) : IO UInt32 := do
  match (← loadEnvAndShards manifestPath ixePath) with
  | .error e => IO.eprintln e; return 1
  | .ok (ixonEnv, shards) => match shards[shardK]? with
    | none => IO.eprintln s!"shard {shardK} out of range ({shards.size} shards)"; return 1
    | some blocks => runShardOwned ixonEnv blocks shardK runOne

/-- Cut `blocks` into contiguous, nonempty, roughly equal-count parts
    (`p` clamped to `[2, blocks.size]`). -/
def cutBlocks (blocks : Array Address) (p : Nat) : Array (Array Address) :=
  let p := min (max p 2) blocks.size
  (Array.range p).map fun i =>
    blocks.extract (blocks.size * i / p) (blocks.size * (i + 1) / p)

/-- Measured-peaks blob for the manifest emit: one 8-byte LE value per
    shard, in shard order. -/
def peaksBlob (peaks : Array Nat) : ByteArray :=
  peaks.foldl (init := ByteArray.empty) fun blob pk =>
    blob ++ pk.toUInt64.toLEBytes

/-- Wire encoding shared by the shard batch FFI and the manifest emit:
    per entry, a 4-byte LE count followed by the 32-byte addresses. -/
def addrListsBlob (lists : Array (Array Address)) : ByteArray :=
  lists.foldl (init := ByteArray.empty) fun blob l =>
    l.foldl (fun b a => b ++ a.hash) (blob ++ l.size.toUInt32.toLEBytes)

/-- One leaf of a source manifest cut into parts, as the prove and check
    split loops produce it: the parts' block lists in block order, each
    with the analytic prover peak measured on its executed record
    (`0` = unmeasured). -/
structure LeafRefinement where
  shard : Nat
  parts : Array (Array Address × Nat)

/-- Wire encoding of `Aiur.shardManifestRefine`'s refinements argument:
    `count(u32)`, then per refined leaf `id(u32) ‖ nparts(u32)` and per
    part `nblocks(u32) ‖ 32·nblocks ‖ peak(u64)`. -/
def refinementsBlob (rs : Array LeafRefinement) : ByteArray :=
  rs.foldl (init := rs.size.toUInt32.toLEBytes) fun blob r =>
    r.parts.foldl
      (init := blob ++ r.shard.toUInt32.toLEBytes ++ r.parts.size.toUInt32.toLEBytes)
      fun blob (blocks, peak) =>
        (blocks.foldl (fun b a => b ++ a.hash) (blob ++ blocks.size.toUInt32.toLEBytes))
          ++ peak.toUInt64.toLEBytes

/-- Group per-leaf run results `(shard, parts)` over the `n` leaves of a
    source manifest into the leaves that split (≥ 2 parts) and the
    measured peaks of the leaves that did not (`0` where a leaf was not
    run). -/
def refinementsOfRuns (n : Nat)
    (runs : Array (Nat × Array (Array Address × Nat))) :
    Array LeafRefinement × Array Nat :=
  runs.foldl (init := (#[], Array.replicate n 0)) fun (rs, measured) (k, parts) =>
    if parts.size > 1 then (rs.push { shard := k, parts }, measured)
    else match parts[0]? with
      | some (_, peak) => (rs, if k < measured.size then measured.set! k peak else measured)
      | none => (rs, measured)

/-- Decode the new-id table `Aiur.shardManifestRefine` returns:
    `count(u32)`, then per refinement `n(u32) ‖ n × id(u32)`. -/
def decodeIdTable (bytes : ByteArray) : Array (Array Nat) := Id.run do
  let u32At (i : Nat) : Option Nat :=
    if i + 4 ≤ bytes.size then
      some (bytes[i]!.toNat ||| (bytes[i+1]!.toNat <<< 8)
        ||| (bytes[i+2]!.toNat <<< 16) ||| (bytes[i+3]!.toNat <<< 24))
    else none
  let some count := u32At 0 | return #[]
  let mut pos := 4
  let mut table : Array (Array Nat) := #[]
  for _ in [0:count] do
    let some n := u32At pos | return table
    pos := pos + 4
    let mut ids : Array Nat := #[]
    for _ in [0:n] do
      let some id := u32At pos | return table
      ids := ids.push id
      pos := pos + 4
    table := table.push ids
  return table

/-- Emit the partition a run actually validated as a refinement of the
    manifest it started from. -/
def emitRefinedManifest (tag : String) (envHandle : Aiur.EnvHandle)
    (sourcePath out : String) (refinements : Array LeafRefinement)
    (measured : Array Nat) (failures : Nat) : IO (Array (Array Nat)) := do
  if failures == 0 then
    let ids ← Aiur.shardManifestRefine envHandle sourcePath
      (refinementsBlob refinements) (peaksBlob measured) out
    IO.println s!"[{tag}] refined manifest → {out} \
      ({refinements.size} leaf/leaves split)"
    pure (decodeIdTable ids)
  else
    IO.eprintln s!"--out-ixes {out} skipped: {failures} failure(s)"
    pure #[]

/-- Claim digest of a leaf from its already-known owned constants (no env
    rescan): the digest `ix prove` persists and `ix aggregate` matches on. -/
def claimDigestOfOwned (ixonEnv : Ixon.Env) (owned : Array Address)
    (assumeBinding : Bool := false) :
    Except String Address := do
  let (claim, _) ← IxVM.ClaimHarness.shardCheckEnvClaimTrees ixonEnv owned assumeBinding
  pure (Address.blake3 (Ix.Claim.ser claim))

/-- `K`, `a-b`, or a comma list of those: the leaf ids a run is restricted
    to, sorted and deduplicated. -/
def parseShardSelection (s : String) : Except String (Array Nat) := do
  let mut ids : Array Nat := #[]
  for piece in s.splitOn "," do
    let piece := piece.trimAscii.toString
    if piece.isEmpty then continue
    match piece.splitOn "-" with
    | [one] =>
      let some k := one.trimAscii.toString.toNat?
        | throw s!"--shards: not a shard id: `{piece}`"
      ids := ids.push k
    | [lo, hi] =>
      let some a := lo.trimAscii.toString.toNat?
        | throw s!"--shards: not a range: `{piece}`"
      let some b := hi.trimAscii.toString.toNat?
        | throw s!"--shards: not a range: `{piece}`"
      if b < a then throw s!"--shards: empty range `{piece}`"
      for k in [a:b+1] do ids := ids.push k
    | _ => throw s!"--shards: malformed `{piece}` (use K, a-b, or a comma list)"
  if ids.isEmpty then throw "--shards: empty selection"
  let sorted := ids.qsort (· < ·)
  pure (sorted.foldl (fun acc k => if acc.back? == some k then acc else acc.push k) #[])

/-- Run the shard operation over EVERY shard — the whole-partition behavior of
    `--ixes` with no `--shard` (used by `prove`). -/
def runShardManifestAll (manifestPath ixePath : String)
    (runOne : Ix.Claim → IxVM.ClaimHarness.ClaimWitness → String → IO UInt32) : IO UInt32 := do
  match (← loadEnvAndShards manifestPath ixePath) with
  | .error e => IO.eprintln e; return 1
  | .ok (ixonEnv, shards) =>
    let mut rc : UInt32 := 0
    for (blocks, k) in shards.mapIdx (fun k b => (b, k)) do
      if (← runShardOwned ixonEnv blocks k runOne) != 0 then rc := 1
    pure rc

/-- Check EVERY shard of the partition concurrently after verifying coverage. -/
def runShardCheckAll (manifestPath ixePath : String) (jobs? : Option Nat)
    (runOne : Ix.Claim → IxVM.ClaimHarness.ClaimWitness → String → IO UInt32) : IO UInt32 := do
  let (ixonEnv, shards) ← match (← loadEnvAndShards manifestPath ixePath) with
    | .error e => IO.eprintln e; return 1
    | .ok r => pure r
  if !(← shardsCover ixonEnv shards) then return 1
  let maxJobs := max 1 (jobs?.getD shards.size)
  let mut rc : UInt32 := 0
  for chunk in (shards.mapIdx (fun k b => (b, k))).toList.toChunks maxJobs do
    let tasks ← chunk.mapM fun (blocks, k) =>
      IO.asTask (prio := .dedicated) (runShardOwned ixonEnv blocks k runOne)
    for t in tasks do
      match t.get with
      | .ok r => if r != 0 then rc := 1
      | .error e => IO.eprintln s!"shard check task failed: {e}"; rc := 1
  pure rc

end Ix.Shard.Check
end
