module
public import Ix.Shard.Manifest
public import Ix.IxVM.ClaimHarness

/-! Manifest ownership, coverage, and environment loading. -/

public section
namespace Ix.Shard

/-- The check-schedule block address of a constant: a projection collapses
    to its SCC/Muts wrapper (`p.block`); everything else is its own block.
    Mirrors `check_schedule_block_addr` (`src/ffi/kernel.rs`). -/
private def blockAddrOf (addr : Address) (c : Ixon.Constant) : Address :=
  match c.info with
  | .iPrj prj => prj.block
  | .cPrj prj => prj.block
  | .rPrj prj => prj.block
  | .dPrj prj => prj.block
  | _ => addr

/-- Each block address mapped to the index of the list owning it. -/
def blockIndexOf (lists : Array (Array Address)) :
    Std.HashMap Address Nat :=
  (lists.mapIdx fun k l => (k, l)).foldl (init := {}) fun m (k, l) =>
    l.foldl (fun m blk => m.insert blk k) m

/-- Owned constants per entry, in ONE env pass: `result[k]` is every env
    constant whose check-schedule block is in `lists[k]`, in
    env-iteration order (identical to a per-entry filter, so claim
    digests are unchanged). Per-entry filtering rescans all consts each
    call — at env scale (241 shards × 688k consts) that is ~30 min of
    setup, vs seconds here.

    Constants whose bytes do not parse are owned by NOBODY. That is safe
    only because `shardsCover` fails the run when any exist; without
    that gate a silent skip here means a constant no shard ever
    checks. -/
def ownedConstsPer (ixonEnv : Ixon.Env) (lists : Array (Array Address)) :
    Array (Array Address) :=
  let blockTo := blockIndexOf lists
  ixonEnv.consts.fold (init := Array.replicate lists.size #[])
    fun owned addr lc =>
      match lc.get? with
      | none => owned
      | some c =>
        match blockTo.get? (blockAddrOf addr c) with
        | some k => owned.modify k (·.push addr)
        | none => owned

/-- Owned constants of one shard: `ownedConstsPer` over a singleton. -/
def ownedConstsForBlocks (ixonEnv : Ixon.Env) (blocks : Array Address) :
    Array Address :=
  (ownedConstsPer ixonEnv #[blocks])[0]!

/-- Partition a shard's already-known `owned` constants among `parts`
    (block lists) by check-schedule block: one pass over the owned
    consts, none over the env — the split-time companion of
    `ownedConstsPer`, whose full env pass runs once per run. -/
def partitionOwned (ixonEnv : Ixon.Env) (owned : Array Address)
    (parts : Array (Array Address)) : Array (Array Address) :=
  let blockTo := blockIndexOf parts
  owned.foldl (init := Array.replicate parts.size #[]) fun acc a =>
    match (ixonEnv.consts.get? a).bind (·.get?) with
    | none => acc
    | some c =>
      match blockTo.get? (blockAddrOf a c) with
      | some k => acc.modify k (·.push a)
      | none => acc

/-- Count each shard's owned constants in one environment pass. Callers first
run `shardsCover`, so every check-schedule block has exactly one owner. This is
the subject-leaf count used by aggregate structural-threshold scheduling. -/
def ownedConstCountsForShards (ixonEnv : Ixon.Env)
    (shards : Array (Array Address)) : Array Nat := Id.run do
  let mut blockToShard : Std.HashMap Address Nat := {}
  for (blocks, shard) in shards.mapIdx fun shard blocks => (blocks, shard) do
    for block in blocks do
      blockToShard := blockToShard.insert block shard
  let mut counts := Array.replicate shards.size 0
  for (addr, lc) in ixonEnv.consts do
    let some c := lc.get? | continue
    let some shard := blockToShard.get? (blockAddrOf addr c) | continue
    counts := counts.modify shard (· + 1)
  return counts

/-- Remove manifest shards that provably own no environment constants, then
contract and densely reindex the corresponding aggregation-tree leaves.

Callers must run `shardsCover` on the unpruned view first. That gate establishes
that every constant is owned exactly once; the zero counts here therefore prove
that dropping these leaves cannot omit a checked subject. `shardIds` preserves
the original ids for diagnostics and for matching legacy manifests. -/
def IxesManifestView.pruneEmpty (view : IxesManifestView)
    (ixonEnv : Ixon.Env) : Except String (IxesManifestView × Array Nat) := do
  if view.shards.size != view.shardIds.size then
    throw "ixes: internal shard/id cardinality mismatch"
  let counts := ownedConstCountsForShards ixonEnv view.shards
  let mut remap : Array (Option Nat) := Array.replicate view.shards.size none
  let mut shards : Array (Array Address) := #[]
  let mut shardIds : Array Nat := #[]
  let mut measuredPeakBytes : Array Nat := #[]
  let mut keptCounts : Array Nat := #[]
  for (count, oldIdx) in counts.mapIdx fun oldIdx count => (count, oldIdx) do
    if count != 0 then
      let some blocks := view.shards[oldIdx]?
        | throw s!"ixes: internal missing shard {oldIdx}"
      let some originalId := view.shardIds[oldIdx]?
        | throw s!"ixes: internal missing shard id {oldIdx}"
      remap := remap.set! oldIdx (some shards.size)
      shards := shards.push blocks
      shardIds := shardIds.push originalId
      measuredPeakBytes := measuredPeakBytes.push ((view.measuredPeakBytes[oldIdx]?).getD 0)
      keptCounts := keptCounts.push count
  let some aggregationTree := view.aggregationTree.pruneAndRemap remap
    | throw "aggregate: manifest has no shard owning an environment constant"
  pure ({ shards, shardIds, aggregationTree, measuredPeakBytes }, keptCounts)

/-- The `CheckEnv` claim digest a shard's proof commits to — reconstructed
    deterministically from the env + the shard's owned blocks. Matches the
    digest `prove --shard K` produced, so a proof can be bound to its shard. -/
def shardClaimDigest (ixonEnv : Ixon.Env) (blocks : Array Address) : Except String Address := do
  let (claim, _) ← IxVM.ClaimHarness.shardCheckEnvClaimTrees ixonEnv
    (ownedConstsForBlocks ixonEnv blocks)
  pure (Address.blake3 (Ix.Claim.ser claim))

/-- Load the `.ixe` env and the `.ixes` shard partition together (each file
    read once). Shared by every manifest-driven shard path. -/
def loadEnvAndShards (manifestPath ixePath : String) :
    IO (Except String (Ixon.Env × Array (Array Address))) := do
  match parseIxesAllShards (← IO.FS.readBinFile manifestPath) with
  | .error e => return .error s!"manifest parse failed: {e}"
  | .ok shards => match Ixon.deEnvAnon (← IO.FS.readBinFile ixePath) with
    | .error e => return .error s!"deserialize {ixePath} failed: {e}"
    | .ok env => return .ok (env, shards)

/-- Coverage check over already-loaded env + shards: every constant's
    check-schedule block is owned by **exactly one** shard. That is the whole
    soundness condition for the check case — each constant is type-checked
    once, and every shard's frontier (closure minus owned) is therefore owned
    (checked) by some other shard. Prints the per-shard report; returns whether
    the partition is a valid disjoint cover (no block owned by two shards, no
    constant whose block no shard owns). -/
def shardsCover (ixonEnv : Ixon.Env) (shards : Array (Array Address)) : IO Bool := do
  -- block → shard, detecting blocks claimed by more than one shard.
  let mut blockToShard : Std.HashMap Address Nat := {}
  let mut dup : Nat := 0
  for (blocks, k) in shards.mapIdx (fun k b => (b, k)) do
    for blk in blocks do
      match blockToShard.get? blk with
      | some _ => dup := dup + 1
      | none => blockToShard := blockToShard.insert blk k
  -- assign every const to a shard via its block; count + detect unowned.
  let mut counts : Array Nat := Array.replicate shards.size 0
  let mut unowned : Nat := 0
  let mut unparsed : Nat := 0
  for (addr, lc) in ixonEnv.consts do
    -- A constant whose bytes do not parse must FAIL the gate, not be
    -- skipped. `.ixe` loading is lazy and `LazyConstant.get?` discards
    -- the error, so such a constant sits in `consts` with its key
    -- present: skipping it assigned it to no shard, counted it as
    -- neither owned nor unowned, and still included it in the "covers
    -- all N consts" total below. It would also enter a referring
    -- shard's frontier, since that admits an edge on key presence
    -- without parsing — an assumption no shard discharges.
    let some c := lc.get? | unparsed := unparsed + 1; continue
    match blockToShard.get? (blockAddrOf addr c) with
    | some k => counts := counts.modify k (· + 1)  -- total: no-op if out of range
    | none => unowned := unowned + 1
  IO.println s!"[shards] {shards.size} shards, {ixonEnv.consts.size} consts"
  for (blocks, k) in shards.mapIdx (fun k b => (b, k)) do
    IO.println s!"  shard {k}: {blocks.size} blocks, {(counts[k]?).getD 0} consts"
  if dup != 0 then
    IO.eprintln s!"[shards] FAIL: {dup} block(s) owned by >1 shard (not disjoint)"
  if unowned != 0 then
    IO.eprintln s!"[shards] FAIL: {unowned} const(s) with no owning shard (coverage gap)"
  if unparsed != 0 then
    IO.eprintln s!"[shards] FAIL: {unparsed} const(s) whose bytes do not parse \
      (cannot be assigned to a shard)"
  let ok := dup == 0 && unowned == 0 && unparsed == 0
  if ok then
    IO.println s!"[shards] OK: partition covers all {ixonEnv.consts.size} consts, disjoint"
  pure ok


end Ix.Shard
end
