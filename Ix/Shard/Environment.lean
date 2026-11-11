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

    A constant outside Lean's logic (unsafe or partial, or projected from
    such a block: `Ixon.Env.outsideLogicAt`) is owned by nobody: IxVM refuses
    it as a claim's seed (`KernelClaim::assert_claimable`). Its whole
    check-schedule block is set aside, projections included. No constant in
    Lean's logic references one, so each shard's claim walk still stays
    within its owned set and its frontier.

    Constants whose bytes do not parse are owned by NOBODY. That is safe
    only because `shardsCover` fails the run when any exist; without
    that gate a silent skip here means a constant no shard ever
    checks. -/
def ownedConstsPer (ixonEnv : Ixon.Env) (lists : Array (Array Address)) :
    Array (Array Address) :=
  let blockTo := blockIndexOf lists
  let (owned, aside) := ixonEnv.consts.fold
    (init := (Array.replicate lists.size (#[] : Array (Address × Address)),
      ({} : Std.HashSet Address)))
    fun (owned, aside) addr lc =>
      match lc.get? with
      | none => (owned, aside)
      | some c =>
        let aside := if c.outsideLogic then aside.insert addr else aside
        let blk := blockAddrOf addr c
        match blockTo.get? blk with
        | some k => (owned.modify k (·.push (addr, blk)), aside)
        | none => (owned, aside)
  owned.map fun l => l.filterMap fun (a, blk) => if aside.contains blk then none else some a

/-- Owned constants of one shard: `ownedConstsPer` over a singleton. -/
def ownedConstsForBlocks (ixonEnv : Ixon.Env) (blocks : Array Address) :
    Array Address :=
  (ownedConstsPer ixonEnv #[blocks])[0]!

/-- Partition a shard's already-known `owned` constants among `parts`
    (block lists) by check-schedule block: one pass over the owned
    consts, none over the env — the split-time companion of
    `ownedConstsPer`, whose full env pass runs once per run (and has
    already set aside the constants outside Lean's logic). -/
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

/-- Count each shard's owned constants in one environment pass (`ownedConstsPer`,
so without the constants outside Lean's logic). Callers first run
`shardsCover`, so every check-schedule block has exactly one owner. This is
the subject-leaf count used by aggregate structural-threshold scheduling. -/
def ownedConstCountsForShards (ixonEnv : Ixon.Env)
    (shards : Array (Array Address)) : Array Nat :=
  (ownedConstsPer ixonEnv shards).map (·.size)

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
def shardClaimDigest (ixonEnv : Ixon.Env) (blocks : Array Address)
    (assumeBinding : Bool := false) : Except String Address := do
  let (claim, _) ← IxVM.ClaimHarness.shardCheckEnvClaimTrees ixonEnv
    (ownedConstsForBlocks ixonEnv blocks) assumeBinding
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

/-- Coverage check over already-loaded env + shards: every constant in Lean's
    logic has its check-schedule block owned by **exactly one** shard. That is
    the whole soundness condition for the check case — each constant is
    type-checked once, and every shard's frontier (closure minus owned) is
    therefore owned (checked) by some other shard. The constants outside Lean's
    logic (`ownedConstsPer`) are set aside, owned by none and counted apart: no
    claim certifies them, and no constant in Lean's logic references them, so
    no frontier holds one. Prints the per-shard report; returns whether the
    partition is a valid disjoint cover (no block owned by two shards, no
    constant in Lean's logic whose block no shard owns). -/
def shardsCover (ixonEnv : Ixon.Env) (shards : Array (Array Address)) : IO Bool := do
  -- block → shard, detecting blocks claimed by more than one shard.
  let mut blockToShard : Std.HashMap Address Nat := {}
  let mut dup : Nat := 0
  for (blocks, k) in shards.mapIdx (fun k b => (b, k)) do
    for blk in blocks do
      match blockToShard.get? blk with
      | some _ => dup := dup + 1
      | none => blockToShard := blockToShard.insert blk k
  -- each parsed const's block, and the records outside Lean's logic
  let mut blockOf : Array Address := #[]
  let mut aside : Std.HashSet Address := {}
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
    if c.outsideLogic then aside := aside.insert addr
    blockOf := blockOf.push (blockAddrOf addr c)
  -- assign every const in Lean's logic to a shard via its block; count + detect unowned.
  let mut counts : Array Nat := Array.replicate shards.size 0
  let mut unowned : Nat := 0
  let mut setAside : Nat := 0
  for blk in blockOf do
    if aside.contains blk then
      setAside := setAside + 1
      continue
    match blockToShard.get? blk with
    | some k => counts := counts.modify k (· + 1)  -- total: no-op if out of range
    | none => unowned := unowned + 1
  IO.println s!"[shards] {shards.size} shards, {ixonEnv.consts.size} consts"
  for (blocks, k) in shards.mapIdx (fun k b => (b, k)) do
    IO.println s!"  shard {k}: {blocks.size} blocks, {(counts[k]?).getD 0} consts"
  if setAside != 0 then
    IO.println s!"[shards] {setAside} const(s) outside Lean's logic (unsafe or partial) \
      set aside: owned by no shard, claimed by none"
  if dup != 0 then
    IO.eprintln s!"[shards] FAIL: {dup} block(s) owned by >1 shard (not disjoint)"
  if unowned != 0 then
    IO.eprintln s!"[shards] FAIL: {unowned} const(s) with no owning shard (coverage gap)"
  if unparsed != 0 then
    IO.eprintln s!"[shards] FAIL: {unparsed} const(s) whose bytes do not parse \
      (cannot be assigned to a shard)"
  let ok := dup == 0 && unowned == 0 && unparsed == 0
  if ok then
    IO.println s!"[shards] OK: partition covers all {ixonEnv.consts.size - setAside} consts \
      in Lean's logic, disjoint"
  pure ok


end Ix.Shard
end
