module
public import Ix.Address

/-! Checked `.ixes` parsing and aggregation-tree planning. -/

public section
namespace Ix.Shard

-- Bounds-checked little-endian cursor over a `.ixes` byte buffer. Every read
-- verifies the buffer has enough bytes and returns `.error` on underflow — no
-- `b[p]!` panics on a truncated/malformed manifest.
private abbrev IxesP := StateT (ByteArray × Nat) (Except String)

private def ixesU8 : IxesP UInt8 := do
  let (b, p) ← get
  if h : p < b.size then
    modify (fun _ => (b, p + 1))
    pure b[p]
  else throw "ixes: truncated (expected a byte)"

private def ixesU32 : IxesP UInt32 := do
  let a ← ixesU8; let b ← ixesU8; let c ← ixesU8; let d ← ixesU8
  pure (a.toUInt32 ||| (b.toUInt32 <<< 8) ||| (c.toUInt32 <<< 16) ||| (d.toUInt32 <<< 24))

private def ixesU64 : IxesP UInt64 := do
  let lo ← ixesU32; let hi ← ixesU32
  pure (lo.toUInt64 ||| (hi.toUInt64 <<< 32))

private def ixesSkip (n : Nat) : IxesP Unit := do
  let (b, p) ← get
  if p + n ≤ b.size then modify (fun _ => (b, p + n)) else throw s!"ixes: truncated (skip {n})"

private def ixesAddr : IxesP Address := do
  let (b, p) ← get
  if p + 32 ≤ b.size then modify (fun _ => (b, p + 32)); pure ⟨b.extract p (p + 32)⟩
  else throw "ixes: truncated (expected a 32-byte address)"

/-- The binary bisection tree stored at the tail of a `.ixes` manifest. Its
leaves are shard ids; internal nodes prescribe the aggregation order that
minimizes how long cross-shard assumptions remain live. -/
inductive AggregationTree where
  | leaf (shard : Nat)
  | node (left right : AggregationTree)
  deriving BEq, Repr, Inhabited

namespace AggregationTree

partial def leaves : AggregationTree → Array Nat
  | .leaf shard => #[shard]
  | .node left right => left.leaves ++ right.leaves

/-- A legacy fallback for manifests written before the optional bisection-tree
tail existed. Leaves remain in ascending shard order. -/
partial def balancedRange (start count : Nat) : AggregationTree :=
  if count ≤ 1 then .leaf start
  else
    let leftCount := count / 2
    .node (balancedRange start leftCount)
      (balancedRange (start + leftCount) (count - leftCount))

/-- One post-order binary aggregation operation. Join child indices always
refer to earlier plan slots, and the final slot is the root. -/
inductive FoldOp where
  | leaf (shard : Nat)
  | join (left right : Nat)
  deriving BEq, Repr

/-- Lower a bisection tree to the slot plan consumed by the binary join host
driver. -/
partial def foldPlan (tree : AggregationTree) : Array FoldOp :=
  (go tree #[]).2
where
  go (node : AggregationTree) (ops : Array FoldOp) : Nat × Array FoldOp :=
    match node with
    | .leaf shard => (ops.size, ops.push (.leaf shard))
    | .node left right =>
      let (leftIdx, ops) := go left ops
      let (rightIdx, ops) := go right ops
      (ops.size, ops.push (.join leftIdx rightIdx))

/-- Drop removed shard leaves, contract unary nodes, and rewrite retained shard
ids to their dense indices in a pruned manifest view. The input tree has
already passed `validateAggregationTree`, so an out-of-range mapping entry is
an internal inconsistency rather than untrusted manifest input. -/
partial def pruneAndRemap (remap : Array (Option Nat)) :
    AggregationTree → Option AggregationTree
  | .leaf shard => (remap[shard]?).join.map .leaf
  | .node left right =>
    match pruneAndRemap remap left, pruneAndRemap remap right with
    | some left, some right => some (.node left right)
    | some tree, none | none, some tree => some tree
    | none, none => none

end AggregationTree

structure IxesManifestView where
  shards : Array (Array Address)
  /-- Original manifest shard id for each (possibly pruned) dense array slot. -/
  shardIds : Array Nat
  aggregationTree : AggregationTree
  /-- Per dense slot, the analytic prover peak (bytes) a previous run measured
  for that shard's executed record — the manifest's trailing measured-peaks
  section — or `0` when it was never measured (planner output, or a manifest
  written before the section existed). -/
  measuredPeakBytes : Array Nat
  deriving BEq, Repr

private partial def ixesAggregationTree : IxesP AggregationTree := do
  match ← ixesU8 with
  | 0 => pure (.leaf (← ixesU32).toNat)
  | 1 => pure (.node (← ixesAggregationTree) (← ixesAggregationTree))
  | tag => throw s!"ixes: invalid aggregation-tree tag {tag.toNat}"

private def validateAggregationTree (tree : AggregationTree)
    (numShards : Nat) : Except String Unit := do
  let leaves := tree.leaves
  if leaves.size != numShards then
    throw s!"ixes: aggregation tree has {leaves.size} leaves for {numShards} shards"
  let mut seen : Std.HashSet Nat := {}
  for shard in leaves do
    if shard ≥ numShards then
      throw s!"ixes: aggregation tree leaf {shard} is out of range"
    if seen.contains shard then
      throw s!"ixes: aggregation tree repeats shard {shard}"
    seen := seen.insert shard

/-- Parse every shard's owned block addresses and aggregation tree from a
serialized `.ixes`
    manifest (`ShardManifest::to_bytes`, `src/ix/shard.rs`):
    magic(8) ‖ total_cross_ingress(u128) ‖ num_shards(u32) ‖ per shard
    { id(u32) ‖ heartbeats(u64) ‖ own_size(u64) ‖ cross_ingress(u64) ‖
      assumption_root(u8 tag + 32?) ‖ blocks(u32 len + 32·len) ‖
      foreign_blocks(u32 len + 32·len) }.
    The optional trailing tree uses preorder `leaf(0,id:u32)` /
    `node(1,left,right)` encoding. Legacy manifests with no tree (or an explicit
    zero presence byte) receive a balanced ascending-id fallback. After the tree
    an optional measured-peaks section follows: presence byte, then one `u64`
    analytic prover peak per shard in id order (`0` = unmeasured); absent on
    manifests written before it existed. Anything after the last known section
    is an error. Bounds-checked: a truncated/malformed file yields `.error`,
    never a panic. -/
def parseIxesManifest (bytes : ByteArray) : Except String IxesManifestView :=
  let go : IxesP IxesManifestView := do
    let m0 ← ixesU8; let m1 ← ixesU8; let m2 ← ixesU8; let m3 ← ixesU8
    if !(m0 == 0x49 && m1 == 0x58 && m2 == 0x45 && m3 == 0x53) then
      throw "not an .ixes file (bad magic)"
    ixesSkip 4    -- rest of the 8-byte magic
    ixesSkip 16   -- total_cross_ingress (u128)
    let n ← ixesU32
    if n == 0 then throw "ixes: manifest contains no shards"
    let mut shards : Array (Array Address) := #[]
    for shardIdx in [0:n.toNat] do
      let shardId ← ixesU32
      if shardId.toNat != shardIdx then
        throw s!"ixes: shard entry {shardIdx} has id {shardId.toNat}"
      ixesSkip (8 + 8 + 8)  -- heartbeats + own_size + cross_ingress
      match ← ixesU8 with
      | 0 => pure ()
      | 1 => ixesSkip 32  -- assumption_root present
      | tag => throw s!"ixes: invalid assumption-root presence tag {tag.toNat}"
      let blen ← ixesU32
      let mut blocks : Array Address := #[]
      for _ in [0:blen.toNat] do
        blocks := blocks.push (← ixesAddr)
      ixesSkip ((← ixesU32).toNat * 32)  -- skip foreign_blocks
      shards := shards.push blocks
    let (buffer, position) ← get
    let tree ← if position == buffer.size then
        pure (AggregationTree.balancedRange 0 n.toNat)
      else
        match ← ixesU8 with
        | 0 => pure (AggregationTree.balancedRange 0 n.toNat)
        | 1 => ixesAggregationTree
        | tag => throw s!"ixes: invalid aggregation-tree presence tag {tag.toNat}"
    validateAggregationTree tree n.toNat
    let (buffer, position) ← get
    let measuredPeakBytes ← if position == buffer.size then
        pure (Array.replicate n.toNat 0)
      else
        match ← ixesU8 with
        | 0 => pure (Array.replicate n.toNat 0)
        | 1 => do
          let mut peaks : Array Nat := #[]
          for _ in [0:n.toNat] do
            peaks := peaks.push (← ixesU64).toNat
          pure peaks
        | tag => throw s!"ixes: invalid measured-peaks presence tag {tag.toNat}"
    let (buffer, position) ← get
    if position != buffer.size then
      throw s!"ixes: {buffer.size - position} trailing bytes after the measured-peaks section"
    pure { shards, shardIds := Array.range n.toNat, aggregationTree := tree,
           measuredPeakBytes }
  go.run' (bytes, 0)

/-- Backward-compatible shard-only view used by check/prove/verify paths that
do not yet consume the aggregation order. -/
def parseIxesAllShards (bytes : ByteArray) : Except String (Array (Array Address)) :=
  (parseIxesManifest bytes).map (·.shards)


end Ix.Shard
end
