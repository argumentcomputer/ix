module
public import Ix.Aggr.Host
public import Ix.Aggr.Protocol
public import Ix.Shard.Environment

/-! Pure reference model for native aggregation plans and statements.

Used by differential tests and the policy benchmark; execution, caching, and
scheduling are owned by the native controller. -/

public section
namespace Aggr.Reference
open IxVM.ClaimHarness

structure PreparedShard where
  claim : Ix.Claim
  statement : Aggr.CheckEnvTrees

/-- Everything claim-derived about a slot, computed for the whole fold before
the first cache lookup or proof. -/
structure AggregateSlotSpec where
  kind : Aggr.ChildKind := .aggr
  statement : Aggr.CheckEnvTrees
  subjectCount : Nat
  outerClaim : Array Aiur.G
  cacheKey : Address

/-- A manifest fold operation annotated with the cumulative subject count and
the monotone flat/structural choice used by the prover. -/
structure ScheduledFold where
  op : Ix.Shard.AggregationTree.FoldOp
  subjectCount : Nat
  structural : Bool
  /-- Result kind of this slot. Only direct-policy leaves are `.ixvm`. -/
  kind : Aggr.ChildKind := .aggr
  /-- `ix_aggr` shape proven by this slot. Direct-policy raw leaves have no
  shape because they are verified and forwarded without a recursion proof. -/
  shape? : Option Nat := none
  deriving BEq, Repr


/-- Reference copy of the native controller's conservative wrap reserve. -/
def aggregateWrapRamBytes : Nat := 195 * aggregateGiB

/-- Structural joins are dominated by the same two recursive-proof checks as
lifts. Keep the conservative lift reserve until the real E2E calibration. -/
def aggregateStructuralJoinRamBytes : Nat := aggregateWrapRamBytes

/-- Native verification and serialization of a raw shard proof in direct mode
is charged to its consuming pair. -/
def aggregateRawShardRamBytes : Nat := 4 * aggregateGiB

/-- Measured upper envelope for an `IxVM + IxVM` pair (shapes 2/6). -/
def aggregateDirectJoinRamBytes : Nat := 390 * aggregateGiB

/-- Measured upper envelope for a mixed recursive/IxVM pair (shapes 3/4/7/8). -/
def aggregateMixedJoinRamBytes : Nat := 340 * aggregateGiB

/-- Flat joins add canonical subject-tree work to the recursive-proof base.
One MiB per subject is a deliberately conservative placeholder: at Init's
~52k-subject root it adds ~51 GiB. The
default structural threshold caps this term near 4 GiB in production. -/
def aggregateFlatJoinRamPerSubjectBytes : Nat := 1024 * 1024

/-- Reference per-shape RAM weight. Shape 5 retains the flat subject-count
reserve; shape 9 is the O(1)-subject structural arm. -/
def aggregateShapeRamBytes (shape subjectCount : Nat) : Nat :=
  match shape with
  | 0 | 1 => aggregateWrapRamBytes
  | 2 | 6 => aggregateDirectJoinRamBytes
  | 3 | 4 | 7 | 8 => aggregateMixedJoinRamBytes
  | 5 => aggregateStructuralJoinRamBytes +
      subjectCount * aggregateFlatJoinRamPerSubjectBytes
  | 9 => aggregateStructuralJoinRamBytes
  | _ => aggregateDirectJoinRamBytes

/-- Reference per-slot RAM weight, also used by the policy benchmark. -/
def aggregateSlotRamBytes (item : ScheduledFold) : Nat :=
  match item.shape? with
  | some shape => aggregateShapeRamBytes shape item.subjectCount
  | none => match item.op with
    | .leaf _ => if item.kind == .ixvm then aggregateRawShardRamBytes
        else aggregateWrapRamBytes
    | .join _ _ =>
      if item.structural then aggregateStructuralJoinRamBytes
      else aggregateStructuralJoinRamBytes +
        item.subjectCount * aggregateFlatJoinRamPerSubjectBytes

def aggregateSlotRamWeights (plan : Array ScheduledFold) : Array Nat :=
  plan.map aggregateSlotRamBytes
/-- Resolve subject counts and the structural threshold once, before proving.
Because parent counts only grow, `count > structuralAbove` makes the mode
monotone: a flat join is never scheduled above a structural child. -/
def schedulePlan (plan : Array Ix.Shard.AggregationTree.FoldOp)
    (shardCounts : Array Nat) (structuralAbove : Nat)
    (directJoins : Bool := false) :
    Except String (Array ScheduledFold) := do
  let mut scheduled : Array ScheduledFold := #[]
  -- A singleton must still produce an `ix_aggr` wrapper. Larger direct plans
  -- keep leaves raw so their first pair can select shapes 2–4/6–8.
  let rawLeaves := directJoins && plan.size > 1
  for op in plan do
    match op with
    | .leaf shard =>
      let some count := shardCounts[shard]?
        | throw s!"aggregate plan references missing shard {shard}"
      let kind := if rawLeaves then Aggr.ChildKind.ixvm else .aggr
      let shape? := if rawLeaves then none
        else some (Aggr.shapeCode (.ixvm, none))
      scheduled := scheduled.push {
        op, subjectCount := count, structural := false, kind, shape?
      }
    | .join left right =>
      let some leftSlot := scheduled[left]?
        | throw s!"aggregate plan references missing left slot {left}"
      let some rightSlot := scheduled[right]?
        | throw s!"aggregate plan references missing right slot {right}"
      let count := leftSlot.subjectCount + rightSlot.subjectCount
      let structural := count > structuralAbove
      let shape := if structural then
          Aggr.structuralShapeCode leftSlot.kind rightSlot.kind
        else
          Aggr.shapeCode (leftSlot.kind, some rightSlot.kind)
      scheduled := scheduled.push {
        op, subjectCount := count, structural, kind := .aggr,
        shape? := some shape
      }
  pure scheduled

/-! ## Converged single-entrypoint slot derivation -/

/-- Derive every converged slot statement, uniform outer claim, kind, and
cache key before proving. Wrap-first leaves use shape 0; direct-policy leaves
remain raw IxVM claims and are deliberately not cache-consumed. -/
def buildAggrSlotSpecs (plan : Array ScheduledFold)
    (prepared : Array PreparedShard) (aggrVk allowed : ByteArray)
    (verifyIdx aggrIdx : Aiur.Bytecode.FunIdx)
    (recursionParameters : Aggr.RecursionParameters) :
    Except String (Array AggregateSlotSpec) := do
  let mut specs : Array AggregateSlotSpec := #[]
  for item in plan do
    match item.op with
    | .leaf shard =>
      let some preparedShard := prepared[shard]?
        | throw s!"aggregate plan references missing prepared shard {shard}"
      if preparedShard.claim != preparedShard.statement.claim then
        throw s!"prepared shard {shard} claim and statement disagree"
      if preparedShard.statement.subjectCount != item.subjectCount then
        throw s!"prepared shard {shard} has {preparedShard.statement.subjectCount} \
          subjects, but the schedule records {item.subjectCount}"
      let claimBytes := Ix.Claim.ser preparedShard.claim
      let verifyInput := IxVM.ClaimHarness.packedDigestKey
        (Address.blake3 claimBytes)
      let innerClaim := Aiur.buildClaim verifyIdx verifyInput #[]
      let outerClaim := match item.kind with
        | .ixvm => innerClaim
        | .aggr => aggregateOuterClaim allowed aggrIdx preparedShard.claim
      match item.kind, item.shape? with
      | .ixvm, none => pure ()
      | .aggr, some 0 => pure ()
      | _, _ => throw s!"aggregate leaf {shard} has inconsistent kind/shape"
      specs := specs.push {
        kind := item.kind
        statement := preparedShard.statement
        subjectCount := item.subjectCount
        outerClaim
        cacheKey := aggregateCacheKey aggrVk recursionParameters outerClaim
      }
    | .join leftIdx rightIdx =>
      let some left := specs[leftIdx]?
        | throw s!"aggregate plan references missing left spec {leftIdx}"
      let some right := specs[rightIdx]?
        | throw s!"aggregate plan references missing right spec {rightIdx}"
      if left.subjectCount + right.subjectCount != item.subjectCount then
        throw "aggregate plan has inconsistent joined subject counts"
      let output := if item.structural then
          left.statement.joinStructural right.statement
        else
          left.statement.join right.statement
      if output.subjectCount != item.subjectCount then
        throw s!"aggregate join reconstructs {output.subjectCount} subjects, \
          but the schedule records {item.subjectCount}"
      let expectedShape := if item.structural then
          Aggr.structuralShapeCode left.kind right.kind
        else
          Aggr.shapeCode (left.kind, some right.kind)
      if item.kind != .aggr || item.shape? != some expectedShape then
        throw s!"aggregate join {leftIdx},{rightIdx} has inconsistent kind/shape"
      let outerClaim := aggregateOuterClaim allowed aggrIdx output.claim
      specs := specs.push {
        kind := .aggr
        statement := output
        subjectCount := item.subjectCount
        outerClaim
        cacheKey := aggregateCacheKey aggrVk recursionParameters outerClaim
      }
  pure specs

private def prepareOwnedShard (env : Ixon.Env) (owned : Array Address) :
    Except String PreparedShard := do
  let (claim, trees) ← IxVM.ClaimHarness.shardCheckEnvClaimTrees env owned
  let statement ← Aggr.CheckEnvTrees.ofClaim claim trees
  pure { claim, statement }

/-- Reconstruct every shard statement after partitioning environment ownership
in one pass. Calling `ownedConstsForBlocks` once per shard rescans the complete
environment for every leaf, which made Mathlib aggregate startup take more
than twenty minutes before the proof store was touched. -/
def prepareShards (env : Ixon.Env) (shards : Array (Array Address))
    (shardIds : Array Nat := #[]) : Except String (Array PreparedShard) := do
  let ownedAll := Ix.Shard.ownedConstsPer env shards
  if ownedAll.size != shards.size then
    throw s!"internal: prepared ownership for {ownedAll.size} shards, expected {shards.size}"
  let mut prepared : Array PreparedShard := #[]
  for (owned, shard) in ownedAll.mapIdx fun shard owned => (owned, shard) do
    let originalShard := (shardIds[shard]?).getD shard
    let item ← match prepareOwnedShard env owned with
      | .error e => throw s!"prepare shard {originalShard}: {e}"
      | .ok item => pure item
    prepared := prepared.push item
  pure prepared


private def shardStatement (env : Ixon.Env) (owned : Array Address) :
    Except String Aggr.CheckEnvTrees := do
  let (claim, trees) ← IxVM.ClaimHarness.shardCheckEnvClaimTrees env owned
  Aggr.CheckEnvTrees.ofClaim claim trees

/-- Reproduce the flat/structural statement fold from a coverage-validated
manifest. Zero-constant leaves are pruned exactly as in `ix aggregate`; no proof
data is needed. Ownership is assigned for every retained shard in one
environment pass; verification must not reintroduce the old shard-by-shard
full-environment scan. -/
def expectedFromManifest (env : Ixon.Env)
    (view : Ix.Shard.IxesManifestView) (structuralAbove : Nat) :
    Except String Aggr.CheckEnvTrees := do
  let (view, counts) ← view.pruneEmpty env
  let owned := Ix.Shard.ownedConstsPer env view.shards
  let plan ← Aggr.Reference.schedulePlan view.aggregationTree.foldPlan
    counts structuralAbove
  let mut slots : Array Aggr.CheckEnvTrees := #[]
  for item in plan do
    match item.op with
    | .leaf shard =>
      let some shardOwned := owned[shard]?
        | throw s!"aggregate plan references missing shard {shard}"
      slots := slots.push (← shardStatement env shardOwned)
    | .join left right =>
      let some leftStatement := slots[left]?
        | throw s!"aggregate plan references missing left slot {left}"
      let some rightStatement := slots[right]?
        | throw s!"aggregate plan references missing right slot {right}"
      slots := slots.push <| if item.structural then
        leftStatement.joinStructural rightStatement
      else
        leftStatement.join rightStatement
  let some root := slots.back? | throw "aggregate manifest produced no root"
  pure root

end Aggr.Reference
end
