module
public import Ix.Aggr.Host
public import Ix.Aggr.Protocol
public import Ix.Shard.Environment

/-! Pure reference model for native aggregation plans and statements. -/

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
  kind : Aggr.ChildKind := .aggr
  shape? : Option Nat := none
  deriving BEq, Repr

/-- Reference copy of the native controller's conservative wrap reserve. -/
def aggregateWrapRamBytes : Nat := 195 * aggregateGiB

def aggregateStructuralJoinRamBytes : Nat := aggregateWrapRamBytes

def aggregateRawShardRamBytes : Nat := 4 * aggregateGiB

def aggregateDirectJoinRamBytes : Nat := 390 * aggregateGiB

def aggregateMixedJoinRamBytes : Nat := 340 * aggregateGiB

def aggregateFlatJoinRamPerSubjectBytes : Nat := 1024 * 1024

def aggregateShapeRamBytes (shape subjectCount : Nat) : Nat :=
  match shape with
  | 0 | 1 => aggregateWrapRamBytes
  | 2 | 6 => aggregateDirectJoinRamBytes
  | 3 | 4 | 7 | 8 => aggregateMixedJoinRamBytes
  | 5 => aggregateStructuralJoinRamBytes +
      subjectCount * aggregateFlatJoinRamPerSubjectBytes
  | 9 => aggregateStructuralJoinRamBytes
  | _ => aggregateDirectJoinRamBytes

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

/-- Resolve subject counts and the structural threshold once, before proving. -/
def schedulePlan (plan : Array Ix.Shard.AggregationTree.FoldOp)
    (shardCounts : Array Nat) (structuralAbove : Nat)
    (directJoins : Bool := false) :
    Except String (Array ScheduledFold) := do
  let mut scheduled : Array ScheduledFold := #[]
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

/-- Derive every converged slot statement, uniform outer claim, kind, and
cache key before proving. -/
def buildAggrSlotSpecs (plan : Array ScheduledFold)
    (prepared : Array PreparedShard) (aggrVk allowed : ByteArray)
    (verifyIdx aggrIdx : Nat)
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

private def prepareOwnedShard (env : Ixon.Env) (owned : Array Address)
    (assumeBinding : Bool := false) :
    Except String PreparedShard := do
  let (claim, trees) ← IxVM.ClaimHarness.shardCheckEnvClaimTrees env owned assumeBinding
  let statement ← Aggr.CheckEnvTrees.ofClaim claim trees
  pure { claim, statement }

/-- Reconstruct every shard statement after partitioning environment ownership
in one pass. -/
def prepareShards (env : Ixon.Env) (shards : Array (Array Address))
    (shardIds : Array Nat := #[]) (assumeBinding : Bool := false) :
    Except String (Array PreparedShard) := do
  let ownedAll := Ix.Shard.ownedConstsPer env shards
  if ownedAll.size != shards.size then
    throw s!"internal: prepared ownership for {ownedAll.size} shards, expected {shards.size}"
  let mut prepared : Array PreparedShard := #[]
  for (owned, shard) in ownedAll.mapIdx fun shard owned => (owned, shard) do
    let originalShard := (shardIds[shard]?).getD shard
    let item ← match prepareOwnedShard env owned assumeBinding with
      | .error e => throw s!"prepare shard {originalShard}: {e}"
      | .ok item => pure item
    prepared := prepared.push item
  pure prepared

private def shardStatement (env : Ixon.Env) (owned : Array Address)
    (assumeBinding : Bool := false) :
    Except String Aggr.CheckEnvTrees := do
  let (claim, trees) ← IxVM.ClaimHarness.shardCheckEnvClaimTrees env owned assumeBinding
  Aggr.CheckEnvTrees.ofClaim claim trees

/-- Reproduce the flat/structural statement fold from a coverage-validated
manifest: the statement of every slot of the fold plan, in plan order, the
root last. -/
def expectedSlotsFromManifest (env : Ixon.Env)
    (view : Ix.Shard.IxesManifestView) (structuralAbove : Nat)
    (assumeBinding : Bool := false) :
    Except String (Array Aggr.CheckEnvTrees) := do
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
      slots := slots.push (← shardStatement env shardOwned assumeBinding)
    | .join left right =>
      let some leftStatement := slots[left]?
        | throw s!"aggregate plan references missing left slot {left}"
      let some rightStatement := slots[right]?
        | throw s!"aggregate plan references missing right slot {right}"
      slots := slots.push <| if item.structural then
        leftStatement.joinStructural rightStatement
      else
        leftStatement.join rightStatement
  pure slots

/-- The root statement of `expectedSlotsFromManifest`. -/
def expectedFromManifest (env : Ixon.Env)
    (view : Ix.Shard.IxesManifestView) (structuralAbove : Nat)
    (assumeBinding : Bool := false) :
    Except String Aggr.CheckEnvTrees := do
  let slots ← expectedSlotsFromManifest env view structuralAbove assumeBinding
  let some root := slots.back? | throw "aggregate manifest produced no root"
  pure root

end Aggr.Reference
end
