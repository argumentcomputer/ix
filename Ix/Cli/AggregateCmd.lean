/-
  `ix aggregate --ixe E --ixes M <shard-proof>...`

  Bind persisted shard proof wrappers to every nonempty shard in a manifest,
  wrap each IxVM proof into the single-entrypoint `ix_aggr` recursion system,
  then execute/prove binary folds in the manifest's bisection-tree order.
  Small folds use flat canonical subjects; folds above `--structural-above`
  use an O(1) root-of-roots subject fold plus assumption-membership paths.
  `--direct-joins` keeps raw IxVM leaves until their first parent as an
  explicitly non-default policy. The final persisted wrapper carries the
  aggregate `CheckEnv` claim and recursive proof bytes.

  The host driver schedules the fold as a dependency DAG. Ready slots run on
  dedicated tasks under explicit job and RAM reservations; every completed
  wrap/fold is persisted in a verified, content-addressed resume cache.
-/
module
import Std.Sync
public import Cli
public import Ix.Aggr
public import Ix.Cli.CheckCmd
public import Ix.IxVM
public import Ix.IxVM.ClaimHarness
public import Ix.MultiStark
public import Ix.Store

public section

namespace Ix.Cli.AggregateCmd

open IxVM.ClaimHarness

structure PreparedShard where
  claim : Ix.Claim
  statement : MultiStark.CheckEnvTrees

structure AggregateSlot where
  /-- Which verifying system a parent must use for this slot. Production
  wrap-first slots are all `.aggr`; direct-join leaf slots remain `.ixvm`. -/
  kind : Aggr.ChildKind := .aggr
  statement : MultiStark.CheckEnvTrees
  subjectCount : Nat
  outerClaim : Array Aiur.G
  proof : Aiur.Proof
  proofAddress? : Option Address
  /-- Serialized singleton outer-claim list consumed by a parent. -/
  claimsBytes : ByteArray := ByteArray.empty

/-- Everything claim-derived about a slot, computed for the whole fold before
the first cache lookup or proof. -/
structure AggregateSlotSpec where
  kind : Aggr.ChildKind := .aggr
  statement : MultiStark.CheckEnvTrees
  subjectCount : Nat
  outerClaim : Array Aiur.G
  cacheKey : Address

structure CachedAggregateProof where
  proof : Aiur.Proof
  address : Address

inductive AggregateCacheAddress where
  | miss
  | hit (address : Address)
  | invalid (reason : String)
  deriving Repr

/-- A manifest fold operation annotated with the cumulative subject count and
the monotone flat/structural choice used by the prover. -/
structure ScheduledFold where
  op : Ix.Cli.CheckCmd.AggregationTree.FoldOp
  subjectCount : Nat
  structural : Bool
  /-- Result kind of this slot. Only direct-policy leaves are `.ixvm`. -/
  kind : Aggr.ChildKind := .aggr
  /-- `ix_aggr` shape proven by this slot. Direct-policy raw leaves have no
  shape because they are verified and forwarded without a recursion proof. -/
  shape? : Option Nat := none
  deriving BEq, Repr

/-- The immutable result of simulating aggregate-slot admission. Runtime and
unit tests share the same admission function; the simulator completes the
lowest-numbered in-flight slot after every admission pass solely to make its
trace deterministic. -/
structure AggregateScheduleTrace where
  admissionOrder : Array Nat
  admissionBatches : Array (Array Nat)
  maxReservedBytes : Nat
  deriving BEq, Repr

def defaultStructuralAbove : Nat := 4096

def aggregateGiB : Nat := 1024 * 1024 * 1024

/-- Calibration-pending q=100 lift reserve from the measured §3.2 upper
bound. A slot heavier than the configured budget is admitted only by itself,
matching the existing Rust-side `RamGate` and avoiding deadlock. -/
def aggregateLiftRamBytes : Nat := 195 * aggregateGiB

/-- M1 name for shape-0 wrap cost. Keep the lift alias above while the
benchmark/test union is migrated in M1-e/M1-f. -/
def aggregateWrapRamBytes : Nat := aggregateLiftRamBytes

/-- Structural joins are dominated by the same two recursive-proof checks as
lifts. Keep the conservative lift reserve until the real E2E calibration. -/
def aggregateStructuralJoinRamBytes : Nat := aggregateLiftRamBytes

/-- Native verification and forwarding of a raw shard proof in direct mode.
The expensive proof-advice expansion is charged to its consuming pair. -/
def aggregateRawShardRamBytes : Nat := 4 * aggregateGiB

/-- Measured upper envelope for an `IxVM + IxVM` pair (shapes 2/6). -/
def aggregateDirectJoinRamBytes : Nat := 390 * aggregateGiB

/-- Measured upper envelope for a mixed recursive/IxVM pair (shapes 3/4/7/8). -/
def aggregateMixedJoinRamBytes : Nat := 340 * aggregateGiB

/-- Flat joins add canonical subject-tree work to the recursive-proof base.
One MiB per subject is a deliberately conservative placeholder: at Init's
~52k-subject root it adds ~51 GiB, consistent with the §11.4 estimate. The
default structural threshold caps this term near 4 GiB in production. -/
def aggregateFlatJoinRamPerSubjectBytes : Nat := 1024 * 1024

/-- Per-shape RAM weight used by the Lean admission gate. Shape 5 retains the
flat subject-count reserve; shape 9 is the O(1)-subject structural arm. The
direct/mixed values are conservative round-ups of the §3.4 measurements. -/
def aggregateShapeRamBytes (shape subjectCount : Nat) : Nat :=
  match shape with
  | 0 | 1 => aggregateWrapRamBytes
  | 2 | 6 => aggregateDirectJoinRamBytes
  | 3 | 4 | 7 | 8 => aggregateMixedJoinRamBytes
  | 5 => aggregateStructuralJoinRamBytes +
      subjectCount * aggregateFlatJoinRamPerSubjectBytes
  | 9 => aggregateStructuralJoinRamBytes
  | _ => aggregateDirectJoinRamBytes

/-- Calibration-pending per-slot RAM weight used by the Lean admission gate.
The `none` fallback preserves the pre-M1 meaning of hand-built test plans. -/
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

private def aggregateScheduleInputsValid (plan : Array ScheduledFold)
    (weights : Array Nat) : Except String Unit := do
  if weights.size != plan.size then
    throw s!"aggregate scheduler received {weights.size} weights for {plan.size} slots"
  for (item, slotIdx) in plan.mapIdx fun slotIdx item => (item, slotIdx) do
    if weights[slotIdx]! == 0 then
      throw s!"aggregate scheduler slot {slotIdx} has zero RAM weight"
    match item.op with
    | .leaf _ => pure ()
    | .join left right =>
      if left >= slotIdx || right >= slotIdx then
        throw s!"aggregate scheduler slot {slotIdx} has non-prior child {left}, {right}"

private def aggregateDependenciesComplete (item : ScheduledFold)
    (completed : Array Bool) : Bool :=
  match item.op with
  | .leaf _ => true
  | .join left right =>
    (completed[left]?).getD false && (completed[right]?).getD false

/-- Select one deterministic admission batch from the currently ready slots.
Candidates are ordered by descending RAM weight, then ascending slot number.
Slots that do not fit are skipped so lighter work can use the remaining
budget. An individually oversized slot may run only when nothing else is
reserved, following the Rust `RamGate` admit-when-alone rule. `jobs = 0`
means no concurrency cap beyond the number of plan slots. -/
def admitAggregateReady (plan : Array ScheduledFold) (weights : Array Nat)
    (completed inFlight : Array Bool) (reservedBytes budgetBytes jobs : Nat) :
    Array Nat := Id.run do
  let active := inFlight.count true
  let maxJobs := if jobs == 0 then max 1 plan.size else max 1 jobs
  if active >= maxJobs then return #[]
  let openJobs := maxJobs - active
  let mut ready : Array Nat := #[]
  for slotIdx in [:plan.size] do
    if !(completed[slotIdx]?).getD false &&
        !(inFlight[slotIdx]?).getD false then
      if let some item := plan[slotIdx]? then
        if aggregateDependenciesComplete item completed then
          ready := ready.push slotIdx
  ready := ready.qsort fun left right =>
    let leftWeight := (weights[left]?).getD 0
    let rightWeight := (weights[right]?).getD 0
    leftWeight > rightWeight || (leftWeight == rightWeight && left < right)
  let mut admitted : Array Nat := #[]
  let mut admittedBytes := 0
  for slotIdx in ready do
    if admitted.size >= openJobs then break
    let weight := (weights[slotIdx]?).getD 0
    let nextReserved := reservedBytes + admittedBytes + weight
    if nextReserved <= budgetBytes ||
        (reservedBytes == 0 && admitted.isEmpty) then
      admitted := admitted.push slotIdx
      admittedBytes := admittedBytes + weight
  return admitted

/-- Pure deterministic exercise of the runtime admission algorithm. This is
used to gate heaviest-first ordering, dependency release, job caps, and peak
reservation without starting proof tasks. -/
def simulateAggregateSchedule (plan : Array ScheduledFold)
    (weights : Array Nat) (jobs budgetBytes : Nat) :
    Except String AggregateScheduleTrace := do
  aggregateScheduleInputsValid plan weights
  if budgetBytes == 0 then throw "aggregate scheduler RAM budget must be positive"
  let mut completed := Array.replicate plan.size false
  let mut inFlight := Array.replicate plan.size false
  let mut completedCount := 0
  let mut reservedBytes := 0
  let mut maxReservedBytes := 0
  let mut admissionOrder : Array Nat := #[]
  let mut admissionBatches : Array (Array Nat) := #[]
  while completedCount < plan.size do
    let admitted := admitAggregateReady plan weights completed inFlight
      reservedBytes budgetBytes jobs
    if !admitted.isEmpty then
      admissionBatches := admissionBatches.push admitted
      for slotIdx in admitted do
        inFlight := inFlight.set! slotIdx true
        reservedBytes := reservedBytes + weights[slotIdx]!
        admissionOrder := admissionOrder.push slotIdx
      maxReservedBytes := max maxReservedBytes reservedBytes
    let mut finish? : Option Nat := none
    for slotIdx in [:plan.size] do
      if finish?.isNone && inFlight[slotIdx]! then finish? := some slotIdx
    let some finished := finish?
      | throw "aggregate scheduler deadlocked with unfinished slots"
    inFlight := inFlight.set! finished false
    completed := completed.set! finished true
    reservedBytes := reservedBytes - weights[finished]!
    completedCount := completedCount + 1
  pure { admissionOrder, admissionBatches, maxReservedBytes }

private def formatAggregateGiB (bytes : Nat) : String :=
  let tenths := bytes * 10 / aggregateGiB
  s!"{tenths / 10}.{tenths % 10}"

/-- Linux `MemTotal` parser kept separate so the 92% default has a pure seam.
The fallback only affects non-Linux hosts; admit-when-alone still guarantees
progress without pretending the fallback is a calibrated capacity. -/
def aggregateMemTotalBytes (contents : String) : Option Nat :=
  (contents.splitOn "\n").findSome? fun line =>
    if line.startsWith "MemTotal:" then
      ((line.splitOn " ").filter (· != "") |>.drop 1).head?.bind fun kib =>
        kib.toNat?.map (· * 1024)
    else none

def defaultAggregateRamBudgetBytes : IO Nat := do
  let contents ← try IO.FS.readFile "/proc/meminfo" catch _ => pure ""
  return match aggregateMemTotalBytes contents with
    | some total => total / 100 * 92
    | none => 16 * aggregateGiB

/-- Bump when aggregate cache identity changes beyond the recursion verifying
key. Version 2 marks M1's uniform `ix_aggr` outer claims. Encoded as `u64`
little-endian in every cache key. -/
def aggregateCacheVersion : Nat := 2

/--
`blake3(version ‖ recursion_vk_digest ‖ fri_params_ser ‖ outer_claim_bytes)`.

`serializeClaims #[outerClaim]` is the canonical, length-delimited outer-claim
encoding. The expected outer claim commits to the single entrypoint, allowed
blob, and output statement at every persisted node.
-/
def aggregateCacheKey (recursionVk : ByteArray)
    (recursionParameters : MultiStark.RecursionParameters)
    (outerClaim : Array Aiur.G) (version : Nat := aggregateCacheVersion) : Address :=
  let recursionVkDigest := (Address.blake3 recursionVk).hash
  let outerClaimBytes := MultiStark.serializeClaims #[outerClaim]
  Address.blake3 ⟨MultiStark.u64le version ++ recursionVkDigest.data ++
    recursionParameters.cacheFriBytes.data ++ outerClaimBytes.data⟩

/-- Resolve the global aggregate cache or a hermetic test root. -/
def aggregateCacheDir (cacheRoot : Option System.FilePath := none) : IO System.FilePath := do
  match cacheRoot with
  | some root =>
    let dir := root / "aggregate"
    IO.FS.createDirAll dir
    pure dir
  | none => StoreIO.toIO (Store.cacheDir "aggregate")

/-- Read an untrusted cache-index entry without turning malformed content into
a command failure. Store loading and proof verification happen separately. -/
def readAggregateCacheAddress (dir : System.FilePath) (key : Address) :
    IO AggregateCacheAddress := do
  let path := dir / toString key
  if !(← path.pathExists) then return .miss
  try
    let raw ← IO.FS.readFile path
    match Address.fromString raw.trimAscii.toString with
    | some address => return .hit address
    | none => return .invalid "index content is not a 64-character store address"
  catch e =>
    return .invalid s!"index read failed: {e}"

/-- Atomically replace one derived cache-index entry. -/
def writeAggregateCacheAddress (dir : System.FilePath) (key address : Address) :
    IO Unit := do
  let tmp := dir / s!"{key}.tmp"
  IO.FS.writeFile tmp s!"{address}\n"
  IO.FS.rename tmp (dir / toString key)

/-- A cached wrapper is reusable only when both its bundled `CheckEnv` claim
and its proof under the exact expected outer Aiur claim validate. -/
def validateAggregateCacheWrapper (recursionSystem : Aiur.AiurSystem)
    (expectedClaim : Ix.Claim) (expectedOuterClaim : Array Aiur.G)
    (wrapper : Ixon.Proof) : Except String Aiur.Proof := do
  if wrapper.claim != expectedClaim then
    throw s!"bundled claim {wrapper.claim} does not match expected {expectedClaim}"
  let proof ← Aiur.Proof.ofBytesChecked wrapper.proof
  recursionSystem.verify expectedOuterClaim proof
  pure proof

/-- Resolve subject counts and the structural threshold once, before proving.
Because parent counts only grow, `count > structuralAbove` makes the mode
monotone: a flat join is never scheduled above a structural child. -/
def schedulePlan (plan : Array Ix.Cli.CheckCmd.AggregationTree.FoldOp)
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

/-- Convert the old host record used by the scheduler/cache tests into the
converged host record. Both commit to the same subject and assumption trees. -/
def toAggrCheckEnvTrees (statement : MultiStark.CheckEnvTrees) :
    Aggr.CheckEnvTrees :=
  { subjects := statement.subjects, assumptions := statement.assumptions }

/-- Convert a converged host fold back into the stable driver record while the
M1-e test union still shares the pre-convergence public structures. -/
def fromAggrCheckEnvTrees (statement : Aggr.CheckEnvTrees) :
    MultiStark.CheckEnvTrees :=
  { subjects := statement.subjects, assumptions := statement.assumptions }

/-- Every persisted aggregate proof now has the same outer claim regardless
of whether its witness used a wrap, flat pair, or structural pair. -/
def aggregateOuterClaim (allowed : ByteArray) (aggrIdx : Aiur.Bytecode.FunIdx)
    (claim : Ix.Claim) : Array Aiur.G :=
  Aiur.buildClaim aggrIdx (Aggr.pubInput allowed (Ix.Claim.ser claim)) #[]

/-- Derive every converged slot statement, uniform outer claim, kind, and
cache key before proving. Wrap-first leaves use shape 0; direct-policy leaves
remain raw IxVM claims and are deliberately not cache-consumed. -/
def buildAggrSlotSpecs (plan : Array ScheduledFold)
    (prepared : Array PreparedShard) (aggrVk allowed : ByteArray)
    (verifyIdx aggrIdx : Aiur.Bytecode.FunIdx)
    (recursionParameters : MultiStark.RecursionParameters) :
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
      let leftAggr := toAggrCheckEnvTrees left.statement
      let rightAggr := toAggrCheckEnvTrees right.statement
      let outputAggr := if item.structural then
          leftAggr.joinStructural rightAggr
        else
          leftAggr.join rightAggr
      let output := fromAggrCheckEnvTrees outputAggr
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

private def addrOfHex (label value : String) : Except String Address :=
  match Address.fromString value with
  | some address => .ok address
  | none => .error
    s!"{label}: expected a 64-character address, got {value.length} characters"

private def prepareOwnedShard (env : Ixon.Env) (owned : Array Address) :
    Except String PreparedShard := do
  let (claim, trees) ← IxVM.ClaimHarness.shardCheckEnvClaimTrees env owned
  let statement ← MultiStark.CheckEnvTrees.ofClaim claim trees
  pure { claim, statement }

/-- Reconstruct every shard statement after partitioning environment ownership
in one pass. Calling `ownedConstsForBlocks` once per shard rescans the complete
environment for every leaf, which made Mathlib aggregate startup take more
than twenty minutes before the proof store was touched. -/
def prepareShards (env : Ixon.Env) (shards : Array (Array Address))
    (shardIds : Array Nat := #[]) : Except String (Array PreparedShard) := do
  let ownedAll := Ix.Cli.CheckCmd.ownedConstsPer env shards
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

private def compileToplevel (label : String)
    (source : Except Aiur.Global Aiur.Source.Toplevel) :
    IO (Except String Aiur.CompiledToplevel) := do
  match source with
  | .error e => return Except.error s!"{label} toplevel merge failed: {e}"
  | .ok top => match top.compile with
    | .error e => return Except.error s!"{label} compilation failed: {e}"
    | .ok compiled => return Except.ok compiled

private structure AggregateBackend where
  compiled : Aiur.CompiledToplevel
  system : Aiur.AiurSystem
  vk : ByteArray

/-- Compile a Lean-authored Aiur program, then perform the Rust-side system
construction and verifying-key serialization in the same worker. Keeping this
pipeline together lets the independent IxVM and recursion backends build in
parallel instead of serializing their Rust setup on the controller thread. -/
private def buildAggregateBackend (label : String)
    (source : Unit → Except Aiur.Global Aiur.Source.Toplevel)
    (commitment : Aiur.CommitmentParameters) (fri : Aiur.FriParameters) :
    IO (Except String AggregateBackend) := do
  let source ← IO.lazyPure source
  let compiled ← match ← compileToplevel label source with
    | .error e => return .error e
    | .ok compiled => pure compiled
  let system := Aiur.AiurSystem.build compiled.bytecode commitment fri
  let vk := system.vkBytes
  return .ok { compiled, system, vk }

private structure LoadedShardProof where
  address : Address
  wrapper : Ixon.Proof

private def loadShardProofs (proofHexes : List String) :
    IO (Except String (Array LoadedShardProof)) := do
  let mut loaded : Array LoadedShardProof := #[]
  for proofHex in proofHexes do
    let proofAddress ← match addrOfHex "shard proof" proofHex with
      | .error e => return .error e
      | .ok address => pure address
    let wrapper ← match Ixon.Proof.de (← StoreIO.toIO (Store.read proofAddress)) with
      | .error e =>
        return .error s!"decode shard proof {proofAddress}: {e}"
      | .ok wrapper => pure wrapper
    loaded := loaded.push { address := proofAddress, wrapper }
  return .ok loaded

private def timed {α : Type} (action : IO α) : IO (α × Nat) := do
  let started ← IO.monoMsNow
  let result ← action
  pure (result, (← IO.monoMsNow) - started)

/-- Execute a post-order aggregate plan as a dependency-driven DAG. The
controller is the sole owner of completion and reservation state: it admits a
heaviest-first batch, starts one dedicated task per slot, then releases child
dependencies as results arrive. `runSlot` receives an immutable snapshot in
which every declared child is complete.

On the first failure no further work is admitted, but already-running tasks
are drained before returning. This prevents orphan proof tasks and permits
successful independent slots to finish publishing cache entries safely. -/
def runAggregateDag (plan : Array ScheduledFold) (weights : Array Nat)
    (jobs budgetBytes : Nat)
    (runSlot : Nat → Array (Option α) → IO (Except String α))
    (trace : Bool := false) : IO (Except String (Array α)) := do
  match aggregateScheduleInputsValid plan weights with
  | .error e => return .error e
  | .ok () => pure ()
  if budgetBytes == 0 then
    return .error "aggregate scheduler RAM budget must be positive"

  let resultChan ← Std.CloseableChannel.Sync.new
    (α := Nat × Nat × Except String α)
  let mut tasks : Array (Task (Except IO.Error Unit)) := #[]
  let mut slots : Array (Option α) := Array.replicate plan.size none
  let mut completed := Array.replicate plan.size false
  let mut inFlight := Array.replicate plan.size false
  let mut completedCount := 0
  let mut active := 0
  let mut reservedBytes := 0
  let mut failures : Array (Nat × String) := #[]
  let maxJobs := if jobs == 0 then max 1 plan.size else max 1 jobs

  while completedCount < plan.size do
    if failures.isEmpty then
      let admitted := admitAggregateReady plan weights completed inFlight
        reservedBytes budgetBytes jobs
      for slotIdx in admitted do
        let weight := weights[slotIdx]!
        inFlight := inFlight.set! slotIdx true
        active := active + 1
        reservedBytes := reservedBytes + weight
        if trace then
          let overBudget := if weight > budgetBytes then "; over-budget slot runs alone" else ""
          IO.println s!"[aggregate] slot {slotIdx}: admitted {formatAggregateGiB weight} GiB; \
            reserved {formatAggregateGiB reservedBytes}/{formatAggregateGiB budgetBytes} GiB; \
            active {active}/{maxJobs}{overBudget}"
        let snapshot := slots
        let task ← IO.asTask (prio := .dedicated) do
          let result ← try runSlot slotIdx snapshot catch e =>
            pure (.error s!"uncaught IO error: {e}")
          discard <| resultChan.send (slotIdx, weight, result)
        tasks := tasks.push task

    if active == 0 then
      if failures.isEmpty then
        failures := failures.push
          (plan.size, "aggregate scheduler deadlocked with unfinished slots")
      break

    match ← resultChan.recv with
    | none =>
      failures := failures.push
        (plan.size, "aggregate scheduler result channel closed unexpectedly")
      break
    | some (slotIdx, weight, result) =>
      if !(inFlight[slotIdx]?).getD false then
        failures := failures.push
          (slotIdx, "aggregate scheduler received a duplicate or unknown result")
      else
        inFlight := inFlight.set! slotIdx false
        active := active - 1
        reservedBytes := reservedBytes - weight
        match result with
        | .error e => failures := failures.push (slotIdx, e)
        | .ok value =>
          slots := slots.set! slotIdx (some value)
          completed := completed.set! slotIdx true
          completedCount := completedCount + 1

  -- A failure stops admission but never abandons tasks already inside an FFI
  -- prove. Drain their channel results before closing and joining handles.
  while active > 0 do
    match ← resultChan.recv with
    | none =>
      failures := failures.push
        (plan.size, "aggregate scheduler result channel closed while draining")
      active := 0
    | some (slotIdx, weight, result) =>
      if (inFlight[slotIdx]?).getD false then
        inFlight := inFlight.set! slotIdx false
        active := active - 1
        reservedBytes := reservedBytes - weight
      match result with
      | .error e => failures := failures.push (slotIdx, e)
      | .ok value =>
        slots := slots.set! slotIdx (some value)
        if !(completed[slotIdx]?).getD false then
          completed := completed.set! slotIdx true
          completedCount := completedCount + 1
  discard <| resultChan.close
  for task in tasks do
    match task.get with
    | .ok () => pure ()
    | .error e =>
      failures := failures.push (plan.size,
        s!"aggregate scheduler task failed: {e}")

  if !failures.isEmpty then
    let sortedFailures := failures.qsort fun left right => left.1 < right.1
    let (slotIdx, e) := sortedFailures[0]!
    return .error (if slotIdx < plan.size then s!"slot {slotIdx}: {e}" else e)

  let mut result : Array α := #[]
  for slotIdx in [:plan.size] do
    let some value := (slots[slotIdx]?).join
      | return .error s!"aggregate scheduler completed without slot {slotIdx}"
    result := result.push value
  pure (.ok result)

def loadCachedAggregateProofWith
    (readStore : Address → IO ByteArray) (dir : System.FilePath) (slotIdx : Nat)
    (spec : AggregateSlotSpec) (recursionSystem : Aiur.AiurSystem) :
    IO (Option CachedAggregateProof) := do
  match ← readAggregateCacheAddress dir spec.cacheKey with
  | .miss => return none
  | .invalid reason =>
    IO.println s!"[aggregate] slot {slotIdx}: cache miss ({reason})"
    return none
  | .hit address =>
    try
      let bytes ← readStore address
      if Address.blake3 bytes != address then
        IO.println s!"[aggregate] slot {slotIdx}: cache miss \
          (store object {address} has a different content digest)"
        return none
      let wrapper ← match Ixon.Proof.de bytes with
        | .ok wrapper => pure wrapper
        | .error e =>
          IO.println s!"[aggregate] slot {slotIdx}: cache miss \
            (wrapper {address} does not decode: {e})"
          return none
      match validateAggregateCacheWrapper recursionSystem spec.statement.claim
          spec.outerClaim wrapper with
      | .ok proof =>
        IO.println s!"[aggregate] slot {slotIdx}: cache hit {address}"
        return some { proof, address }
      | .error e =>
        IO.println s!"[aggregate] slot {slotIdx}: cache miss \
          (wrapper {address} rejected: {e})"
        return none
    catch e =>
      IO.println s!"[aggregate] slot {slotIdx}: cache miss \
        (cannot load wrapper {address}: {e})"
      return none

private def loadCachedAggregateProof (dir : System.FilePath) (slotIdx : Nat)
    (spec : AggregateSlotSpec) (recursionSystem : Aiur.AiurSystem) :
    IO (Option CachedAggregateProof) :=
  loadCachedAggregateProofWith (fun address => StoreIO.toIO (Store.read address))
    dir slotIdx spec recursionSystem

private def persistAggregateCacheProof (dir : System.FilePath) (slotIdx : Nat)
    (spec : AggregateSlotSpec) (proof : Aiur.Proof) : IO (Option Address) := do
  try
    let _ ← StoreIO.toIO (Store.write (Ix.Claim.ser spec.statement.claim))
    let wrapper : Ixon.Proof := { claim := spec.statement.claim, proof := proof.toBytes }
    let address ← StoreIO.toIO (Store.write (Ixon.Proof.ser wrapper))
    writeAggregateCacheAddress dir spec.cacheKey address
    IO.println s!"[aggregate] slot {slotIdx}: cached proof {address}"
    return some address
  catch e =>
    IO.eprintln s!"[aggregate] slot {slotIdx}: warning: could not persist cache entry: {e}"
    return none

private def printPlan (plan : Array ScheduledFold) (shardIds : Array Nat)
    (structuralAbove : Nat) : IO Unit := do
  let leaves := plan.countP fun item => match item.op with
    | .leaf _ => true
    | .join _ _ => false
  let wraps := plan.countP fun item => match item.op with
    | .leaf _ => item.kind == .aggr
    | .join _ _ => false
  let structural := plan.countP (·.structural)
  let directLeaves := leaves - wraps
  let leafPolicy := if directLeaves == 0 then s!"{wraps} wraps"
    else s!"{directLeaves} direct IxVM leaves"
  IO.println s!"[aggregate] plan: {leafPolicy} + {plan.size - leaves} binary joins \
    ({structural} structural; threshold > {structuralAbove} subject leaves)"
  for (item, slot) in plan.mapIdx fun slot item => (item, slot) do
    match item.op with
    | .leaf shard =>
      let originalShard := (shardIds[shard]?).getD shard
      let mode := if item.kind == .ixvm then "raw shard" else "wrap shard"
      IO.println s!"  slot {slot}: {mode} {originalShard} ({item.subjectCount} subjects)"
    | .join left right =>
      let mode := if item.structural then "structural" else "flat"
      IO.println s!"  slot {slot}: {mode} shape {item.shape?.getD 255} \
        slots {left}, {right} ({item.subjectCount} subjects)"

private structure AggregateProveContext where
  plan : Array ScheduledFold
  specs : Array AggregateSlotSpec
  prepared : Array PreparedShard
  proofsByShard : Std.HashMap Nat Ixon.Proof
  shardIds : Array Nat
  ixvmSystem : Aiur.AiurSystem
  aggrSystem : Aiur.AiurSystem
  ixvmVk : ByteArray
  aggrVk : ByteArray
  allowed : ByteArray
  verifyIdx : Aiur.Bytecode.FunIdx
  aggrIdx : Aiur.Bytecode.FunIdx
  cacheDir? : Option System.FilePath

/-- Prove or resume one slot whose dependencies have already completed. The
scheduler catches IO exceptions around this function; protocol and validation
failures stay explicit so the lowest failed slot can be reported
deterministically after all admitted tasks drain. -/
private def proveAggregateSlot (ctx : AggregateProveContext) (slotIdx : Nat)
    (slots : Array (Option AggregateSlot)) : IO (Except String AggregateSlot) := do
  let some item := ctx.plan[slotIdx]?
    | return .error "missing scheduled fold item"
  let some spec := ctx.specs[slotIdx]?
    | return .error "missing prepared aggregate slot"
  match item.op with
  | .leaf shard =>
    let originalShard := (ctx.shardIds[shard]?).getD shard
    let some wrapper := ctx.proofsByShard.get? shard
      | return .error s!"no proof for shard {originalShard}"
    let some preparedShard := ctx.prepared[shard]?
      | return .error s!"no statement for shard {originalShard}"
    let claimBytes := Ix.Claim.ser preparedShard.claim
    let verifyInput := IxVM.ClaimHarness.packedDigestKey
      (Address.blake3 claimBytes)
    let innerClaim := Aiur.buildClaim ctx.verifyIdx verifyInput #[]
    let innerProof ← match Aiur.Proof.ofBytesChecked wrapper.proof with
      | .error e =>
        return Except.error s!"shard {originalShard} proof does not decode: {e}"
      | .ok proof => pure proof
    match ctx.ixvmSystem.verify innerClaim innerProof with
    | .error e =>
      return Except.error s!"shard {originalShard} proof fails native verification: {e}"
    | .ok () => pure ()
    let innerClaimsBytes := MultiStark.serializeClaims #[innerClaim]
    match spec.kind with
    | .ixvm =>
      if spec.outerClaim != innerClaim then
        return .error "direct shard slot has an unexpected outer claim"
      return .ok {
        kind := .ixvm
        statement := spec.statement
        subjectCount := spec.subjectCount
        outerClaim := innerClaim
        proof := innerProof
        proofAddress? := none
        claimsBytes := innerClaimsBytes
      }
    | .aggr =>
      let cached? ← match ctx.cacheDir? with
        | none => pure none
        | some dir => loadCachedAggregateProof dir slotIdx spec ctx.aggrSystem
      let (proof, proofAddress?) ← match cached? with
        | some cached => pure (cached.proof, some cached.address)
        | none =>
          let innerProofAdvice ← match ctx.ixvmSystem.proofToAdviceBytes
              innerClaim innerProof with
            | .error e =>
              return .error s!"shard {originalShard} proof advice encoding failed: {e}"
            | .ok bytes => pure bytes
          let shape := item.shape?.getD (Aggr.shapeCode (.ixvm, none))
          let pubInput := Aggr.pubInput ctx.allowed claimBytes
          IO.println s!"[aggregate] wrapping shard {originalShard} into slot {slotIdx}"
          (← IO.getStdout).flush
          let result := ctx.aggrSystem.proveIxAggr ctx.aggrIdx pubInput shape
            innerProofAdvice ByteArray.empty ctx.ixvmVk ctx.aggrVk
            innerClaimsBytes ByteArray.empty claimBytes ctx.allowed
            (Aggr.preimagesBlob #[]) (Aggr.treesBlob #[]) (Aggr.pathsBlob #[])
          let (outerClaim, proof) ← match result with
            | .error e => return .error s!"wrap proving failed: {e}"
            | .ok result => pure result
          if outerClaim != spec.outerClaim then
            return .error "wrap produced an unexpected outer claim"
          let proofAddress? ← match ctx.cacheDir? with
            | none => pure none
            | some dir => persistAggregateCacheProof dir slotIdx spec proof
          pure (proof, proofAddress?)
      return .ok {
        kind := .aggr
        statement := spec.statement
        subjectCount := spec.subjectCount
        outerClaim := spec.outerClaim
        proof
        proofAddress?
        claimsBytes := MultiStark.serializeClaims #[spec.outerClaim]
      }
  | .join leftIdx rightIdx =>
    let some left := (slots[leftIdx]?).join
      | return .error s!"missing completed left slot {leftIdx}"
    let some right := (slots[rightIdx]?).join
      | return .error s!"missing completed right slot {rightIdx}"
    let output := spec.statement
    let outputClaimBytes := Ix.Claim.ser output.claim
    let cached? ← match ctx.cacheDir? with
      | none => pure none
      | some dir => loadCachedAggregateProof dir slotIdx spec ctx.aggrSystem
    let (proof, proofAddress?) ← match cached? with
      | some cached => pure (cached.proof, some cached.address)
      | none =>
        let pubInput := Aggr.pubInput ctx.allowed outputClaimBytes
        let leftClaimsBytes := left.claimsBytes
        let rightClaimsBytes := right.claimsBytes
        let leftStatement := toAggrCheckEnvTrees left.statement
        let rightStatement := toAggrCheckEnvTrees right.statement
        let outputStatement := toAggrCheckEnvTrees output
        let preimagesBlob := Aggr.preimagesBlob
          #[Ix.Claim.ser left.statement.claim, Ix.Claim.ser right.statement.claim]
        let trees := if item.structural then
            Aggr.CheckEnvTrees.structuralAdviceTrees
              leftStatement rightStatement outputStatement
          else
            Aggr.CheckEnvTrees.adviceTrees
              leftStatement rightStatement outputStatement
        let treesBlob := Aggr.treesBlob trees
        let pathsBlob := if item.structural then
            Aggr.pathsBlob
              (Aggr.CheckEnvTrees.structuralPathAdvice
                leftStatement rightStatement outputStatement)
          else
            Aggr.pathsBlob #[]
        let mode := if item.structural then "structural" else "flat"
        let leftSystem := match left.kind with
          | .ixvm => ctx.ixvmSystem
          | .aggr => ctx.aggrSystem
        let rightSystem := match right.kind with
          | .ixvm => ctx.ixvmSystem
          | .aggr => ctx.aggrSystem
        let leftProofAdvice ← match leftSystem.proofToAdviceBytes
            left.outerClaim left.proof with
          | .error e => return .error s!"left child proof advice encoding failed: {e}"
          | .ok bytes => pure bytes
        let rightProofAdvice ← match rightSystem.proofToAdviceBytes
            right.outerClaim right.proof with
          | .error e => return .error s!"right child proof advice encoding failed: {e}"
          | .ok bytes => pure bytes
        IO.println s!"[aggregate] {mode}-joining slots {leftIdx}, {rightIdx} into {slotIdx}"
        (← IO.getStdout).flush
        let some shape := item.shape?
          | return .error "aggregate pair is missing its ix_aggr shape"
        let result := ctx.aggrSystem.proveIxAggr ctx.aggrIdx pubInput shape
          leftProofAdvice rightProofAdvice ctx.ixvmVk ctx.aggrVk
          leftClaimsBytes rightClaimsBytes outputClaimBytes ctx.allowed
          preimagesBlob treesBlob pathsBlob
        let (outerClaim, proof) ← match result with
          | .error e => return .error e
          | .ok result => pure result
        if outerClaim != spec.outerClaim then
          return .error "join produced an unexpected outer claim"
        let proofAddress? ← match ctx.cacheDir? with
          | none => pure none
          | some dir => persistAggregateCacheProof dir slotIdx spec proof
        pure (proof, proofAddress?)
    return .ok {
      kind := .aggr
      statement := output
      subjectCount := spec.subjectCount
      outerClaim := spec.outerClaim
      proof
      proofAddress?
      claimsBytes := MultiStark.serializeClaims #[spec.outerClaim]
    }

/-- Production Stage 2 entrypoint. The Lean-authored circuit sources still
compile here, in parallel with mmap-loading the environment. Once both Aiur
systems exist, one FFI call transfers the complete data-dependent pipeline to
Rust; no Lean statement tree or scheduler task survives on this path. -/
private def runAggregateCmdNativeWith
    (recursionParameters : MultiStark.RecursionParameters)
    (p : Cli.Parsed) : IO UInt32 := do
  let some ixePath := (p.flag? "ixe").map (·.as! String) | do
    p.printError "error: aggregate requires --ixe <env.ixe>"
    return 1
  let some manifestPath := (p.flag? "ixes").map (·.as! String) | do
    p.printError "error: aggregate requires --ixes <manifest.ixes>"
    return 1
  let maxRamGb? := (p.flag? "max-ram").map (·.as! Nat)
  if maxRamGb? == some 0 then
    IO.eprintln "error: --max-ram must be positive"
    return 1
  let ramBudgetBytes ← match maxRamGb? with
    | some gib => pure (gib * aggregateGiB)
    | none => defaultAggregateRamBudgetBytes
  let jobs := ((p.flag? "jobs").map (·.as! Nat)).getD 0
  let structuralAbove := ((p.flag? "structural-above").map (·.as! Nat)).getD
    defaultStructuralAbove
  let proofHexes := String.intercalate "\n"
    (p.variableArgsAs! String).toList

  let setupStarted ← IO.monoMsNow
  let envTask ← IO.asTask (prio := .dedicated) do
    timed (IO.lazyPure fun _ => Aiur.EnvHandle.fromIxe ixePath)
  let ixvmBackendTask ← IO.asTask (prio := .dedicated) do
    timed (buildAggregateBackend "IxVM" (fun _ => IxVM.ixVM)
      Aiur.defaultCommitmentParameters Aiur.defaultFriParameters)
  let aggrBackendTask ← IO.asTask (prio := .dedicated) do
    timed (buildAggregateBackend "ixAggr recursion" (fun _ => Aggr.ixAggr)
      recursionParameters.commitment recursionParameters.fri)

  -- Join every setup branch before selecting an error, so a failed branch
  -- cannot orphan compilation work in the process.
  let (envResult, envMs) ← IO.ofExcept envTask.get
  let (ixvmResult, ixvmMs) ← IO.ofExcept ixvmBackendTask.get
  let (aggrResult, aggrMs) ← IO.ofExcept aggrBackendTask.get
  let setupMs := (← IO.monoMsNow) - setupStarted
  IO.println s!"[aggregate] parallel host setup: {setupMs}ms \
    (environment {envMs}ms, IxVM backend {ixvmMs}ms, ixAggr backend {aggrMs}ms)"
  (← IO.getStdout).flush

  let envHandle ← match envResult with
    | .error e => IO.eprintln s!"EnvHandle.fromIxe {ixePath}: {e}"; return 1
    | .ok handle => pure handle
  let ixvmBackend ← match ixvmResult with
    | .error e => IO.eprintln e; return 1
    | .ok backend => pure backend
  let aggrBackend ← match aggrResult with
    | .error e => IO.eprintln e; return 1
    | .ok backend => pure backend
  let verifyIdx := ixvmBackend.compiled.getFuncIdx `verify_claim |>.get!
  let aggrIdx := aggrBackend.compiled.getFuncIdx `ix_aggr |>.get!
  let nativeResult ← IO.lazyPure fun _ =>
    ixvmBackend.system.aggregateStage2 aggrBackend.system envHandle
      manifestPath proofHexes verifyIdx aggrIdx jobs ramBudgetBytes
      structuralAbove (p.hasFlag "direct-joins")
      (p.hasFlag "plan-only")
      recursionParameters.cacheFriBytes !(p.hasFlag "no-cache")
  match nativeResult with
  | .error e => IO.eprintln s!"aggregate failed: {e}"; return 1
  | .ok _ => return 0

/-- Aggregate with an explicit recursion-proof configuration. The CLI wrapper
below supplies `defaultRecursionParameters`; keeping this seam explicit lets a
future policy or cache layer select a recursion configuration without changing
the canonical IxVM proof parameters. -/
private def runAggregateCmdLeanReferenceWith
    (recursionParameters : MultiStark.RecursionParameters)
    (p : Cli.Parsed) : IO UInt32 := do
  let some ixePath := (p.flag? "ixe").map (·.as! String) | do
    p.printError "error: aggregate requires --ixe <env.ixe>"
    return 1
  let some manifestPath := (p.flag? "ixes").map (·.as! String) | do
    p.printError "error: aggregate requires --ixes <manifest.ixes>"
    return 1

  let startupStarted ← IO.monoMsNow

  let rawView ← match Ix.Cli.CheckCmd.parseIxesManifest
      (← IO.FS.readBinFile manifestPath) with
    | .error e => IO.eprintln s!"manifest parse failed: {e}"; return 1
    | .ok view => pure view
  let env ← match Ixon.deEnvAnon (← IO.FS.readBinFile ixePath) with
    | .error e => IO.eprintln s!"deserialize {ixePath} failed: {e}"; return 1
    | .ok env => pure env
  if !(← Ix.Cli.CheckCmd.shardsCover env rawView.shards) then return 1
  let (view, shardCounts) ← match rawView.pruneEmpty env with
    | .error e => IO.eprintln e; return 1
    | .ok pruned => pure pruned
  let prunedCount := rawView.shards.size - view.shards.size
  if prunedCount != 0 then
    IO.println s!"[aggregate] pruned {prunedCount} zero-constant manifest shard(s)"

  let structuralAbove := ((p.flag? "structural-above").map (·.as! Nat)).getD
    defaultStructuralAbove
  let directJoins := p.hasFlag "direct-joins"
  let plan ← match schedulePlan view.aggregationTree.foldPlan shardCounts
      structuralAbove directJoins with
    | .error e => IO.eprintln e; return 1
    | .ok plan => pure plan
  printPlan plan view.shardIds structuralAbove
  let jobs := ((p.flag? "jobs").map (·.as! Nat)).getD 0
  let maxRamGb? := (p.flag? "max-ram").map (·.as! Nat)
  if maxRamGb? == some 0 then
    IO.eprintln "error: --max-ram must be positive"
    return 1
  let ramBudgetBytes ← match maxRamGb? with
    | some gib => pure (gib * aggregateGiB)
    | none => defaultAggregateRamBudgetBytes
  let slotWeights := aggregateSlotRamWeights plan
  let jobsLabel := if jobs == 0 then "all ready slots" else toString jobs
  let budgetSource := if maxRamGb?.isSome then "--max-ram" else "92% MemTotal"
  IO.println s!"[aggregate] scheduler: jobs={jobsLabel}, RAM budget \
    {formatAggregateGiB ramBudgetBytes} GiB ({budgetSource}); \
    wrap/self reserve {formatAggregateGiB aggregateWrapRamBytes} GiB, \
    direct {formatAggregateGiB aggregateDirectJoinRamBytes} GiB, mixed \
    {formatAggregateGiB aggregateMixedJoinRamBytes} GiB, flat +1 MiB/subject"
  if p.hasFlag "plan-only" then return 0

  let proofHexes := (p.variableArgsAs! String).toList
  if proofHexes.length != view.shards.size then
    IO.eprintln s!"aggregate requires exactly {view.shards.size} shard proofs; got {proofHexes.length}"
    return 1

  -- Statement preparation, proof loading, and the two independent backend
  -- setup pipelines have no data dependencies. Run all four branches together,
  -- then join every task before selecting a deterministic error to report.
  let parallelStarted ← IO.monoMsNow
  let prepareTask ← IO.asTask (prio := .dedicated) do
    timed (IO.lazyPure fun _ => prepareShards env view.shards view.shardIds)
  let proofsTask ← IO.asTask (prio := .dedicated) do
    timed (loadShardProofs proofHexes)
  let ixvmBackendTask ← IO.asTask (prio := .dedicated) do
    timed (buildAggregateBackend "IxVM" (fun _ => IxVM.ixVM)
      Aiur.defaultCommitmentParameters Aiur.defaultFriParameters)
  let aggrBackendTask ← IO.asTask (prio := .dedicated) do
    timed (buildAggregateBackend "ixAggr recursion" (fun _ => Aggr.ixAggr)
      recursionParameters.commitment recursionParameters.fri)

  let prepareOutcome := prepareTask.get
  let proofsOutcome := proofsTask.get
  let ixvmBackendOutcome := ixvmBackendTask.get
  let aggrBackendOutcome := aggrBackendTask.get
  let (prepareResult, prepareMs) ← IO.ofExcept prepareOutcome
  let (proofsResult, proofsMs) ← IO.ofExcept proofsOutcome
  let (ixvmBackendResult, ixvmBackendMs) ← IO.ofExcept ixvmBackendOutcome
  let (aggrBackendResult, aggrBackendMs) ← IO.ofExcept aggrBackendOutcome
  let parallelMs := (← IO.monoMsNow) - parallelStarted
  let startupMs := (← IO.monoMsNow) - startupStarted
  IO.println s!"[aggregate] startup: parse/plan {parallelStarted - startupStarted}ms; \
    parallel wall {parallelMs}ms (prepare {prepareMs}ms, proofs {proofsMs}ms, \
    IxVM backend {ixvmBackendMs}ms, ixAggr backend {aggrBackendMs}ms); \
    total {startupMs}ms"
  (← IO.getStdout).flush

  let prepared ← match prepareResult with
    | .error e => IO.eprintln e; return 1
    | .ok prepared => pure prepared
  let loadedProofs ← match proofsResult with
    | .error e => IO.eprintln e; return 1
    | .ok loaded => pure loaded
  let ixvmBackend ← match ixvmBackendResult with
    | .error e => IO.eprintln e; return 1
    | .ok backend => pure backend
  let aggrBackend ← match aggrBackendResult with
    | .error e => IO.eprintln e; return 1
    | .ok backend => pure backend

  -- Proof arguments may be in any order. Match them by their bundled claim and
  -- reject duplicates/missing shards before starting an expensive wrap.
  let mut digestToShard : Std.HashMap Address Nat := {}
  for (item, shard) in prepared.mapIdx fun shard item => (item, shard) do
    let originalShard := (view.shardIds[shard]?).getD shard
    let digest := Address.blake3 (Ix.Claim.ser item.claim)
    if digestToShard.contains digest then
      IO.eprintln s!"duplicate reconstructed shard claim digest {digest} \
        (manifest shard {originalShard})"
      return 1
    digestToShard := digestToShard.insert digest shard

  let mut proofsByShard : Std.HashMap Nat Ixon.Proof := {}
  for loaded in loadedProofs do
    let proofAddress := loaded.address
    let wrapper := loaded.wrapper
    let digest := Address.blake3 (Ix.Claim.ser wrapper.claim)
    let some shard := digestToShard.get? digest | do
      IO.eprintln s!"proof {proofAddress} claim {digest} matches no manifest shard"
      return 1
    let some expected := prepared[shard]? | do
      IO.eprintln s!"internal: missing prepared shard {shard}"
      return 1
    let originalShard := (view.shardIds[shard]?).getD shard
    if wrapper.claim != expected.claim then
      IO.eprintln s!"proof {proofAddress} hit a claim-digest collision for shard {originalShard}"
      return 1
    if proofsByShard.contains shard then
      IO.eprintln s!"more than one proof supplied for shard {originalShard}"
      return 1
    proofsByShard := proofsByShard.insert shard wrapper
  if proofsByShard.size != view.shards.size then
    IO.eprintln "not every manifest shard has a supplied proof"
    return 1

  let verifyIdx := ixvmBackend.compiled.getFuncIdx `verify_claim |>.get!
  let aggrIdx := aggrBackend.compiled.getFuncIdx `ix_aggr |>.get!
  let ixvmSystem := ixvmBackend.system
  let aggrSystem := aggrBackend.system
  let ixvmVk := ixvmBackend.vk
  let aggrVk := aggrBackend.vk
  let allowed := Aggr.allowedBlob ixvmVk verifyIdx aggrVk aggrIdx
  let specs ← match buildAggrSlotSpecs plan prepared aggrVk allowed
      verifyIdx aggrIdx recursionParameters with
    | .error e => IO.eprintln s!"prepare aggregate slots: {e}"; return 1
    | .ok specs => pure specs
  let cacheDir? ← if p.hasFlag "no-cache" then
      IO.println "[aggregate] cache disabled (--no-cache)"
      pure none
    else
      pure (some (← aggregateCacheDir))

  let proveContext : AggregateProveContext := {
    plan, specs, prepared, proofsByShard, shardIds := view.shardIds
    ixvmSystem, aggrSystem, ixvmVk, aggrVk, allowed
    verifyIdx, aggrIdx, cacheDir?
  }
  let slots ← match ← runAggregateDag plan slotWeights jobs ramBudgetBytes
      (proveAggregateSlot proveContext) true with
    | .error e => IO.eprintln s!"aggregate failed: {e}"; return 1
    | .ok slots => pure slots

  let some root := slots.back? | do
    IO.eprintln "aggregate plan produced no root slot"
    return 1
  if root.kind != .aggr then
    IO.eprintln "aggregate plan produced a raw IxVM root instead of an ix_aggr proof"
    return 1
  let some envTree := IxVM.ClaimHarness.envCanonicalTree env | do
    IO.eprintln "cannot aggregate an empty environment"
    return 1
  let some canonicalRoot := Ix.AssumptionTree.canonical root.statement.subjects.leaves | do
    IO.eprintln "aggregate root subject tree has no real leaves"
    return 1
  if canonicalRoot.root != envTree.root then
    IO.eprintln s!"aggregate root subjects canonicalize to {canonicalRoot.root}, not env root {envTree.root}"
    return 1
  if root.statement.assumptions.isSome then
    IO.eprintln s!"aggregate root retains undischarged assumptions {root.statement.assumptions.map (·.root)}"
    return 1
  match aggrSystem.verify root.outerClaim root.proof with
  | .error e => IO.eprintln s!"aggregate root proof failed native verification: {e}"; return 1
  | .ok () => pure ()

  let proofAddress ← match root.proofAddress? with
    | some address => pure address
    | none =>
      let claim := root.statement.claim
      let _ ← StoreIO.toIO (Store.write (Ix.Claim.ser claim))
      let wrapper : Ixon.Proof := { claim, proof := root.proof.toBytes }
      StoreIO.toIO (Store.write (Ixon.Proof.ser wrapper))
  IO.println s!"[aggregate] root proof: {proofAddress}"
  return 0

/-- Aggregate through the native Stage 2 controller. The retained Lean driver
above is a protocol reference and unit-test seam; it is not on the CLI path. -/
def runAggregateCmdWith (recursionParameters : MultiStark.RecursionParameters)
    (p : Cli.Parsed) : IO UInt32 :=
  runAggregateCmdNativeWith recursionParameters p

def runAggregateCmd (p : Cli.Parsed) : IO UInt32 :=
  runAggregateCmdWith MultiStark.defaultRecursionParameters p

end Ix.Cli.AggregateCmd

open Ix.Cli.AggregateCmd in
def aggregateCmd : Cli.Cmd := `[Cli|
  aggregate VIA runAggregateCmd;
  "Wrap shard proofs and fold multi-shard manifests into one recursive aggregate"

  FLAGS:
    "ixe" : String;  "Path to the serialized environment whose shards were proven."
    "ixes" : String; "Path to the shard manifest; its bisection tree determines join order."
    "plan-only";     "Validate coverage and print the wrap/join slot plan without loading or proving shard proofs."
    "no-cache";      "Bypass aggregate cache reads and intermediate cache writes; the root wrapper is still persisted."
    "jobs" : Nat;    "Maximum aggregate slots proving concurrently (default 0: all ready slots, subject to the RAM gate)."
    "max-ram" : Nat; "Aggregate in-flight RAM budget in GiB (default: 92% of MemTotal). An estimated-oversized slot runs alone."
    "structural-above" : Nat; "Use structural joins when a node contains more than N subject leaves (default 4096; 0 means every join)."
    "direct-joins";  "Keep IxVM leaves raw until their first pair instead of wrapping first (non-default; substantially higher RAM)."

  ARGS:
    ...proofs : String; "Persisted shard-proof wrapper addresses, in any order (exactly one per nonempty shard unless --plan-only)."
]

end
