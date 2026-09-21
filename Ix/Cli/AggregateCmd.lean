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
public import Cli
public import Ix.Aggr
public import Ix.Cli.CheckCmd
public import Ix.IxVM
public import Ix.IxVM.ClaimHarness
public import MultiStark
public import Ix.Store

public section

namespace Ix.Cli.AggregateCmd

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
  op : Ix.Cli.CheckCmd.AggregationTree.FoldOp
  subjectCount : Nat
  structural : Bool
  /-- Result kind of this slot. Only direct-policy leaves are `.ixvm`. -/
  kind : Aggr.ChildKind := .aggr
  /-- `ix_aggr` shape proven by this slot. Direct-policy raw leaves have no
  shape because they are verified and forwarded without a recursion proof. -/
  shape? : Option Nat := none
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

/-- Native verification and serialization of a raw shard proof in direct mode
is charged to its consuming pair. -/
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
    (recursionParameters : Aggr.RecursionParameters)
    (outerClaim : Array Aiur.G) (version : Nat := aggregateCacheVersion) : Address :=
  let recursionVkDigest := (Address.blake3 recursionVk).hash
  let outerClaimBytes := MultiStark.serializeClaims #[outerClaim]
  Address.blake3 ⟨MultiStark.u64le version ++ recursionVkDigest.data ++
    recursionParameters.cacheFriBytes.data ++ outerClaimBytes.data⟩

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
    (source : Except Aiur.Global Aiur.Source.Toplevel)
    (groups : Array (String × Array String)) :
    IO (Except String Aiur.CompiledToplevel) := do
  match source with
  | .error e => return Except.error s!"{label} toplevel merge failed: {e}"
  | .ok top => match top.compileWithGroups groups with
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
    (groups : Array (String × Array String))
    (commitment : Aiur.CommitmentParameters) (fri : Aiur.FriParameters) :
    IO (Except String AggregateBackend) := do
  let source ← IO.lazyPure source
  let compiled ← match ← compileToplevel label source groups with
    | .error e => return .error e
    | .ok compiled => pure compiled
  let system := Aiur.AiurSystem.build compiled.bytecode commitment fri
  let vk := system.vkBytes
  return .ok { compiled, system, vk }

private def timed {α : Type} (action : IO α) : IO (α × Nat) := do
  let started ← IO.monoMsNow
  let result ← action
  pure (result, (← IO.monoMsNow) - started)

/-- Production Stage 2 entrypoint. The Lean-authored circuit sources still
compile here, in parallel with mmap-loading the environment. Once both Aiur
systems exist, one FFI call transfers the complete data-dependent pipeline to
Rust; no Lean statement tree or scheduler task survives on this path. -/
private def runAggregateCmdNativeWith
    (recursionParameters : Aggr.RecursionParameters)
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
  let reproveSlot? := (p.flag? "reprove-slot").map (·.as! Nat)
  if reproveSlot?.isSome && p.hasFlag "plan-only" then
    IO.eprintln "error: --reprove-slot cannot be combined with --plan-only"
    return 1
  if reproveSlot?.isSome && p.hasFlag "no-cache" then
    IO.eprintln "error: --reprove-slot requires aggregate cache reads"
    return 1
  let reproveSlotCode := reproveSlot?.map (· + 1) |>.getD 0
  let proofHexes := String.intercalate "\n"
    (p.variableArgsAs! String).toList

  let setupStarted ← IO.monoMsNow
  let envTask ← IO.asTask (prio := .dedicated) do
    timed (IO.lazyPure fun _ => Aiur.EnvHandle.fromIxe ixePath)
  let ixvmBackendTask ← IO.asTask (prio := .dedicated) do
    timed (buildAggregateBackend "IxVM" (fun _ => IxVM.ixVM) IxVM.functionGroups
      Aiur.defaultCommitmentParameters Aiur.defaultFriParameters)
  let aggrBackendTask ← IO.asTask (prio := .dedicated) do
    timed (buildAggregateBackend "ixAggr recursion" (fun _ => Aggr.ixAggr)
      Aggr.functionGroups recursionParameters.commitment recursionParameters.fri)

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
      structuralAbove reproveSlotCode (p.hasFlag "direct-joins")
      (p.hasFlag "plan-only")
      recursionParameters.cacheFriBytes (!(p.hasFlag "no-cache"))
      (!(p.hasFlag "no-write"))
  match nativeResult with
  | .error e => IO.eprintln s!"aggregate failed: {e}"; return 1
  | .ok _ => return 0

/-- Aggregate through the native controller. -/
def runAggregateCmdWith (recursionParameters : Aggr.RecursionParameters)
    (p : Cli.Parsed) : IO UInt32 :=
  runAggregateCmdNativeWith recursionParameters p

def runAggregateCmd (p : Cli.Parsed) : IO UInt32 :=
  runAggregateCmdWith Aggr.defaultRecursionParameters p

end Ix.Cli.AggregateCmd

open Ix.Cli.AggregateCmd in
def aggregateCmd : Cli.Cmd := `[Cli|
  aggregate VIA runAggregateCmd;
  "Wrap shard proofs and fold multi-shard manifests into one recursive aggregate"

  FLAGS:
    "ixe" : String;  "Path to the serialized environment whose shards were proven."
    "ixes" : String; "Path to the shard manifest; its bisection tree determines join order."
    "plan-only";     "Validate coverage and print the wrap/join slot plan without loading or proving shard proofs."
    "no-cache";      "Bypass aggregate cache reads and intermediate cache writes; the root wrapper is still persisted unless --no-write."
    "no-write";      "Do not change the proof store or aggregate cache; useful with --reprove-slot for a read-only spot check."
    "reprove-slot" : Nat; "Recompute exactly Stage 2 slot N from verified cached immediate children, bypassing that slot's cache entry."
    "jobs" : Nat;    "Maximum aggregate slots proving concurrently (default 0: all ready slots, subject to the RAM gate)."
    "max-ram" : Nat; "Aggregate in-flight RAM budget in GiB (default: 92% of MemTotal). An estimated-oversized slot runs alone."
    "structural-above" : Nat; "Use structural joins when a node contains more than N subject leaves (default 4096; 0 means every join)."
    "direct-joins";  "Keep IxVM leaves raw until their first pair instead of wrapping first (non-default; substantially higher RAM)."

  ARGS:
    ...proofs : String; "Persisted shard-proof wrapper addresses, in any order (one per nonempty shard, except --plan-only or replay with aggregate children)."
]

end
