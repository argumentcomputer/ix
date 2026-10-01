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
import Ix.TracingTexray
public import Cli
public import Ix.Aggr
public import Ix.Aggr.Backend
public import Ix.IxVM
public import MultiStark
public import Ix.Store

public section

namespace Ix.Cli.AggregateCmd

open Aggr

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
  let subtree? := (p.flag? "subtree").map (·.as! Nat)
  if subtree?.isSome && reproveSlot?.isSome then
    IO.eprintln "error: --subtree cannot be combined with --reprove-slot"
    return 1
  if subtree?.isSome && p.hasFlag "wrap-root" then
    IO.eprintln "error: --wrap-root applies to the root; --subtree proves a subtree"
    return 1
  if subtree?.isSome && p.hasFlag "no-cache" && !p.hasFlag "plan-only" then
    IO.eprintln "error: --subtree publishes its root through the aggregate cache; \
      it cannot run with --no-cache"
    return 1
  let subtreeCode := subtree?.map (· + 1) |>.getD 0
  let proofHexes := String.intercalate "\n"
    (p.variableArgsAs! String).toList

  let setupStarted ← IO.monoMsNow
  let envTask ← IO.asTask (prio := .dedicated) do
    timed (IO.lazyPure fun _ => Aiur.EnvHandle.fromIxe ixePath)
  let ixvmBackendTask ← IO.asTask (prio := .dedicated) do
    timed (Aggr.compileBackend "IxVM" (fun _ => IxVM.ixVM) IxVM.functionGroups
      Aiur.defaultCommitmentParameters Aiur.defaultFriParameters)
  let aggrBackendTask ← IO.asTask (prio := .dedicated) do
    timed (Aggr.compileBackend "ixAggr recursion" (fun _ => Aggr.ixAggr)
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
      (!(p.hasFlag "no-write")) (p.hasFlag "trace-shards")
      (((p.flag? "range").map (·.as! Nat)).getD 0) (p.hasFlag "wrap-root")
      (((p.flag? "exec-ahead").map (·.as! Nat)).getD 1) false subtreeCode
  match nativeResult with
  | .error e => IO.eprintln s!"aggregate failed: {e}"; return 1
  | .ok address =>
    -- The root (or subtree root) proof address, alone on stdout, is what
    -- a driver reads; the log lines are on stderr.
    if !address.isEmpty then
      IO.println address
      (← IO.getStdout).flush
    return 0

/-- Aggregate through the native controller. -/
def runAggregateCmdWith (recursionParameters : Aggr.RecursionParameters)
    (p : Cli.Parsed) : IO UInt32 :=
  runAggregateCmdNativeWith recursionParameters p

def runAggregateCmd (p : Cli.Parsed) : IO UInt32 := do
  -- Streamed `[texray]` span lines on stderr: the per-node wall and RSS
  -- breakdown of every slot's execution, witness and STARK phases.
  if p.hasFlag "texray" then TracingTexray.init {}
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
    "texray";        "Stream per-phase `[texray]` timing/RSS lines (execute, witness, STARK stages of every slot) to stderr as each span closes."
    "no-write";      "Do not change the proof store or aggregate cache; useful with --reprove-slot for a read-only spot check."
    "reprove-slot" : Nat; "Recompute exactly Stage 2 slot N from verified cached immediate children, bypassing that slot's cache entry."
    "jobs" : Nat;    "Maximum aggregate slots proving concurrently (default 0: all ready slots, subject to the RAM gate)."
    "max-ram" : Nat; "Aggregate in-flight RAM budget in GiB (default: 92% of MemTotal). An estimated-oversized slot runs alone."
    "structural-above" : Nat; "Use structural joins when a node contains more than N subject leaves (default 4096; 0 means every join)."
    "direct-joins";  "Keep IxVM leaves raw until their first pair instead of wrapping first (non-default; substantially higher RAM)."
    "trace-shards";  "Prove each slot as a batch of trace shards within its share of --max-ram (the budget divided by --jobs) instead of one unbudgeted proof; a slot no shard count can fit fails the run."
    "exec-ahead" : Nat; "Slots executing ahead of the provers (default 1): a ready join executes and plans while the previous one proves, so one GPU prover never waits for an execution; each slot ahead holds its execution record. 0: each slot executes and proves on one worker, --jobs at a time."
    "wrap-root";     "Wrap the root proof, each wrap a proof that verifies the previous one, until the final proof is a single trace shard."
    "subtree" : Nat; "Prove only the plan subtree rooted at slot N (slot numbers as --plan-only prints them) from the proofs of the leaves under it, and print that slot's proof address; root validation and --wrap-root do not apply. The proof is published through the aggregate cache, where a later full run over every shard proof finds it and proves only what is above it. With --plan-only, print `subtree N shards: <ids>`, the --shards argument for `ix prove` over those leaves."
    "range" : Nat;   "Wrap a shard proof of more than N trace shards as a range-sum tree — leaves verifying at most N shards each (--jobs at a time), joins, and a root with the wrap's statement — instead of one proof verifying every shard. 0 (default): with --trace-shards, two leaves per node slot (2 × --jobs), so each slot executes its next leaf while proving one; without, wrap whole."

  ARGS:
    ...proofs : String; "Persisted shard-proof wrapper addresses, in any order (one per nonempty shard, except --plan-only or replay with aggregate children)."
]

end
