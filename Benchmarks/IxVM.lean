import Cli
import Ix.Cli.BenchCmd
import Ix.Cli.FormalAggregate
import Ix.KernelCheck
import Ix.FormalCompiler

/-!
# `bench-ixvm`: one constant's IxVM benchmark row, measured in process

```
bench-ixvm --ixe <env.ixe> --const <name> --json <rows.json> [--mode execute|prove]
           [--root-out <file>] [--max-ram <GiB>]
```

The environment and the formal programs load once, outside every timed
window. Execution is one `Check` claim of the constant, timed by its
`aiur/execute` span (`execute-time`), with the process's peak RSS sampled over
it (`peak-rss`). Prove mode then extracts the constant into an environment of
its own and partitions it into `proveShards` shards (setup, untimed), proves
both claims and their join on the aggregate controller (`prove-time`,
`prove-peak-rss`, `prove-proof-size`, and `prove-trace-shards`, the trace
shards of the two claim proofs), and verifies the root (`verify-time`) after
checking it proves the environment's statement.

Each stage's fields are merged into the constant's row as it completes, so a
killed run keeps what it measured. Exit codes: `0` every stage ran, `3` the
kernel rejected the constant (its row is on disk), `6` a stage after
execution failed (the execution row is on disk), `2` a usage error; anything
else is an infrastructure failure. `ix bench run --backend ixvm` runs this
once per constant.
-/

open Lean Aggr
open Ix.Benchmark.Results
open Ix Ix.Cli Ix.Cli.FormalAiur

namespace Benchmarks.IxVM

/-- Seconds since `start`, from the monotonic clock. -/
def since (start : Nat) : IO Float :=
  return ((← IO.monoNanosNow) - start).toFloat / 1e9

/-- Run `act` and return its result, its wall-clock seconds and the process's
peak RSS sampled over it. -/
def measured {α : Type} (act : IO α) : IO (α × Float × Nat) := do
  TracingTexray.resetPeakTreeRss
  let start ← IO.monoNanosNow
  let result ← act
  let seconds ← since start
  return (result, seconds, ← TracingTexray.peakTreeRssBytes)

/-- The aggregation context over already loaded programs: the same systems
and pinned identity `FormalAggregate.context` builds. -/
def aggregateContext (ixvm aggregation : Selected) : IO FormalAggregate.Context := do
  let ixvmSystem ← ixvm.system
  let aggrSystem ← aggregation.system
  let aggr ← FormalAggregate.identity aggrSystem true
  let ixvmId ← FormalAggregate.identity ixvmSystem false
  let allowed ← Ix.Cli.FormalKeys.pinnedAllowed ixvmId.key ixvmId.index aggr.key aggr.index
  return { ixvmArtifact := ixvm.path, aggrArtifact := aggregation.path, ixvmSystem,
           aggrSystem, ixvm := ixvmId, aggr, allowed }

/-- The root statement `manifest` folds to over the environment at `ixe`,
with every constant audited, as `ix verify --aggregate` recomputes it. -/
def expectedRoot (ixe manifest : String) : IO Ix.Claim := do
  let env ← IO.ofExcept (IxVM.ClaimHarness.withDefaultRoleBinding
    (← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile ixe))))
  let view ← IO.ofExcept (Ix.Shard.parseIxesManifest (← IO.FS.readBinFile manifest))
  unless ← Ix.Shard.shardsCover env view.shards do
    throw (IO.userError "invalid manifest coverage")
  let (view, _) ← IO.ofExcept (view.pruneEmpty env)
  let root ← IO.ofExcept (Reference.expectedFromManifest env view defaultStructuralAbove)
  let _ ← IO.ofExcept (auditAggregateConstants env root)
  return root.claim

/-- Prove `name` end to end on the aggregate controller and merge the prove
stage's fields into its row. Returns the root's store address. -/
def prove (p : Cli.Parsed) (ctx : FormalAggregate.Context) (ixe name out : String)
    (constants : Nat) (dir : System.FilePath) : IO Address := do
  let one := (dir / "env.ixe").toString
  let manifest := (dir / "env.ixes").toString
  let proven := (dir / "proven.ixes").toString
  Ix.KernelCheck.rsEnvExtractFFI ixe #[name] one true
  Ix.KernelCheck.rsShardEnvStaticFFI one Ix.Cli.BenchCmd.proveShards.toUSize 0 5 manifest 3
  let (_, handle) ← Ix.Check.loadBoundIxe one
  let options ← hostOptions p
  let lanes := Ix.Cli.BenchCmd.proveShards
  let config : FormalProver.LaneConfig := {
    manifest, lanes, device := options.device
    maxRamBytes := ((p.flag? "max-ram").map (·.as! Nat)).map (· * 1024^3 / lanes) |>.getD 0
    execJobs := 0, structuralAbove := defaultStructuralAbove, outManifest := some proven
    select := none, bindingProof := none, options := options.job
    useCache := false, useIndex := false, claimsOnly := false, assumeBinding := false }
  let (result, proveSeconds, provePeak) ← measured
    (FormalProver.proveLanes ctx.ixvmSystem ctx.aggrSystem handle config)
  let .root bytes traceShards := result
    | throw (IO.userError "the controller returned claims instead of a root")
  let address : Address := ⟨bytes⟩
  let wrapper ← FormalAggregate.resultWrapper address
  unless wrapper.claim == (← expectedRoot one proven) do
    throw (IO.userError "the controller's root does not prove the environment's statement")
  let size := (← (← StoreIO.toIO (Store.storePath address)).metadata).byteSize.toNat
  Ix.Cli.BenchCmd.addFields out name [
    ("prove-time", jsonRound 6 proveSeconds), ("prove-peak-rss", toJson provePeak),
    ("prove-proof-size", toJson size), ("prove-trace-shards", toJson traceShards),
    ("prove-throughput", jsonRound 2 (constants.toFloat / proveSeconds))]
  let (_, verifySeconds, _) ← measured (FormalAggregate.verifyWrapper ctx .aggr wrapper)
  Ix.Cli.BenchCmd.addFields out name [("verify-time", jsonRound 6 verifySeconds)]
  return address

def run (p : Cli.Parsed) : IO UInt32 := do
  let some ixe := (p.flag? "ixe").map (·.as! String)
    | p.printError "error: --ixe is required"; return exitUsage
  let some name := (p.flag? "const").map (·.as! String)
    | p.printError "error: --const is required"; return exitUsage
  let some out := (p.flag? "json").map (·.as! String)
    | p.printError "error: --json is required"; return exitUsage
  let mode := ((p.flag? "mode").map (·.as! String)).getD "execute"
  unless mode == "execute" || mode == "prove" do
    p.printError s!"error: unknown mode `{mode}` (expected execute or prove)"; return exitUsage
  let spans := out ++ ".spans"
  TracingTexray.init { namePrefixes := "aiur/", trackRam := false, streaming := false }
  TracingTexray.jsonSink spans
  TracingTexray.startSampler
  let registry ← FormalProver.Registry.new
  let (ixvm, aggregation) ← if mode == "prove" then do
      let selected ← selectAll p registry #[.ixvm, .aggregation]
      let (some ixvm, some aggregation) := (selected[0]?, selected[1]?)
        | throw (IO.userError "missing selected programs")
      pure (ixvm, some aggregation)
    else pure (← artifact p registry, none)
  let (ixonEnv, handle) ← Ix.Check.loadBoundIxe ixe
  let some addr := Ix.Cli.NameResolve.resolveIxeAddr ixonEnv name
    | p.printError s!"error: {name} not found in {ixe}"; return exitUsage
  let claim ← Ix.Check.checkClaimOf ixonEnv addr
  -- The constants the claim checks: its closure, as main's Aiur throughput
  -- counted them.
  let constants := (IxVM.ClaimHarness.closureFromRoots ixonEnv #[addr]).size
  let env ← FormalProver.Env.ofHandle handle
  let options ← hostOptions p
  let (result, _, peak) ← measured
    (one p ixvm options "execute" claim (fun _ => targetRequest (some env) claim (.addr addr)) name)
  let execute := ((← Ix.Cli.BenchCmd.readSpans spans).find? (·.1 == "aiur/execute")).map (·.2)
  let some seconds := execute
    | IO.eprintln s!"[bench-ixvm] {name}: the check failed before executing its claim (code {result.code})"
      return 1
  let row := Json.mkObj [("execute-time", jsonRound 6 seconds), ("peak-rss", toJson peak),
    ("throughput", jsonRound 2 (constants.toFloat / seconds))]
  if result.code != 0 then
    writeEntry out name (row.setObjVal! "status" (.str "rejected"))
    return exitRejected
  writeEntry out name row
  let some aggregation := aggregation | return 0
  let ctx ← aggregateContext ixvm aggregation
  try
    let root ← IO.FS.withTempDir fun dir => prove p ctx ixe name out constants dir
    if let some path := (p.flag? "root-out").map (·.as! String) then
      IO.FS.writeFile path s!"{root}\n"
    return 0
  catch e =>
    IO.eprintln s!"[bench-ixvm] {name}: proving failed: {e}"
    return exitStageFailed

end Benchmarks.IxVM

open Benchmarks.IxVM in
def benchIxvmCmd : Cli.Cmd := `[Cli|
  "bench-ixvm" VIA run;
  "Measure one constant's IxVM execution, and with --mode prove its aggregate proof and root verification, in one process; merge the fields into its row of a benchmark results JSON."

  FLAGS:
    ixe             : String; "The environment (.ixe) the constant lives in"
    const           : String; "The constant to measure"
    json            : String; "Benchmark results JSON to merge the constant's row into"
    mode            : String; "execute (default) or prove"
    "root-out"      : String; "With --mode prove: write the verified root's store address here"
    "max-ram"       : Nat;    "Total RAM budget in GiB for execution and the controller's lanes (default: 85% of available memory)"
    "aiur-artifact" : String; "Trusted exported formal IxVM artifact; otherwise compile/cache local sources"
    "aggr-artifact" : String; "Trusted formal aggregation artifact; otherwise compile/cache local sources"
]

def main (args : List String) : IO UInt32 := benchIxvmCmd.validate args
