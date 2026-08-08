/-
  `ix profile <path.ixe>`: run the Ix kernel out of circuit over a serialized
  `.ixe` environment, recording per-block heartbeats and the delta-unfold graph
  into a `.ixprof` sidecar. This is the cost model consumed by `ix shard`
  (see `plans/sharding.md`).

  Recording defaults to *cache-isolated* mode: the kernel clears its
  cross-constant reduction-memo caches between constants so every delta-unfold
  re-executes (sound recording) and recorded heartbeats reflect the in-circuit
  (un-memoized) cost. `--keep-caches` trades fidelity for speed.
-/
module
public import Cli
public import Ix.Common
public import Ix.KernelCheck
public import Std.Internal.UV.System

public section

open Ix.KernelCheck

namespace Ix.Cli.ProfileCmd

def runSweepCmd (p : Cli.Parsed) : IO UInt32 := do
  let some pathArg := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a .ixe file"
      return 1
  let envPath := pathArg.as! String
  let base := if envPath.endsWith ".ixe" then (envPath.dropEnd 4).toString else envPath
  let profPath := (p.flag? "prof").map (·.as! String) |>.getD (base ++ ".ixprof")
  let csvPath  := (p.flag? "out").map (·.as! String) |>.getD (base ++ "-sweep.csv")
  let budget   := (p.flag? "budget").map (·.as! Nat) |>.getD 64
  let topBlocks := (p.flag? "top-blocks").map (·.as! Nat) |>.getD 10
  let reps     := (p.flag? "reps").map (·.as! Nat) |>.getD 10
  IO.println s!"Sweeping {envPath} × {profPath} → {csvPath} (budget {budget} GiB)"
  rsProfileSweepFFI envPath profPath csvPath (toString budget)
    (toString topBlocks) (toString reps)
  IO.println s!"[sweep] wrote {csvPath}"
  return 0

def sweepCmd : Cli.Cmd := `[Cli|
  "sweep" VIA runSweepCmd;
  "Closure cost sweep: predicted Aiur execute/prove cost for every named constant's dependency closure, plus feasibility/bottleneck/diversity reports"

  FLAGS:
    prof         : String; "Input .ixprof from `ix profile` (default: <env>.ixprof)"
    out          : String; "Output CSV path (default: <env>-sweep.csv)"
    budget       : Nat;    "RAM budget in GiB for the feasibility report (default 64)"
    "top-blocks" : Nat;    "Expensive blocks tracked for the min-root report (default 10, max 64)"
    reps         : Nat;    "Diverse feature-mix representatives to pick (default 10; 0 disables)"

  ARGS:
    path : String; "Path to the serialized .ixe the .ixprof was profiled from"
]

def runProfileCmd (p : Cli.Parsed) : IO UInt32 := do
  let some pathArg := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a .ixe file"
      return 1
  let envPath := pathArg.as! String
  let outPath : String :=
    match p.flag? "out" with
    | some flag => flag.as! String
    -- Default sidecar mirrors the env's base name: `init.ixe` → `init.ixprof`
    -- (not `init.ixe.ixprof`); a non-`.ixe` path just gets `.ixprof` appended.
    | none      =>
      let base := if envPath.endsWith ".ixe" then (envPath.dropEnd 4).toString else envPath
      base ++ ".ixprof"
  let isolate := !(p.flag? "keep-caches" |>.isSome)
  let quiet   := !(p.flag? "verbose" |>.isSome)

  if let some flag := p.flag? "workers" then
    let n := flag.as! Nat
    if n == 0 then
      p.printError "error: --workers must be > 0"
      return 1
    Std.Internal.UV.System.osSetenv "IX_KERNEL_CHECK_WORKERS" (toString n)

  let top := (p.flag? "top").map (·.as! Nat) |>.getD 10
  let backend := (p.flag? "backend").map (·.as! String) |>.getD "all"
  if backend != "all" && backend != "aiur" && backend != "zisk" then
    p.printError s!"error: --backend must be all, aiur, or zisk (got {backend})"
    return 1

  IO.println s!"Profiling {envPath} → {outPath} (isolate={isolate})"
  let start ← IO.monoMsNow
  rsProfileAnonFFI envPath outPath isolate quiet (toString top) backend
  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"[profile] wrote {outPath} in {elapsed.formatMs}"
  return 0

end Ix.Cli.ProfileCmd

open Ix.Cli.ProfileCmd in
def profileCmd : Cli.Cmd := `[Cli|
  "profile" VIA runProfileCmd;
  "Profile a `.ixe` out of circuit → `.ixprof` (sharding cost + delta graph)"

  FLAGS:
    out           : String; "Output .ixprof path (default: <env>.ixprof, e.g. init.ixe → init.ixprof)"
    "keep-caches";          "Keep cross-constant caches: faster, lower-fidelity, may under-record"
    workers       : Nat;    "Parallel kernel workers (default: available_parallelism). Plumbs IX_KERNEL_CHECK_WORKERS."
    verbose;                "Log every constant (default: quiet)"
    top           : Nat;    "Block-leaderboard size in the summary: top N by heartbeats, substitutions, ingress bytes, and predicted per-backend cost (default 10; 0 disables)"
    backend       : String; "Cost models in the summary: all (default), aiur, or zisk"

  ARGS:
    path : String; "Path to a serialized .ixe environment"

  SUBCOMMANDS:
    sweepCmd
]

end
