/-
  `ix shard <path>`: partition an environment into shards, dispatched on
  the input type.

  `.ixe` input — the default, Aiur mode: **measured scan-and-cut**. The
  env's check schedule executes through the codegen'd Aiur kernel as
  thin-frontier `CheckEnv` claims with a running FFT readout, and shard
  boundaries are cut where the measured cost reaches the `--max-ram`
  budget's FFT equivalent (see `crates/ffi/src/aiur/scan.rs`). No profile
  pass, no cost model — the manifest carries the MEASURED per-shard cost.

  `.ixe` input with `--backend zisk`: Zisk's planner from the env in one
  command — the Rust-kernel profiling pass writes `<env>.ixprof`, then
  the guest-cost packer runs on it (the profile is kept: re-tuning the
  budget is pure offline graph work on the `.ixprof`).

  `.ixprof` input — the profile-driven packer directly (Zisk):
  - default / `--max-ram G` / `--max-cycles C`: **bin-pack to a per-shard
    cycle/RAM cap** — the fewest shards that each stay under the budget, each
    packed as full as the dependency structure allows (no `--max-ram` ⇒ sized to
    detected system RAM). Not balanced: packing yields the minimal shard count.
  - `--shards N`: force exactly `N` **balanced** min-cut shards (manual override).

  The `.ixprof` comes from `ix profile` (pure offline graph work, so the
  budget/`N` is cheap to re-tune without re-running the kernel). Both modes
  write a `.ixes` manifest (format v2, per-shard tagged costs) and print a
  what-if report. The partitioner is self-contained — no external
  graph-library dependency.

  `ix shard extract <path.ixe> --consts <n1,n2,…>`: the pipeline's scoping
  step — extract the named constants' dependency closure from a serialized
  env into a standalone `.ixe`, without recompiling from source. The output
  carries the closure's genuine constant bytes, blobs, and reducibility
  hints, plus each closure constant's name→address entry, so it composes
  with everything that consumes a `.ixe` (`ix profile` → `ix shard`,
  `ix check-rs --consts`, the zkVM hosts, `bench-typecheck`).
-/
module
public import Cli
public import Ix.Aiur.Compiler
public import Ix.Aiur.Protocol
public import Ix.Benchmark.Results
public import Ix.IxVM
public import Ix.IxVM.Toplevel
public import Ix.KernelCheck
public import Ix.TracingTexray
public import Ix.Cli.ConstsFile
public import Ix.Cli.NameOfCmd

public section

open Ix.KernelCheck

namespace Ix.Cli.ShardCmd

/-- Shard a `.ixe` env by MEASURED cost (the default `ix shard` mode for
    Aiur): execute the check schedule through the codegen'd Aiur kernel
    with a running FFT readout and cut boundaries at the RAM budget's FFT
    equivalent. No profile, no prediction; the manifest carries measured
    per-shard cost. -/
def runShardScan (p : Cli.Parsed) (ixePath : String) : IO UInt32 := do
  let outPath : String :=
    match p.flag? "out" with
    | some flag => flag.as! String
    | none      =>
      let base := if ixePath.endsWith ".ixe" then (ixePath.dropEnd 4).toString else ixePath
      base ++ ".ixes"
  let budget := (p.flag? "max-ram").map (·.as! Nat) |>.getD 250
  let eps := (p.flag? "eps").map (·.as! Nat) |>.getD 2
  let workers := (p.flag? "workers").map (·.as! Nat) |>.getD 0
  let noFailFast := p.hasFlag "no-fail-fast"
  if noFailFast && p.hasFlag "fail-fast" then
    p.printError "error: --fail-fast and --no-fail-fast are mutually exclusive"
    return 1
  -- Deferred ranges (regions whose opening cone exceeds a fleet slot —
  -- cone-bound kernel execution measured at hours of worker time on
  -- FLT/Mathlib-class content) are named infeasible instead of walked
  -- under fat caps, and the exclusion inventory is resolved to Lean
  -- names in `<out>.failed-names.txt`. Implies --no-fail-fast; the
  -- mode reaches the scanner as fail-fast mode string "2".
  let deferInfeasible := p.hasFlag "defer-infeasible"
  -- Cold re-price (opt-in): replace summed shard costs with one
  -- measured cold execution per merged shard, packing past the cut by
  -- the validated slack. Adopt per env only after its re-priced
  -- manifest passes the heaviest-shard prove protocol.
  let reprice := p.hasFlag "reprice"
  let toplevel ← match IxVM.ixVM with
    | .error e => IO.eprintln s!"Toplevel merging failed: {e}"; return 1
    | .ok t => pure t
  let compiled ← match toplevel.compile with
    | .error e => IO.eprintln s!"Compilation failed: {e}"; return 1
    | .ok c => pure c
  let funIdx ← match compiled.getFuncIdx `verify_claim with
    | some i => pure i
    | none => IO.eprintln "error: verify_claim missing"; return 1
  let envHandle ← match Aiur.EnvHandle.fromIxe ixePath with
    | .error e => IO.eprintln s!"EnvHandle.fromIxe {ixePath}: {e}"; return 1
    | .ok h => pure h
  let workersDesc := if workers == 0 then "auto" else toString workers
  IO.println s!"Scanning {ixePath} @ {budget} GiB (ε {eps}%, {workersDesc} workers)"
  (← IO.getStdout).flush
  -- `benchJson = (out, rowName)` reports the scan as a benchmark row
  -- (the `aiur` bench backend's whole-env execute row): the scan IS a
  -- whole-env execution — the cut on top of it is an in-memory merge
  -- over the collected block records — so the wall reports as
  -- `execute-time`, windowing the scan itself: the env mmap and
  -- toplevel build are excluded, so the measure tracks the kernel
  -- execution, not the loader. `peak-rss` is the process tree's
  -- absolute high-water, matching the check rows' semantics.
  let benchJson := (p.flag? "json").map fun f =>
    (f.as! String, ((p.flag? "json-name").map (·.as! String)).getD "scan")
  if benchJson.isSome then
    TracingTexray.startSampler
    TracingTexray.resetPeakTreeRss
  let start ← IO.monoMsNow
  -- The compiled system feeds the scanner's analytic peak-prove-RAM
  -- model (circuit widths, lookup shapes, quotient degrees); its one-time
  -- build cost (preprocessed gadget commit) is seconds against a
  -- minutes-scale scan.
  let system := Aiur.AiurSystem.build compiled.bytecode
    Aiur.productionCommitmentParameters Aiur.productionFriParameters
  -- Process-pool mode: the scan spawns `<this binary> shard-worker`
  -- children under cgroup memory caps, so an over-cap worker is
  -- OOM-killed alone and recovered, never the box.
  let workerBin := (← IO.appPath).toString
  match Aiur.AiurSystem.scanShardsWithEnv system funIdx
      envHandle (toString budget) (toString eps) (toString workers)
      (if deferInfeasible && reprice then "4"
       else if reprice then "3"
       else if deferInfeasible then "2"
       else if noFailFast then "0"
       else "1")
      outPath workerBin ixePath with
  | .ok () =>
    if let some (out, rowName) := benchJson then
      let secs := ((← IO.monoMsNow) - start).toFloat / 1000.0
      let peakRss ← TracingTexray.peakTreeRssBytes
      Ix.Benchmark.Results.writeRow out rowName "ok"
        [ ("execute-time", Ix.Benchmark.Results.jsonRound 3 secs)
        , ("peak-rss", Lean.toJson peakRss) ]
    IO.println s!"[shard scan] wrote {outPath} (+ .costs.csv, measured)"
    -- Resolve the exclusion inventory to Lean names: one env decode +
    -- batch reverse-index lookup (`ix name-of --addrs-file` semantics),
    -- so a shard run over dense content ends with a readable list of
    -- exactly which constants were excluded and why.
    if deferInfeasible then
      let failedPath := outPath ++ ".failed.csv"
      if ← System.FilePath.pathExists failedPath then
        let mut addrs : Array Address := #[]
        for line in (← IO.FS.readFile failedPath).splitOn "\n" do
          let addrStr := (line.splitOn ",").headD ""
          if let some a := Address.fromString addrStr then
            addrs := addrs.push a
        if !addrs.isEmpty then
          let bytes ← IO.FS.readBinFile ixePath
          match Ixon.deEnvAnon bytes with
          | .error e =>
            IO.eprintln s!"[shard scan] failed-names resolution skipped: {e}"
          | .ok ixonEnv =>
            let resolved :=
              Ix.Cli.NameOfCmd.resolveAddrs ixonEnv addrs
            let namesPath := outPath ++ ".failed-names.txt"
            let lines := resolved.map fun (a, disp) => s!"{a} {disp}"
            IO.FS.writeFile namesPath
              (String.intercalate "\n" lines.toList ++ "\n")
            IO.println
              s!"[shard scan] {addrs.size} excluded block(s) resolved → \
                 {namesPath}"
    return 0
  | .error e =>
    IO.eprintln s!"error: shard scan failed: {e}"
    return 1

def runShardExtractCmd (p : Cli.Parsed) : IO UInt32 := do
  let some pathArg := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a .ixe file"
      return 1
  let envPath := pathArg.as! String
  let names ← Ix.Cli.ConstsFile.gather p
  if names.isEmpty then
    p.printError "error: pass at least one name via --consts or --consts-file"
    return 1
  let outPath : String :=
    match p.flag? "out" with
    | some flag => flag.as! String
    -- Default output mirrors the first constant's slug next to the source
    -- env: `init.ixe --consts Nat.add_comm` → `nat_add_comm.ixe`.
    | none =>
      let slug := names[0]!.map fun c =>
        if c.isAlphanum then c.toLower else '_'
      s!"{slug}.ixe"
  let quiet := !(p.flag? "verbose" |>.isSome)
  rsEnvExtractFFI envPath names outPath quiet
  IO.println s!"[extract] wrote {outPath} ({names.size} root name(s))"
  return 0

def shardExtractCmd : Cli.Cmd := `[Cli|
  "extract" VIA runShardExtractCmd;
  "Extract named constants + their dependency closure from a `.ixe` into a standalone `.ixe`"

  FLAGS:
    consts        : String; "Comma-separated EXACT constant names (displayed form) to extract, e.g. `Nat.add_comm,String.append`. Same flag/shape as `ix check-rs --consts`. A mutual-block member extracts its whole block."
    "consts-file" : String; "Additionally read names from a file (one per line; `#` comments and blank lines ignored). Unions with --consts."
    out           : String; "Output `.ixe` path. Defaults to a slug of the first name (e.g. `nat_add_comm.ixe`)."
    verbose;                "Print extraction details to stderr."

  ARGS:
    path : String; "Path to the source `.ixe` (e.g. from `ix compile`)."
]

def runShardCmd (p : Cli.Parsed) : IO UInt32 := do
  let some pathArg := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a .ixe (measured scan) or .ixprof (profile packer)"
      return 1
  let path := pathArg.as! String
  -- Dispatch on the input: a `.ixe` env runs the backend's own planner
  -- from the env itself — aiur (default) is the measured scan-and-cut;
  -- zisk chains the Rust-kernel profiling pass into the guest-cost
  -- packer, leaving the `.ixprof` next to the env so the budget can be
  -- re-tuned offline without re-running the kernel. A `.ixprof` input
  -- skips straight to the profile-driven packer.
  let mut espPath := path
  if path.endsWith ".ixe" then
    match (p.flag? "backend").map (·.as! String) |>.getD "aiur" with
    | "aiur" => return ← runShardScan p path
    | "zisk" =>
      let prof := (path.dropEnd 4).toString ++ ".ixprof"
      IO.println s!"Profiling {path} → {prof} (Rust-kernel pass, zisk counters)"
      (← IO.getStdout).flush
      rsProfileAnonFFI path prof true true "0" "zisk"
      espPath := prof
    | other =>
      p.printError s!"error: --backend must be aiur or zisk (got {other})"
      return 1
  let balancePct : Nat :=
    match p.flag? "balance" with
    | some flag => flag.as! Nat
    | none      => 5
  let outPath : String :=
    match p.flag? "out" with
    | some flag => flag.as! String
    -- Default manifest mirrors the profile's base name: `init.ixprof` →
    -- `init.ixes` (not `init.ixprof.ixes`).
    | none      =>
      let base := if espPath.endsWith ".ixprof" then (espPath.dropEnd 7).toString else espPath
      base ++ ".ixes"
  let shardsFlag : Option Nat := (p.flag? "shards").map (·.as! Nat)
  let maxCycles  : Option Nat := (p.flag? "max-cycles").map (·.as! Nat)
  let maxRam     : Option Nat := (p.flag? "max-ram").map (·.as! Nat)
  -- Provers the prove-time estimate assumes (wall clock = max(seq/P, slowest
  -- shard)). Sharded proving is sequential today, so the default is 1.
  let parallelism : Nat :=
    match p.flag? "parallelism" with
    | some flag => max 1 (flag.as! Nat)
    | none      => 1
  let backend := (p.flag? "backend").map (·.as! String) |>.getD "zisk"
  if backend != "zisk" && backend != "aiur" then
    p.printError s!"error: --backend must be zisk or aiur (got {backend})"
    return 1
  -- Reaching here with `aiur` means a `.ixprof` input (a `.ixe` dispatched
  -- to the scan above): the model packer that served it is gone.
  if backend == "aiur" then
    p.printError "error: the Aiur model packer was removed; run the measured scan on the .ixe instead"
    return 1

  -- Precedence: explicit --shards (fixed count) > explicit --max-cycles/--max-ram
  -- (budget) > default (size to detected system RAM).
  match shardsFlag with
  | some n =>
    IO.println s!"Sharding {espPath} into {n} shards (balance ±{balancePct}%)"
    rsShardEspFFI espPath (toString n) (toString balancePct) (toString parallelism)
      outPath
  | none =>
    if maxCycles.isNone && maxRam.isNone then
      IO.println s!"Sharding {espPath} to detected system RAM ({backend} model, balance ±{balancePct}%)"
    else
      IO.println s!"Sharding {espPath} to budget ({backend} model, max-cycles={maxCycles.getD 0}, max-ram={maxRam.getD 0} GiB, balance ±{balancePct}%)"
    rsShardEspCapFFI espPath (toString (maxCycles.getD 0)) (toString (maxRam.getD 0))
      (toString balancePct) (toString parallelism) outPath backend
  if !outPath.isEmpty then
    IO.println s!"[shard] wrote {outPath}"
  return 0

/-- The child side of the scan's process pool: build the same
    toplevel/system/env as the parent, then hand off to the Rust worker
    loop (stdin commands, stdout replies) until EOF. -/
def runShardWorkerCmd (p : Cli.Parsed) : IO UInt32 := do
  let some ixe := (p.flag? "ixe").map (·.as! String) | do
    p.printError "error: shard-worker requires --ixe"
    return 1
  let cutGib := (p.flag? "cut-gib").map (·.as! String) |>.getD "inf"
  let batch := (p.flag? "batch").map (·.as! Nat) |>.getD 128
  let softCap := (p.flag? "soft-cap-gib").map (·.as! String) |>.getD "inf"
  let pieces := (p.flag? "pieces").map (·.as! Nat) |>.getD 16
  let toplevel ← match IxVM.ixVM with
    | .error e => IO.eprintln s!"Toplevel merging failed: {e}"; return 1
    | .ok t => pure t
  let compiled ← match toplevel.compile with
    | .error e => IO.eprintln s!"Compilation failed: {e}"; return 1
    | .ok c => pure c
  let funIdx ← match compiled.getFuncIdx `verify_claim with
    | some i => pure i
    | none => IO.eprintln "error: verify_claim missing"; return 1
  let system := Aiur.AiurSystem.build compiled.bytecode
    Aiur.productionCommitmentParameters Aiur.productionFriParameters
  let envHandle ← match Aiur.EnvHandle.fromIxe ixe with
    | .error e => IO.eprintln s!"EnvHandle.fromIxe {ixe}: {e}"; return 1
    | .ok h => pure h
  match Aiur.AiurSystem.scanWorker system funIdx envHandle cutGib
      (toString batch) softCap (toString pieces)
      (if p.hasFlag "defer-growth" then "2"
       else if p.hasFlag "exec-only" then "1"
       else "0") with
  | .ok () => return 0
  | .error e => IO.eprintln s!"shard-worker: {e}"; return 1

end Ix.Cli.ShardCmd

open Ix.Cli.ShardCmd in
def shardCmd : Cli.Cmd := `[Cli|
  "shard" VIA runShardCmd;
  "Partition an env into shards. A `.ixe` input runs the MEASURED Aiur scan-and-cut (default; no profile pass); a `.ixprof` input runs the profile-driven packer (Zisk)"

  FLAGS:
    "max-ram" : Nat;  "Per-shard host-RAM budget, GiB (scan default 250; .ixprof default: detected system RAM)"
    backend   : String; "Planner: aiur (default on `.ixe`: measured scan) or zisk (`.ixe`: profile pass + guest-cost pack in one command; `.ixprof`: pack directly)."
    out       : String; "Output .ixes manifest path (default: input basename + .ixes)"
    eps       : Nat;  "Scan only: pre-charged cut headroom, percent (default 2): covers the batched claim readout's measured drift (~1%) plus merge-sum conservatism"
    workers   : Nat;  "Scan only: parallel chunk scanners (default 0 = autoscale to cores and detected RAM). Each holds one segment's query record and faulted witness, so workers × segment footprint must fit the box"
    "fail-fast";      "Scan: halt on the first kernel-rejected block (the default; flag accepted for explicitness)."
    "no-fail-fast";   "Scan: skip kernel-rejected blocks (named as skipped, excluded from the partition, listed in <out>.failed.csv). The manifest then does not cover them — the downstream coverage gate reports exactly which."
    "reprice"; "Scan: cold re-price — pack past the cut on summed costs, then measure each merged shard's true cost with one cold CheckEnv execution (splits over-cut shards). Opt-in; validate per env by proving the heaviest re-priced shard before adopting its manifest."
    "defer-infeasible"; "Scan: name deferred dense regions (opening cone exceeds a fleet slot) resource-infeasible instead of walking them under fat caps, and resolve the whole exclusion inventory to Lean names in <out>.failed-names.txt. Implies --no-fail-fast. The partition covers only tractable content; failed.csv + failed-names.txt carry the exact boundary."
    json        : String; "Scan only: benchmark results JSON accumulator — append an `execute-time`/`peak-rss` row (the scan wall is a whole-env execution wall). Used by `ix bench run --backend aiur` for the whole-env execute row."
    "json-name" : String; "Row name for --json (default: scan)."
    shards       : Nat;    ".ixprof only: fixed number of shards N (overrides the budget sizing)"
    "max-cycles" : Nat;    ".ixprof only: per-shard guest-cycle budget (overrides the RAM sizing)"
    balance      : Nat;    ".ixprof only: per-bisection balance tolerance, percent (default 5)"
    parallelism  : Nat;    ".ixprof only: provers assumed for the prove-time estimate (default 1 = sequential)"

  ARGS:
    path : String; "A serialized `.ixe` env (measured scan) or a `.ixprof` from `ix profile` (profile packer)"

  SUBCOMMANDS:
    shardExtractCmd
]

open Ix.Cli.ShardCmd in
def shardWorkerCmd : Cli.Cmd := `[Cli|
  "shard-worker" VIA runShardWorkerCmd;
  "INTERNAL: scan-worker child for the shard scanner's process pool — spawned automatically under a cgroup memory cap; not for direct use"

  FLAGS:
    ixe            : String; "Path to the `.ixe` env (same file as the parent scan)"
    "cut-gib"      : String; "Segment cut, GiB of predicted prove RSS (decimal string)"
    batch          : Nat;    "Blocks per measurement claim"
    "soft-cap-gib" : String; "Graceful record ceiling, GiB — segments cut here so only mid-claim growth reaches the cgroup kill"
    pieces         : Nat;    "Schedule piece count (must match the parent's chunking)"
    "exec-only";             "Execute-only mode: record-bytes cut, no prove model"
    "defer-growth";          "Execute-only phase 1: hand dense range remainders back (DEFER) when measured record growth per block crosses the phase threshold; implies --exec-only"
]

end
