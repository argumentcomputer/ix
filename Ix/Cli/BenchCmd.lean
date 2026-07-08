/-
  `ix bench run`: the benchmark cell orchestrator — one command that
  reproduces a CI benchmark cell locally, byte-for-byte on the same tools.

  A cell is (backend, env, mode). The orchestrator:

  1. selects constant names from `Benchmarks/Vectors.csv` (filters ported
     from the `!benchmark` manifest: env, tier, primary subset, shard flag);
  2. ensures the env's `.ixe` exists (`ix compile`, reused when present and
     `--reuse-ixe` is set — except for the `compile` backend, where the
     compile IS the benchmark);
  3. spawns the cell's measured tool — `bench-typecheck` (aiur),
     `zisk-host`/`sp1-host` (zkVM execute), `ix check-rs` (ooc),
     `ix compile` (compile) — with the full name list, wrapped in the RAM
     watchdog (`watchdog.sh`, TERM → grace → KILL);
  4. on an abnormal exit, marks the in-flight constant's row `status: oom`
     (preserving any partial metrics the tool flushed) and respawns with the
     remaining names — one constant's death costs one constant;
  5. gates the cell on the row contract (`Ix.Benchmark.Results`): exit 3
     when any row is `rejected`, exit 1 when NO rows were produced, else 0.

  Every tool self-reports through the same `--json` results-rows contract,
  so there is no output scraping anywhere: state flows through rows and
  exit codes only. Registry data (env slugs/modules, backend modes,
  testbeds) comes from `Benchmarks/bench-config.json`.

  Note for the zisk backend: ZisK's ASM microservices need an unlimited
  memlock hard limit (mmap with MAP_LOCKED). Raise it in the invoking shell
  before running (`sudo prlimit --pid $$ --memlock=unlimited:unlimited`);
  the tools inherit it.
-/
module
public import Cli
public import Lean.Data.Json
public import Ix.Benchmark.Results
public import Ix.Cli.ConstsFile

public section

open System (FilePath)
open Ix.Benchmark.Results

namespace Ix.Cli.BenchCmd

/-- One `Vectors.csv` row (comments/header dropped). `shardTarget` and
    `primary` default to false when the trailing columns are omitted. -/
structure VectorRow where
  name : String
  env : String
  tier : String
  shardTarget : Bool
  primary : Bool

def parseVectorsCsv (contents : String) : Array VectorRow :=
  (contents.splitOn "\n").filterMap (fun line =>
    let s := ((line.splitOn "#").head?.getD "").trimAscii.toString
    if s.isEmpty then none else
    let cols := (s.splitOn ",").map (·.trimAscii.toString)
    match cols with
    | name :: env :: tier :: rest =>
      if name == "name" || name.isEmpty then none
      else some {
        name, env, tier
        shardTarget := rest.head?.getD "0" == "1"
        primary := (rest.drop 1).head?.getD "0" == "1"
      }
    | _ => none) |>.toArray

/-- Manifest selection, mirroring the `!benchmark` config surface: the env's
    rows, restricted to the primary subset unless `full`, to `tier` when
    given (prove-mode full runs default to `cheap` — the prove-feasible
    set), and to shard targets under `shardOnly`. -/
def selectNames (rows : Array VectorRow) (env : String) (mode : String)
    (full : Bool) (tier : String) (shardOnly : Bool) :
    Array VectorRow := Id.run do
  let effTier :=
    if tier != "" then tier
    else if mode == "prove" && full then "cheap" else "all"
  rows.filter fun r =>
    r.env == env
    && (full || r.primary)
    && (effTier == "all" || r.tier == effTier)
    && (!shardOnly || r.shardTarget)

/-- Registry entry for one env from `bench-config.json`. -/
structure EnvInfo where
  key : String
  slug : String
  module : String

def loadConfig (path : String) : IO Lean.Json := do
  match Lean.Json.parse (← IO.FS.readFile path) with
  | .ok j => return j
  | .error e => throw <| IO.userError s!"bench-config {path}: {e}"

def envInfo (cfg : Lean.Json) (env : String) : IO EnvInfo := do
  let some entry := (cfg.getObjVal? "envs" |>.toOption).bind
      (·.getObjVal? env |>.toOption)
    | throw <| IO.userError s!"env '{env}' not in bench-config envs"
  let get (k : String) : IO String := do
    match entry.getObjVal? k with
    | .ok (.str s) => return s
    | _ => throw <| IO.userError s!"env '{env}': missing '{k}' in bench-config"
  return { key := env, slug := ← get "slug", module := ← get "module" }

/-- Resolve a tool binary: prefer the in-tree build under `repo` (so a base
    checkout measures the base's code), else PATH. -/
def resolveBin (repo : String) (name : String) : IO String := do
  let inTree := s!"{repo}/.lake/build/bin/{name}"
  if ← FilePath.pathExists inTree then
    return inTree
  return name

/-- Spawn `cmd args` (inheriting stdio) under the RAM watchdog when one is
    configured, and wait for its exit code. -/
def runGuarded (watchdog : Option String) (ceilingGb : Nat)
    (cmd : String) (args : Array String) (cwd : Option String := none) :
    IO UInt32 := do
  let (cmd, args) := match watchdog with
    | some wd => (wd, #[toString ceilingGb, cmd] ++ args)
    | none => (cmd, args)
  IO.eprintln s!"[bench] run: {cmd} {" ".intercalate args.toList}"
  let child ← IO.Process.spawn {
    cmd, args
    cwd := cwd.map FilePath.mk
  }
  child.wait

/-- Merge `status: oom` into a constant's row, PRESERVING metrics the tool
    flushed before the kill (e.g. bench-typecheck persists Phase-1 fields
    before the prove starts). The compare surface renders OOM only for the
    metrics that are absent. -/
def markOom (out : String) (name : String) : IO Unit := do
  let rows ← readRows out
  let row := (rows.getObjVal? name).toOption.getD (Lean.Json.mkObj [])
  IO.FS.writeFile out
    (rows.setObjVal! name (row.setObjVal! "status" (Lean.Json.str "oom"))
      |>.compress)

/-- Names from `remaining` that have no row in `out` yet. -/
def namesWithoutRows (out : String) (remaining : Array String) :
    IO (Array String) := do
  let rows ← readRows out
  return remaining.filter fun n => (rows.getObjVal? n).toOption.isNone

/-- Run a per-constant tool over `names` with crash isolation: on an
    abnormal exit (watchdog kill, kernel OOM, crash) the in-flight
    constant — the first remaining name without a row — is marked
    `status: oom` and the tool respawns with the rest. One constant's
    death costs one constant; O(failures) respawns, not O(names).

    `spawn` receives the names file to run. Exits the loop on 0 (done) and
    on `exitRejected` (the tool fail-fasts after flushing the rejected row;
    the final gate reddens the cell from the rows). -/
def resumeLoop (out : String) (names : Array String)
    (namesFile : String) (spawn : String → IO UInt32) : IO Unit := do
  let mut remaining := names
  while !remaining.isEmpty do
    IO.FS.writeFile namesFile ("\n".intercalate remaining.toList ++ "\n")
    let exit ← spawn namesFile
    if exit == 0 || exit == exitRejected then
      return
    -- Only a KILLED tool (≥128: the watchdog's TERM/KILL or the kernel OOM
    -- killer) implicates the in-flight constant. Any other failure is
    -- deterministic (usage error, missing input, crash on startup) —
    -- poisoning and respawning would just relabel every remaining constant
    -- as oom, one spawn at a time (e.g. a base-side binary that predates a
    -- flag this side passes).
    if exit < 128 then
      IO.eprintln s!"[bench] tool failed (exit {exit}, not a kill); aborting the remaining {remaining.size} name(s)"
      return
    let missing ← namesWithoutRows out remaining
    match missing[0]? with
    | none =>
      -- Every requested name has a row; the kill landed after the last
      -- row (e.g. teardown) — nothing to resume.
      return
    | some poisoned =>
      IO.eprintln s!"[bench] '{poisoned}' killed (exit {exit}); recording oom and resuming"
      markOom out poisoned
      remaining := missing.filter (· != poisoned)

/-- Ensure the env's `.ixe` exists at `<repo>/<env>.ixe`, compiling it when
    absent (or when reuse is off). Returns the `.ixe` path. -/
def ensureIxe (repo : String) (info : EnvInfo) (reuse : Bool) : IO String := do
  let ixe := s!"{repo}/{info.key}.ixe"
  if reuse && (← FilePath.pathExists ixe) then
    IO.eprintln s!"[bench] reusing {ixe}"
    return ixe
  let ix ← resolveBin repo "ix"
  let exit ← runGuarded none 0 ix
    #["compile", s!"{repo}/{info.module}", "--out", ixe]
  if exit != 0 then
    throw <| IO.userError s!"ix compile {info.module} failed (exit {exit})"
  return ixe

/-- Cut the closure-shard artifacts for one heavy constant: `ix shard
    extract` (standalone closure env) → `ix profile` → `ix shard`
    (heartbeat-profiled min-cut manifest, capped by predicted RAM). Skips
    work when the artifacts already exist. Returns `(ixe, ixes)` on
    success, `none` when any step fails (the caller falls back to the
    single-leaf run — the watchdog then records the honest OOM row). -/
def cutClosureShards (ix : String) (envIxe : String)
    (dir : String) (name : String) (maxRamGb : Nat) :
    IO (Option (String × String)) := do
  let slug := name.map fun c =>
    if c == '/' || c == ' ' || c == '.' || c == ':' then '_' else c
  let subIxe := s!"{dir}/{slug}.ixe"
  let manifest := s!"{dir}/{slug}.ixes"
  if (← FilePath.pathExists subIxe) && (← FilePath.pathExists manifest) then
    return some (subIxe, manifest)
  IO.FS.createDirAll dir
  let prof := s!"{dir}/{slug}.ixprof"
  let steps : List (Array String) :=
    [ #["shard", "extract", envIxe, "--consts", name, "--out", subIxe]
    , #["profile", subIxe, "--out", prof]
    , #["shard", prof, "--max-ram", toString maxRamGb, "--out", manifest] ]
  for args in steps do
    let exit ← runGuarded none 0 ix args
    if exit != 0 then
      IO.eprintln s!"[bench] shard pipeline failed for '{name}' (exit {exit}); falling back to single leaf"
      return none
  return some (subIxe, manifest)

/-- Final cell gate from the rows themselves: exit 3 when any row is
    `rejected` (red cell, rows on disk say why), exit 1 when no rows were
    produced (a silent-empty run must never look green), else 0. -/
def gate (out : String) : IO UInt32 := do
  let rows ← readRows out
  match rows with
  | .obj kvs =>
    let entries := kvs.toArray
    if entries.isEmpty then
      IO.eprintln "[bench] error: no rows were produced"
      return 1
    let rejected := entries.filter fun ⟨_, row⟩ =>
      (row.getObjVal? "status").toOption == some (Lean.Json.str "rejected")
    for ⟨name, _⟩ in rejected do
      IO.eprintln s!"[bench] ❌ '{name}' FAILED TO TYPECHECK — kernel rejected it"
    IO.eprintln s!"[bench] {entries.size} row(s), {rejected.size} rejected"
    return if rejected.isEmpty then 0 else exitRejected
  | _ =>
    IO.eprintln "[bench] error: results file is not an object"
    return 1

/-- Save the run as the local baseline (`.bench/<cell>.json`), rotating the
    previous baseline to `.prev.json` — `ix bench compare` defaults to it,
    so a bare local rerun compares against the last run automatically. -/
def saveBaseline (out : String) (cell : String) : IO Unit := do
  IO.FS.createDirAll ".bench"
  let base := s!".bench/{cell}.json"
  if ← FilePath.pathExists base then
    IO.FS.writeFile s!".bench/{cell}.prev.json" (← IO.FS.readFile base)
  IO.FS.writeFile base (← IO.FS.readFile out)

def runBenchRunCmd (p : Cli.Parsed) : IO UInt32 := do
  let backend := (p.flag? "backend").map (·.as! String) |>.getD ""
  let env := (p.flag? "env").map (·.as! String) |>.getD "initStd"
  let cfg ← loadConfig <| (p.flag? "config").map (·.as! String)
    |>.getD "Benchmarks/bench-config.json"
  let some backendCfg := (cfg.getObjVal? "backends" |>.toOption).bind
      (·.getObjVal? backend |>.toOption)
    | p.printError s!"error: unknown backend '{backend}' (see bench-config.json)"
      return exitUsage
  let defaultMode :=
    match backendCfg.getObjVal? "default_mode" with
    | .ok (.str s) => s
    | _ => "execute"
  let mode := (p.flag? "mode").map (·.as! String) |>.getD defaultMode
  let repo := (p.flag? "repo").map (·.as! String) |>.getD "."
  let out := (p.flag? "out").map (·.as! String) |>.getD "bench.json"
  let full := p.hasFlag "full"
  let tier := (p.flag? "tier").map (·.as! String) |>.getD ""
  let ceilingGb : Nat :=
    match p.flag? "ceiling-gb" with
    | some f => f.as! Nat
    | none =>
      match cfg.getObjVal? "ram_ceiling_gb" with
      | .ok (.num n) => n.mantissa.toNat
      | _ => 120
  let watchdogPath := (p.flag? "watchdog").map (·.as! String)
    |>.getD s!"{repo}/.github/scripts/watchdog.sh"
  let watchdog : Option String ←
    if ← FilePath.pathExists watchdogPath then pure (some watchdogPath)
    else do
      IO.eprintln s!"[bench] warning: no watchdog at {watchdogPath}; running unguarded"
      pure none

  let info ← envInfo cfg env
  let csv := (p.flag? "csv").map (·.as! String)
    |>.getD s!"{repo}/Benchmarks/Vectors.csv"
  let rows := parseVectorsCsv (← IO.FS.readFile csv)
  -- `--names-file` overrides the CSV selection (the caller already knows
  -- exactly which names it wants — e.g. bench-pr's targeted base run over
  -- just the constants bencher lacked); tier metadata still comes from the
  -- CSV so heavy zisk names keep their sharded pipeline.
  let selected ← match p.flag? "names-file" with
    | some f => do
      let wanted ← Ix.Cli.ConstsFile.read (f.as! String)
      pure <| wanted.map fun n =>
        (rows.find? (fun r => r.name == n && r.env == env)).getD
          { name := n, env, tier := "cheap", shardTarget := false, primary := false }
    | none =>
      pure <| selectNames rows env mode full tier (p.hasFlag "shard-only")
  let names := selected.map (·.name)
  IO.eprintln s!"[bench] cell {backend}-{env}-{mode}: {names.size} constant(s)"

  -- Fresh accumulator per run.
  if ← FilePath.pathExists out then IO.FS.removeFile out
  let namesFile := out ++ ".names.txt"

  match backend with
  | "compile" =>
    -- The compile IS the benchmark: always fresh, row keyed by the env slug.
    let ix ← resolveBin repo "ix"
    let exit ← runGuarded watchdog ceilingGb ix
      #["compile", s!"{repo}/{info.module}", "--out", s!"{repo}/{env}.ixe",
        "--json", out, "--json-name", info.slug]
    if exit != 0 then
      IO.eprintln s!"[bench] ix compile failed (exit {exit})"
      return 1
  | "ooc" =>
    let ixe ← ensureIxe repo info (p.hasFlag "reuse-ixe")
    let ix ← resolveBin repo "ix"
    -- Whole-env row (keyed by the env slug) …
    let exit ← runGuarded watchdog ceilingGb ix
      #["check-rs", ixe, "--anon", "--json", out, "--json-name", info.slug]
    if exit != 0 && exit != exitRejected then
      IO.eprintln s!"[bench] whole-env check failed (exit {exit})"
    -- … plus one full-closure row per primary, env loaded once.
    if !names.isEmpty then
      resumeLoop out names namesFile fun nf =>
        runGuarded watchdog ceilingGb ix
          #["check-rs", ixe, "--anon", "--consts-file", nf, "--json", out]
  | "aiur" =>
    let ixe ← ensureIxe repo info (p.hasFlag "reuse-ixe")
    let bt ← resolveBin repo "bench-typecheck"
    let modeArgs := if mode == "execute" then #["--execute-only"] else #[]
    resumeLoop out names namesFile fun nf =>
      runGuarded watchdog ceilingGb bt
        (#["--ixe", ixe, "--consts-file", nf, "--json", out, "--texray"]
          ++ modeArgs)
  | "zisk" | "sp1" =>
    if mode != "execute" then
      p.printError s!"error: {backend} supports only execute mode"
      return exitUsage
    let ixe ← ensureIxe repo info (p.hasFlag "reuse-ixe")
    let ixeAbs := (← IO.FS.realPath ixe).toString
    let outAbs ← do
      IO.FS.writeFile out ""  -- realPath needs an existing file
      pure (← IO.FS.realPath out).toString
    let host := s!"{backend}-host"
    let work := s!"{repo}/{backend}"
    let build ← runGuarded none 0 "cargo"
      #["build", "--quiet", "--release", "--bin", host] (cwd := some work)
    if build != 0 then
      IO.eprintln s!"[bench] cargo build {host} failed (exit {build})"
      return 1
    let bin := (← IO.FS.realPath s!"{work}/target/release/{host}").toString
    -- Heavy-tier zisk constants run as their closure-shard partition (a
    -- single full-closure leaf would blow the runner's RAM); everything
    -- else goes through the host's own per-constant loop.
    let heavy := if backend == "zisk"
      then (selected.filter (·.tier == "heavy")).map (·.name) else #[]
    let light := names.filter (!heavy.contains ·)
    if !light.isEmpty then
      resumeLoop outAbs light namesFile fun nf => do
        let nfAbs := (← IO.FS.realPath nf).toString
        runGuarded watchdog ceilingGb bin
          #["--execute", "--ixe", ixeAbs, "--consts-file", nfAbs,
            "--json", outAbs, "--texray"] (cwd := some work)
    let ix ← resolveBin repo "ix"
    for name in heavy do
      let plan ← cutClosureShards ix ixe s!"{repo}/zkshards-{env}"
        name ceilingGb
      let exit ← match plan with
        | some (subIxe, manifest) =>
          runGuarded watchdog ceilingGb bin
            #["--execute", "--ixe", (← IO.FS.realPath subIxe).toString,
              "--shard-plan", (← IO.FS.realPath manifest).toString,
              "--json", outAbs, "--json-name", name, "--texray"]
            (cwd := some work)
        | none =>
          runGuarded watchdog ceilingGb bin
            #["--execute", "--ixe", ixeAbs, "--consts", name,
              "--json", outAbs, "--texray"] (cwd := some work)
      if exit != 0 && exit != exitRejected then
        IO.eprintln s!"[bench] heavy '{name}' died (exit {exit}); recording oom"
        markOom outAbs name
  | other =>
    p.printError s!"error: backend '{other}' has no runner"
    return exitUsage

  let code ← gate out
  if code == 0 || code == exitRejected then
    saveBaseline out s!"{backend}-{env}-{mode}"
  return code

/-- `ix bench shard`: pre-cut the closure-shard artifacts for the env's
    heavy-tier constants into `zkshards-<env>/` — `ix shard extract` →
    `ix profile` → `ix shard` per name, skipping names whose artifacts
    already exist. Not a benchmark cell (no rows, no watchdog): bench-main's
    compile job runs it next to the fresh `.ixe` so the artifacts ride the
    same cache; the zisk cells cut lazily as a fallback when they're
    absent. -/
def runBenchShardCmd (p : Cli.Parsed) : IO UInt32 := do
  let env := (p.flag? "env").map (·.as! String) |>.getD "initStd"
  let cfg ← loadConfig <| (p.flag? "config").map (·.as! String)
    |>.getD "Benchmarks/bench-config.json"
  let repo := (p.flag? "repo").map (·.as! String) |>.getD "."
  let ceilingGb : Nat :=
    match p.flag? "ceiling-gb" with
    | some f => f.as! Nat
    | none =>
      match cfg.getObjVal? "ram_ceiling_gb" with
      | .ok (.num n) => n.mantissa.toNat
      | _ => 120
  let info ← envInfo cfg env
  let csv := (p.flag? "csv").map (·.as! String)
    |>.getD s!"{repo}/Benchmarks/Vectors.csv"
  let rows := parseVectorsCsv (← IO.FS.readFile csv)
  let heavy := (rows.filter fun r =>
    r.env == env && r.primary && r.tier == "heavy").map (·.name)
  IO.eprintln s!"[bench] shard {env}: {heavy.size} heavy constant(s)"
  let ixe ← ensureIxe repo info (p.hasFlag "reuse-ixe")
  let ix ← resolveBin repo "ix"
  for name in heavy do
    let _ ← cutClosureShards ix ixe s!"{repo}/zkshards-{env}" name ceilingGb
  return 0

end Ix.Cli.BenchCmd

open Ix.Cli.BenchCmd in
def benchRunCmd : Cli.Cmd := `[Cli|
  "run" VIA runBenchRunCmd;
  "Run one benchmark cell (backend × env × mode), writing benchmark results JSON. Exits 0 on success (rows saved as the local baseline), 3 when the kernel rejected any constant, 1 when no rows were produced."

  FLAGS:
    backend      : String; "aiur | zisk | sp1 | ooc | compile"
    env          : String; "Benchmark env from bench-config.json (default: initStd)"
    mode         : String; "prove | execute | compile (default: the backend's default_mode)"
    out          : String; "Benchmark results JSON output path (default: bench.json)"
    repo         : String; "Checkout to benchmark: tools resolve from <repo>/.lake/build/bin first, then PATH (default: .)"
    config       : String; "Registry path (default: Benchmarks/bench-config.json)"
    csv          : String; "Vectors path (default: <repo>/Benchmarks/Vectors.csv)"
    full;                  "Run the env's full curated set instead of the primary subset"
    "names-file" : String; "Run exactly these names (one per line) instead of the Vectors.csv selection"
    tier         : String; "cheap | heavy | all — tier filter (default: all; prove-mode --full defaults to cheap)"
    "shard-only";          "Restrict to shard_target rows"
    "reuse-ixe";           "Reuse an existing <env>.ixe instead of recompiling (ignored by the compile backend)"
    "ceiling-gb" : Nat;    "RAM watchdog ceiling in GB (default: bench-config ram_ceiling_gb)"
    watchdog     : String; "Watchdog wrapper path (default: <repo>/.github/scripts/watchdog.sh; missing = run unguarded)"
]

open Ix.Cli.BenchCmd in
def benchShardCmd : Cli.Cmd := `[Cli|
  "shard" VIA runBenchShardCmd;
  "Pre-cut closure-shard artifacts (ix shard extract → profile → shard) for the env's heavy-tier constants into zkshards-<env>/; skips names already cut. The zisk cells cut lazily when these are absent — this front-loads the work so the artifacts can be cached once per commit."

  FLAGS:
    env          : String; "Benchmark env from bench-config.json (default: initStd)"
    repo         : String; "Checkout to shard: tools resolve from <repo>/.lake/build/bin first, then PATH (default: .)"
    config       : String; "Registry path (default: Benchmarks/bench-config.json)"
    csv          : String; "Vectors path (default: <repo>/Benchmarks/Vectors.csv)"
    "reuse-ixe";           "Reuse an existing <env>.ixe instead of recompiling"
    "ceiling-gb" : Nat;    "Predicted-RAM cap per shard, passed to `ix shard --max-ram` (default: bench-config ram_ceiling_gb)"
]

