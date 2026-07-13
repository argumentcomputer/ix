/-
  `ix bench run`: the benchmark cell orchestrator — one command that
  reproduces a CI benchmark cell locally, byte-for-byte on the same tools.

  A cell is (backend, env, mode). The orchestrator:

  1. selects constant names from `Benchmarks/Vectors.csv` (filters ported
     from the `!benchmark` manifest: env, tier, primary subset, shard flag);
  2. resolves the env's `.ixe` (an explicit `--ixe` path, else `ix
     compile` — except for the `compile` backend, where the compile IS
     the benchmark);
  3. spawns the cell's measured tool — `bench-typecheck` (aiur),
     `zisk-host`/`sp1-host` (zkVM execute), `ix check-rs` (ooc),
     `ix compile` (compile) — wrapped in the RAM watchdog (`watchdog.sh`:
     cgroup `memory.max` via a systemd user scope; the kernel OOM-kills
     at the ceiling). The per-constant backends (aiur, zkVM) spawn
     ONE PROCESS PER CONSTANT: a kill costs exactly that constant (its row
     is marked `status: oom`, keeping whatever the tool flushed), and each
     spawn's texray window (`<out>.spans`) belongs wholly to it, folded
     into the row as flat `phase-<span>` fields — independent bencher
     measures with no attribution machinery;
  4. gates the cell on the row contract (`Ix.Benchmark.Results`): exit 3
     when any row is `rejected`, exit 1 when NO rows were produced, else 0.

  Every tool self-reports through the same `--json` results-rows contract,
  so there is no output scraping anywhere: state flows through rows and
  exit codes only. Registry data (envs, backends, testbeds) lives in this
  module (`envSpecs`/`backendSpecs`) — one language, one owner.

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
    else if (mode == "prove" || mode == "recursive") && full then "cheap"
    else "all"
  rows.filter fun r =>
    r.env == env
    && (full || r.primary)
    && (effTier == "all" || r.tier == effTier)
    && (!shardOnly || r.shardTarget)

/-! ## The registry — single source of truth for the benchmark pipeline

`Benchmarks/Vectors.csv` holds the per-constant rows; everything else lives
here, in one language with one owner. The workflows never read it directly:
`ix bench ci matrix` serves the job matrices and `ix bench ci parse` the
`!benchmark` cells, both post-build. (`bencher-thresholds-reset.yml` keeps
a static workload list with a sync note — it runs on cheap runners with no
built `ix`.) -/

/-- One benchmark env. `name` (e.g. `InitStd`) is the single identifier
    everywhere: the `!benchmark` token (matched case-insensitively), the
    `ix bench run --env` value, the `<name>.ixe` filename, the cache-key
    suffix, and the env-keyed bencher benchmark name. -/
structure EnvSpec where
  name : String
  /-- The Lean source `ix compile` builds the env from. -/
  module : String
  /-- In the bench-main matrices (and `!benchmark`'s allowed env set). -/
  benched : Bool

def envSpecs : List EnvSpec := [
  { name := "InitStd", module := "Benchmarks/Compile/CompileInitStd.lean", benched := true },
  { name := "Lean",    module := "Benchmarks/Compile/CompileLean.lean",    benched := false },
  { name := "Mathlib", module := "Benchmarks/Compile/CompileMathlib.lean", benched := true },
  { name := "FLT",     module := "Benchmarks/Compile/CompileFLT.lean",     benched := false }
]

def findEnv (token : String) : Option EnvSpec :=
  envSpecs.find? fun e => e.name.toLower == token.toLower

/-- One benchmark backend. Backends with several modes run one bench-main
    cell per (mode, testbed) entry — shared measure names (`peak-rss`,
    `throughput`) mean that mode's phase, and a `!benchmark` cell of either
    mode finds a cached bencher baseline. -/
structure BackendSpec where
  name : String
  defaultMode : String
  /-- `some reason` ⇒ `parse` skips the backend with the note in the
      config summary. -/
  disabled : Option String := none
  /-- (mode, bencher testbed). -/
  testbeds : List (String × String)
  /-- (mode, compare-table columns), rendered in list order; the head is
      the table's row sort key. Column convention: the mode's headline
      wall-clock time, throughput, peak-rss, then detail (secondary times,
      sizes, deterministic counters). -/
  metrics : List (String × List String)

def backendSpecs : List BackendSpec := [
  -- prove is aiur's default: the real-workload simulation (it measures
  -- Phase 1 — execute-time, fft-cost — inside the same process en route).
  -- execute is the fast Phase-1-only signal. recursive layers the in-circuit
  -- multi-stark verifier on prove: execute it over each fresh proof, then
  -- prove that execution — the recursion cell. It runs under the
  -- recursion-tuned FRI parameters, so even its shared-name metrics
  -- (prove-time, peak-rss) are not comparable to the prove cell's. An
  -- IxVM-scale verifier execute needs >108 GB, beyond the CI ceiling; the
  -- kill lands as a `status: oom` row that bmf drops, which is why no CI
  -- job schedules this testbed.
  { name := "aiur", defaultMode := "prove",
    testbeds := [("prove", "aiur-check-prove-x64-32x"),
                 ("execute", "aiur-check-execute-x64-32x"),
                 ("recursive", "aiur-check-recursive-x64-32x")],
    metrics := [("prove", ["prove-time", "throughput", "peak-rss",
                           "execute-time", "verify-time", "proof-size",
                           "fft-cost"]),
                ("execute", ["execute-time", "throughput", "peak-rss",
                             "fft-cost"]),
                ("recursive", ["recursive-prove-time", "recursive-peak-rss",
                               "recursive-proof-size", "recursive-verify-time",
                               "recursive-execute-time", "recursive-fft-cost",
                               "prove-time", "proof-size"])] },
  -- The aiur-recursive toy (bench-recursive-verifier): fixed tiny
  -- statements (`recursiveConfigs`), proving the in-circuit multi-stark
  -- verifier end-to-end. Env-independent: the cell ignores --env and never
  -- needs an .ixe. Unlike the aiur recursive mode above, the floor
  -- config's outer prove fits a 128 GB host, so CI schedules this testbed.
  { name := "aiur-recursive", defaultMode := "prove",
    testbeds := [("prove", "aiur-recursive-x64-32x")],
    metrics := [("prove", ["recursive-prove-time", "recursive-peak-rss",
                           "recursive-proof-size", "recursive-verify-time",
                           "recursive-execute-time", "recursive-fft-cost",
                           "prove-time", "proof-size", "verify-time",
                           "peak-rss"])] },
  { name := "zisk", defaultMode := "execute",
    testbeds := [("execute", "zisk-check-execute-x64-32x")],
    metrics := [("execute", ["execute-time", "throughput", "peak-rss",
                             "cycles", "constants", "shards"])] },
  { name := "sp1", defaultMode := "execute",
    disabled := some "execute run too slow for per-push CI; re-enable here once trimmed",
    testbeds := [("execute", "sp1-check-execute-x64-32x")],
    metrics := [("execute", ["execute-time", "throughput", "peak-rss",
                             "cycles"])] },
  { name := "ooc", defaultMode := "execute",
    testbeds := [("execute", "ooc-check-x64-32x")],
    metrics := [("execute", ["check-time", "throughput", "peak-rss"])] },
  { name := "compile", defaultMode := "execute",
    testbeds := [("execute", "ix-compile-x64-32x")],
    metrics := [("execute", ["compile-time", "throughput", "peak-rss",
                             "file-size", "constants"])] },
  -- The inverse of compile: decompiles the env's `.ixe` back to Lean
  -- constants (roundtrip-verified). Env-keyed like compile, but a `.ixe`
  -- CONSUMER — it reuses the compile cell's fresh `.ixe` rather than
  -- producing one.
  { name := "decompile", defaultMode := "execute",
    testbeds := [("execute", "ix-decompile-x64-32x")],
    metrics := [("execute", ["decompile-time", "throughput", "peak-rss",
                             "file-size", "constants"])] }
]

def findBackend (name : String) : Option BackendSpec :=
  backendSpecs.find? (·.name == name)

/-- The `recursive` backend's rows: (row name, bench-recursive-verifier
    config args). Fixed configs rather than `Vectors.csv` constants — the
    toy proves the same tiny statements everywhere: `square-q1-b1` is the
    floor config (completes at ~80 GB under Keccak; ~2.6 GB under Blake3)
    and `factorial-q3-b2` the recursion-tuned default. -/
def recursiveConfigs : List (String × Array String) := [
  ("square-q1-b1", #["--trivial", "--queries", "1", "--blowup", "1"]),
  ("factorial-q3-b2", #[])
]

def BackendSpec.testbedFor (b : BackendSpec) (mode : String) : Option String :=
  (b.testbeds.find? (·.1 == mode)).map (·.2)

def BackendSpec.metricsFor (b : BackendSpec) (mode : String) : List String :=
  ((b.metrics.find? (·.1 == mode)).map (·.2)).getD []

/-- Default RAM watchdog ceiling, same rule for all backends: the
    machine's total RAM minus 15 GB (the ~123 GiB CI runner lands at
    ~108 — above Mathlib `ix compile`'s ~100 GB peak, the largest
    legitimate workload). Enforced as cgroup `memory.max` on a systemd
    user scope: the kernel OOM-kills the tool at the ceiling (exit 137);
    the 15 GB stays outside the cap for the OS, runner agent, and page
    cache. `--ceiling-gb` overrides. -/
def defaultCeilingGb : IO Nat := do
  let s ← try IO.FS.readFile "/proc/meminfo" catch _ => pure ""
  let kb := (s.splitOn "\n").findSome? fun l =>
    if l.startsWith "MemTotal:" then
      ((l.splitOn " ").filter (· ≠ "") |>.drop 1).head?.bind (·.toNat?)
    else none
  return match kb with
    | some kb => max 8 (kb / (1024 * 1024) - 15)
    | none => 16

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
  writeEntry out name (row.setObjVal! "status" (Lean.Json.str "oom"))

/-- Sum a texray spans JSONL window (`{"span": s, "seconds": n}` per line)
    by span name. Missing or unparseable content contributes nothing. -/
def readSpans (path : String) : IO (Array (String × Float)) := do
  if !(← FilePath.pathExists path) then return #[]
  let mut acc : Array (String × Float) := #[]
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if let .ok j := Lean.Json.parse line then
      let span := (j.getObjVal? "span").toOption.bind (·.getStr?.toOption)
      let secs := match (j.getObjVal? "seconds").toOption with
        | some (.num n) => some n.toFloat
        | _ => none
      if let (some s, some v) := (span, secs) then
        match acc.findIdx? (·.1 == s) with
        | some i => acc := acc.set! i (s, acc[i]!.2 + v)
        | none => acc := acc.push (s, v)
  return acc

/-- A span name as a bencher-legal measure slug: lowercase alphanumerics
    with every other character folded to `-` (`stark/stage1_commit` →
    `stark-stage1-commit`). Row keys ARE bencher measure slugs — the slug
    is the one identity uploads and `fetch-main` agree on — so they must
    be born slug-shaped. -/
def slugify (s : String) : String :=
  let dashed := s.toList.map fun c => if c.isAlphanum then c.toLower else '-'
  -- Collapse runs so `a__b` and `a_b` can't alias two spellings apart.
  let folded := dashed.foldl (init := []) fun acc c =>
    if c == '-' && acc.head? == some '-' then acc else c :: acc
  String.ofList folded.reverse

/-- Fold a spawn's texray window (`<out>.spans`) into its constant's row as
    flat `phase-<span>` fields — the aiur prover's tracing spans and the
    zkVM hosts' `record_manual` entries alike — then drop the window file.
    The keys pass straight through `bmf` as independent bencher measures
    and come back from `fetch-main` in the same shape. No row (the tool
    died before writing one) → nothing to attach the spans to. -/
def mergeSpans (out : String) (name : String) : IO Unit := do
  let spansPath := out ++ ".spans"
  let spans ← readSpans spansPath
  if !spans.isEmpty then
    let rows ← readRows out
    if let some row := (rows.getObjVal? name).toOption then
      let row := spans.foldl (init := row) fun r (s, v) =>
        r.setObjVal! s!"phase-{slugify s}" (jsonRound 6 v)
      writeEntry out name row
  if ← FilePath.pathExists spansPath then
    IO.FS.removeFile spansPath

/-- Run a per-constant tool: ONE PROCESS PER CONSTANT, so a kill costs
    exactly that constant with no resume inference, and each spawn's texray
    window (`<out>.spans`, truncated by the tool at startup) belongs wholly
    to it. Per exit: ≥128 (watchdog TERM/KILL or the kernel OOM killer) →
    mark the row `oom` (keeping whatever the tool flushed, spans included)
    and continue; `exitRejected` → the rejected row is on disk, continue
    (the final gate reddens the cell); any other nonzero exit is
    deterministic (usage error, missing input, crash on startup) and would
    repeat for every remaining name — abort loudly.

    `doneKey` is the mode's completion metric (e.g. `prove-time`): a kill
    that lands AFTER the row carries it hit teardown, not measurement —
    typically the prover releasing tens of GB right after the final row
    write, while RSS is still at its peak — so the finished row stays ok. -/
def runPerConstant (out : String) (names : Array String)
    (doneKey : String) (spawn : String → IO UInt32) : IO Unit := do
  for name in names do
    let exit ← spawn name
    -- 255 is never a signal death (our kills exit 134/137/143) — it's a
    -- failed exec ("could not execute external process") or a tool bailing
    -- with -1; labeling it oom would turn a broken spawn into a green cell
    -- of fake-OOM rows.
    if exit == 255 || (exit != 0 && exit != exitRejected && exit < 128) then
      IO.eprintln s!"[bench] tool failed on '{name}' (exit {exit}, not a kill); aborting the remaining names"
      return
    if exit ≥ 128 then
      let rows ← readRows out
      let complete := ((rows.getObjVal? name).toOption.bind
        fun r => (r.getObjVal? doneKey).toOption).isSome
      if complete then
        IO.eprintln s!"[bench] '{name}' killed in teardown (exit {exit}); row already complete"
      else
        IO.eprintln s!"[bench] '{name}' killed (exit {exit}); recording oom"
        markOom out name
    mergeSpans out name

/-- Resolve the env's `.ixe`: an explicit `--ixe` path is used as-is (and
    must exist — no silent recompile of a mistyped path); otherwise the
    env is compiled fresh to `<repo>/<env>.ixe`. -/
def ensureIxe (repo : String) (info : EnvSpec) (explicit : Option String) :
    IO String := do
  if let some path := explicit then
    if ← FilePath.pathExists path then
      return path
    throw <| IO.userError s!"--ixe {path} not found"
  let ixe := s!"{repo}/{info.name}.ixe"
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

/-- Final cell gate from the rows themselves: exit 1 when any EXPECTED name
    lacks a row (an aborted loop, a killed batch, or a dropped whole-env
    check must never look green — every selected name owes exactly one
    row), exit 3 when any row is `rejected` (red cell, rows on disk say
    why), else 0. -/
def gate (out : String) (expected : Array String) : IO UInt32 := do
  let rows ← readRows out
  match rows with
  | .obj kvs =>
    let entries := kvs.toArray
    let missing := expected.filter fun n =>
      !(entries.any fun ⟨name, _⟩ => name == n)
    for n in missing do
      IO.eprintln s!"[bench] error: no row for '{n}'"
    let rejected := entries.filter fun ⟨_, row⟩ =>
      (row.getObjVal? "status").toOption == some (Lean.Json.str "rejected")
    for ⟨name, _⟩ in rejected do
      IO.eprintln s!"[bench] ❌ '{name}' FAILED TO TYPECHECK — kernel rejected it"
    IO.eprintln s!"[bench] {entries.size} row(s), {missing.size} missing, {rejected.size} rejected"
    if !missing.isEmpty then return 1
    return if rejected.isEmpty then 0 else exitRejected
  | _ =>
    IO.eprintln "[bench] error: results file is not an object"
    return 1

/-- The benchmark output root shared with the `Ix.Benchmark` framework:
    `BENCH_OUTPUT_DIR`, defaulting to `.lake/benches` (see
    `Ix.Benchmark.Common.Config.outputDir`). -/
def benchOutputDir : IO String :=
  return (← IO.getEnv "BENCH_OUTPUT_DIR").getD ".lake/benches"

/-- Save the run as the local baseline (`<benchOutputDir>/<cell>.json`),
    rotating the previous baseline to `.prev.json` — `ix bench compare`
    defaults to the pair, so a bare local rerun compares against the last
    run automatically. -/
def saveBaseline (out : String) (cell : String) : IO Unit := do
  let dir ← benchOutputDir
  IO.FS.createDirAll dir
  let base := s!"{dir}/{cell}.json"
  if ← FilePath.pathExists base then
    IO.FS.writeFile s!"{dir}/{cell}.prev.json" (← IO.FS.readFile base)
  IO.FS.writeFile base (← IO.FS.readFile out)

def runBenchRunCmd (p : Cli.Parsed) : IO UInt32 := do
  let backend := (p.flag? "backend").map (·.as! String) |>.getD ""
  let some spec := findBackend backend
    | p.printError s!"error: unknown backend '{backend}' (see backendSpecs)"
      return exitUsage
  let some info := findEnv ((p.flag? "env").map (·.as! String) |>.getD "InitStd")
    | p.printError "error: unknown env (see envSpecs)"
      return exitUsage
  let env := info.name
  let mode := (p.flag? "mode").map (·.as! String) |>.getD spec.defaultMode
  let repo := (p.flag? "repo").map (·.as! String) |>.getD "."
  let out := (p.flag? "out").map (·.as! String) |>.getD "bench.json"
  let full := p.hasFlag "full"
  let tier := (p.flag? "tier").map (·.as! String) |>.getD ""
  let ceilingGb : Nat ← match p.flag? "ceiling-gb" with
    | some f => pure (f.as! Nat)
    | none => defaultCeilingGb
  let watchdogPath := (p.flag? "watchdog").map (·.as! String)
    |>.getD s!"{repo}/.github/scripts/watchdog.sh"
  -- Absolute: the zkVM hosts spawn with their workspace as cwd, where a
  -- repo-relative script path would fail to exec. No watchdog, no run —
  -- an unenforced ceiling is not a benchmark run.
  let watchdog : Option String ←
    if ← FilePath.pathExists watchdogPath then
      pure (some (← IO.FS.realPath watchdogPath).toString)
    else do
      p.printError s!"error: no watchdog at {watchdogPath} (--watchdog overrides)"
      return exitUsage
  let csv := (p.flag? "csv").map (·.as! String)
    |>.getD s!"{repo}/Benchmarks/Vectors.csv"
  let rows := parseVectorsCsv (← IO.FS.readFile csv)
  -- `--consts` overrides the CSV selection — a one-off local run, or
  -- bench-pr's targeted base run over just the constants bencher lacked;
  -- tier metadata still comes from the CSV so heavy zisk names keep
  -- their sharded pipeline.
  let wanted := ((p.flag? "consts").map
    (fun f => Ix.Cli.ConstsFile.parseCommaList (f.as! String))).getD #[]
  let selected :=
    if wanted.isEmpty then
      selectNames rows env mode full tier (p.hasFlag "shard-only")
    else
      wanted.map fun n =>
        (rows.find? (fun r => r.name == n && r.env == env)).getD
          { name := n, env, tier := "cheap", shardTarget := false, primary := false }
  let names := selected.map (·.name)
  match backend with
  | "aiur-recursive" =>
    IO.eprintln s!"[bench] cell {backend}-{mode}: {recursiveConfigs.length} config(s)"
  | _ =>
    IO.eprintln s!"[bench] cell {backend}-{env}-{mode}: {names.size} constant(s)"

  -- Fresh accumulator per run.
  if ← FilePath.pathExists out then IO.FS.removeFile out
  let namesFile := out ++ ".names.txt"

  match backend with
  | "compile" =>
    -- The compile IS the benchmark: always fresh, row keyed by the env name.
    let ix ← resolveBin repo "ix"
    let exit ← runGuarded watchdog ceilingGb ix
      #["compile", s!"{repo}/{info.module}", "--out", s!"{repo}/{env}.ixe",
        "--json", out, "--json-name", info.name]
    if exit != 0 then
      IO.eprintln s!"[bench] ix compile failed (exit {exit})"
      return 1
  | "decompile" =>
    -- The inverse of compile: consume the env's `.ixe` (the compile cell's
    -- fresh artifact) and decompile it back to Lean constants. Env-keyed row,
    -- like compile. A malformed decompile exits nonzero and reddens the cell;
    -- deep roundtrip fidelity is gated by the canonical roundtrip checks
    -- (`ix validate` / the roundtrip tests), not measured here.
    let ixe ← ensureIxe repo info ((p.flag? "ixe").map (·.as! String))
    let ix ← resolveBin repo "ix"
    let exit ← runGuarded watchdog ceilingGb ix
      #["decompile", ixe, "--json", out, "--json-name", info.name]
    if exit != 0 then
      IO.eprintln s!"[bench] ix decompile failed (exit {exit})"
  | "ooc" =>
    let ixe ← ensureIxe repo info ((p.flag? "ixe").map (·.as! String))
    let ix ← resolveBin repo "ix"
    -- Whole-env row (keyed by the env name) …
    let exit ← runGuarded watchdog ceilingGb ix
      #["check-rs", ixe, "--anon", "--json", out, "--json-name", info.name]
    if exit != 0 && exit != exitRejected then
      IO.eprintln s!"[bench] whole-env check failed (exit {exit})"
    -- … plus one full-closure row per primary. ONE process for all names
    -- (unlike the per-constant backends below): the check-rs rows mode
    -- attributes per name internally with the env loaded once — a
    -- per-constant process would re-pay the multi-minute Mathlib env parse
    -- per name — and out-of-circuit checks don't approach the RAM ceiling.
    if !names.isEmpty then
      IO.FS.writeFile namesFile ("\n".intercalate names.toList ++ "\n")
      let exit ← runGuarded watchdog ceilingGb ix
        #["check-rs", ixe, "--anon", "--consts-file", namesFile, "--json", out]
      if exit != 0 && exit != exitRejected then
        IO.eprintln s!"[bench] per-constant checks failed (exit {exit})"
  | "aiur" =>
    let ixe ← ensureIxe repo info ((p.flag? "ixe").map (·.as! String))
    let bt ← resolveBin repo "bench-typecheck"
    let modeArgs := match mode with
      | "execute" => #["--execute-only"]
      | "recursive" => #["--recursive"]
      | _ => #[]
    let doneKey := match mode with
      | "execute" => "execute-time"
      | "recursive" => "recursive-prove-time"
      | _ => "prove-time"
    runPerConstant out names doneKey fun name =>
      runGuarded watchdog ceilingGb bt
        (#["--ixe", ixe, "--consts", name, "--json", out, "--texray"]
          ++ modeArgs)
  | "aiur-recursive" =>
    -- Fixed-config rows; no env, no .ixe. One process per config under the
    -- watchdog, self-reporting through the rows contract like every other
    -- per-row backend.
    let brv ← resolveBin repo "bench-recursive-verifier"
    runPerConstant out (recursiveConfigs.map (·.1)).toArray "recursive-prove-time"
      fun name =>
        let cfgArgs := ((recursiveConfigs.find? (·.1 == name)).map (·.2)).getD #[]
        runGuarded watchdog ceilingGb brv
          (cfgArgs ++ #["--json", out, "--json-name", name, "--texray"])
  | "zisk" | "sp1" =>
    if mode != "execute" then
      p.printError s!"error: {backend} supports only execute mode"
      return exitUsage
    let ixe ← ensureIxe repo info ((p.flag? "ixe").map (·.as! String))
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
    -- else runs as one host process per constant like the aiur cells.
    let heavy := if backend == "zisk"
      then (selected.filter (·.tier == "heavy")).map (·.name) else #[]
    let light := names.filter (!heavy.contains ·)
    runPerConstant outAbs light "execute-time" fun name =>
      runGuarded watchdog ceilingGb bin
        #["--execute", "--ixe", ixeAbs, "--consts", name,
          "--json", outAbs, "--texray"] (cwd := some work)
    let ix ← resolveBin repo "ix"
    runPerConstant outAbs heavy "execute-time" fun name => do
      let plan ← cutClosureShards ix ixe s!"{repo}/zkshards-{env}"
        name ceilingGb
      match plan with
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
  | other =>
    p.printError s!"error: backend '{other}' has no runner"
    return exitUsage

  -- Every selected name owes a row; the env-keyed backends owe the env
  -- row too.
  let expected := match backend with
    | "compile" => #[info.name]
    | "decompile" => #[info.name]
    | "ooc" => #[info.name] ++ names
    | "aiur-recursive" => (recursiveConfigs.map (·.1)).toArray
    | _ => names
  let code ← gate out expected
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
  let some info := findEnv ((p.flag? "env").map (·.as! String) |>.getD "InitStd")
    | p.printError "error: unknown env (see envSpecs)"
      return exitUsage
  let env := info.name
  let repo := (p.flag? "repo").map (·.as! String) |>.getD "."
  let ceilingGb : Nat ← match p.flag? "ceiling-gb" with
    | some f => pure (f.as! Nat)
    | none => defaultCeilingGb
  let csv := (p.flag? "csv").map (·.as! String)
    |>.getD s!"{repo}/Benchmarks/Vectors.csv"
  let rows := parseVectorsCsv (← IO.FS.readFile csv)
  let heavy := (rows.filter fun r =>
    r.env == env && r.primary && r.tier == "heavy").map (·.name)
  IO.eprintln s!"[bench] shard {env}: {heavy.size} heavy constant(s)"
  let ixe ← ensureIxe repo info ((p.flag? "ixe").map (·.as! String))
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
    backend      : String; "aiur | zisk | sp1 | ooc | compile | decompile | aiur-recursive"
    env          : String; "Benchmark env from the registry (default: InitStd)"
    mode         : String; "prove | execute | recursive (default: the backend's defaultMode)"
    out          : String; "Benchmark results JSON output path (default: bench.json)"
    repo         : String; "Checkout to benchmark: tools resolve from <repo>/.lake/build/bin first, then PATH (default: .)"
    csv          : String; "Vectors path (default: <repo>/Benchmarks/Vectors.csv)"
    full;                  "Run the env's full curated set instead of the primary subset"
    consts       : String; "Run exactly these comma-separated names instead of the Vectors.csv selection (same grammar as the tools' --consts)"
    tier         : String; "cheap | heavy | all — tier filter (default: all; prove-mode --full defaults to cheap)"
    "shard-only";          "Restrict to shard_target rows"
    ixe          : String; "Path to an existing .ixe env to use (default: compile <env> fresh; ignored by the compile backend)"
    "ceiling-gb" : Nat;    "RAM watchdog ceiling in GB (default: machine RAM minus 15 GB)"
    watchdog     : String; "Watchdog wrapper path (default: <repo>/.github/scripts/watchdog.sh; missing = run unguarded)"
]

open Ix.Cli.BenchCmd in
def benchShardCmd : Cli.Cmd := `[Cli|
  "shard" VIA runBenchShardCmd;
  "Pre-cut closure-shard artifacts (ix shard extract → profile → shard) for the env's heavy-tier constants into zkshards-<env>/; skips names already cut. The zisk cells cut lazily when these are absent — this front-loads the work so the artifacts can be cached once per commit."

  FLAGS:
    env          : String; "Benchmark env from the registry (default: InitStd)"
    repo         : String; "Checkout to shard: tools resolve from <repo>/.lake/build/bin first, then PATH (default: .)"
    csv          : String; "Vectors path (default: <repo>/Benchmarks/Vectors.csv)"
    ixe          : String; "Path to an existing .ixe env to use (default: compile <env> fresh)"
    "ceiling-gb" : Nat;    "Predicted-RAM cap per shard, passed to `ix shard --max-ram` (default: machine RAM minus 15 GB)"
]

