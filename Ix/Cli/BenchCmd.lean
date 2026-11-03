module
public import Cli
public import Lean.Data.Json
public import Ix.BenchConstants
public import Ix.Benchmark.Results
public import Ix.Cli.ConstsFile
public import Ix.Watchdog

/-!
  `ix bench run`: the benchmark orchestrator — one command that
  reproduces a CI benchmark run locally, byte-for-byte on the same tools.

  A run executes one parameter combination: (backend, env, mode). The
  orchestrator:

  1. selects the env's constants from the shared set
     (`Ix.BenchConstants`), minus the `(backend, mode)` exclusions;
  2. resolves the env's `.ixe` (an explicit `--ixe` path, else `ix
     compile` — except for the `compile` backend, where the compile IS
     the benchmark);
  3. spawns the run's measured tool — `ix check-lean` (ooc),
     `ix compile` (compile), `ix decompile` (decompile) — wrapped in the
     RAM watchdog (`Ix.Watchdog`: cgroup `memory.max` via a systemd user
     scope; the kernel OOM-kills at the ceiling);
  4. gates the run on the row contract (`Ix.Benchmark.Results`): exit 3
     when any row is `rejected`, exit 1 when NO rows were produced, else 0.

  Every tool self-reports through the same `--json` results-rows contract,
  so there is no output scraping anywhere: state flows through rows and
  exit codes only. Registry data (envs, backends, testbeds) lives in this
  module (`envSpecs`/`backendSpecs`) — one language, one owner.

-/

public section

open System (FilePath)
open Ix.Benchmark.Results
open Ix.BenchConstants

namespace Ix.Cli.BenchCmd

/-- Per-constant benchmark exclusions: `(name, backend, mode)` a constant
    must NOT run for, `"*"` wildcarding a dimension. Applied on top of the
    shared `benchConstants` set, for the constants that are hard-infeasible
    in a cell — not merely expensive (a too-large prove records an honest
    `oom` row instead). `--consts` runs bypass this: an explicit request
    always runs. -/
def benchExclusions : List (String × String × String) := []

/-- Whether `benchExclusions` bars `name` from this `(backend, mode)`. -/
def isExcluded (name backend mode : String) : Bool :=
  benchExclusions.any fun (n, b, m) =>
    n == name && (b == "*" || b == backend) && (m == "*" || m == mode)

/-- The env's slice of the shared `benchConstants` set, minus the
    `(backend, mode)` exclusions — the one selection every per-constant
    backend runs. -/
def selectNames (env : String) (backend : String) (mode : String) :
    Array BenchConstant :=
  benchConstants.filter fun c =>
    c.env == env && !isExcluded c.name backend mode

/-! ## The registry — single source of truth for the benchmark pipeline

`Ix.BenchConstants` holds the shared constant set; everything else lives
here, in one language with one owner. The workflows never read it directly:
`ix bench ci matrix` serves the job matrices and `ix bench ci parse` the
`!benchmark` runs, both post-build. (`bencher-thresholds-reset.yml` keeps
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

def envSpecs : List EnvSpec := [
  { name := "InitStd", module := "Benchmarks/Compile/CompileInitStd.lean" },
  { name := "Lean",    module := "Benchmarks/Compile/CompileLean.lean" },
  -- Init+Std+Lean+Batteries as ONE env (the union deduplicates — Lean
  -- already carries Init and Std).
  { name := "ISLB",    module := "Benchmarks/Compile/CompileISLB.lean" },
  { name := "Mathlib", module := "Benchmarks/Compile/CompileMathlib.lean" },
  { name := "FLT",     module := "Benchmarks/Compile/CompileFLT.lean" },
  { name := "AnthropicFLT",
    module := "Benchmarks/Compile/CompileAnthropicFLT.lean" }
]

def findEnv (token : String) : Option EnvSpec :=
  envSpecs.find? fun e => e.name.toLower == token.toLower

/-- How a backend enumerates the inputs its runs measure over — the single
    registry declaration every consumer (plot specs, CI job matrices, the
    `.ixe` cache gate) reads, so none special-cases a backend by name.
      · `perEnv` — one row per compiled env, keyed by the env name itself; runs
        over EVERY compiled env. The env-keyed compile/decompile pair: a `.ixe`
        producer and its consumer, both measuring the whole env.
      · `perConstant` — one row per selected `benchConstants` entry, over
        the envs whose entries select any — an env joins this fan-out by
        gaining constants, not by a registry flag.
      · `perConstantWithEnv` — `perConstant` plus a whole-env row (ooc). -/
inductive BenchInputs
  | perEnv
  | perConstant
  | perConstantWithEnv
  deriving BEq

/-- EC2 instance types with separate benchmark histories. -/
def benchmarkMachines : List String := ["r8i.8xlarge"]

def benchmarkMachine : IO String := do
  let machine := (← IO.getEnv "IX_BENCH_MACHINE").getD "r8i.8xlarge"
  unless benchmarkMachines.contains machine do
    throw <| IO.userError s!"unsupported IX_BENCH_MACHINE: {machine}"
  return machine

/-- Hardware and code generation both determine whether timings are comparable. -/
def testbedSuffix (machine : String) : String :=
  s!"-runs-on-{machine.replace "." "-"}-native"

/-- A testbed minus its hardware suffix — the workload key the threshold
    reset anchors (`refs/bencher/<workload>`), the dashboard plot titles,
    and the run metadata are written against. -/
def workloadOf (testbed : String) : String :=
  match (benchmarkMachines.map testbedSuffix).find? (testbed.endsWith ·) with
  | some suffix => (testbed.dropEnd suffix.length).toString
  | none => testbed

def testbedOnMachine (testbed machine : String) : String :=
  workloadOf testbed ++ testbedSuffix machine

/-- The stage qualifiers a pipeline measure may carry ahead of its base
    name — one per pipeline stage, named for what the stage proves
    (`ixvm-`: the IxVM typecheck; `fri-verifier-`: the in-circuit FRI
    verifier over the previous proof; `join-`: the optional pair-wide
    aggregate join; the KZG stages add their own entries as they land) —
    plus `pipeline-` for the whole run. Stripped
    wherever a measure is interpreted by its base name (formatting kind,
    units) or labelled under a heading that already says the stage. -/
def stagePrefixes : List String :=
  ["ixvm-", "fri-verifier-", "join-", "pipeline-"]

/-- The stage qualifier `metric` carries, if any. -/
def stagePrefixOf (metric : String) : Option String :=
  stagePrefixes.find? (metric.startsWith ·)

/-- `metric` with its stage qualifier removed, if it has one. -/
def dropStagePrefix (metric : String) : String :=
  match stagePrefixOf metric with
  | some p => (metric.drop p.length).toString
  | none => metric

/-- One benchmark backend. Backends with several modes schedule one bench-main
    matrix entry per (mode, testbed); each mode's measures live on its own
    testbed. -/
structure BackendSpec where
  name : String
  defaultMode : String
  /-- The inputs (envs and row names) this backend's runs fan over. -/
  inputs : BenchInputs
  /-- For a `perEnv` backend: restrict the fan-out to these registry env
      names instead of every compiled env (`none` = all). Ignored for
      the per-constant backends, whose env set comes from `Vectors.csv`
      row selection. -/
  envs : Option (List String) := none
  /-- `some reason` ⇒ `parse` skips the backend with the note in the
      config summary. -/
  disabled : Option String := none
  /-- Modes present for local / on-demand runs only (`ix bench run --mode`,
      an explicit `!benchmark` backend) — scheduled by no CI job, so they
      carry a testbed for the compare surface but never upload to bencher
      and get no dashboard plot. -/
  unscheduled : List String := []
  /-- (mode, bencher testbed stem). Hardware suffixes identify the measured host. -/
  testbeds : List (String × String)
  /-- (mode, compare-table columns), rendered in list order; the head is
      the table's row sort key. Column convention: the mode's headline
      wall-clock time, throughput, peak-rss, then detail (secondary times,
      sizes, deterministic counters). For a mode listed in `stages` the
      columns come from there, and this list instead names measures the
      mode TRACKS without giving them a column — uploaded, thresholded,
      and plotted like any other, just not tabled. -/
  metrics : List (String × List String)
  /-- (mode, [(stage title, that stage's measures)]) for a mode whose run
      walks a multi-stage pipeline: the compare table splits into one
      table per stage. A stage's measures carry their stage
      qualifier (`ixvm-prove-time`) — the stage tables strip it for
      display (`sectionLabelDrop`), so columns still read plain. List
      order is render order, so the closing entry is the ledger over the
      whole run. -/
  stages : List (String × List (String × List String)) := []
  /-- Regression bounds per tracked measure: (measure, upper, lower), each
      bound a percentage over the baseline as a decimal fraction ("0.10"),
      "0" for an exact pin, or "_" for unbounded on that side. Rendered by
      `thresholdFlags` into the bencher-track action's `--threshold-*`
      triples. Shared across the backend's scheduled modes: a threshold
      naming a measure absent from a mode's upload just sits empty on that
      testbed. Bound conventions:
        · deterministic counters (constants) pin exactly (0/0) — a drop
          means lost coverage, not an improvement;
        · deterministic costs that only drop on a real win (cycles, shards,
          fft-cost) take an upper-only bound — flag regressions, let wins
          through;
        · noisy wall-clock / RAM take ~10% upper bounds; throughput's
          regression is a drop, so its bound is the lower side;
        · sizes are structural (fixed layout) and ride tight 1–5% bands.
      The dynamically-named `phase-<span>` measures upload un-thresholded
      (noisy; the PR-comment drill-down does the phase-level compare). -/
  thresholds : List (String × String × String) := []

def backendSpecs : List BackendSpec := [
  { name := "ooc", defaultMode := "execute", inputs := .perConstantWithEnv,
    testbeds := [("execute", "ooc-check")],
    metrics := [("execute", ["check-time", "throughput", "peak-rss"])],
    thresholds := [("constants", "0", "0"), ("check-time", "0.10", "_"),
                   ("throughput", "_", "0.10"), ("peak-rss", "0.10", "_")] },
  -- AnthropicFLT remains on-demand: its from-scratch upstream build needs
  -- substantially more than the per-push workflow's one-hour budget. An
  -- explicit `--env AnthropicFLT` or `BENCH_ENVS=AnthropicFLT` still runs it.
  { name := "compile", defaultMode := "execute", inputs := .perEnv,
    envs := some ["InitStd", "Lean", "ISLB", "Mathlib", "FLT"],
    -- A distinct baseline keeps the cost of certification out of comparisons
    -- against historical Rust compiler timings.
    testbeds := [("execute", "ix-compile-certified")],
    metrics := [("execute", ["compile-time", "throughput", "peak-rss",
                             "file-size", "constants"])],
    -- file-size wiggles slightly run-to-run (the serialized env is not
    -- byte-reproducible — worth its own investigation for a
    -- content-addressed store) → a tight ±1% band instead of a pin.
    thresholds := [("compile-time", "0.05", "_"), ("throughput", "_", "0.05"),
                   ("file-size", "0.01", "0.01"), ("constants", "0", "0"),
                   ("peak-rss", "0.10", "_")] },
  -- The inverse of compile: decompiles the env's `.ixe` back to Lean
  -- constants (roundtrip-verified). Env-keyed like compile, but a `.ixe`
  -- CONSUMER — it reuses the compile run's fresh `.ixe` rather than
  -- producing one.
  { name := "decompile", defaultMode := "execute", inputs := .perEnv,
    -- ISLB is excluded: its content is Lean + Batteries, so a decompile
    -- row would mostly re-measure Lean's.
    envs := some ["InitStd", "Lean", "Mathlib", "FLT"],
    testbeds := [("execute", "ix-decompile")],
    metrics := [("execute", ["decompile-time", "throughput", "peak-rss",
                             "file-size", "constants"])],
    -- file-size (the input `.ixe`) duplicates the compile run's, so it
    -- uploads for the row's completeness but rides no threshold here.
    thresholds := [("constants", "0", "0"), ("decompile-time", "0.10", "_"),
                   ("throughput", "_", "0.10"), ("peak-rss", "0.10", "_")] }
]

def findBackend (name : String) : Option BackendSpec :=
  backendSpecs.find? (·.name == name)

def BackendSpec.testbedFor (b : BackendSpec) (mode : String) : Option String :=
  (b.testbeds.find? (·.1 == mode)).map (·.2)

/-- The pipeline stages this mode's compare table splits into, empty for
    the single-table modes. -/
def BackendSpec.stagesFor (b : BackendSpec) (mode : String) :
    List (String × List String) :=
  ((b.stages.find? (·.1 == mode)).map (·.2)).getD []

/-- Every measure the mode tracks — what the dashboard plots. For an
    unstaged mode that is exactly its `metrics` columns; for a staged one
    it is the stage tables' measures plus any `metrics` entry, which is
    how a measure gets tracked and plotted without taking a column. -/
def BackendSpec.metricsFor (b : BackendSpec) (mode : String) : List String :=
  let extra := ((b.metrics.find? (·.1 == mode)).map (·.2)).getD []
  match b.stagesFor mode with
  | [] => extra
  | stages => ((stages.map (·.2)).flatten ++ extra).eraseDups

/-- `thresholds` rendered as the bencher-track action's `--threshold-*`
    flags, one percentage-test triple per measure. `__WINDOW__` is the
    action's placeholder for the per-workload baseline window (data points
    since the workload's reset anchor); the action word-splits the string,
    so every flag value stays a single token. -/
def BackendSpec.thresholdFlags (b : BackendSpec) : String :=
  "\n".intercalate <| b.thresholds.map fun (m, upper, lower) =>
    s!"--threshold-measure {m} --threshold-test percentage\n" ++
    s!"--threshold-max-sample-size __WINDOW__ --threshold-upper-boundary {upper}\n" ++
    s!"--threshold-lower-boundary {lower}"

/-- The scheduled modes of this backend: its testbed modes minus the
    `unscheduled` (local-only) ones. -/
def BackendSpec.scheduledModes (b : BackendSpec) : List String :=
  b.testbeds.filterMap fun (m, _) =>
    if b.unscheduled.contains m then none else some m

/-- The envs this backend's runs cover, from its `inputs`: `perEnv` covers
    every registry env; the per-constant backends cover the envs where at
    least one constant is selected in ANY scheduled mode — an env joins
    their fan-out by gaining constants, not by a registry flag, and a
    constant excluded from one mode still keeps its env if another
    scheduled mode runs it. -/
def BackendSpec.envNames (b : BackendSpec) : List String :=
  let names := envSpecs.map (·.name)
  match b.inputs with
  | .perEnv => match b.envs with
    | some restricted => names.filter restricted.contains
    | none => names
  | .perConstant | .perConstantWithEnv =>
    names.filter fun env =>
      b.scheduledModes.any fun m =>
        !(selectNames env b.name m).isEmpty

/-- The benchmark row names this backend uploads — the bencher slugs the
    dashboard plots and compare table key on — from its `inputs`: env-keyed
    backends key one row per compiled env; the per-constant backends select
    from `benchConstants` over their env set (`perConstantWithEnv` prepends
    a whole-env row). Dynamic shard sub-rows (`<name>/shard-N`) are
    excluded — the parent row carries the headline trend. -/
def BackendSpec.benchmarkNames (b : BackendSpec) (mode : String) :
    Array String := Id.run do
  match b.inputs with
  | .perEnv => return b.envNames.toArray
  | .perConstant | .perConstantWithEnv =>
    let mut ns : Array String := #[]
    for env in b.envNames do
      if b.inputs == .perConstantWithEnv then ns := ns.push env
      ns := ns ++ (selectNames env b.name mode).map (·.name)
    return ns

/-- Default RAM watchdog ceiling (`--ceiling-gb` overrides): see
    `Ix.Watchdog.defaultCeilingGb`, the one rule for every consumer. -/
def defaultCeilingGb : IO Nat := Ix.Watchdog.defaultCeilingGb

/-- Resolve a tool binary: prefer the in-tree build under `repo` (so a base
    checkout measures the base's code), else PATH. -/
def resolveBin (repo : String) (name : String) : IO String := do
  let inTree := s!"{repo}/.lake/build/bin/{name}"
  if ← FilePath.pathExists inTree then
    return inTree
  return name

/-- Spawn `cmd args` (inheriting stdio) under the RAM watchdog when
    `watchdog` is set (`Ix.Watchdog.run`: cgroup scope, whole-tree kill
    at the ceiling), and wait for its exit code. -/
def runGuarded (watchdog : Bool) (ceilingGb : Nat)
    (cmd : String) (args : Array String) (cwd : Option String := none) :
    IO UInt32 := do
  let guard := if watchdog then s!" (≤{ceilingGb}G)" else ""
  IO.eprintln s!"[bench] run{guard}: {cmd} {" ".intercalate args.toList}"
  if watchdog then
    Ix.Watchdog.run ceilingGb cmd args (cwd.map FilePath.mk)
  else
    let child ← IO.Process.spawn {
      cmd, args
      cwd := cwd.map FilePath.mk
    }
    child.wait

/-- Resolve the env's `.ixe`: an explicit `--ixe` path is used as-is (and
    must exist — no silent recompile of a mistyped path); otherwise the
    env is compiled fresh to `<repo>/<env>.ixe` with the default compiler,
    under the benchmark's RAM ceiling. -/
def ensureIxe (repo : String) (info : EnvSpec) (explicit : Option String)
    (ceilingGb : Nat) : IO String := do
  if let some path := explicit then
    if ← FilePath.pathExists path then
      return path
    throw <| IO.userError s!"--ixe {path} not found"
  let ixe := s!"{repo}/{info.name}.ixe"
  let ix ← resolveBin repo "ix"
  let exit ← runGuarded true ceilingGb ix
    #["compile", s!"{repo}/{info.module}", "--out", ixe]
  if exit != 0 then
    throw <| IO.userError s!"ix compile {info.module} failed (exit {exit})"
  return ixe

/-- Final run gate from the rows themselves: exit 1 when any EXPECTED name
    lacks a row (an aborted loop, a killed batch, or a dropped whole-env
    check must never look green — every selected name owes exactly one
    row), exit 3 when any row is `rejected` (a failing exit, with the rows
    on disk saying why), else 0. -/
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

/-- Save the run as the local baseline (`<benchOutputDir>/<params>.json`),
    rotating the previous baseline to `.prev.json` — `ix bench compare`
    defaults to the pair, so a bare local rerun compares against the last
    run automatically. -/
def saveBaseline (out : String) (params : String) : IO Unit := do
  let dir ← benchOutputDir
  IO.FS.createDirAll dir
  let base := s!"{dir}/{params}.json"
  if ← FilePath.pathExists base then
    IO.FS.writeFile s!"{dir}/{params}.prev.json" (← IO.FS.readFile base)
    -- Rotate the per-constant attribution CSV alongside its results file.
    if ← FilePath.pathExists s!"{base}.perconst.csv" then
      IO.FS.writeFile s!"{dir}/{params}.prev.json.perconst.csv"
        (← IO.FS.readFile s!"{base}.perconst.csv")
  IO.FS.writeFile base (← IO.FS.readFile out)
  if ← FilePath.pathExists s!"{out}.perconst.csv" then
    IO.FS.writeFile s!"{base}.perconst.csv"
      (← IO.FS.readFile s!"{out}.perconst.csv")

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
  let ceilingGb : Nat ← match p.flag? "ceiling-gb" with
    | some f => pure (f.as! Nat)
    | none => defaultCeilingGb
  -- No watchdog, no run — an unenforced ceiling is not a benchmark run.
  -- `Ix.Watchdog.available` probes the whole path end to end (systemd
  -- user scope, oom.group shim) before any tool spawns.
  let watchdog : Bool ←
    if ← Ix.Watchdog.available then
      pure true
    else do
      p.printError "error: RAM watchdog unavailable (systemd user scope \
with cgroup memory.oom.group failed the probe) — an unenforced ceiling \
is not a benchmark run"
      return exitUsage
  -- `--consts` overrides the shared-set selection — a one-off local run,
  -- or bench-pr's targeted base run over just the constants bencher
  -- lacked.
  let wanted := ((p.flag? "consts").map
    (fun f => Ix.Cli.ConstsFile.parseCommaList (f.as! String))).getD #[]
  let names :=
    if wanted.isEmpty then (selectNames env backend mode).map (·.name)
    else wanted
  IO.eprintln s!"[bench] run {backend}-{env}-{mode}: {names.size} constant(s)"

  -- Fresh accumulator per run.
  if ← FilePath.pathExists out then IO.FS.removeFile out
  let namesFile := out ++ ".names.txt"

  match backend with
  | "compile" =>
    -- The compile IS the benchmark: always fresh, row keyed by the env name.
    -- Measure the default compiler, including its certification checks.
    let ix ← resolveBin repo "ix"
    let exit ← runGuarded watchdog ceilingGb ix
      #["compile", s!"{repo}/{info.module}", "--out", s!"{repo}/{env}.ixe",
        "--json", out, "--json-name", info.name]
    if exit != 0 then
      IO.eprintln s!"[bench] ix compile failed (exit {exit})"
      return 1
  | "decompile" =>
    -- The inverse of compile: consume the env's `.ixe` (the compile run's
    -- fresh artifact) and decompile it back to Lean constants. Env-keyed row,
    -- like compile. A malformed decompile exits nonzero and fails the job;
    -- deep roundtrip fidelity is gated by the canonical roundtrip checks
    -- (`ix validate` / the roundtrip tests), not measured here.
    let ixe ← ensureIxe repo info ((p.flag? "ixe").map (·.as! String)) ceilingGb
    let ix ← resolveBin repo "ix"
    let exit ← runGuarded watchdog ceilingGb ix
      #["decompile", ixe, "--json", out, "--json-name", info.name]
    if exit != 0 then
      IO.eprintln s!"[bench] ix decompile failed (exit {exit})"
  | "ooc" =>
    let ixe ← ensureIxe repo info ((p.flag? "ixe").map (·.as! String)) ceilingGb
    let ix ← resolveBin repo "ix"
    -- Whole-env row (keyed by the env name), plus the per-constant
    -- attribution CSV the compare drill-down reads (top movers).
    let exit ← runGuarded watchdog ceilingGb ix
      #["check-lean", ixe, "--anon", "--json", out, "--json-name", info.name,
        "--per-const", s!"{out}.perconst.csv"]
    if exit != 0 && exit != exitRejected then
      IO.eprintln s!"[bench] whole-env check failed (exit {exit})"
    -- … plus one full-closure row per constant. ONE process for all names:
    -- the check-lean rows mode attributes per name internally with the env
    -- loaded once — a per-constant process would re-pay the multi-minute
    -- Mathlib env parse per name — and out-of-circuit checks don't approach
    -- the RAM ceiling.
    if !names.isEmpty then
      IO.FS.writeFile namesFile ("\n".intercalate names.toList ++ "\n")
      let exit ← runGuarded watchdog ceilingGb ix
        #["check-lean", ixe, "--anon", "--consts-file", namesFile, "--json", out]
      if exit != 0 && exit != exitRejected then
        IO.eprintln s!"[bench] per-constant checks failed (exit {exit})"
  | other =>
    p.printError s!"error: backend '{other}' has no runner"
    return exitUsage

  -- Every selected name owes a row; the env-keyed backends owe the env
  -- row too.
  let expected := match backend with
    | "compile" => #[info.name]
    | "decompile" => #[info.name]
    | "ooc" => #[info.name] ++ names
    | _ => names
  let code ← gate out expected
  if code == 0 || code == exitRejected then
    saveBaseline out s!"{backend}-{env}-{mode}"
  return code

end Ix.Cli.BenchCmd

open Ix.Cli.BenchCmd in
def benchRunCmd : Cli.Cmd := `[Cli|
  "run" VIA runBenchRunCmd;
  "Execute one benchmark run (backend × env × mode), writing benchmark results JSON. Exits 0 on success (rows saved as the local baseline), 3 when the kernel rejected any constant, 1 when no rows were produced."

  FLAGS:
    backend      : String; "ooc | compile | decompile"
    env          : String; "Benchmark env from the registry (default: InitStd)"
    mode         : String; "Backend mode (default: the backend's defaultMode)"
    out          : String; "Benchmark results JSON output path (default: bench.json)"
    repo         : String; "Checkout to benchmark: tools resolve from <repo>/.lake/build/bin first, then PATH (default: .)"
    consts       : String; "Run exactly these comma-separated names instead of the shared benchConstants selection (same grammar as the tools' --consts)"
    ixe          : String; "Path to an existing .ixe env to use (default: compile <env> fresh; ignored by the compile backend)"
    "ceiling-gb" : Nat;    "RAM watchdog ceiling in GB (default: machine RAM minus 15 GB)"
]
