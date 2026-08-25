/-
  `ix bench run`: the benchmark orchestrator — one command that
  reproduces a CI benchmark run locally, byte-for-byte on the same tools.

  A run executes one parameter combination: (backend, env, mode). The
  orchestrator:

  1. selects the env's constants from the shared set
     (`Ix.BenchConstants`), minus the `(backend, mode)` exclusions;
  2. resolves the env's `.ixe` (an explicit `--ixe` path, else `ix
     compile` — except for the `compile` backend, where the compile IS
     the benchmark);
  3. spawns the run's measured tool — `bench-typecheck` (aiur),
     `zisk-host`/`sp1-host` (zkVM execute), `ix check-rs` (ooc),
     `bench-lean4lean` (lean4lean; olean-driven, no `.ixe`),
     `ix compile` (compile) — wrapped in the RAM watchdog (`Ix.Watchdog`:
     cgroup `memory.max` via a systemd user scope; the kernel OOM-kills
     at the ceiling). The per-constant backends (aiur, zkVM) spawn
     ONE PROCESS PER CONSTANT: a kill costs exactly that constant (its row
     is marked `status: oom`, keeping whatever the tool flushed), and each
     spawn's texray window (`<out>.spans`) belongs wholly to it, folded
     into the row as flat `phase-<span>` fields — independent bencher
     measures with no attribution machinery;
  4. gates the run on the row contract (`Ix.Benchmark.Results`): exit 3
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
public import Ix.BenchConstants
public import Ix.Benchmark.Results
public import Ix.Cli.ConstsFile
public import Ix.Watchdog

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
def benchExclusions : List (String × String × String) :=
  let bitblast :=
    "Std.Tactic.BVDecide.BVExpr.bitblast.goCache_Inv_of_Inv._mutual"
  [ -- ~18B-step atomic mutual block: Aiur executes it, but the zkVM
    -- executor OOMs (ASM MO crash) before any measurement lands.
    (bitblast, "zisk", "*"),
    (bitblast, "sp1", "*") ]

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
  -- Init+Std+Lean+Batteries as ONE env: the whole-env Aiur execution
  -- benchmark's fast tier (the union deduplicates — Lean already
  -- carries Init and Std).
  { name := "ISLB",    module := "Benchmarks/Compile/CompileISLB.lean" },
  { name := "Mathlib", module := "Benchmarks/Compile/CompileMathlib.lean" },
  { name := "FLT",     module := "Benchmarks/Compile/CompileFLT.lean" }
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
        gaining constants, not by a registry flag. The prove/execute
        backends (aiur, zisk, sp1).
      · `perConstantWithEnv` — `perConstant` plus a whole-env row (ooc). -/
inductive BenchInputs
  | perEnv
  | perConstant
  | perConstantWithEnv
  deriving BEq

/-- A testbed minus its runner-arch suffix — the workload key the threshold
    reset anchors (`refs/bencher/<workload>`), the dashboard plot titles,
    and the run metadata are written against. -/
def workloadOf (testbed : String) : String :=
  if testbed.endsWith "-x64-32x" then (testbed.dropEnd 8).toString
  else testbed

/-- The stage qualifiers a pipeline measure may carry ahead of its base
    name — one per pipeline stage, named for what the stage proves
    (`ixvm-`: the IxVM typecheck; `fri-verifier-`: the in-circuit FRI
    verifier over the previous proof; the KZG stages add their own
    entries as they land) — plus `pipeline-` for the whole run. Stripped
    wherever a measure is interpreted by its base name (formatting kind,
    units) or labelled under a heading that already says the stage. -/
def stagePrefixes : List String := ["ixvm-", "fri-verifier-", "pipeline-"]

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
    testbed (aiur's pipeline mode stage-qualifies its measure names, while
    its standalone execute mode keeps the plain Phase-1 names). -/
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
  /-- Modes present for local / on-demand `ix bench run --mode` only —
      scheduled by no CI job (too heavy for the CI host), so they carry a
      testbed for the compare surface but never upload to bencher and get
      no dashboard plot. -/
  unscheduled : List String := []
  /-- (mode, bencher testbed). -/
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
  -- aiur: the proof-pipeline benchmark (bench-typecheck --recursive) —
  -- every stage of the pipeline, per constant, plus the total. The ixvm
  -- stage proves the constant's IxVM typecheck; the fri-verifier stage
  -- executes the in-circuit multi-stark verifier over that fresh proof
  -- and proves THAT execution; the KZG stages will join as stages 3/4
  -- when they land, folding into the same ledger. Each stage reports the
  -- same seven columns — witness execute, prove, throughput, peak RAM,
  -- proof size, verify, FFT cost — and the closing ledger table carries
  -- `total-time` (the stages' proves, summed — each prove already runs
  -- its own witness execution, so the standalone execute times are
  -- instrumentation and are not added), the end-to-end
  -- `pipeline-throughput`, and the run's RAM ceiling. The whole system
  -- runs under the
  -- recursion-tuned parameters — 50 FRI queries at log-blowup 2 for
  -- both stages' proofs alike, the soundness level taking
  -- precedence over fitting every constant in the host's RAM (see
  -- `recursiveFriParameters` in Benchmarks/Typecheck.lean). execute is
  -- the fast Phase-1-only signal (witness generation, no proving),
  -- `unscheduled`: a local / on-demand mode that never uploads.
  { name := "aiur", defaultMode := "prove", inputs := .perConstant,
    testbeds := [("prove", "aiur-x64-32x"),
                 ("execute", "aiur-execute-x64-32x")],
    unscheduled := ["execute"],
    stages := [("prove",
      [("IxVM on FRI",
         ["ixvm-execute-time", "ixvm-prove-time", "ixvm-throughput",
          "ixvm-peak-rss", "ixvm-proof-size", "ixvm-verify-time",
          "ixvm-fft-cost"]),
       ("FRI verifier on FRI",
         ["fri-verifier-execute-time", "fri-verifier-prove-time",
          "fri-verifier-throughput", "fri-verifier-peak-rss",
          "fri-verifier-proof-size", "fri-verifier-verify-time",
          "fri-verifier-fft-cost"]),
       ("Pipeline total",
         ["total-time", "pipeline-throughput", "pipeline-peak-rss"])])],
    metrics := [("execute", ["execute-time", "throughput", "peak-rss",
                             "fft-cost"])],
    -- ixvm-fft-cost is deterministic but only ever drops on a real Aiur
    -- win → upper-only 5% instead of a hard pin. fri-verifier-fft-cost
    -- drifts ~±15% run-to-run (the parallel prover emits byte-different
    -- valid proofs, so the verifier authenticates different Merkle
    -- paths) → the loose 25% bound. Proof sizes are structural (fixed
    -- query count and path depth) → the tight 5%. `total-time` carries
    -- NO bound: it is the two prove times summed, and a sum cannot
    -- breach a percentage bound unless one of its terms already breached
    -- the same one — so it could only ever duplicate an alert the proves
    -- fired. The throughputs likewise carry no bound: `constants` is
    -- pinned exactly, so each is the pure inverse of an already-bounded
    -- time.
    thresholds := [("constants", "0", "0"), ("ixvm-fft-cost", "0.05", "_"),
                   ("fri-verifier-fft-cost", "0.25", "_"),
                   ("ixvm-execute-time", "0.10", "_"),
                   ("ixvm-prove-time", "0.10", "_"),
                   ("fri-verifier-execute-time", "0.10", "_"),
                   ("fri-verifier-prove-time", "0.10", "_"),
                   ("ixvm-peak-rss", "0.10", "_"),
                   ("fri-verifier-peak-rss", "0.10", "_"),
                   ("pipeline-peak-rss", "0.10", "_"),
                   ("ixvm-proof-size", "0.05", "_"),
                   ("fri-verifier-proof-size", "0.05", "_"),
                   ("ixvm-verify-time", "0.10", "_"),
                   ("fri-verifier-verify-time", "0.10", "_")] },
  -- aiur-sharded-env: whole-env Aiur execution — the sharded feeder pipeline
  -- end-to-end at env scale, one row per env. Shards the `.ixe` for the
  -- runner's RAM (`ix shard --max-ram 100`: naive sizing → ~3.5 GB
  -- execution RSS per shard on a 128 GB runner), then one gated
  -- full-width rayon batch (`ix check --ixe --ixes`) over the whole
  -- manifest — the byte-weighted RamGate, not a thread cap, bounds peak
  -- RSS, so the same entry is correct on any runner class. ISLB only
  -- for now (~10 min/run); add "FLT" / "Mathlib" to `envs` for the
  -- env-scale tiers (~30-45 min each on the 32x runner) when their
  -- per-push cost is warranted. `shards` is deterministic per
  -- (env bytes, budget) and only drops on a real compression win →
  -- upper-only pin.
  { name := "aiur-sharded-env", defaultMode := "execute", inputs := .perEnv,
    envs := some ["ISLB"],
    testbeds := [("execute", "aiur-sharded-env-check-x64-32x")],
    metrics := [("execute", ["check-time", "throughput", "peak-rss",
                             "constants", "shards"])],
    thresholds := [("constants", "0", "0"), ("shards", "0", "_"),
                   ("check-time", "0.10", "_"), ("throughput", "_", "0.10"),
                   ("peak-rss", "0.10", "_")] },
  { name := "zisk", defaultMode := "execute", inputs := .perConstant,
    testbeds := [("execute", "zisk-check-execute-x64-32x")],
    metrics := [("execute", ["execute-time", "throughput", "peak-rss",
                             "cycles", "constants", "shards"])],
    -- cycles / shards / max-shard-cycles are deterministic per guest ELF,
    -- but a real guest / packer improvement legitimately drops them →
    -- upper-only 0% bounds.
    thresholds := [("constants", "0", "0"), ("cycles", "0", "_"),
                   ("shards", "0", "_"), ("max-shard-cycles", "0", "_"),
                   ("execute-time", "0.10", "_"), ("peak-rss", "0.10", "_"),
                   ("throughput", "_", "0.10")] },
  { name := "sp1", defaultMode := "execute", inputs := .perConstant,
    disabled := some "execute run too slow for per-push CI; re-enable here once trimmed",
    testbeds := [("execute", "sp1-check-execute-x64-32x")],
    metrics := [("execute", ["execute-time", "throughput", "peak-rss",
                             "cycles"])],
    thresholds := [("constants", "0", "0"), ("cycles", "0", "_"),
                   ("execute-time", "0.10", "_"), ("peak-rss", "0.10", "_"),
                   ("throughput", "_", "0.10")] },
  { name := "ooc", defaultMode := "execute", inputs := .perConstantWithEnv,
    testbeds := [("execute", "ooc-check-x64-32x")],
    metrics := [("execute", ["check-time", "throughput", "peak-rss"])],
    thresholds := [("constants", "0", "0"), ("check-time", "0.10", "_"),
                   ("throughput", "_", "0.10"), ("peak-rss", "0.10", "_")] },
  -- lean4lean (github.com/digama0/lean4lean, required by the lakefile at a
  -- pinned rev): the reference Lean4-in-Lean4 kernel, the external
  -- yardstick for the Ix kernels (`ooc` / `ix check-lean`) on the same
  -- libraries. Checks the env's library from its oleans (no `.ixe`):
  -- whole-library row (module-parallel replay of the import closure) plus
  -- one full-closure row per constant, mirroring ooc's row shape and
  -- metric names so cross-kernel tables line up. Disabled in CI until a
  -- bencher testbed exists — `ix bench run --backend lean4lean` works
  -- locally regardless (`disabled` only gates the CI matrix and
  -- `!benchmark` scheduling).
  { name := "lean4lean", defaultMode := "execute",
    inputs := .perConstantWithEnv,
    disabled := some "local-only: no bencher testbed yet",
    testbeds := [("execute", "lean4lean-check-x64-32x")],
    metrics := [("execute", ["check-time", "throughput", "peak-rss",
                             "constants"])] },
  { name := "compile", defaultMode := "execute", inputs := .perEnv,
    testbeds := [("execute", "ix-compile-x64-32x")],
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
    -- Pinned to the pre-ISLB env set: ISLB exists for the aiur-sharded-env
    -- whole-env execution benchmark, and its content is Lean +
    -- Batteries — a decompile row would mostly re-measure Lean's.
    envs := some ["InitStd", "Lean", "Mathlib", "FLT"],
    testbeds := [("execute", "ix-decompile-x64-32x")],
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

/-- Merge a kill `status` (`oom` or `crash`) into a constant's row,
    PRESERVING metrics the tool flushed before the kill (e.g.
    bench-typecheck persists Phase-1 fields before the prove starts). The
    compare surface renders the status only for the metrics that are
    absent. -/
def markKilled (out : String) (name : String) (status : String) : IO Unit := do
  let rows ← readRows out
  let row := (rows.getObjVal? name).toOption.getD (Lean.Json.mkObj [])
  writeEntry out name (row.setObjVal! "status" (Lean.Json.str status))

/-- Status for a 128+signal death: explicit kills (137 KILL — cgroup breach
    or watchdog; 143 TERM) and allocator aborts (134 — e.g. Rust's OOM
    abort) are capacity kills, `oom`. Everything else (139 SIGSEGV, 135
    SIGBUS, …) is a genuine fault in the tool, `crash` — conflating the two
    turned a zisk mem-planner segfault into a phantom OOM row. -/
def killStatus (exit : UInt32) : String :=
  if exit == 137 || exit == 143 || exit == 134 then "oom" else "crash"

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
    to it. Per exit: ≥128 (watchdog TERM/KILL, the kernel OOM killer, or a
    fault in the tool) → mark the row `oom`/`crash` per `killStatus`
    (keeping whatever the tool flushed, spans included)
    and continue; `exitRejected` → the rejected row is on disk, continue
    (the final gate fails the job); any other nonzero exit is
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
    -- with -1; labeling it oom would turn a broken spawn into a passing job
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
        let status := killStatus exit
        IO.eprintln s!"[bench] '{name}' killed (exit {exit}); recording {status}"
        markKilled out name status
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
  let exit ← runGuarded false 0 ix
    #["compile", s!"{repo}/{info.module}", "--out", ixe]
  if exit != 0 then
    throw <| IO.userError s!"ix compile {info.module} failed (exit {exit})"
  return ixe

/-- Cut the closure-shard artifacts for one constant: `ix shard
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
    , #["shard", subIxe, "--profile", prof, "--max-ram", toString maxRamGb,
        "--out", manifest] ]
  for args in steps do
    let exit ← runGuarded false 0 ix args
    if exit != 0 then
      IO.eprintln s!"[bench] shard pipeline failed for '{name}' (exit {exit}); falling back to single leaf"
      return none
  return some (subIxe, manifest)

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
    let ixe ← ensureIxe repo info ((p.flag? "ixe").map (·.as! String))
    let ix ← resolveBin repo "ix"
    let exit ← runGuarded watchdog ceilingGb ix
      #["decompile", ixe, "--json", out, "--json-name", info.name]
    if exit != 0 then
      IO.eprintln s!"[bench] ix decompile failed (exit {exit})"
  | "ooc" =>
    let ixe ← ensureIxe repo info ((p.flag? "ixe").map (·.as! String))
    let ix ← resolveBin repo "ix"
    -- Whole-env row (keyed by the env name), plus the per-constant
    -- attribution CSV the compare drill-down reads (top movers).
    let exit ← runGuarded watchdog ceilingGb ix
      #["check-rs", ixe, "--anon", "--json", out, "--json-name", info.name,
        "--per-const", s!"{out}.perconst.csv"]
    if exit != 0 && exit != exitRejected then
      IO.eprintln s!"[bench] whole-env check failed (exit {exit})"
    -- … plus one full-closure row per constant. ONE process for all names
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
  | "aiur-sharded-env" =>
    -- Whole-env sharded Aiur execution: shard the env for the runner's
    -- RAM (naive `--max-ram 100` sizing → ~3.5 GB execution RSS per
    -- shard), then ONE gated full-width rayon batch over the manifest —
    -- the RamGate bounds peak RSS, so no `--jobs` is passed. The check
    -- writes the env-keyed row itself (`--json`): check-time,
    -- throughput, peak-rss, constants, shards. The shard step is
    -- deterministic setup, not part of the measured window.
    let ixe ← ensureIxe repo info ((p.flag? "ixe").map (·.as! String))
    let ix ← resolveBin repo "ix"
    let manifest := s!"{env}-exec.ixes"
    let exit ← runGuarded watchdog ceilingGb ix
      #["shard", ixe, "--max-ram", "100", "--out", manifest]
    if exit != 0 then
      IO.eprintln s!"[bench] ix shard failed (exit {exit})"
      return 1
    let exit ← runGuarded watchdog ceilingGb ix
      #["check", "--ixe", ixe, "--ixes", manifest,
        "--json", out, "--json-name", info.name]
    if exit != 0 && exit != exitRejected then
      IO.eprintln s!"[bench] whole-env aiur check failed (exit {exit})"
  | "lean4lean" =>
    -- The reference Lean4-in-Lean4 kernel checks the env's library from
    -- its oleans, so no `.ixe` is resolved. The tool takes the same
    -- registry `module` path `ix compile` does (its lake project supplies
    -- the search path; the tool builds the module itself, outside every
    -- timed window). Whole-library row keyed by the env name …
    let bl ← resolveBin repo "bench-lean4lean"
    let modulePath := s!"{repo}/{info.module}"
    let exit ← runGuarded watchdog ceilingGb bl
      #[modulePath, "--json", out, "--json-name", info.name]
    if exit != 0 && exit != exitRejected then
      IO.eprintln s!"[bench] whole-library replay failed (exit {exit})"
    -- … plus one full-closure row per constant. ONE process for all names
    -- (the ooc pattern): the imported env is shared across the closure
    -- replays instead of re-paying the library import per name.
    if !names.isEmpty then
      IO.FS.writeFile namesFile ("\n".intercalate names.toList ++ "\n")
      let exit ← runGuarded watchdog ceilingGb bl
        #[modulePath, "--no-build", "--consts-file", namesFile, "--json", out]
      if exit != 0 && exit != exitRejected then
        IO.eprintln s!"[bench] per-constant closures failed (exit {exit})"
  | "aiur" =>
    -- prove runs the whole pipeline (`bench-typecheck --recursive`):
    -- every stage per constant, closed by the pipeline ledger. One process
    -- per constant under the watchdog; `total-time` is the ledger's last
    -- field, so it doubles as the completion marker — a kill before the
    -- pipeline finishes records an honest oom/crash row.
    let ixe ← ensureIxe repo info ((p.flag? "ixe").map (·.as! String))
    let bt ← resolveBin repo "bench-typecheck"
    let (modeArgs, doneKey) := match mode with
      | "execute" => (#["--execute-only"], "execute-time")
      | _ => (#["--recursive"], "total-time")
    runPerConstant out names doneKey fun name =>
      runGuarded watchdog ceilingGb bt
        (#["--ixe", ixe, "--consts", name, "--json", out, "--texray"]
          ++ modeArgs)
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
    let build ← runGuarded false 0 "cargo"
      #["build", "--quiet", "--release", "--bin", host] (cwd := some work)
    if build != 0 then
      IO.eprintln s!"[bench] cargo build {host} failed (exit {build})"
      return 1
    let bin := (← IO.FS.realPath s!"{work}/target/release/{host}").toString
    -- zisk decides sharding at run time, per constant: the closure is
    -- extracted and profiled, and the shard planner's RAM budget sizes
    -- the partition from the closure's predicted cost — a closure that
    -- fits gets a one-shard plan and runs as a single leaf. The artifacts
    -- are cached under `zkshards-<env>/` (pre-cut next to the fresh
    -- `.ixe` by `ix bench shard` when available). A failed cut falls
    -- back to the whole closure from the env's `.ixe` — the watchdog
    -- then records the honest OOM row if it doesn't fit. sp1 always
    -- runs whole closures.
    let ix ← resolveBin repo "ix"
    runPerConstant outAbs names "execute-time" fun name => do
      let plan ← if backend == "zisk"
        then cutClosureShards ix ixe s!"{repo}/zkshards-{env}" name ceilingGb
        else pure none
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
    | "ooc" | "lean4lean" => #[info.name] ++ names
    | _ => names
  let code ← gate out expected
  if code == 0 || code == exitRejected then
    saveBaseline out s!"{backend}-{env}-{mode}"
  return code

/-- `ix bench shard`: pre-cut the closure-shard artifacts for the env's
    zisk constants into `zkshards-<env>/` — `ix shard extract` →
    `ix profile` → `ix shard` per name, skipping names whose artifacts
    already exist. Not a benchmark run (no rows, no watchdog): bench-main's
    compile job runs it next to the fresh `.ixe` so the artifacts ride the
    same cache; the zisk runs cut lazily as a fallback when they're
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
  let names := (selectNames env "zisk" "execute").map (·.name)
  IO.eprintln s!"[bench] shard {env}: {names.size} constant(s)"
  let ixe ← ensureIxe repo info ((p.flag? "ixe").map (·.as! String))
  let ix ← resolveBin repo "ix"
  for name in names do
    let _ ← cutClosureShards ix ixe s!"{repo}/zkshards-{env}" name ceilingGb
  return 0

end Ix.Cli.BenchCmd

open Ix.Cli.BenchCmd in
def benchRunCmd : Cli.Cmd := `[Cli|
  "run" VIA runBenchRunCmd;
  "Execute one benchmark run (backend × env × mode), writing benchmark results JSON. Exits 0 on success (rows saved as the local baseline), 3 when the kernel rejected any constant, 1 when no rows were produced."

  FLAGS:
    backend      : String; "aiur | aiur-sharded-env | zisk | sp1 | ooc | lean4lean | compile | decompile"
    env          : String; "Benchmark env from the registry (default: InitStd)"
    mode         : String; "prove | execute (default: the backend's defaultMode)"
    out          : String; "Benchmark results JSON output path (default: bench.json)"
    repo         : String; "Checkout to benchmark: tools resolve from <repo>/.lake/build/bin first, then PATH (default: .)"
    consts       : String; "Run exactly these comma-separated names instead of the shared benchConstants selection (same grammar as the tools' --consts)"
    ixe          : String; "Path to an existing .ixe env to use (default: compile <env> fresh; ignored by the compile backend)"
    "ceiling-gb" : Nat;    "RAM watchdog ceiling in GB (default: machine RAM minus 15 GB)"
]

open Ix.Cli.BenchCmd in
def benchShardCmd : Cli.Cmd := `[Cli|
  "shard" VIA runBenchShardCmd;
  "Pre-cut closure-shard artifacts (ix shard extract → profile → shard) for the env's zisk constants into zkshards-<env>/; skips names already cut. The zisk runs cut lazily when these are absent — this front-loads the work so the artifacts can be cached once per commit."

  FLAGS:
    env          : String; "Benchmark env from the registry (default: InitStd)"
    repo         : String; "Checkout to shard: tools resolve from <repo>/.lake/build/bin first, then PATH (default: .)"
    ixe          : String; "Path to an existing .ixe env to use (default: compile <env> fresh)"
    "ceiling-gb" : Nat;    "Predicted-RAM cap per shard, passed to `ix shard --max-ram` (default: machine RAM minus 15 GB)"
]
