module
public import Cli
public import Lean.Data.Json
public import Ix.BenchConstants
public import Ix.Benchmark.Results
public import Ix.Cli.ConstsFile
public import Ix.Shard.Manifest
public import Ix.TracingTexray

/-!
  `ix bench run`: the benchmark orchestrator — one command that
  reproduces a CI benchmark run locally, byte-for-byte on the same tools.

  A run executes one cell: (backend, env). Its rows are constant rows (the
  env's shared constants, keyed by name) and the env row (the whole env,
  keyed by the env name); `--constants` and `--no-env-row` select them.
  The orchestrator:

  1. selects the env's constant rows from the shared set
     (`Ix.BenchConstants`), for a backend with constant rows;
  2. resolves the env's `.ixe` (an explicit `--ixe` path, else `ix
     compile` — except for the `compile` backend, where the compile IS
     the benchmark);
  3. spawns the run's measured tool — `ix check` (ixvm), `ix check-lean`
     (ixvm-ooc), `ix compile` (compile), `ix decompile` (decompile). The
     tools set no memory limit; CI runs `ix bench run` in a capped cgroup,
     where the kernel OOM-kills the largest process, the tool. The ixvm
     constant rows spawn one process per constant, so a kill costs exactly
     that constant (its row is marked `status: oom`);
  4. gates the run on the row contract (`Ix.Benchmark.Results`): exit 3
     when any row is `rejected`, exit 1 when a selected row is missing,
     else 0.

  The compile-side tools self-report through the `--json` results-rows
  contract. `ix check` has no rows of its own, so the orchestrator writes
  the ixvm rows from the spawn's wall time, the texray tree sampler's peak,
  and the `aiur/execute` spans `ix check` writes to `IX_TEXRAY_JSON`.
  Registry data (envs, backends, testbeds) lives in this module
  (`envSpecs`/`backendSpecs`) — one language, one owner.

-/

public section

open System (FilePath)
open Ix.Benchmark.Results
open Ix.BenchConstants

namespace Ix.Cli.BenchCmd

/-- The env's slice of the shared `benchConstants` set: the constant rows
    a backend with constant rows runs over that env. -/
def selectNames (env : String) : Array BenchConstant :=
  benchConstants.filter (·.env == env)

/-! ## The registry — single source of truth for the benchmark pipeline

`Ix.BenchConstants` holds the shared constant set; everything else lives
here, in one language with one owner. The workflows never read it directly:
`ix bench ci matrix` serves the job matrices and `ix bench ci parse` the
`!benchmark` runs, both post-build. -/

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
  -- Init+Std+Lean+Batteries as one env (the union deduplicates: Lean
  -- already carries Init and Std).
  { name := "ISLB",    module := "Benchmarks/Compile/CompileISLB.lean" },
  { name := "Mathlib", module := "Benchmarks/Compile/CompileMathlib.lean" }
]

def findEnv (token : String) : Option EnvSpec :=
  envSpecs.find? fun e => e.name.toLower == token.toLower

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

/-- A testbed minus its hardware suffix — the workload key the dashboard
    plot titles and ordering are written against. -/
def workloadOf (testbed : String) : String :=
  match (benchmarkMachines.map testbedSuffix).find? (testbed.endsWith ·) with
  | some suffix => (testbed.dropEnd suffix.length).toString
  | none => testbed

def testbedOnMachine (testbed machine : String) : String :=
  workloadOf testbed ++ testbedSuffix machine

/-- One benchmark backend. A backend's rows are of two kinds: constant
    rows, one per shared constant (`Ix.BenchConstants`) run in its env and
    keyed by the constant's name, and env rows, one per registry env and
    keyed by the env's name. Both kinds upload to the backend's one
    testbed, so they draw as lines of the same plot per measure. -/
structure BackendSpec where
  name : String
  /-- `some reason` ⇒ `parse` skips the backend with the note in the
      config summary. -/
  disabled : Option String := none
  /-- The bencher testbed stem; hardware suffixes identify the measured
      host. -/
  testbed : String
  /-- Compare-table columns of the constant rows, in order (the head is
      the row sort key); empty for a backend without constant rows. Column
      convention: the headline wall-clock time, throughput, peak-rss, then
      detail (secondary times, sizes, deterministic counters). -/
  constantMetrics : List String := []
  /-- Compare-table columns of the env rows, in the same convention. -/
  envMetrics : List String

def backendSpecs : List BackendSpec := [
  -- ixvm: execution of the certified IxVM claim verifier by `ix check`,
  -- no proving. A constant row is one `ix check --ixe <env>.ixe <name>`:
  -- `execute-time` is the in-process `aiur/execute` span (bind + run),
  -- `check-time` the whole process (adding the env load, program load and
  -- claim construction), `peak-rss` the texray tree sampler's peak over
  -- it. The env row shards the env with `ix shard --max-ram 100` (setup,
  -- outside the measured window), then one `ix check --ixes` executes
  -- every shard's claim across all cores; its `execute-time` sums the
  -- shards' spans; `shards` counts the partition.
  { name := "ixvm", testbed := "ixvm",
    constantMetrics := ["execute-time", "check-time", "peak-rss"],
    envMetrics := ["check-time", "peak-rss", "execute-time", "shards"] },
  -- ixvm-ooc: the out-of-circuit IxC kernel (`ix check-lean --anon`). The
  -- constant rows check each constant's full closure in one process per
  -- env; the env row checks the whole env and writes the per-constant
  -- attribution CSV the compare drill-down reads.
  { name := "ixvm-ooc", testbed := "ixvm-ooc",
    constantMetrics := ["check-time", "throughput", "peak-rss"],
    envMetrics := ["check-time", "throughput", "peak-rss"] },
  -- A distinct baseline keeps the cost of certification out of comparisons
  -- against historical Rust compiler timings.
  { name := "compile", testbed := "ix-compile-certified",
    envMetrics := ["compile-time", "throughput", "peak-rss", "file-size", "constants"] },
  -- The inverse of compile: decompiles the env's `.ixe` back to Lean
  -- constants (roundtrip-verified). A `.ixe` consumer: it reuses the
  -- compile run's fresh `.ixe` rather than producing one.
  { name := "decompile", testbed := "ix-decompile-lean",
    envMetrics := ["decompile-time", "throughput", "peak-rss", "file-size", "constants"] }
]

def findBackend (name : String) : Option BackendSpec :=
  backendSpecs.find? (·.name == name)

/-- Whether the backend has constant rows. -/
def BackendSpec.hasConstants (b : BackendSpec) : Bool :=
  !b.constantMetrics.isEmpty

/-- Every measure the backend tracks: its constant and env columns. -/
def BackendSpec.metrics (b : BackendSpec) : List String :=
  (b.constantMetrics ++ b.envMetrics).eraseDups

/-- The benchmark row names this backend uploads for a measure — the
    bencher slugs the dashboard plots key on: the shared constants when the
    measure is a constant column, then the envs when it is an env column.
    Dynamic shard sub-rows (`<name>/shard-N`) are excluded — the parent row
    carries the headline trend. -/
def BackendSpec.benchmarkNames (b : BackendSpec) (measure : String) : Array String :=
  (if b.constantMetrics.contains measure
    then benchConstants.map (·.name) else #[])
  ++ (if b.envMetrics.contains measure
    then (envSpecs.map (·.name)).toArray else #[])

/-- Resolve a tool binary: prefer the in-tree build under `repo` (so a base
    checkout measures the base's code), else PATH. -/
def resolveBin (repo : String) (name : String) : IO String := do
  let inTree := s!"{repo}/.lake/build/bin/{name}"
  if ← FilePath.pathExists inTree then
    return inTree
  return name

/-- Spawn `cmd args` (inheriting stdio) and wait for its exit code. The
    tools set no memory limit of their own: CI runs `ix bench run` in a
    capped cgroup, where an OOM kill lands on the largest process, the
    tool, and this run records it. -/
def runTool (cmd : String) (args : Array String)
    (env : Array (String × Option String) := #[]) : IO UInt32 := do
  IO.eprintln s!"[bench] run: {cmd} {" ".intercalate args.toList}"
  let child ← IO.Process.spawn { cmd, args, env }
  child.wait

/-- `runTool` for a tool that writes no rows itself: also returns the
    spawn's wall-clock seconds and the texray tree sampler's peak RSS over
    it, which includes this process's own small resident set. -/
def runMeasured (cmd : String) (args : Array String)
    (env : Array (String × Option String) := #[]) : IO (UInt32 × Float × Nat) := do
  TracingTexray.startSampler
  TracingTexray.resetPeakTreeRss
  let start ← IO.monoNanosNow
  let exit ← runTool cmd args env
  let seconds := ((← IO.monoNanosNow) - start).toFloat / 1e9
  return (exit, seconds, ← TracingTexray.peakTreeRssBytes)

/-- Merge a kill `status` (`oom` or `crash`) into a row, preserving any
    metrics written before the kill. The compare surface renders the
    status only for the metrics that are absent. -/
def markKilled (out : String) (name : String) (status : String) : IO Unit := do
  let rows ← readRows out
  let row := (rows.getObjVal? name).toOption.getD (Lean.Json.mkObj [])
  writeEntry out name (row.setObjVal! "status" (Lean.Json.str status))

/-- Status for a 128+signal death: explicit kills (137 KILL, as from a
    cgroup OOM kill; 143 TERM) and allocator aborts (134, e.g. Rust's OOM
    abort) are capacity kills, `oom`. Everything else (139 SIGSEGV, 135
    SIGBUS, …) is a fault in the tool, recorded as `crash`. -/
def killStatus (exit : UInt32) : String :=
  if exit == 137 || exit == 143 || exit == 134 then "oom" else "crash"

/-- Whether `exit` is a signal death. 255 never is (the kills above exit
    134/137/143): it is a failed exec or a tool exiting with -1. -/
def isKill (exit : UInt32) : Bool := exit ≥ 128 && exit != 255

/-- Sum a texray spans JSONL file (`{"span": s, "seconds": n}` per line)
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

/-- Run a per-constant tool: one process per constant, so a kill costs
    exactly that constant, and each spawn's spans belong wholly to it. Per
    exit: a signal death marks the row `oom`/`crash` per `killStatus`
    (keeping whatever was written) and continues; `exitRejected` means the
    rejected row is on disk, so continue (the final gate fails the run);
    any other nonzero exit is deterministic (usage error, missing input,
    unknown name) and would repeat for every remaining name, so abort. -/
def runPerConstant (out : String) (names : Array String)
    (spawn : String → IO UInt32) : IO Unit := do
  for name in names do
    let exit ← spawn name
    if isKill exit then
      let status := killStatus exit
      IO.eprintln s!"[bench] '{name}' killed (exit {exit}); recording {status}"
      markKilled out name status
    else if exit != 0 && exit != exitRejected then
      IO.eprintln s!"[bench] tool failed on '{name}' (exit {exit}, not a kill); aborting the remaining names"
      return

/-- Resolve the env's `.ixe`: an explicit `--ixe` path is used as-is (and
    must exist — no silent recompile of a mistyped path); otherwise the
    env is compiled fresh to `<repo>/<env>.ixe` with the default compiler. -/
def ensureIxe (repo : String) (info : EnvSpec) (explicit : Option String) :
    IO String := do
  if let some path := explicit then
    if ← FilePath.pathExists path then
      return path
    throw <| IO.userError s!"--ixe {path} not found"
  let ixe := s!"{repo}/{info.name}.ixe"
  let ix ← resolveBin repo "ix"
  let exit ← runTool ix
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

/-- The `ixvm` constant rows: one `ix check` per constant, its
    `aiur/execute` span written to the run's texray sink. The span closes
    on a rejection too, so a failing exit with the span is a verdict;
    without it the check never reached the claim. Execution runs inside
    `ix check`, so an OOM kill takes that process (exit 137) and the row
    records it. -/
def runIxvmConstants (ix ixe out : String) (names : Array String) : IO Unit := do
  let spans := out ++ ".spans"
  runPerConstant out names fun name => do
    let (exit, seconds, peak) ← runMeasured ix
      #["check", "--ixe", ixe, name] #[("IX_TEXRAY_JSON", some spans)]
    let execute := ((← readSpans spans).find? (·.1 == "aiur/execute")).map (·.2)
    if ← FilePath.pathExists spans then IO.FS.removeFile spans
    let rejected := exit != 0 && !isKill exit && execute.isSome
    if exit == 0 || rejected then
      let row := Lean.Json.mkObj [("check-time", jsonRound 6 seconds),
        ("peak-rss", Lean.toJson peak)]
      let row := match execute with
        | some t => row.setObjVal! "execute-time" (jsonRound 6 t)
        | none => row
      writeEntry out name <|
        if rejected then row.setObjVal! "status" (.str "rejected") else row
    return if rejected then exitRejected else exit

/-- The `ixvm` env row: seed the partition for the runner's RAM from the
    env's static block-shape score (setup, outside the measured window),
    then one `ix check` executes every shard's claim, one job per core,
    writing every shard's `aiur/execute` span to the one sink. -/
def runIxvmEnv (ix ixe out env : String) : IO Unit := do
  let manifest := s!"{env}-exec.ixes"
  let exit ← runTool ix #["shard", ixe, "--max-ram", "100", "--out", manifest]
  if exit != 0 then
    IO.eprintln s!"[bench] ix shard failed (exit {exit})"
    return
  let shards := match Ix.Shard.parseIxesManifest (← IO.FS.readBinFile manifest) with
    | .ok view => view.shards.size
    | .error _ => 0
  let spans := out ++ ".spans"
  let (exit, seconds, peak) ← runMeasured ix
    #["check", "--ixe", ixe, "--ixes", manifest, "--jobs", "0"]
    #[("IX_TEXRAY_JSON", some spans)]
  let execute := ((← readSpans spans).find? (·.1 == "aiur/execute")).map (·.2)
  if ← FilePath.pathExists spans then IO.FS.removeFile spans
  if isKill exit then
    markKilled out env (killStatus exit)
  else if exit == 0 || execute.isSome then
    let row := Lean.Json.mkObj [("check-time", jsonRound 6 seconds),
      ("peak-rss", Lean.toJson peak), ("shards", Lean.toJson shards)]
    let row := match execute with
      | some t => row.setObjVal! "execute-time" (jsonRound 6 t)
      | none => row
    writeEntry out env <|
      if exit == 0 then row else row.setObjVal! "status" (.str "rejected")
    if exit != 0 then
      IO.eprintln s!"[bench] whole-env ixvm check rejected (exit {exit})"
  else
    IO.eprintln s!"[bench] whole-env ixvm check failed before execution (exit {exit})"

/-- Parse `--constants`: `all` (the default) is the env's shared
    constants, `none` is no constant rows, anything else a comma list. -/
def parseConstants (env : String) (flag : Option String) : Array String :=
  match flag with
  | none | some "all" => (selectNames env).map (·.name)
  | some "none" => #[]
  | some list => Ix.Cli.ConstsFile.parseCommaList list

def runBenchRunCmd (p : Cli.Parsed) : IO UInt32 := do
  let backend := (p.flag? "backend").map (·.as! String) |>.getD ""
  let some spec := findBackend backend
    | p.printError s!"error: unknown backend '{backend}' (see backendSpecs)"
      return exitUsage
  let some info := findEnv ((p.flag? "env").map (·.as! String) |>.getD "InitStd")
    | p.printError "error: unknown env (see envSpecs)"
      return exitUsage
  let env := info.name
  let repo := (p.flag? "repo").map (·.as! String) |>.getD "."
  let out := (p.flag? "out").map (·.as! String) |>.getD "bench.json"
  let names := if spec.hasConstants
    then parseConstants env ((p.flag? "constants").map (·.as! String)) else #[]
  let envRow := !p.hasFlag "no-env-row"
  IO.eprintln s!"[bench] run {backend}-{env}: {names.size} constant row(s){if envRow then " + env row" else ""}"

  -- Fresh accumulator per run.
  if ← FilePath.pathExists out then IO.FS.removeFile out
  let namesFile := out ++ ".names.txt"
  let ix ← resolveBin repo "ix"

  match backend with
  | "compile" =>
    -- The compile IS the benchmark: always fresh, row keyed by the env name.
    -- Measure the default compiler, including its certification checks.
    if envRow then
      let exit ← runTool ix
        #["compile", s!"{repo}/{info.module}", "--out", s!"{repo}/{env}.ixe",
          "--json", out, "--json-name", info.name]
      if exit != 0 then
        IO.eprintln s!"[bench] ix compile failed (exit {exit})"
        return 1
  | "decompile" =>
    -- The inverse of compile: consume the env's `.ixe` (the compile run's
    -- fresh artifact) and decompile it back to Lean constants. A malformed
    -- decompile exits nonzero and fails the job; deep roundtrip fidelity is
    -- gated by the canonical roundtrip checks (`ix validate` / the
    -- roundtrip tests), not measured here.
    if envRow then
      let ixe ← ensureIxe repo info ((p.flag? "ixe").map (·.as! String))
      let exit ← runTool ix
        #["decompile", ixe, "--json", out, "--json-name", info.name]
      if exit != 0 then
        IO.eprintln s!"[bench] ix decompile failed (exit {exit})"
  | "ixvm-ooc" =>
    let ixe ← ensureIxe repo info ((p.flag? "ixe").map (·.as! String))
    if envRow then
      -- Whole-env row, plus the per-constant attribution CSV the compare
      -- drill-down reads (top movers).
      let exit ← runTool ix
        #["check-lean", ixe, "--anon", "--json", out, "--json-name", info.name,
          "--per-const", s!"{out}.perconst.csv"]
      if exit != 0 && exit != exitRejected then
        IO.eprintln s!"[bench] whole-env check failed (exit {exit})"
    -- One full-closure row per constant, from ONE process for all names:
    -- the check-lean rows mode attributes per name internally with the env
    -- loaded once — a per-constant process would re-pay the env parse per
    -- name — and out-of-circuit checks stay small.
    if !names.isEmpty then
      IO.FS.writeFile namesFile ("\n".intercalate names.toList ++ "\n")
      let exit ← runTool ix
        #["check-lean", ixe, "--anon", "--consts-file", namesFile, "--json", out]
      if exit != 0 && exit != exitRejected then
        IO.eprintln s!"[bench] per-constant checks failed (exit {exit})"
  | "ixvm" =>
    let ixe ← ensureIxe repo info ((p.flag? "ixe").map (·.as! String))
    runIxvmConstants ix ixe out names
    if envRow then runIxvmEnv ix ixe out env
  | other =>
    p.printError s!"error: backend '{other}' has no runner"
    return exitUsage

  -- Every selected row owes a result.
  let code ← gate out (if envRow then names.push env else names)
  if code == 0 || code == exitRejected then
    saveBaseline out s!"{backend}-{env}"
  return code

end Ix.Cli.BenchCmd

open Ix.Cli.BenchCmd in
def benchRunCmd : Cli.Cmd := `[Cli|
  "run" VIA runBenchRunCmd;
  "Execute one benchmark cell (backend × env): the env's selected constant rows and its env row, writing benchmark results JSON. Exits 0 on success (rows saved as the local baseline), 3 when the kernel rejected any constant, 1 when a selected row was not produced."

  FLAGS:
    backend      : String; "ixvm | ixvm-ooc | compile | decompile"
    env          : String; "Benchmark env from the registry (default: InitStd)"
    constants    : String; "Constant rows: `all` (default: the env's shared constants), `none`, or comma-separated names (same grammar as the tools' --consts). Ignored by backends without constant rows."
    "no-env-row";          "Skip the env row (the whole-env measurement)"
    out          : String; "Benchmark results JSON output path (default: bench.json)"
    repo         : String; "Checkout to benchmark: tools resolve from <repo>/.lake/build/bin first, then PATH (default: .)"
    ixe          : String; "Path to an existing .ixe env to use (default: compile <env> fresh; ignored by the compile backend)"
]
