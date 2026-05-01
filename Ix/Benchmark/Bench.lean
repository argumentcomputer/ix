module
public import Ix.Address
public import Ix.Meta
public import Ix.Cronos
public import Ix.Address
public import Batteries

public import Ix.Benchmark.Report

public section

open Batteries (RBMap)

/-!
# Benchmarking library modeled after Criterion in Rust and Haskell

## Quick start

Simple benchmark of a pure function:

```
import Ix.Benchmark.Bench
open BgroupM

def main : IO Unit := do
  let _ ← bgroup "sorting" {} do
    bench "List.mergeSort 1000" List.mergeSort (List.range 1000)
    bench "List.mergeSort 10000" List.mergeSort (List.range 10000)
```

With throughput, iterating over input sizes:

```
import Ix.Benchmark.Bench
open BgroupM

def sizes := #[1000, 10000, 100000]

def main : IO Unit := do
  let _ ← bgroup "sorting" { avgThroughput := true, report := true } do
    for n in sizes do
      throughput (.Elements n.toUInt64 "items")
      bench s!"mergeSort n={n}" List.mergeSort (List.range n)
```

## Verbosity

Three levels controlled by `Config.verbosity` or the `BENCH_VERBOSITY` env var
(env var overrides `Config` default). See `getConfigEnv` and the `Verbosity`
enum doc comments for details.

- `quiet`   — only per-bench summary lines (time / thrpt / change / perf note)
- `normal`  — default; adds warmup + running lines, plus the outlier-variance warning when moderate or severe
- `verbose` — adds R² alongside the time line, always prints outlier-variance + Tukey breakdown

Example: `BENCH_VERBOSITY=v lake exe bench-shardmap`

## Limitations
- Measures time in nanoseconds using `IO.monoNanosNow`, which is less precise than the picoseconds used in Criterion.rs
-/

/--
Computes the result and then wraps the return type in IO. This prevents Lean from optimizing away the function call due to an unused return value.
-/
@[never_extract, noinline]
def blackBoxIO (f : α → β) (a : α) : IO β := do
  pure $ f a

/--
A benchmark group defines a collection of related benchmarks that share a configuration, such as number of samples and noise threshold
-/
structure BenchGroup where
  name : String
  config : Config

/--
A registered benchmark ready to run. Its function and argument are held inside
the `run` closure, so one `bgroup` can collect benches with different input
and output types in a single `Array`:

```
bench "sort ints"   (List.mergeSort (α := Int))    [3, 1, 2]
bench "length str"  String.length                  "hello"
```
-/
structure Benchmarkable where
  name : String
  /-- Runs one iteration. Pure functions are wrapped in `blackBoxIO` so the
      compiler can't elide the call. -/
  run : IO Unit
  /-- If `true`, this bench runs in one-shot mode (a single un-sampled
      iteration) even when the group is otherwise sampled. Set to `true` on
      individual slow stages like proof generation. -/
  oneShot : Bool := false

/-- Runs the benchmark repeatedly for `warmupTime` seconds and returns the
    mean per-iteration time in nanoseconds. Iteration counts increase linearly
    (1, 2, 3, 4, …) between clock checks to minimize the overhead of
    `IO.monoNanosNow` syscalls. -/
def BenchGroup.warmup (bg : BenchGroup) (bench : Benchmarkable) (style : CliStyle) (benchId : String) : IO Float := do
  style.printEphemeral s!"Benchmarking {benchId}: Warming up for {bg.config.warmupTime.floatPretty 2}s"
  let warmupNanos := Cronos.secToNano bg.config.warmupTime
  let startTime ← IO.monoNanosNow
  let mut totalIters : Nat := 0
  let mut elapsed : Nat := 0
  let mut batchSize : Nat := 1
  while elapsed < warmupNanos do
    for _ in List.range batchSize do
      bench.run
    totalIters := totalIters + batchSize
    let now ← IO.monoNanosNow
    elapsed := now - startTime
    batchSize := batchSize + 1
  let mean := Float.ofNat elapsed / Float.ofNat (totalIters.max 1)
  return mean

-- Formats a sample-iters array as a compact preview: first 3 entries,
-- then `...`, then the last entry (e.g. `[94, 188, 282, ..., 9400]`).
def formatItersPreview (iters : Array Nat) : String :=
  if iters.size ≤ 4 then
    s!"[{", ".intercalate (iters.toList.map toString)}]"
  else
    let head := (iters.extract 0 3).toList.map toString
    s!"[{", ".intercalate head}, ..., {iters.back!}]"

-- Core sampling loop that runs the benchmark function and returns the array of measured timings
def runSample (sampleIters : Array Nat) (bench : Benchmarkable) : IO (Array Nat) := do
  let mut timings : Array Nat := #[]
  for iters in sampleIters do
    let start ← IO.monoNanosNow
    for _i in Array.range iters do
      bench.run
    let finish ← IO.monoNanosNow
    timings := timings.push (finish - start)
  return timings

/--
Runs the sample as a sequence of constant iterations per data point, where the iteration count attempts to fit into the configurable `sampleTime` but cannot be less than 1.

Returns the iteration counts and elapsed time per data point.
-/
def BenchGroup.sampleFlat (bg : BenchGroup) (bench : Benchmarkable)
(warmupMean : Float) (style : CliStyle) (benchId : String) : IO (Array Nat × Array Nat) := do
  let targetTime := bg.config.sampleTime.toNanos
  let timePerSample := targetTime / (Float.ofNat bg.config.numSamples)
  let itersPerSample := (timePerSample / warmupMean).ceil.toUInt64.toNat.max 1
  let totalIters := itersPerSample * bg.config.numSamples
  let expectedTime := warmupMean * Float.ofNat itersPerSample * bg.config.numSamples.toSeconds
  printRunning bg.config style benchId expectedTime totalIters itersPerSample
  let sampleIters := Array.replicate bg.config.numSamples itersPerSample
  if bg.config.verbosity == .verbose then
    IO.println s!"Iterations per sample: {formatItersPreview sampleIters}"
  let timings ← runSample sampleIters bench
  return (sampleIters, timings)

/--
Runs the sample as a sequence of linearly increasing iterations [d, 2d, 3d, ..., Nd] where `N` is the total number of samples and `d` is a factor derived from the warmup iteration time.

The sum of this series should be roughly equivalent to the total `sampleTime`.

Returns the iteration counts and elapsed time per sample.
-/
def BenchGroup.sampleLinear (bg : BenchGroup) (bench : Benchmarkable) (warmupMean : Float) (style : CliStyle) (benchId : String) : IO (Array Nat × Array Nat) := do
  let totalRuns := bg.config.numSamples * (bg.config.numSamples + 1) / 2
  let targetTime := bg.config.sampleTime.toNanos
  -- `d` has a minimum value of 1 if the `warmupMean` is sufficiently large
  -- If so, that likely means the benchmark takes too long and target time should be increased, as well as considering other config options like flat sampling mode
  let d := (targetTime / warmupMean / (Float.ofNat totalRuns)).ceil.toUInt64.toNat.max 1
  let expectedTime := (Float.ofNat totalRuns) * (Float.ofNat d) * warmupMean.toSeconds
  let sampleIters := (Array.range bg.config.numSamples).map (fun x => (x + 1) * d)
  printRunning bg.config style benchId expectedTime sampleIters.sum d
  if bg.config.verbosity == .verbose then
    IO.println s!"Iterations per sample: {formatItersPreview sampleIters}"
  let timings ← runSample sampleIters bench
  return (sampleIters, timings)

/-- Picks a concrete sampling mode for `.auto`: choose linear iff the expected total
    linear-mode time is at most 2× the target sample time, else fall back to
    flat. For `.flat` / `.linear` this returns the user's explicit choice. -/
def chooseSamplingMode (config : Config) (warmupMean : Float) : SamplingMode :=
  match config.samplingMode with
  | .flat => .flat
  | .linear => .linear
  | .auto =>
    let targetTime := config.sampleTime.toNanos
    let totalRuns := config.numSamples * (config.numSamples + 1) / 2
    let d := (targetTime / warmupMean / (Float.ofNat totalRuns)).ceil.toUInt64.toNat.max 1
    let expectedNs := (Float.ofNat totalRuns) * (Float.ofNat d) * warmupMean
    if expectedNs > 2 * targetTime then .flat else .linear

/--
On-disk payload for `sample.{fmt}`. Carries the raw `(iters, time)` data plus
a snapshot of the `Config` used to collect this run, so that a later run can
decide whether it's statistically comparable.

`config.samplingMode` is always the resolved mode (`.flat` or `.linear`);
`.auto` is resolved in `bgroup` before the `SampleRun` is constructed, and the
`Serialize SamplingMode` instance panics if `.auto` ever reaches disk.
-/
structure SampleRun where
  data : Data
  config : Config
  deriving Repr, Lean.ToJson, Lean.FromJson

def putSampleRun (r : SampleRun) : Ixon.PutM Unit := do
  Ixon.Serialize.put r.data
  Ixon.Serialize.put r.config

def getSampleRun : Ixon.GetM SampleRun := do
  let data ← Ixon.Serialize.get
  let config ← Ixon.Serialize.get
  return { data, config }

instance : Ixon.Serialize SampleRun where
  put := putSampleRun
  get := getSampleRun

/-- Compares bench results against prior run, using T-test to determine statistical significance -/
def BenchGroup.compare (bg : BenchGroup) (baseSample : Data) (baseEstimates : Estimates) (avgTimes : Distribution) (gen : StdGen) : ComparisonData :=
  -- Gets `base` data for comparison
  let baseAvgTimes : Distribution := { d := baseSample.d.map (fun (x,y) => Float.ofNat y / Float.ofNat x) }
  -- Then performs statistical analysis
  let (tValue, tDistribution) := tTest avgTimes baseAvgTimes bg.config gen
  let (relativeEstimates, relativeDistributions) := changeEstimates avgTimes baseAvgTimes bg.config gen
  let pValue := tDistribution.pValue tValue
  {
    pValue,
    tDistribution,
    tValue,
    relativeEstimates,
    relativeDistributions,
    significanceThreshold := bg.config.significanceLevel,
    noiseThreshold := bg.config.noiseThreshold,
    baseSample,
    baseAvgTimes,
    baseEstimates
  }

/-- Retrieves prior bench result from disk and runs the comparison. Refuses
    to compare if the base was collected with a different resolved sampling
    mode (flat vs linear), since mixing the two through the same bootstrap
    gives misleading confidence intervals. -/
def BenchGroup.getComparison (bg : BenchGroup) (benchName : String)
    (avgTimes : Distribution) (config : Config) (resolvedMode : SamplingMode)
    (style : CliStyle) : IO (Option ComparisonData) := do
  let benchPath := config.outputDir / bg.name / benchName
  let fileExt := toString config.serde
  -- Base data is at `new` since we haven't written the latest result to disk yet, which moves the prior data to `base`
  let basePath := benchPath / "new"
  if !(← System.FilePath.pathExists (basePath / s!"estimates.{fileExt}")) then
    return none
  let baseRun? : Option SampleRun ← try
    let r : SampleRun ← loadFile config.serde (basePath / s!"sample.{fileExt}")
    pure (some r)
  catch _ =>
    style.overwrite
    IO.eprintln s!"Skipping comparison for {benchName}: failed to parse base sample.{fileExt}"
    pure none
  let some baseRun := baseRun? | return none
  if baseRun.config.samplingMode != resolvedMode then
    style.overwrite
    IO.eprintln s!"Skipping comparison for {benchName}: base ran in {repr baseRun.config.samplingMode} mode, current run is {repr resolvedMode}"
    return none
  let baseEstimates : Estimates ← loadFile config.serde (basePath / s!"estimates.{fileExt}")
  let gen ← IO.stdGenRef.get
  return some $ bg.compare baseRun.data baseEstimates avgTimes gen

def saveComparison (groupName : String) (benchName : String) (comparison : ComparisonData) (config : Config) : IO Unit := do
  let changePath := config.outputDir / groupName / benchName / "change"
  storeFile config.serde comparison.relativeEstimates (changePath / s!"estimates.{toString config.serde}")

def mkDirs (outputDir : System.FilePath) (groupName : String) (benchName : String) : IO (System.FilePath × System.FilePath) := do
  let benchPath := outputDir / groupName / benchName
  let (basePath, changePath, newPath) := (benchPath / "base", benchPath / "change", benchPath / "new")
  IO.FS.createDirAll basePath
  IO.FS.createDirAll changePath
  IO.FS.createDirAll newPath
  return (basePath, newPath)

def moveBaseFile (file : System.FilePath) (baseDir : System.FilePath) : IO Unit := do
  if (← System.FilePath.pathExists file) then
    -- Move prior bench from `new` to `base`, preserving the filename.
    if let some fname := file.fileName then
      IO.FS.rename file (baseDir / fname)

-- Results are always saved to `<outputDir>/<groupName>/<benchName>/new`. If files of the same serde format already exist from a prior run, move them to `base`.
-- `config.samplingMode` must be the resolved mode (`.flat` / `.linear`) — callers must never pass `.auto` here.
def saveMeasurement (groupName : String) (benchName : String) (mData : MeasurementData) (config : Config) : IO Unit := do
  let (basePath, newPath) ← mkDirs config.outputDir groupName benchName
  let fileExt := toString config.serde
  if let some compData := mData.comparison then
    saveComparison groupName benchName compData config
  let (newEstimatesFile, newSampleFile) := (newPath / s!"estimates.{fileExt}", newPath / s!"sample.{fileExt}")
  let newThroughputFile := newPath / s!"throughput.{fileExt}"
  moveBaseFile newSampleFile basePath
  moveBaseFile newEstimatesFile basePath
  moveBaseFile newThroughputFile basePath
  let sampleRun : SampleRun := { data := mData.data, config }
  storeFile config.serde sampleRun newSampleFile
  storeFile config.serde mData.absoluteEstimates newEstimatesFile
  if let some t := mData.throughput then
    storeFile config.serde t newThroughputFile

def oneShotBench (groupName : String) (b : Benchmarkable)
    (tput : Option Throughput) (config : Config) (style : CliStyle) : IO BenchReport := do
  let benchId := s!"{groupName}/{b.name}"
  style.printEphemeral s!"Benchmarking {benchId}"
  if config.verbosity == .verbose then
    IO.println "Sampling mode: one-shot"
  let start ← IO.monoNanosNow
  b.run
  let finish ← IO.monoNanosNow
  let benchTime := finish - start
  style.overwrite
  -- Use the same 24-char column layout as sampled mode
  printBenchLine benchId s!"time:   {Ansi.bold (benchTime.toFloat.formatNanos)}"
  if let some t := tput then
    IO.println s!"{indent24}thrpt:  {Ansi.bold (t.formatRate benchTime.toFloat)}"
  let (basePath, newPath) ← mkDirs config.outputDir groupName b.name
  let oneShotFile := s!"one-shot.{toString config.serde}"
  let newFile := newPath / oneShotFile
  let (baseBench, percentChange) ← if (← System.FilePath.pathExists newFile) then do
    let baseBench : OneShot ← loadFile config.serde newFile
    let baseTime := baseBench.benchTime.toFloat
    let percentChange := (benchTime.toFloat - baseTime) / baseTime
    IO.println s!"{indent24}change: {Ansi.bold (percentChangeToString percentChange)}"
    IO.FS.rename newFile (basePath / oneShotFile)
    pure (some baseBench, some percentChange)
  else
    pure (.none, .none)
  -- One-shot mode embeds throughput inside the OneShot record so there is no
  -- separate throughput file on disk — switching between sample and one-shot
  -- modes never overlaps on the same filename.
  let newBench : OneShot := { benchTime, throughput := tput }
  storeFile config.serde newBench newFile
  let benchReport : BenchReport := {
    function := b.name,
    newBench := (.oneShot newBench),
    baseBench := baseBench.map .oneShot,
    percentChange,
    throughput := tput
  }
  return benchReport

/--
Runs a single benchmark end-to-end: warms up (sampled mode only), takes
measurements, prints the result line, writes timings to disk, and returns the
`BenchReport`. Picks one-shot mode if either `config.oneShot` or
`b.oneShot` is set; otherwise samples according to `config.samplingMode`.
-/
def runSingleBench (groupName : String) (b : Benchmarkable)
    (tput : Option Throughput) (config : Config) (style : CliStyle) : IO BenchReport := do
  let benchId := s!"{groupName}/{b.name}"
  let bg : BenchGroup := { name := groupName, config }
  -- Per-bench override: bench is one-shot if either the group config or the
  -- bench itself is marked one-shot, so a mostly-sampled group can still
  -- include e.g. a slow setup stage that takes seconds per iteration.
  let isOneShot := config.oneShot || b.oneShot
  if isOneShot then
    oneShotBench groupName b tput config style
  else
    -- Ephemeral: "Benchmarking {id}" → overwrite → "Warming up" → overwrite → "Collecting" → overwrite → permanent results
    style.printEphemeral s!"Benchmarking {benchId}"
    let warmupMean ← bg.warmup b style benchId
    -- Resolve `.auto` to a concrete mode now so both sampling and the
    -- downstream regression-vs-mean choice see the same decision.
    let resolvedMode := chooseSamplingMode bg.config warmupMean
    if bg.config.verbosity == .verbose then
      let modeName := match resolvedMode with
        | .flat => "flat"
        | .linear => "linear"
        | .auto => "auto"
      let picked := if bg.config.samplingMode == .auto then " (picked by auto)" else ""
      IO.println s!"Sampling mode: {modeName}{picked}"
    -- From here on use `resolvedConfig` (never `.auto`) so the `SampleRun`
    -- persisted to disk and the regression branch agree on the actual mode.
    let resolvedConfig := { bg.config with samplingMode := resolvedMode }
    let (iters, times) ← match resolvedMode with
      | .flat => bg.sampleFlat b warmupMean style benchId
      | .linear => bg.sampleLinear b warmupMean style benchId
      | .auto => bg.sampleFlat b warmupMean style benchId -- unreachable
    -- Show "Analyzing" ephemeral while bootstrap runs (matches criterion.rs)
    style.printEphemeral s!"Benchmarking {benchId}: Analyzing"
    let data := iters.zip times
    let avgTimes : Distribution := { d := data.map (fun (x,y) => Float.ofNat y / Float.ofNat x) }
    let gen ← IO.stdGenRef.get
    let mut (distributions, estimates) := avgTimes.estimates resolvedConfig gen
    let mut rSquared : Option Float := none
    if resolvedMode == .linear
    then
      let data' : Data := { d := data }
      let (distribution, slope, r2) := data'.regression resolvedConfig gen
      estimates := { estimates with slope := .some slope }
      distributions := { distributions with slope := .some distribution }
      rSquared := some r2
    -- Outlier analysis: classify per-sample average times and compute the
    -- variance-inflation metric (consumed by `printResults` under the verbosity gate).
    let outliers := avgTimes.classifyOutliers
    let ov := outlierVariance estimates.mean estimates.stdDev (Float.ofNat resolvedConfig.numSamples)
    let comparisonData : Option ComparisonData ← bg.getComparison b.name avgTimes resolvedConfig resolvedMode style
    let measurement : MeasurementData :=  {
      data := { d := data },
      avgTimes,
      absoluteEstimates := estimates,
      distributions,
      comparison := comparisonData
      throughput := tput
      rSquared,
      outlierVariance := some ov,
      outliers := some outliers
    }
    style.overwrite
    printResults groupName resolvedConfig b.name measurement
    saveMeasurement groupName b.name measurement resolvedConfig
    return {
      function := b.name,
      newBench := (.sample estimates),
      baseBench := (comparisonData.map (.sample ·.baseEstimates)),
      percentChange := comparisonData.map (·.relativeEstimates.mean.pointEstimate),
      throughput := tput
    }

/-!
## Monadic bgroup builder

Inside a `bgroup` do-block, benches run in the order they appear. `benchStep`
returns the result of its function so you can feed it to the next stage with
`let x ← benchStep …`; `bench` is the discard-the-result variant. `throughput`
and `skipE2E` / `countInE2E` are stateful toggles — they affect every bench
that comes after the call, so you can set them once and register several
benches, or flip them between registrations.
-/

/-- Internal state threaded through a `bgroup` do-block. -/
structure GroupState where
  /-- Group name, used when forming per-bench `benchId`s. -/
  groupName : String
  config : Config
  /-- Reports collected as each bench runs, in declaration order. -/
  reports : Array BenchReport := #[]
  /-- Sum of per-bench times (ns) for benches that were counted toward the
      end-to-end total. Each bench reads `config.countInE2E` when it runs
      (flip with `skipE2E` / `countInE2E`) and adds its time here if set.
      Reported as the e2e total when `config.e2e` is on. -/
  e2eSumNs : Float := 0.0

/-- Monad used inside a `bgroup` do-block. -/
abbrev BgroupM := StateT GroupState IO

namespace BgroupM

/-- Attach throughput info to subsequent benches in this group. Each bench
    records whatever throughput is current when it runs, so setting this
    in the middle of a group only affects benches that come after. -/
def throughput (t : Throughput) : BgroupM Unit :=
  modify fun s => { s with config := { s.config with throughput := some t } }

/-- Stops attaching throughput info to subsequent benches. -/
def clearThroughput : BgroupM Unit :=
  modify fun s => { s with config := { s.config with throughput := none } }

/-- Stops subsequent benches from contributing to the end-to-end total (when
    `config.e2e` is on). Pair with `countInE2E` to flip back on. Typical use:
    group side-benches (micro-measurements already covered by a bigger
    pipeline stage) under `skipE2E` so they don't double-count. -/
def skipE2E : BgroupM Unit :=
  modify fun s => { s with config := { s.config with countInE2E := false } }

/-- Resumes counting subsequent benches toward the end-to-end total. -/
def countInE2E : BgroupM Unit :=
  modify fun s => { s with config := { s.config with countInE2E := true } }

/-- Runs `b` via `runSingleBench`, appends the resulting `BenchReport` to the
    group state, adds the bench's time to the e2e total if `countInE2E` is
    set, and returns the `β` the bench stashed in `resultRef`. -/
def runCapturedBench (b : Benchmarkable) (resultRef : IO.Ref (Option β)) : BgroupM β := do
  let st ← get
  let style : CliStyle := { overwriteEnabled := st.config.verbosity != .verbose }
  let report ← runSingleBench st.groupName b st.config.throughput st.config style
  IO.println ""
  let delta := if st.config.countInE2E then report.newBench.getTime else 0.0
  modify fun s => { s with
    reports  := s.reports.push report
    e2eSumNs := s.e2eSumNs + delta
  }
  match ← resultRef.get with
  | some r => return r
  | none => throw (IO.userError s!"benchStep '{b.name}' produced no result")

/--
Benchmarks `fn arg` and returns the last iteration's result so it can feed the
next pipeline stage. Equivalent to a `let x := fn arg` that also times the
call:

```
bgroup "pipeline" {} do
  let parsed  ← benchStep "parse"    parseFile   input
  let checked ← benchStep "check"    typecheck   parsed
  let _       ← benchStep "emit"     emit        checked
```

Pass `oneShot := true` for stages whose single iteration already takes long
enough that sampling would be wasteful.
-/
def benchStep (name : String) (fn : α → β) (arg : α) (oneShot : Bool := false) : BgroupM β := do
  let resultRef ← IO.mkRef (none : Option β)
  let run : IO Unit := do resultRef.set (some (← blackBoxIO fn arg))
  runCapturedBench { name, run, oneShot } resultRef

/-- Like `benchStep`, but for `fn : α → IO β`. The final iteration's `β` is
    captured and returned; every iteration's side effects have already run
    during measurement. -/
def benchStepIO (name : String) (fn : α → IO β) (arg : α) (oneShot : Bool := false) : BgroupM β := do
  let resultRef ← IO.mkRef (none : Option β)
  let run : IO Unit := do resultRef.set (some (← fn arg))
  runCapturedBench { name, run, oneShot } resultRef

/--
Like `benchStep`, but for `fn : α → Except ε β`. Returns `β` on success and
throws an `IO.userError` carrying `{name}: {e}` on `.error`, so a pipeline
can chain through fallible stages without an extra `match`:

```
let decls ← benchStepE "simplify" Toplevel.checkAndSimplify toplevel
-- decls : TypedDecls (unwrapped from Except CheckError TypedDecls)
```
-/
def benchStepE [ToString ε] (name : String) (fn : α → Except ε β) (arg : α)
    (oneShot : Bool := false) : BgroupM β := do
  match ← benchStep name fn arg oneShot with
  | .ok x    => return x
  | .error e => throw (IO.userError s!"{name}: {e}")

/-- Benchmarks `fn arg` and discards the result. Use this when a stage's
    output isn't needed downstream — surrounding `skipE2E` / `countInE2E`
    controls whether the time counts toward the end-to-end total. -/
def bench (name : String) (fn : α → β) (arg : α) (oneShot : Bool := false) : BgroupM Unit := do
  let _ ← benchStep name fn arg oneShot
  return ()

/-- Like `bench`, but for `fn : α → IO β`. -/
def benchIO (name : String) (fn : α → IO β) (arg : α) (oneShot : Bool := false) : BgroupM Unit := do
  let _ ← benchStepIO name fn arg oneShot
  return ()

end BgroupM

/-- Runs the benches in `action` under the given name and config, then — after
    all benches have finished — prints the average throughput, the end-to-end
    total, and the Markdown comparison table, each gated by its corresponding
    `config` flag. Returns the collected `BenchReport`s. -/
def bgroup (name: String) (config : Config := {})
    (action : BgroupM Unit) : IO $ Array BenchReport := do
  let config ← getConfigEnv config
  let (_, state) ← action.run { groupName := name, config }
  let reports := state.reports
  if config.avgThroughput then
    match weightedAverageThroughput reports with
    | some (t, primaryAvg, secondaryAvg) =>
      IO.println s!"Average throughput: {t.formatRateValue primaryAvg}"
      -- For ElementsAndBytes, also print the secondary bytes/s average
      if let some bytesAvg := secondaryAvg then
        IO.println s!"Average throughput (bytes): {Float.formatBytesRate bytesAvg}"
    | none =>
      IO.eprintln "Average throughput: skipped (no throughput set, or mixed Throughput variants across benches)"
  -- End-to-end total: sum of per-stage mean/one-shot times, compared against
  -- the prior saved total for change tracking. Not itself sampled.
  let reports ← if config.e2e then do
    let totalNs : Float := state.e2eSumNs
    let reportDir := config.outputDir / name
    let e2eFile := reportDir / s!"e2e.{toString config.serde}"
    let priorTotal : Option Float ← if ← System.FilePath.pathExists e2eFile then do
      let prior : E2ETotal ← loadFile config.serde e2eFile
      pure (some prior.totalNs)
    else pure none
    let percentChange : Option Float := priorTotal.bind fun prior =>
      if prior == 0 then none else some ((totalNs - prior) / prior)
    -- Summary line: matches per-bench 24-char column layout.
    printBenchLine s!"{name}/end-to-end" s!"time:   {Ansi.bold totalNs.formatNanos}"
    if let some pc := percentChange then
      IO.println s!"{indent24}change: {Ansi.bold (percentChangeToString pc)}"
    IO.println ""
    -- Persist for next run, then (if we're writing a report) append the total
    -- as a synthetic row so the Markdown table includes it.
    IO.FS.createDirAll reportDir
    storeFile config.serde { totalNs : E2ETotal } e2eFile
    let totalToOneShot (t : Float) : BenchResult :=
      .oneShot { benchTime := t.round.toUInt64.toNat, throughput := none }
    pure <| reports.push {
      function     := "end-to-end"
      newBench     := totalToOneShot totalNs
      baseBench    := priorTotal.map totalToOneShot
      percentChange
      throughput   := none
    }
  else pure reports
  if config.report then
    -- Plaintext table (`## {name}\n\n...`) to stdout; GitHub-flavored Markdown
    -- (table wrapped in `<details>`) to disk for the PR-workflow comment.
    IO.println (mkReportPlain name reports)
    let reportDir := config.outputDir / name
    IO.FS.createDirAll reportDir
    IO.FS.writeFile (reportDir / "report.md") (mkReportMarkdown name reports)
  return reports

end
