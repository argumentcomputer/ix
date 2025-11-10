import Ix.Ixon
import Ix.Address
import Ix.Meta
import Ix.CompileM
import Ix.Cronos
import Ix.Address
import Batteries

import Ix.Benchmark.Ixon
import Lean.Data.Json.FromToJson
import Lean.Data.Json.FromToJson.Basic
import Ix.Benchmark.Tukey

open Batteries (RBMap)

/-!
# Benchmarking library modeled after Criterion in Haskell and Rust

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

inductive BenchFn ( α β : Type) where
| pure (fn : α → β)
| io (fn : α → IO β)

structure Benchmarkable (α β : Type) where
  name : String
  func : BenchFn α β
  arg : α

/--
Creates a `Benchmarkable` instance. Use with pure functions, which will later be called with `blackBoxIO` to prevent compiler optimizations.
-/
def bench (name : String) (fn : α → β) (arg : α) : Benchmarkable α β := { name, func := BenchFn.pure fn, arg }

/--
Creates a `Benchmarkable` instance. Use with functions that return IO, as they don't need to be black boxed.
-/
def benchIO (name : String) (fn : α → IO β) (arg : α) : Benchmarkable α β :=  { name, func := BenchFn.io fn, arg }

/-- If the function is pure, we need to wrap it in `blackBoxIO` so that Lean doesn't optimize away the result -/
def Benchmarkable.getFn ( bench: Benchmarkable α β) : α → IO β :=
  match bench.func with
  | .pure f => blackBoxIO f
  | .io f => f

-- TODO: According to Criterion.rs docs the warmup iterations should increase linearly until the warmup time is reached, rather than one iteration per time check
def BenchGroup.warmup (bg : BenchGroup) (bench : Benchmarkable α β) : IO Float := do
  IO.println s!"Warming up for {bg.config.warmupTime.floatPretty 2}s"
  let mut count := 0
  let warmupNanos := Cronos.secToNano bg.config.warmupTime
  let mut elapsed := 0
  let func := bench.getFn
  let startTime ← IO.monoNanosNow
  while elapsed < warmupNanos do
    let _res ← func bench.arg
    let now ← IO.monoNanosNow
    count := count + 1
    elapsed := now - startTime
  let mean := Float.ofNat elapsed / Float.ofNat count
  --IO.println s!"{bench.name} warmup avg: {mean}ns"
  return mean

-- TODO: Combine with other sampling functions, DRY
-- TODO: Recommend sample count if expectedTime >>> bg.config.sampleTime (i.e. itersPerSample == 1)
/--
Runs the sample as a sequence of constant iterations per data point, where the iteration count attempts to fit into the configurable `sampleTime` but cannot be less than 1.

Returns the iteration counts and elapsed time per data point.
-/
def BenchGroup.sampleFlat (bg : BenchGroup) (bench : Benchmarkable α β)
(warmupMean : Float) : IO (Array Nat × Array Nat) := do
  let targetTime := bg.config.sampleTime.toNanos
  let timePerSample := targetTime / (Float.ofNat bg.config.numSamples)
  let itersPerSample := (timePerSample / warmupMean).ceil.toUInt64.toNat.max 1
  let totalIters := itersPerSample * bg.config.numSamples
  let expectedTime := warmupMean * Float.ofNat itersPerSample * bg.config.numSamples.toSeconds
  if itersPerSample == 1
  then
    IO.eprintln s!"Warning: Unable to complete {bg.config.numSamples} samples in {bg.config.sampleTime.floatPretty 2}s. You may wish to increase target time to {expectedTime.floatPretty 2}s"
  IO.println s!"Running {bg.config.numSamples} samples in {expectedTime.floatPretty 2}s ({totalIters.natPretty} iterations)\n"
  --IO.println s!"Flat sample. Iters per sample: {itersPerSample}"
  let func := bench.getFn
  let mut timings : Array Nat := #[]
  let sampleIters := Array.replicate bg.config.numSamples itersPerSample
  for iters in sampleIters do
    let start ← IO.monoNanosNow
    for _i in Array.range iters do
      let _res ← func bench.arg
    let finish ← IO.monoNanosNow
    timings := timings.push (finish - start)
  return (sampleIters, timings)

/--
Runs the sample as a sequence of linearly increasing iterations [d, 2d, 3d, ..., Nd] where `N` is the total number of samples and `d` is a factor derived from the warmup iteration time.

The sum of this series should be roughly equivalent to the total `sampleTime`.

Returns the iteration counts and elapsed time per sample.
-/
def BenchGroup.sampleLinear (bg : BenchGroup) (bench : Benchmarkable α β) (warmupMean : Float) : IO (Array Nat × Array Nat) := do
  let totalRuns := bg.config.numSamples * (bg.config.numSamples + 1) / 2
  let targetTime := bg.config.sampleTime.toNanos
  let d := (targetTime / warmupMean / (Float.ofNat totalRuns)).ceil.toUInt64.toNat.max 1
  let expectedTime := (Float.ofNat totalRuns) * (Float.ofNat d) * warmupMean.toSeconds
  let sampleIters := (Array.range bg.config.numSamples).map (fun x => (x + 1) * d)
  -- `d` has a minimum value of 1 if the `warmupMean` is sufficiently large
  -- If so, that likely means the benchmark takes too long and target time should be increased, as well as other config options like flat sampling mode
  if d == 1
  then
    IO.eprintln s!"Warning: Unable to complete {bg.config.numSamples} samples in {bg.config.sampleTime.floatPretty 2}s. You may wish to increase target time to {expectedTime.floatPretty 2}s"
  IO.println s!"Running {bg.config.numSamples} samples in {expectedTime.floatPretty 2}s ({sampleIters.sum.natPretty} iterations)\n"
  --IO.println s!"Linear sample. Iters increase by a factor of {d} per sample"
  let func := bench.getFn
  let mut timings : Array Nat := #[]
  for iters in sampleIters do
    let start ← IO.monoNanosNow
    for _i in Array.range iters do
      let _res ← func bench.arg
    let finish ← IO.monoNanosNow
    timings := timings.push (finish - start)
  return (sampleIters, timings)

def BenchGroup.sample (bg : BenchGroup) (bench : Benchmarkable α β) (warmupMean : Float) : IO (Array Nat × Array Nat) := do
  match bg.config.samplingMode with
  | .flat => bg.sampleFlat bench warmupMean
  | .linear => bg.sampleLinear bench warmupMean

-- TODO
inductive Throughput where
| Bytes (n : UInt64)
| BytesDecimal (n : UInt64)
| Elements (n : UInt64)
| Bits (n : UInt64)

structure MeasurementData where
  data : Data
  avgTimes : Distribution
  absoluteEstimates : Estimates
  distributions : Distributions
  comparison : Option ComparisonData
  throughput : Option Throughput

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

def loadJson (α) [Lean.FromJson α] (path : System.FilePath) : IO α := do
  let jsonStr ← IO.FS.readFile path
  let json ← match Lean.Json.parse jsonStr with
  | .ok js => pure js
  | .error e => throw $ IO.userError s!"{repr e}"
  match Lean.fromJson? json with
  | .ok d => pure d
  | .error e => throw $ IO.userError s!"{repr e}"

def loadIxon (α) [Ixon.Serialize α] (path : System.FilePath) : IO α := do
  let ixonBytes ← IO.FS.readBinFile path
  match Ixon.de ixonBytes with
  | .ok d => pure d
  | .error e => throw $ IO.userError s!"expected a, go {repr e}"

-- TODO: Don't compare if different sampling modes were used
/-- Retrieves prior bench result from disk and runs the comparison -/
def BenchGroup.getComparison (bg : BenchGroup) (benchName : String) (avgTimes : Distribution) (config: Config) : IO (Option ComparisonData) := do
  let benchPath := System.mkFilePath [".", ".lake", "benches", benchName]
  let fileExt := toString config.serde
  -- Base data is at `new` since we haven't written the latest result to disk yet, which moves the prior data to `base`
  let basePath := benchPath / "new"
  if (← System.FilePath.pathExists (basePath / s!"estimates.{fileExt}")) then do
    let (baseSample, baseEstimates) ← match config.serde with
    | .json => do
      let baseSample ← loadJson Data (basePath / "sample.json")
      let baseEstimates ← loadJson Estimates (basePath / "estimates.json")
      pure (baseSample, baseEstimates)
    | .ixon => do
      let baseSample ← loadIxon Data (basePath / "sample.ixon")
      let baseEstimates ← loadIxon Estimates (basePath / "estimates.ixon")
      pure (baseSample, baseEstimates)
    let gen ← IO.stdGenRef.get
    return some $ bg.compare baseSample baseEstimates avgTimes gen
  else
    return none

inductive ComparisonResult where
| Improved
| Regressed
| NonSignificant

def compareToThreshold (estimate : Estimate) (noiseThreshold : Float) : ComparisonResult :=
  let ci := estimate.confidenceInterval
  let (lb, ub) := (ci.lowerBound, ci.upperBound)
  let noiseNeg := noiseThreshold.neg

  if lb < noiseNeg && ub < noiseNeg
  then
    ComparisonResult.Improved
  else if lb > noiseThreshold && ub > noiseThreshold
  then
    ComparisonResult.Regressed
  else
    ComparisonResult.NonSignificant

-- TODO: Print ~24 whitespace characters before time, change, regression
def BenchGroup.printResults (bg : BenchGroup) (benchName : String) (m : MeasurementData) : IO Unit := do
  let estimates := m.absoluteEstimates
  let typicalEstimate := estimates.slope.getD estimates.mean
  IO.println s!"{bg.name}/{benchName}"
  let lb := typicalEstimate.confidenceInterval.lowerBound.formatNanos
  let pointEst := typicalEstimate.pointEstimate.formatNanos
  let ub := typicalEstimate.confidenceInterval.upperBound.formatNanos
  IO.println s!"time:   [{lb} {pointEst} {ub}]"
  if let some comp := m.comparison
  then
    let diffMean := comp.pValue < comp.significanceThreshold
    let meanEst := comp.relativeEstimates.mean
    let pointEst := (meanEst.pointEstimate * 100).floatPretty 4
    let lb := (meanEst.confidenceInterval.lowerBound * 100).floatPretty 4
    let ub := (meanEst.confidenceInterval.upperBound * 100).floatPretty 4
    let symbol := if diffMean then "<" else ">"
    IO.println s!"change: [{lb}% {pointEst}% {ub}%] (p = {comp.pValue.floatPretty 2} {symbol} {comp.significanceThreshold.floatPretty 2})"
    let explanation := if diffMean
    then
      "No change in performance detected"
    else
      match compareToThreshold meanEst comp.noiseThreshold with
      | ComparisonResult.Improved => "Performance has improved"
      | ComparisonResult.Regressed => "Performance has regressed"
      | ComparisonResult.NonSignificant => "Change within noise threshold"
    IO.println explanation
  IO.println ""
  m.avgTimes.tukey

/-- Writes JSON to disk at `benchPath/fileName` -/
def storeJson [Lean.ToJson α] (data : α) (benchPath : System.FilePath) : IO Unit :=
  let json := Lean.toJson data
  IO.FS.writeFile benchPath json.pretty

/-- Writes Ixon to disk at `benchPath/fileName` -/
def storeIxon [Ixon.Serialize α] (data : α) (benchPath : System.FilePath) : IO Unit :=
  let ixon := Ixon.ser data
  IO.FS.writeBinFile benchPath ixon

-- TODO: Write sampling mode and config in `sample.json` for comparison
def saveComparison (benchName : String) (comparison : ComparisonData) (config : Config) : IO Unit := do
  let changePath := System.mkFilePath [".", ".lake", "benches", benchName, "change"]
  match config.serde with
  | .json => storeJson comparison.relativeEstimates (changePath / "estimates.json")
  | .ixon => storeIxon comparison.relativeEstimates (changePath / "estimates.ixon")

-- Results are always saved to `.lake/benches/<benchName>/new`. If files of the same serde format already exist from a prior run, move them to `base`
def saveResults (benchName : String) (m : MeasurementData) (config : Config) : IO Unit := do
  let benchPath := System.mkFilePath [".", ".lake", "benches", benchName]
  let (basePath, changePath, newPath) := (benchPath / "base", benchPath / "change", benchPath / "new")
  let (baseDir, changeDir, newDir) := (basePath.toString, changePath.toString, newPath.toString)
  let _out ← IO.Process.run {cmd := "mkdir", args := #["-p", baseDir, changeDir, newDir] }
  let fileExt := toString config.serde
  if (← System.FilePath.pathExists (newPath / s!"estimates.{fileExt}"))
  then do
    -- Move prior bench from `new` to `base`
    for entry in (← System.FilePath.readDir newDir) do
      let path := entry.path
      if path.extension == fileExt
      then
        let _ ← IO.Process.run { cmd := "mv", args := #[path.toString, baseDir] }
    if let some compData := m.comparison then saveComparison benchName compData config
    else IO.eprintln s!"Error: expected `comparisonData` to write but found none"
  match config.serde with
  | .json =>
    storeJson m.data (newPath / "sample.json")
    storeJson m.absoluteEstimates (newPath / "estimates.json")
  | .ixon =>
    storeIxon m.data (newPath / "sample.ixon")
    storeIxon m.absoluteEstimates (newPath / "estimates.ixon")

structure OneShot where
  benchTime : Nat
deriving Lean.ToJson, Lean.FromJson

def getOneShot: Ixon.GetM OneShot := do
  return { benchTime := (← Ixon.Serialize.get) }

instance : Ixon.Serialize OneShot where
  put os := Ixon.Serialize.put os.benchTime
  get := getOneShot

def oneShotBench {α β : Type} (bench: Benchmarkable α β) (config : Config) : IO Unit := do
  let start ← IO.monoNanosNow
  let _res ← bench.getFn bench.arg
  let finish ← IO.monoNanosNow
  let benchTime := finish - start
  IO.println s!"time:   {benchTime.toFloat.formatNanos}"
  let benchPath := System.mkFilePath [".", ".lake", "benches", bench.name]
  let fileExt := toString config.serde
  let basePath := benchPath / "new" / s!"one-shot.{fileExt}"
  if (← System.FilePath.pathExists basePath) then do
    let baseBench ← match config.serde with
    | .json => loadJson OneShot basePath
    | .ixon => loadIxon OneShot basePath
    let baseTime := baseBench.benchTime.toFloat
    let percentChange := 100 * (benchTime.toFloat - baseTime) / baseTime
    let percentChangeStr := percentChange.floatPretty 2
    let percentChangeStr :=
      if percentChange < 0 then s!"{percentChangeStr.drop 1}% faster"
      else if percentChange > 0 then s!"{percentChangeStr}% slower"
      else "No change"
    IO.println s!"change: {percentChangeStr}"
    let _ ← IO.Process.run { cmd := "mv", args := #[basePath.toString, (benchPath / "base").toString] }
  let newBench : OneShot := { benchTime }
  IO.println ""
  match config.serde with
  | .json => storeJson newBench basePath
  | .ixon => storeIxon newBench basePath

-- TODO: Autoscale column width based on longest name. GitHub  and editor markdown modes should do this automatically, but needed for pretty CLI output
/--
Generates a Markdown table with comparative benchmark timings based on the results on disk.
Each table row contains the benchmakr function name, the new timing, the base timing, and the percent change between the two.
-/
def mkReport (name : String) (benches: List (Benchmarkable α β)) (config : Config) : IO Unit := do
  let path := System.mkFilePath [".", ".lake", "benches"]
  let mut table :=
    "| Function | New Benchmark | Base Benchmark | % change |\n"
    ++
    "|----------|---------------|----------------|--------|\n"

  for bench in benches do
    let benchPath := path / bench.name
    let newPath := benchPath / "new"
    let basePath := benchPath / "base"
    let row : String ← do
      if config.oneShot then
        let fileName := s!"one-shot.{toString config.serde}"
        let oneShotNew ← match config.serde with
        | .json => loadJson OneShot (newPath / fileName)
        | .ixon => loadIxon OneShot (newPath / fileName)
        let newTime := oneShotNew.benchTime.toFloat
        let mut row := s!"| {bench.name} | {newTime.formatNanos} | "
        if (← System.FilePath.pathExists (basePath /
        fileName)) then
          let oneShotBase ← match config.serde with
          | .json => loadJson OneShot (basePath / fileName)
          | .ixon => loadIxon OneShot (basePath / fileName)
          let baseTime := oneShotBase.benchTime.toFloat
          let percentChange := 100 * (newTime - baseTime) / baseTime
          let percentChangeStr := percentChange.floatPretty 2
          let percentChangeStr :=
            if percentChange < 0 then s!"{percentChangeStr.drop 1}% faster"
            else if percentChange > 0 then s!"{percentChangeStr}% slower"
            else "No change"
          row := row ++ s!"{baseTime.formatNanos} | {percentChangeStr} |\n"
        pure row
      else
        let fileName := s!"estimates.{toString config.serde}"
        let estimatesNew ← match config.serde with
        | .json => loadJson ChangeEstimates (newPath / fileName)
        | .ixon => loadIxon ChangeEstimates (newPath / fileName)
        let newTime := estimatesNew.mean.pointEstimate
        let mut row := s!"| {bench.name} | {newTime.formatNanos} | "
        if (← System.FilePath.pathExists (basePath / fileName )) then
          let estimatesBase ← match config.serde with
          | .json => loadJson ChangeEstimates (basePath / fileName)
          | .ixon => loadIxon ChangeEstimates (basePath / fileName)
          let baseTime := estimatesBase.mean.pointEstimate
          let changePath := benchPath / "change"
          let estimatesChange ← match config.serde with
          | .json => loadJson ChangeEstimates (changePath / fileName)
          | .ixon => loadIxon ChangeEstimates (changePath / fileName)
          let percentChange := estimatesChange.mean.pointEstimate
          let percentChangeStr := percentChange.floatPretty 2
          let percentChangeStr :=
            if percentChange < 0 then s!"{percentChangeStr.drop 1}% faster"
            else if percentChange > 0 then s!"{percentChangeStr}% slower"
            else "No change"
          row := row ++ s!"{baseTime.formatNanos} | {percentChangeStr} |\n"
        else
          row := row ++
            "| |\n"
        pure row
    table := table ++ row
  IO.println $ table ++
    "|----------|---------------|----------------|--------|\n"
  IO.FS.writeFile (System.mkFilePath [".", s!"benchmark-report-{name}.md"]) table

-- TODO: Integrate this with a `lake bench` CLI to set config options via flags
/-- Overrides config values with the corresponding `BENCH_<SETTING>` env vars if they are set -/
def getConfigEnv (config : Config) : IO Config := do
  let serde : SerdeFormat := if (← IO.getEnv "BENCH_SERDE") == some "ixon" then .ixon else config.serde
  let report := if let some val := (← IO.getEnv "BENCH_REPORT") then val == "1" else config.report
  return { config with serde, report }

-- TODO: Make sure compiler isn't caching partial evaluation result for future runs of the same function (measure first vs subsequent runs)
/-- Runs each benchmark in a `BenchGroup` and analyzes the results -/
def bgroup {α β : Type} (name: String) (benches : List (Benchmarkable α β)) (config : Config := {}) : IO Unit := do
  let config ← getConfigEnv config
  let bg : BenchGroup := { name, config }
  IO.println s!"Running bench group {name}\n"
  for b in benches do
    if config.oneShot then
      IO.println s!"{bg.name}/{b.name}"
      oneShotBench b config
    else
      let warmupMean ← bg.warmup b
      IO.println s!"Running {b.name}"
      let (iters, times) ← bg.sample b warmupMean
      let data := iters.zip times
      let avgTimes : Distribution := { d := data.map (fun (x,y) => Float.ofNat y / Float.ofNat x) }
      let gen ← IO.stdGenRef.get
      let mut (distributions, estimates) := avgTimes.estimates bg.config gen
      if bg.config.samplingMode == .linear
      then
        let data' : Data := { d := data }
        let (distribution, slope) := data'.regression bg.config gen
        estimates := { estimates with slope := .some slope }
        distributions := { distributions with slope := .some distribution }
      let comparisonData : Option ComparisonData ← bg.getComparison b.name avgTimes bg.config
      let measurement :=  {
        data := { d := data },
        avgTimes,
        absoluteEstimates := estimates,
        distributions,
        comparison := comparisonData
        throughput := none
      }
      bg.printResults b.name measurement
      IO.println ""
      saveResults b.name measurement config
  if config.report then
    mkReport name benches config
