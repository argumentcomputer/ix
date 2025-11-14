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
def storeJson [Lean.ToJson α] (data : α) (benchPath : System.FilePath) : IO Unit := do
  let json := Lean.toJson data
  IO.FS.writeFile benchPath json.pretty

/-- Writes Ixon to disk at `benchPath/fileName` -/
def storeIxon [Ixon.Serialize α] (data : α) (benchPath : System.FilePath) : IO Unit := do
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
  let (estimatesFile, sampleFile) := (newPath / s!"estimates.{fileExt}", newPath / s!"sample.{fileExt}")
  if (← System.FilePath.pathExists estimatesFile) && (← System.FilePath.pathExists sampleFile)
  then do
    -- Move prior bench from `new` to `base`
    let _ ← IO.Process.run { cmd := "mv", args := #[estimatesFile.toString, sampleFile.toString, baseDir] }
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
deriving Lean.ToJson, Lean.FromJson, Repr

def getOneShot: Ixon.GetM OneShot := do
  return { benchTime := (← Ixon.Serialize.get) }

instance : Ixon.Serialize OneShot where
  put os := Ixon.Serialize.put os.benchTime
  get := getOneShot

-- TODO: Use a typeclass instead?
inductive BenchResult where
| oneShot : OneShot → BenchResult
| sample : Estimates → BenchResult
deriving Repr

structure BenchReport where
  function: String
  newBench : BenchResult
  baseBench : Option BenchResult
  percentChange : Option Float

def oneShotBench {α β : Type} (bench: Benchmarkable α β) (config : Config) : IO BenchReport := do
  let start ← IO.monoNanosNow
  let _res ← bench.getFn bench.arg
  let finish ← IO.monoNanosNow
  let benchTime := finish - start
  IO.println s!"time:   {benchTime.toFloat.formatNanos}"
  let benchPath := System.mkFilePath [".", ".lake", "benches", bench.name]
  let (basePath, changePath, newPath) := (benchPath / "base", benchPath / "change", benchPath / "new")
  let (baseDir, changeDir, newDir) := (basePath.toString, changePath.toString, newPath.toString)
  let _out ← IO.Process.run {cmd := "mkdir", args := #["-p", baseDir, changeDir, newDir] }
  let fileExt := toString config.serde
  let newFile := newPath / s!"one-shot.{fileExt}"
  let (baseBench, percentChange) ← if (← System.FilePath.pathExists newFile) then do
    let baseBench ← match config.serde with
    | .json => loadJson OneShot newFile
    | .ixon => loadIxon OneShot newFile
    let baseTime := baseBench.benchTime.toFloat
    let percentChange := 100 * (benchTime.toFloat - baseTime) / baseTime
    let percentChangeStr := percentChange.floatPretty 2
    let percentChangeStr :=
      if percentChange < 0 then s!"{percentChangeStr.drop 1}% faster"
      else if percentChange > 0 then s!"{percentChangeStr}% slower"
      else "No change"
    IO.println s!"change: {percentChangeStr}"
    let _ ← IO.Process.run { cmd := "mv", args := #[newFile.toString, (benchPath / "base").toString] }
    pure (some baseBench, some percentChange)
  else
    let _ ← IO.Process.run { cmd := "mkdir", args := #["-p", newPath.toString] }
    pure (.none, .none)
  let newBench : OneShot := { benchTime }
  IO.println ""
  match config.serde with
  | .json => storeJson newBench newFile
  | .ixon => storeIxon newBench newFile
  let benchReport : BenchReport := { function := bench.name, newBench := (.oneShot newBench), baseBench := (baseBench).map .oneShot, percentChange }
  return benchReport

structure ColumnWidths where
  function : Nat
  newBench : Nat
  baseBench : Nat
  percentChange : Nat

-- Gets the max lengths of each data type for pretty-printing columns
def getColumnWidths (report : Array BenchReport) : ColumnWidths := Id.run do
  let mut maxFunctionLen := "Function".length
  let mut maxNewLen := "New Benchmark".length
  let mut maxBaseLen := "Base Benchmark".length
  let mut maxPercentLen := "% change".length
  for row in report do
    let fnLen := row.function.length
    if fnLen > maxFunctionLen then maxFunctionLen := fnLen
    let newLen := match row.newBench with
    | .oneShot o => o.benchTime.toFloat.formatNanos.length 
    | .sample s => s.mean.pointEstimate.formatNanos.length
    if newLen > maxNewLen then maxNewLen := newLen
    if let some baseBench := row.baseBench then
      let baseLen := match baseBench with
      | .oneShot o => o.benchTime.toFloat.formatNanos.length
      | .sample s => s.mean.pointEstimate.formatNanos.length
      if baseLen > maxBaseLen then maxBaseLen := baseLen
    if let some percentChange := row.percentChange then
      let percentChangeStr := (percentChange * 100).floatPretty 2
      let percentChangeStr :=
        if percentChange < 0 then s!"{percentChangeStr.drop 1}% faster"
        else if percentChange > 0 then s!"{percentChangeStr}% slower"
        else "No change"
      let percentLen := percentChangeStr.length
      if percentLen > maxPercentLen then
        maxPercentLen := percentLen
  { function := maxFunctionLen, newBench := maxNewLen, baseBench := maxBaseLen, percentChange := maxPercentLen }

-- Centers a string with padded whitespace given the total width
def padWhitespace (input : String) (width : Nat) : String :=
  let padWidth := width - input.length 
  let leftPad := padWidth / 2
  let rightPad := padWidth - leftPad
  String.mk (List.replicate leftPad ' ') ++ input ++ (String.mk (List.replicate rightPad ' '))

def padDashes (width : Nat) : String :=
  String.mk (List.replicate width '-')

-- TODO: Bold the faster result and faster/slower % change
/--
Generates a Markdown table with comparative benchmark timings based on the results on disk.
Each table row contains the benchmakr function name, the new timing, the base timing, and the percent change between the two.
-/
def mkReportPretty (groupName : String) (report : Array BenchReport) : String := Id.run do
  let columnWidths := getColumnWidths report
  let title := s!"## {groupName}\n\n"
  let (fn, new, base, percent) := (
    padWhitespace "Function" columnWidths.function,
    padWhitespace "New Benchmark" columnWidths.newBench,
    padWhitespace "Base Benchmark" columnWidths.baseBench,
    padWhitespace "% change" columnWidths.percentChange
  )
  let header := s!"| {fn} | {new} | {base} | {percent} |\n"
  let (d1, d2, d3, d4) := (
    padDashes columnWidths.function,
    padDashes columnWidths.newBench,
    padDashes columnWidths.baseBench,
    padDashes columnWidths.percentChange
  )
  let dashes := s!"|-{d1}-|-{d2}-|-{d3}-|-{d4}-|\n"
  let mut reportPretty := title ++ header ++ dashes
  for row in report do
    let functionStr := padWhitespace row.function columnWidths.function
    let newBenchStr := match row.newBench with
    | .oneShot o => o.benchTime.toFloat.formatNanos
    | .sample s => s.mean.pointEstimate.formatNanos
    let newBenchStr := padWhitespace newBenchStr columnWidths.newBench
    let baseBenchStr := if let some baseBench := row.baseBench then
      match baseBench with
      | .oneShot o => o.benchTime.toFloat.formatNanos
      | .sample s => s.mean.pointEstimate.formatNanos
    else "None"
    let baseBenchStr := padWhitespace baseBenchStr columnWidths.baseBench
    let percentChangeStr := if let some percentChange := row.percentChange then
      let percentChangeStr := (percentChange * 100).floatPretty 2
      if percentChange < 0 then s!"{percentChangeStr.drop 1}% faster"
      else if percentChange > 0 then s!"{percentChangeStr}% slower"
      else "No change"
    else "N/A" 
    let percentChangeStr := padWhitespace percentChangeStr columnWidths.percentChange
    let rowPretty :=
      s!"| {functionStr} | {newBenchStr} | {baseBenchStr} | {percentChangeStr} |\n"
    reportPretty := reportPretty ++ rowPretty
  return reportPretty

-- TODO: Make sure compiler isn't caching partial evaluation result for future runs of the same function (measure first vs subsequent runs)
/-- Runs each benchmark in a `BenchGroup` and analyzes the results -/
def bgroup {α β : Type} (name: String) (benches : List (Benchmarkable α β)) (config : Config := {}) : IO Unit := do
  let config ← getConfigEnv config
  let bg : BenchGroup := { name, config }
  IO.println s!"Running bench group {name}\n"
  let mut reports : Array BenchReport := #[]
  for b in benches do
    let report : BenchReport ← if config.oneShot then do
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
      let benchReport : BenchReport := { function := b.name, newBench := (.sample estimates), baseBench := (comparisonData.map (.sample ·.baseEstimates)), percentChange := comparisonData.map (·.relativeEstimates.mean.pointEstimate) }
      pure benchReport
    reports := reports.push report
  if config.report then
    let table := mkReportPretty name reports
    IO.println table
    IO.FS.writeFile (System.mkFilePath [".", s!"benchmark-report-{name}.md"]) table
  else
    return


