import Ix.Address
import Ix.Meta
import Ix.CompileM
import Ix.Cronos
import Ix.Address
import Batteries

import Ix.Benchmark.Serde
import Ix.Benchmark.Tukey
import Ix.Benchmark.Throughput

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

inductive BenchFn (α β : Type) where
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

def printRunning (config : Config) (expectedTime : Float) (numIters : Nat) (warningFactor : Nat) : IO Unit := do
  if warningFactor == 1 then
    IO.eprintln s!"Warning: Unable to complete {config.numSamples} samples in {config.sampleTime.floatPretty 2}s. You may wish to increase target time to {expectedTime.floatPretty 2}s"
  IO.println s!"Running {config.numSamples} samples in {expectedTime.floatPretty 2}s ({numIters.natPretty} iterations)\n"

-- Core sampling loop that runs the benchmark function for a fixed (if flat) or linearly increasing (if linear) number of iterations per sample, and returns the final dataset as the array of measured times for each sample
def runSamples (sampleIters : Array Nat) (bench : Benchmarkable α β) : IO (Array Nat) := do
  let func := bench.getFn
  let mut timings : Array Nat := #[]
  for iters in sampleIters do
    let start ← IO.monoNanosNow
    for _i in Array.range iters do
      let _res ← func bench.arg
    let finish ← IO.monoNanosNow
    timings := timings.push (finish - start)
  return timings

-- TODO: Recommend sample count if expectedTime >>> bg.config.sampleTime (i.e. itersPerSample == 1)
/--
Runs the benchmark samples as a sequence of constant iterations per data point, where the iteration count attempts to fit into the configurable `sampleTime` but cannot be less than 1.

Returns the iteration counts and elapsed time per sample.
-/
def BenchGroup.sampleFlat (bg : BenchGroup) (bench : Benchmarkable α β)
(warmupMean : Float) : IO (Array Nat × Array Nat) := do
  let targetTime := bg.config.sampleTime.toNanos
  let timePerSample := targetTime / (Float.ofNat bg.config.numSamples)
  let itersPerSample := (timePerSample / warmupMean).ceil.toUInt64.toNat.max 1
  let totalIters := itersPerSample * bg.config.numSamples
  let expectedTime := warmupMean * Float.ofNat itersPerSample * bg.config.numSamples.toSeconds
  printRunning bg.config expectedTime totalIters itersPerSample
  --IO.println s!"Flat sample. Iters per sample: {itersPerSample}"
  let sampleIters := Array.replicate bg.config.numSamples itersPerSample
  let timings ← runSamples sampleIters bench
  return (sampleIters, timings)

/--
Runs the benchmarks samples as a sequence of linearly increasing iterations [d, 2d, 3d, ..., Nd] where `N` is the total number of samples and `d` is a factor derived from the warmup iteration time.

The sum of this series should be roughly equivalent to the total `sampleTime`.

Returns the iteration counts and elapsed time per sample.
-/
def BenchGroup.sampleLinear (bg : BenchGroup) (bench : Benchmarkable α β) (warmupMean : Float) : IO (Array Nat × Array Nat) := do
  let totalRuns := bg.config.numSamples * (bg.config.numSamples + 1) / 2
  let targetTime := bg.config.sampleTime.toNanos
  -- `d` has a minimum value of 1 if the `warmupMean` is sufficiently large
  -- If so, that likely means the benchmark takes too long and target time should be increased, as well as considering other config options like flat sampling mode
  let d := (targetTime / warmupMean / (Float.ofNat totalRuns)).ceil.toUInt64.toNat.max 1
  let expectedTime := (Float.ofNat totalRuns) * (Float.ofNat d) * warmupMean.toSeconds
  let sampleIters := (Array.range bg.config.numSamples).map (fun x => (x + 1) * d)
  printRunning bg.config expectedTime sampleIters.sum d
  --IO.println s!"Linear sample. Iters increase by a factor of {d} per sample"
  let timings ← runSamples sampleIters bench
  return (sampleIters, timings)

def BenchGroup.sample (bg : BenchGroup) (bench : Benchmarkable α β) (warmupMean : Float) : IO (Array Nat × Array Nat) := do
  match bg.config.samplingMode with
  | .flat => bg.sampleFlat bench warmupMean
  | .linear => bg.sampleLinear bench warmupMean

structure MeasurementData where
  data : Data
  avgTimes : Distribution
  absoluteEstimates : Estimates
  distributions : Distributions
  comparison : Option ComparisonData
  throughput : Option Throughput
  deriving Repr

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

-- TODO: Don't compare if different sampling modes were used
/-- Retrieves prior bench result from disk and runs the comparison -/
def BenchGroup.getComparison (bg : BenchGroup) (benchName : String) (avgTimes : Distribution) (config: Config) : IO (Option ComparisonData) := do
  let benchPath := System.mkFilePath [".", ".lake", "benches", bg.name, benchName]
  let fileExt := toString config.serde
  -- Base data is at `new` since we haven't written the latest result to disk yet, which moves the prior data to `base`
  let basePath := benchPath / "new"
  if (← System.FilePath.pathExists (basePath / s!"estimates.{fileExt}")) then do
    let baseSample : Data ← loadFile config.serde (basePath / s!"sample.{fileExt}")
    let baseEstimates : Estimates ← loadFile config.serde (basePath / s!"estimates.{fileExt}")
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

  if lb < noiseNeg && ub < noiseNeg then
    ComparisonResult.Improved
  else if lb > noiseThreshold && ub > noiseThreshold then
    ComparisonResult.Regressed
  else
    ComparisonResult.NonSignificant

-- TODO: Does color of change percents depend on positive T-test?
def BenchGroup.printResults (bg : BenchGroup) (benchName : String) (m : MeasurementData) : IO Unit := do
  let estimates := m.absoluteEstimates
  let typicalEstimate := estimates.slope.getD estimates.mean
  let title := green s!"{bg.name}/{benchName}"
  let indentWidth := 24
  let indent := String.mk <| List.replicate indentWidth ' '
  IO.print title
  -- Print time on separate line from title if title is >22 chars long
  if title.length + 2 > indentWidth then
    IO.print s!"\n{indent}"
  else
    IO.print <| indent.drop title.length
  let lb := typicalEstimate.confidenceInterval.lowerBound
  let pointEst := typicalEstimate.pointEstimate
  let ub := typicalEstimate.confidenceInterval.upperBound
  println! "time:   [{lb.formatNanos} {bold pointEst.formatNanos} {ub.formatNanos}]"
  let thrpts : Option Throughput :=
    bg.config.throughput.map (fun thrpt =>
      match thrpt with
      | .bytes b =>
        thrptsFromBps b.toFloat lb pointEst ub
      | .elements _e => ⟨ 1.0, 2.0, 3.0, 4.0 ⟩)
  if let some ts := thrpts then
    let (lbStr, pointEstStr, ubStr) :=
      (formatThrpt ts.lowerBound, formatThrpt ts.pointEstimate, formatThrpt ts.upperBound)
    println! "{indent}thrpt:  [{lbStr} {bold pointEstStr} {ubStr}]"

  if let some comp := m.comparison then
    let diffMean := comp.pValue > comp.significanceThreshold
    let meanEst := comp.relativeEstimates.mean
    let (explanation, color) := if diffMean then
      ("No change in performance detected", false)
    else
      match compareToThreshold meanEst comp.noiseThreshold with
      | ComparisonResult.Improved => (s!"Performance has {green "improved"}", true)
      | ComparisonResult.Regressed => (s!"Performance has {red "regressed"}", true)
      | ComparisonResult.NonSignificant => ("Change within noise threshold", false)
    let (lb, pointEst, ub) := meanEst.formatPercents color
    let symbol := if diffMean then ">" else "<"
    let changeStr := "change:"
    if let some thrptsNew := thrpts then
      let changeIndent := indent.drop changeStr.length
      IO.println <| changeIndent ++ changeStr
      println! "{indent}time:   [{lb} {pointEst} {ub}] (p = {comp.pValue.floatPretty 2} {symbol} {comp.significanceThreshold.floatPretty 2})"
      let base := comp.baseEstimates
      let typical := base.slope.getD base.mean
      let thrptsBase := thrptsFromBps thrptsNew.size typical.confidenceInterval.lowerBound typical.pointEstimate typical.confidenceInterval.upperBound

      let (lbStr, pointEstStr, ubStr) := thrptsNew.formatPercents thrptsBase color
      println! "{indent}thrpt:  [{lbStr}, {pointEstStr}, {ubStr}]"
    else
      IO.println s!"{indent}{changeStr} [{lb} {pointEst} {ub}] (p = {comp.pValue.floatPretty 2} {symbol} {comp.significanceThreshold.floatPretty 2})"
    IO.println <| indent ++ explanation
  m.avgTimes.runTukey

-- TODO: Write sampling mode and config in `sample.json` for comparison
def saveComparison (groupName : String) (benchName : String) (comparison : ComparisonData) (config : Config) : IO Unit := do
  let changePath := System.mkFilePath [".", ".lake", "benches", groupName, benchName, "change"]
  storeFile config.serde comparison.relativeEstimates (changePath / s!"estimates.{toString config.serde}")

def mkDirs (groupName : String) (benchName : String) : IO (System.FilePath × System.FilePath) := do
  let benchPath := System.mkFilePath [".", ".lake", "benches", groupName, benchName]
  let (basePath, changePath, newPath) := (benchPath / "base", benchPath / "change", benchPath / "new")
  let (baseDir, changeDir, newDir) := (basePath.toString, changePath.toString, newPath.toString)
  let _out ← IO.Process.run {cmd := "mkdir", args := #["-p", baseDir, changeDir, newDir] }
  return (basePath, newPath)

def moveBaseFile (file : System.FilePath) (baseDir : String) : IO Unit := do
  if (← System.FilePath.pathExists file) then do
    -- Move prior bench from `new` to `base`
    let _ ← IO.Process.run { cmd := "mv", args := #[file.toString, baseDir] }

-- Results are always saved to `.lake/benches/<benchName>/new`. If files of the same serde format already exist from a prior run, move them to `base`
def saveMeasurement (groupName : String) (benchName : String) (mData : MeasurementData) (config : Config) : IO Unit := do
  let (basePath, newPath) ← mkDirs groupName benchName
  let baseDir := basePath.toString
  let fileExt := toString config.serde
  if let some compData := mData.comparison then saveComparison groupName benchName compData config
  else
  let (newEstimatesFile, newSampleFile) := (newPath / s!"estimates.{fileExt}", newPath / s!"sample.{fileExt}")
  moveBaseFile newSampleFile baseDir
  moveBaseFile newEstimatesFile baseDir
  storeFile config.serde mData.data newSampleFile
  storeFile config.serde mData.absoluteEstimates newEstimatesFile

-- TODO: Use a typeclass instead?
inductive BenchResult where
| oneShot : OneShot → BenchResult
| sample : Estimates → BenchResult
  deriving Repr

def BenchResult.getTime (bench: BenchResult) : Float :=
  match bench with
  | oneShot o => o.benchTime.toFloat
  | sample s => s.mean.pointEstimate

-- TODO: Include input parameters if specified for post-processing
-- E.g. Blake3 bench wants to have `dataSize` and `numHashes`
-- Currently has to parse this from the `function` string
structure BenchReport where
  function: String
  newBench : BenchResult
  baseBench : Option BenchResult
  percentChange : Option Float

def percentChangeToString (pc : Float) : String :=
  let rounded := (100 * pc).floatPretty 2
  if pc < 0 then s!"{rounded.drop 1}% faster"
  else if pc > 0 then s!"{rounded}% slower"
  else "No change"

structure ColumnWidths where
  function : Nat
  newBench : Nat
  baseBench : Nat
  percentChange : Nat

def getColumnWidths' (maxWidths : ColumnWidths) (row: BenchReport) : ColumnWidths :=
  let fnLen := row.function.length
  let function := if fnLen > maxWidths.function then fnLen else maxWidths.function
  let newBenchLen := row.newBench.getTime.formatNanos.length
  let newBench := if newBenchLen > maxWidths.newBench then newBenchLen else maxWidths.newBench
  let baseBench :=
    row.baseBench.elim maxWidths.baseBench (fun baseBench =>
      let baseBenchLen := baseBench.getTime.formatNanos.length
      if baseBenchLen > maxWidths.baseBench then baseBenchLen
      else maxWidths.baseBench)
  let percentChange :=
    row.percentChange.elim maxWidths.percentChange (fun percentChange =>
      let percentChangeStr := percentChangeToString percentChange
      let percentLen := percentChangeStr.length
      if percentLen > maxWidths.percentChange then percentLen
      else maxWidths.percentChange)
  { function, newBench, baseBench, percentChange }

-- Gets the max lengths of each data type for pretty-printing columns
def getColumnWidths (report : Array BenchReport) : ColumnWidths :=
  let maxWidths : ColumnWidths := {
    function := "Function".length
    newBench := "New Benchmark".length
    baseBench := "Base Benchmark".length
    percentChange := "% change".length
  }
  report.foldl getColumnWidths' maxWidths

-- Centers a string with padded whitespace given the total width
def padWhitespace (input : String) (width : Nat) : String :=
  let padWidth := width - input.length 
  let leftPad := padWidth / 2
  let rightPad := padWidth - leftPad
  String.ofList (List.replicate leftPad ' ') ++ input ++ (String.ofList (List.replicate rightPad ' '))

def padDashes (width : Nat) : String :=
  String.ofList (List.replicate width '-')

def mkReportPretty' (columnWidths : ColumnWidths) (reportPretty : String) (row : BenchReport) : String :=
  let functionStr := padWhitespace row.function columnWidths.function
  let newBenchStr := row.newBench.getTime.formatNanos
  let newBenchStr := padWhitespace newBenchStr columnWidths.newBench
  let baseBenchStr :=
    row.baseBench.elim "None" (·.getTime.formatNanos)
  let baseBenchStr := padWhitespace baseBenchStr columnWidths.baseBench
  let percentChangeStr :=
    row.percentChange.elim "N/A" (percentChangeToString ·)
  let percentChangeStr := padWhitespace percentChangeStr columnWidths.percentChange
  let rowPretty :=
    s!"| {functionStr} | {newBenchStr} | {baseBenchStr} | {percentChangeStr} |\n"
  reportPretty ++ rowPretty

-- TODO: Bold the faster result and faster/slower % change
/--
Generates a Markdown table with comparative benchmark timings based on the results on disk.
Each table row contains the benchmakr function name, the new timing, the base timing, and the percent change between the two.
-/
def mkReportPretty (groupName : String) (report : Array BenchReport) : String :=
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
  let reportPretty := title ++ header ++ dashes
  report.foldl (mkReportPretty' columnWidths) reportPretty

def oneShotBench {α β : Type} (groupName : String) (bench: Benchmarkable α β) (config : Config) : IO BenchReport := do
  let start ← IO.monoNanosNow
  let _res ← bench.getFn bench.arg
  let finish ← IO.monoNanosNow
  let benchTime := finish - start
  let title := green s!"{groupName}/{bench.name}"
  let indentWidth := 24
  let indent := String.mk <| List.replicate indentWidth ' '
  IO.print title
  -- Print time on separate line from title if title is >22 chars long
  if title.length + 2 > indentWidth then
    IO.print s!"\n{indent}"
  else
    IO.print <| indent.drop title.length
  IO.println s!"time:   {bold benchTime.toFloat.formatNanos}"
  let thrpts : Option Throughput :=
    bg.config.throughput.map (fun thrpt =>
      match thrpt with
      | .bytes b =>
        bytesPerSecond b 
      | .elements _e => ⟨ 1.0, 2.0, 3.0, 4.0 ⟩)
  if let some ts := thrpts then
    let thrpt := formatThrpt ts
    println! "{indent}thrpt: {bold thrpt}"
  let (basePath, newPath) ← mkDirs groupName bench.name
  let fileExt := toString config.serde
  let newFile := newPath / s!"one-shot.{fileExt}"
  let (baseBench, percentChange) ← if (← System.FilePath.pathExists newFile) then do
    let baseBench : OneShot ← loadFile config.serde newFile
    let baseTime := baseBench.benchTime.toFloat
    let percentChange := (benchTime.toFloat - baseTime) / baseTime
    IO.println s!"change: {percentChangeToString percentChange}"
    let _ ← IO.Process.run { cmd := "mv", args := #[newFile.toString, basePath.toString] }
    pure (some baseBench, some percentChange)
  else
    let _ ← IO.Process.run { cmd := "mkdir", args := #["-p", newPath.toString] }
    pure (.none, .none)
  let newBench : OneShot := { benchTime }
  IO.println ""
  storeFile config.serde newBench newFile
  let benchReport : BenchReport := { function := bench.name, newBench := (.oneShot newBench), baseBench := baseBench.map .oneShot, percentChange }
  return benchReport

-- TODO: Make sure compiler isn't caching partial evaluation result for future runs of the same function (measure first vs subsequent runs)
/-- Runs each benchmark in a `BenchGroup` and analyzes the results -/
def bgroup {α β : Type} (name: String) (benches : List (Benchmarkable α β)) (config : Config := {}) : IO $ Array BenchReport := do
  let config ← getConfigEnv config
  let bg : BenchGroup := { name, config }
  IO.println s!"Running bench group {name}\n"
  let mut reports : Array BenchReport := #[]
  for b in benches do
    let report : BenchReport ← if config.oneShot then do
      oneShotBench name b config
    else
      let warmupMean ← bg.warmup b
      IO.println s!"Running {b.name}"
      let (iters, times) ← bg.sample b warmupMean
      let data := iters.zip times
      let avgTimes : Distribution := { d := data.map (fun (x,y) => Float.ofNat y / Float.ofNat x) }
      let gen ← IO.stdGenRef.get
      let mut (distributions, estimates) := avgTimes.estimates bg.config gen
      if bg.config.samplingMode == .linear then
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
        throughput := config.throughput
      }
      bg.printResults b.name measurement
      IO.println ""
      saveMeasurement name b.name measurement config
      let benchReport : BenchReport := { function := b.name, newBench := (.sample estimates), baseBench := (comparisonData.map (.sample ·.baseEstimates)), percentChange := comparisonData.map (·.relativeEstimates.mean.pointEstimate) }
      pure benchReport
    reports := reports.push report
  if config.report then
    let table := mkReportPretty name reports
    IO.println table
    IO.FS.writeFile (System.mkFilePath [".", s!"benchmark-report-{name}.md"]) table
  return reports

