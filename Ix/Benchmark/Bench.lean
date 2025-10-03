import Ix.Ixon
import Ix.Address
import Ix.Meta
import Ix.CompileM
import Ix.Cronos
import Ix.Ixon.Expr
import Ix.Address
import Batteries

import Ix.Benchmark.Serde
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
  -- TODO: `mkArray` deprecated in favor of `replicate` in Lean v4.19
  let sampleIters := Array.mkArray bg.config.numSamples itersPerSample
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

/-- Compare performance against prior run -/
def BenchGroup.compare (bg : BenchGroup) (baseSample : Data) (baseEstimates : Estimates) (avgTimes : Distribution) (gen : StdGen) : ComparisonData :=
  -- Get `base` data for comparison
  let baseAvgTimes : Distribution := { d := baseSample.d.map (fun (x,y) => Float.ofNat y / Float.ofNat x) }
  -- Then perform statistical analysis
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
def BenchGroup.getComparison (bg : BenchGroup) (benchName : String) (avgTimes : Distribution) : IO (Option ComparisonData) := do
  let benchPath := System.mkFilePath [".", ".lake", "benches", benchName]
  let basePath := benchPath / "base"
  if (← System.FilePath.pathExists basePath)
  then do
    let newPath := benchPath / "new"
    -- If 2 or more prior runs, then the base data was stored in `new`
    let basePath' := if (← System.FilePath.pathExists newPath)
    then
      newPath
    else
      basePath
    let baseEstimateBytes ← IO.FS.readBinFile (basePath' / "estimates.ixon")
    let baseEstimates ← match (Ixon.Serialize.get baseEstimateBytes : Except String Estimates) with
    | .ok bd' => pure bd'
    | e => throw $ IO.userError s!"expected `Estimates`, got {repr e}"
    let baseSampleBytes ← IO.FS.readBinFile (basePath' / "sample.ixon")
    let baseSample ← match (Ixon.Serialize.get baseSampleBytes : Except String Data) with
    | .ok bd' => pure bd'
    | e => throw $ IO.userError s!"expected `Data`, got {repr e}"
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

def saveComparison! (benchName : String) (comparison : Option ComparisonData) : IO Unit := do
  match comparison with
  | some comp => do
    let changeIxon := Ixon.Serialize.put comp.relativeEstimates
    let benchPath := System.mkFilePath [".", ".lake", "benches", benchName]
    let changePath := benchPath / "change"
    let _out ← IO.Process.run {cmd := "mkdir", args := #["-p", changePath.toString ] }
    IO.FS.writeBinFile (changePath / "estimates.ixon") changeIxon
  | none => IO.eprintln s!"Error: expected `comparisonData` to write but found none"

-- TODO: Write sampling mode in `sample.json` for comparison
def saveResults (benchName : String) (m : MeasurementData) : IO Unit := do
  let benchPath := System.mkFilePath [".", ".lake", "benches", benchName]
  let _out ← IO.Process.run {cmd := "mkdir", args := #["-p", benchPath.toString] }
  let basePath := benchPath / "base"
  let baseDir := basePath.toString
  -- If prior results were saved to disk, don't overwrite them
  let newPath ← if (← System.FilePath.pathExists basePath)
    then do
      let newPath := benchPath / "new"
      let newDir := newPath.toString
      -- If 2 or more prior runs, then the base data was stored in `new`
      -- Move the base data to `base`
      if (← System.FilePath.pathExists newPath)
      then do
        let _out ← IO.Process.run {cmd := "rm", args := #["-r", baseDir] }
        let _out ← IO.Process.run {cmd := "mv", args := #[newDir, baseDir] }
      let _out ← IO.Process.run {cmd := "mkdir", args := #["-p", newPath.toString] }
      saveComparison! benchName m.comparison
      pure newPath
  else do
    let _out ← IO.Process.run {cmd := "mkdir", args := #["-p", baseDir] }
    pure basePath
  let sampleIxon := Ixon.Serialize.put m.data
  IO.FS.writeBinFile (newPath / "sample.ixon") sampleIxon
  let estimateIxon := Ixon.Serialize.put m.absoluteEstimates
  IO.FS.writeBinFile (newPath / "estimates.ixon") estimateIxon

-- TODO: Make sure compiler isn't caching partial evaluation result for future runs of the same function (measure first vs subsequent runs)
/-- Runs each benchmark in a `BenchGroup` and analyzes the results -/
def bgroup {α β : Type} (name: String) (benches : List (Benchmarkable α β)) (config : Config := {}) : IO Unit := do
  let bg : BenchGroup := { name, config }
  IO.println s!"Running bench group {name}\n"
  for b in benches do
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
    let comparisonData : Option ComparisonData ← bg.getComparison b.name avgTimes
    let m :=  {
      data := { d := data },
      avgTimes,
      absoluteEstimates := estimates,
      distributions,
      comparison := comparisonData
      throughput := none
    }
    bg.printResults b.name m
    IO.println ""
    saveResults b.name m
