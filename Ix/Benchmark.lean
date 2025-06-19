import Ix.Claim
import Ix.Address
import Ix.Meta
import Ix.CompileM
import Ix.Cronos
import Ix.Ixon.Expr
import Ix.Address
import Batteries

open Batteries (RBMap)

/--
Benchmarking library modeled after Criterion in Haskell and Rust

Limitations:
- Measures time in nanoseconds using `IO.monoNanosNow`, which is less precise than the picoseconds used in Criterion.rs
-/

-- This prevents inline optimization for benchmarking, but doesn't work if the result is never used
--@[never_extract, noinline]
--def blackBox : α → α := id

-- Compute the result and then discard the result
@[never_extract, noinline]
def blackBoxIO (f : α → β) (a : α) : IO β := do
  pure $ f a

def Float.toNanos (f : Float) : Float := f * 10 ^ 9

def Float.toSeconds (f : Float) : Float := f / 10 ^ 9

def Nat.toSeconds (n : Nat) : Float := Float.ofNat n / 10 ^ 9

-- TODO: Maybe add tenths place before M and B
def Nat.natPretty (n : Nat) : String :=
  if n ≥ 10 ^ 9
  then
    toString (n / 10 ^ 9) ++ "B"
  else if n ≥ 10 ^ 6
  then
    toString (n / 10 ^ 6 ) ++ "M"
  else
    toString n

def putStrNat (tup : String × Nat) : Ixon.PutM := do
  Ixon.putExpr $ .strl tup.fst
  Ixon.putExpr $ .natl tup.snd

def putCron (cron: Cronos) : Ixon.PutM := do
  Ixon.putArray (fun x => putStrNat x) cron.data.toList

def toIxon (c : Cronos) : ByteArray := Ixon.runPut (putCron c)

-- TODO: Not self-describing, add a 4-bit prefix for tuples generally
def getStrNat : Ixon.GetM (String × Nat) := do
  match (← Ixon.getExpr) with
  | .strl s =>
    match (← Ixon.getExpr) with
    | .natl n => return (s, n)
    | x => throw s!"expected Expr.Nat, got {repr x}"
  | x => throw s!"expected Expr.String, got {repr x}"

instance : Ixon.Serialize (RBMap String Nat compare) where
  put xs := (Ixon.runPut ∘ (Ixon.putArray (fun x => putStrNat x))) xs.toList
  get xs := (Ixon.runGet (Ixon.getArray getStrNat) xs).map (fun x => RBMap.ofList x compare)

def getStr : Ixon.GetM String := do
  match (← Ixon.getExpr) with
  | .strl s => return s
  | x => throw s!"expected Expr.String, got {repr x}"

instance : Ixon.Serialize (List String) where
  put := (Ixon.runPut ∘ (Ixon.putArray (fun x => Ixon.putExpr (.strl x))))
  get := Ixon.runGet (Ixon.getArray getStr)

def putFloat (x : Float): Ixon.PutM := Ixon.putUInt64LE x.toBits
def getFloat : Ixon.GetM Float := Ixon.getUInt64LE.map Float.ofBits

instance : Ixon.Serialize Float where
  put := Ixon.runPut ∘ putFloat
  get := Ixon.runGet getFloat

inductive SamplingMode where
  | flat : SamplingMode
  | linear : SamplingMode
deriving Repr, BEq

structure Config where
  -- Warmup time in seconds
  warmupTime : Float := 3.0
  -- Target sample time in seconds. If the time per iteration is too long then the actual sample time will run longer and print a warning
  sampleTime : Float := 5.0
  -- Number of data points to collect per sample
  numSamples : Nat := 100
  -- Sample in flat or linear mode
  samplingMode : SamplingMode := .flat
  -- Number of bootstrap samples (with replacement) to run
  bootstrapSamples : Nat := 100000
  -- Confidence level for estimates
  confidenceLevel : Float := 0.95
  -- Noise threshold when comparing two benchmark means, if percent change is within this threshold then it's considered noise
  noiseThreshold : Float := 0.02 -- 2%
deriving Repr

-- A benchmark group defines a collection of related benchmarks that share a configuration, such as number of samples and noise threshold
structure BenchGroup where
  name : String
  config : Config

def percentChange (old : Float) (new : Float) : Float :=
  (new - old) / old.abs * 100

def Float.variablePrecision (float : Float) (precision : Nat) : Float :=
  let moveDecimal := Float.ofNat $ 10 ^ precision
  -- Move the decimal right to the desired precision, round to the nearest integer, then move the decimal back
  (float * moveDecimal).round / moveDecimal

-- Panics if float is a NaN
def Float.floatPretty (float : Float) (precision : Nat): String :=
  let precise := float.variablePrecision precision
  let parts := precise.toString.splitOn "."
  let integer := parts[0]!
  let fractional := parts[1]!.take precision
  if !fractional.isEmpty
  then integer ++ "." ++ fractional
  else integer

-- Formats a time in ns as an xx.yy string with correct units
def Float.formatNanos (f : Float) : String :=
  if f ≥ 10 ^ 9
  then
    (f / 10 ^ 9).floatPretty 2 ++ "s"
  else if f ≥ 10 ^ 6
  then
    (f / 10 ^ 6).floatPretty 2 ++ "ms"
  else if f ≥ 10 ^ 3
  then
    (f / 10 ^ 3).floatPretty 2 ++ "µs"
  else
    f.floatPretty 2  ++ "ns"


structure Benchmarkable (α β : Type) where
  name : String
  func : α → β
  arg : α

def bench (name : String) (func : α → β) (arg : α) : Benchmarkable α β := ⟨ name, func, arg ⟩

def BenchGroup.warmup (bg : BenchGroup) (bench : Benchmarkable α β) : IO Float := do
  IO.println s!"Warming up for {bg.config.warmupTime.floatPretty 2}s"
  let mut count := 0
  let warmupNanos := Cronos.secToNano bg.config.warmupTime
  let mut elapsed := 0
  let startTime ← IO.monoNanosNow
  while elapsed < warmupNanos do
    let _res ← blackBoxIO bench.func bench.arg
    count := count + 1
    let now ← IO.monoNanosNow
    elapsed := now - startTime
  let mean := Float.ofNat elapsed / Float.ofNat count
  --IO.println s!"{bench.name} warmup avg: {mean}ns"
  --IO.println s!"Ran {count} iterations in {bg.config.warmupTime.floatPretty 2}s\n"
  return mean

-- TODO: Combine with other sampling functions, DRY
-- TODO: Recommend sample count if expectedTime >>> bg.config.sampleTime (i.e. itersPerSample == 1)
-- Runs the sample as a sequence of constant iterations per data point, where the iteration count attempts to fit into the configurable `sampleTime` but cannot be less than 1
-- Returns the iteration counts and elapsed time per data point
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
  IO.println s!"Running {bg.config.numSamples} samples in {expectedTime.floatPretty 2}s ({totalIters.natPretty} iterations)"
  --IO.println s!"Flat sample. Iters per sample: {itersPerSample}"
  let mut timings : Array Nat := #[]
  -- TODO: `mkArray` deprecated in favor of `replicate` in Lean v4.19
  let sampleIters := Array.mkArray bg.config.numSamples itersPerSample
  for iters in sampleIters do
    --IO.println s!"Data with {itersPerSample} iterations"
    --IO.println s!"Running sample {s}"
    let start ← IO.monoNanosNow
    for _i in Array.range iters do
      let _res ← blackBoxIO bench.func bench.arg
    let finish ← IO.monoNanosNow
    timings := timings.push (finish - start)
  return (sampleIters, timings)

-- Runs the sample as a sequence of linearly increasing iterations [d, 2d, 3d, ..., Nd]
-- where `N` is the total number of samples and `d` is a factor derived from the warmup iteration time. The sum of this series should be roughly equivalent to the total `sampleTime`
-- Returns the iteration counts and elapsed time per sample
def BenchGroup.sampleLinear (bg : BenchGroup) (bench : Benchmarkable α β) (warmupMean : Float) : IO (Array Nat × Array Nat) := do
  -- `d` has a minimum value of 1 if the `warmupMean` is sufficiently large
  -- In this case,
  let totalRuns := bg.config.numSamples * (bg.config.numSamples + 1) / 2
  let targetTime := bg.config.sampleTime.toNanos
  let d := (targetTime / warmupMean / (Float.ofNat totalRuns)).ceil.toUInt64.toNat.max 1
  let expectedTime := (Float.ofNat totalRuns) * (Float.ofNat d) * warmupMean.toSeconds
  let sampleIters := (Array.range bg.config.numSamples).map (fun x => (x + 1) * d)
  if d == 1
  then
    IO.eprintln s!"Warning: Unable to complete {bg.config.numSamples} samples in {bg.config.sampleTime.floatPretty 2}s. You may wish to increase target time to {expectedTime.floatPretty 2}s"
  IO.println s!"Running {bg.config.numSamples} samples in {expectedTime.floatPretty 2}s ({sampleIters.sum.natPretty} iterations)"
  IO.println s!"Linear sample. Iters increase by a factor of {d} per sample"
  let mut timings : Array Nat := #[]
  for iters in sampleIters do
    --IO.println s!"Data with {iters} iterations"
    let start ← IO.monoNanosNow
    for _i in Array.range iters do
      let _res ← blackBoxIO bench.func bench.arg
    let finish ← IO.monoNanosNow
    timings := timings.push (finish - start)
  return (sampleIters, timings)

def BenchGroup.sample (bg : BenchGroup) (bench : Benchmarkable α β) (warmupMean : Float) : IO (Array Nat × Array Nat) := do
  match bg.config.samplingMode with
  | .flat => bg.sampleFlat bench warmupMean
  | .linear => bg.sampleLinear bench warmupMean

-- TODO: Implement Coe with ↑ to coerce to the underlying list
-- TODO: Ensure all array instances are used linearly for optimal performance
structure Distribution where
  d : Array Float := #[]

instance : Coe Distribution (Array Float) where
  coe x := x.d

def Distribution.percentile? (data : Distribution) (p : Float): Option Float :=
  if data.d.isEmpty || p > 100
  then .none
  else
    --let data := data.d.sortBy (fun x y => compareOfLessAndBEq x y)
    let data := data.d.qsort
    let r := (p / 100) * (Float.ofNat data.size - 1) + 1
    let rf := r - r.floor
    if rf == 0
    then
      data[r.toUInt64.toNat - 1]?
    else
      let ri := r.floor.toUInt64.toNat
      -- TODO: use fallible ? indices and monadically chain state
      .some $ data[ri-1]! + (rf) * (data[ri]! - data[ri-1]!)

-- Outliers are classified following https://bheisler.github.io/criterion.rs/book/analysis.html#outlier-classification
structure Outliers where
  outliers : List Float
  highSevere : Nat
  highMild : Nat
  lowMild : Nat
  lowSevere : Nat
deriving Repr

def Outliers.getTotal (o : Outliers) : Nat :=
  o.highSevere + o.highMild + o.lowMild + o.lowSevere

-- TODO: Refactor to cut down verbosity, and return the list for plotting
def Distribution.tukey (data : Distribution) : IO Unit := do
  let upper := (data.percentile? 75).get!
  let lower := (data.percentile? 25).get!
  let iqr := upper - lower
  let fences := [lower - 3 * iqr, lower - 1.5 * iqr, upper + 1.5 * iqr, upper + 3 * iqr]
  let mut out : Outliers := ⟨ [], 0, 0, 0, 0 ⟩
  for elem in data.d do
    if elem < fences[1]!
    then
      if elem < fences[0]! then
        out := { out with outliers := elem :: out.outliers, lowSevere := out.lowSevere + 1 }
      else
        out := { out with outliers := elem :: out.outliers, lowMild := out.lowMild + 1 }
    else if elem > fences[2]! then
      if elem > fences[3]! then
        out := { out with outliers := elem :: out.outliers, highSevere := out.highSevere + 1 }
      else
        out := { out with outliers := elem :: out.outliers, highMild := out.highMild + 1 }
  let outLength := out.outliers.length
  if outLength > 0 then
    let samples := data.d.size
    IO.println s!"Found {outLength} outliers among {samples} measurements"
    if out.lowMild > 0 then
      let pct := Float.ofNat out.lowMild / (Float.ofNat samples) * 100
      IO.println s!"  {out.lowMild} ({pct.floatPretty 2}%) low mild"
    if out.lowSevere > 0 then
      let pct := Float.ofNat out.lowSevere / (Float.ofNat samples) * 100
      IO.println s!"  {out.lowSevere} ({pct.floatPretty 2}%) low severe"
    if out.highMild > 0 then
      let pct := Float.ofNat out.highMild / (Float.ofNat samples) * 100
      IO.println s!"  {out.highMild} ({pct.floatPretty 2}%) high mild"
    if out.highSevere > 0 then
      let pct := Float.ofNat out.highSevere / (Float.ofNat samples) * 100
      IO.println s!"  {out.highSevere} ({pct.floatPretty 2}%) high severe"

structure Distributions where
  means: Distribution := { d := #[] }
  medians: Distribution := { d := #[] }
  medianAbsDevs : Distribution := { d := #[] }
  slope : Option (Distribution) := none
  stdDevs : Distribution := { d := #[] }

structure ConfidenceInterval where
  confidenceLevel : Float
  lowerBound : Float
  upperBound : Float
deriving Repr

def putConfidenceInterval (ci : ConfidenceInterval) : Ixon.PutM := do
  putFloat ci.confidenceLevel
  putFloat ci.lowerBound
  putFloat ci.upperBound

def getConfidenceInterval : Ixon.GetM ConfidenceInterval := do
  return { confidenceLevel := (← getFloat), lowerBound := (← getFloat), upperBound := (← getFloat)}

structure Estimate where
  confidenceInterval : ConfidenceInterval
  pointEstimate : Float
  stdErr : Float
deriving Repr

def putEstimate (est : Estimate) : Ixon.PutM := do
  putConfidenceInterval est.confidenceInterval
  putFloat est.pointEstimate
  putFloat est.stdErr

def getEstimate : Ixon.GetM Estimate := do
  return { confidenceInterval := (← getConfidenceInterval), pointEstimate := (← getFloat), stdErr := (← getFloat)}

structure Estimates where
  mean : Estimate
  median : Estimate
  medianAbsDev : Estimate
  slope : Option Estimate
  stdDev : Estimate
deriving Repr

def putEstimates (est : Estimates) : Ixon.PutM := do
  putEstimate est.mean
  putEstimate est.median
  putEstimate est.medianAbsDev
  if let .some x := est.slope
  then
    Ixon.putUInt8 1
    putEstimate x
  else
    Ixon.putUInt8 0
  putEstimate est.stdDev

def getEstimates : Ixon.GetM Estimates := do
  let mean ← getEstimate
  let median ← getEstimate
  let medianAbsDev ← getEstimate
  let slope ← match (← Ixon.getUInt8) with
    | 1 => pure $ some (← getEstimate)
    | _ => pure none
  let stdDev ← getEstimate
  return { mean, median, medianAbsDev, slope, stdDev }

instance : Ixon.Serialize Estimates where
  put := Ixon.runPut ∘ putEstimates
  get := Ixon.runGet getEstimates

structure PointEstimates where
  mean : Float
  median : Float
  medianAbsDev : Float
  stdDev : Float

def Distribution.confidenceInterval (dist : Distribution) (confidenceLevel : Float) : ConfidenceInterval :=
  let lowerBound := (dist.percentile? (50 * (1 - confidenceLevel))).get!
  let upperBound := (dist.percentile? (50 * (1 + confidenceLevel))).get!
  { confidenceLevel, lowerBound, upperBound }

def Distribution.mean (dist : Distribution) : Float :=
  dist.d.sum / Float.ofNat dist.d.size

def Distribution.median (dist : Distribution) : Float :=
  (dist.percentile? 50).get!

def Distribution.variance (dist : Distribution) (mean : Float) : Float :=
  let sum := dist.d.foldl (fun acc x => acc + ((x - mean) ^ 2)) 0.0
  sum / Float.ofNat (dist.d.size - 1)

def Distribution.stdDev (dist : Distribution) (mean : Float) : Float :=
  (dist.variance mean).sqrt

def Distribution.medianAbsDev (dist : Distribution) (median : Float) : Float :=
  let absDevs : Distribution := { d := dist.d.map (fun x => (x - median).abs) }
  (absDevs.percentile? 50).get! * 1.4826

-- Returns the data point in the distribution at a random index
def Distribution.randDistM (dist : Distribution) : StateM StdGen Float := do
  let gen ← get
  let (n, gen') := randNat gen 0 (dist.d.size - 1)
  set gen'
  return dist.d[n]!

-- Creates a random permutation of the distribution with replacement (i.e. duplicates are permitted)
def Distribution.resampleM (dist : Distribution) (numSamples : Nat) : StateM StdGen Distribution := do
  let mut rands := #[]
  for _ in Array.range numSamples do
    let res ← dist.randDistM
    rands := rands.push res
  return { d := rands }

-- Assumes `numSamples ≥ 2`
-- Gets `numSamples` resamples of the distribution and computes statistics for each
-- Returns
def Distribution.bootstrap (dist : Distribution) (numSamples bootstrapSamples : Nat) : StateM StdGen Distributions := do
  let mut means : Distribution := {}
  let mut stdDevs : Distribution := {}
  let mut medians : Distribution := {}
  let mut medianAbsDevs : Distribution := {}
  for _ in Array.range bootstrapSamples do
    let resample ← Distribution.resampleM dist numSamples
    means := { means with d := means.d.push resample.mean }
    stdDevs := { stdDevs with d := stdDevs.d.push (resample.stdDev resample.mean) }
    medians := { medians with d := medians.d.push resample.median }
    medianAbsDevs := { medianAbsDevs with d := medianAbsDevs.d.push (resample.medianAbsDev resample.median) }
  return { means, medians, medianAbsDevs, slope := none, stdDevs }

def Distribution.toEstimate (dist : Distribution) (pointEstimate : Float) (confidenceLevel : Float) : Estimate :=
  let confidenceInterval := dist.confidenceInterval confidenceLevel
  let mean := dist.mean
  let stdErr := dist.stdDev mean
 { confidenceInterval, pointEstimate, stdErr }

def buildEstimates (dists : Distributions) (points : PointEstimates) (confidenceLevel : Float) : Estimates :=
  let mean := dists.means.toEstimate points.mean confidenceLevel
  let median := dists.medians.toEstimate points.median confidenceLevel
  let medianAbsDev := dists.medianAbsDevs.toEstimate points.medianAbsDev confidenceLevel
  let slope := none
  let stdDev := dists.stdDevs.toEstimate points.stdDev confidenceLevel
  { mean, median, medianAbsDev, slope, stdDev }

def Distribution.estimates (avgTimes : Distribution) (config : Config) (gen : StdGen) : (Distributions × Estimates) :=
  let mean := avgTimes.mean
  let stdDev := avgTimes.stdDev mean
  let median := avgTimes.median
  let medianAbsDev := avgTimes.medianAbsDev median
  let points : PointEstimates := { mean, median, medianAbsDev, stdDev }
  let dists := ((avgTimes.bootstrap config.numSamples config.bootstrapSamples).run gen).fst
  let est := buildEstimates dists points config.confidenceLevel
  (dists, est)

structure Data where
  d : Array (Nat × Nat) := #[]

def dots (acc xys : Nat × Nat) : (Nat × Nat) :=
  let xy := acc.fst + xys.fst * xys.snd
  let xs := acc.snd + xys.fst * xys.fst
  (xy, xs)

def Data.slope (data : Data) : Float :=
  let (xy, x2) := data.d.foldl dots (0, 0)
  Float.ofNat xy / Float.ofNat x2

-- Returns the data point in the distribution at a random index
def Data.randDataM (data : Data) : StateM StdGen (Nat × Nat) := do
  let gen ← get
  let (n, gen') := randNat gen 0 (data.d.size - 1)
  set gen'
  return data.d[n]!

-- Creates a random permutation of the distribution with replacement (i.e. duplicates are permitted)
def Data.resampleM (data : Data) (numSamples : Nat) : StateM StdGen Data := do
  let mut rands := #[]
  for _ in Array.range numSamples do
    let res ← data.randDataM
    rands := rands.push res
  return { d := rands }

def Data.bootstrap (data : Data) (numSamples bootstrapSamples : Nat): StateM StdGen Distribution := do
  let mut slopes : Array Float := #[]
  for _ in Array.range bootstrapSamples do
    let resample ← Data.resampleM data numSamples
    let slope := resample.slope
    slopes := slopes.push slope
  return { d := slopes }

-- Performs a linear regression on a sample, returning a pair of the bootstrap samples and the estimated slope by fitting the data to a straight line
-- Used only with linear sampling mode
def Data.regression (data : Data) (config : Config) (gen : StdGen) : (Distribution × Estimate) :=
  let distribution := ((data.bootstrap config.numSamples config.bootstrapSamples).run gen).fst
  let pointEstimate := data.slope
  let confidenceInterval := distribution.confidenceInterval config.confidenceLevel
  let mean := distribution.mean
  let stdErr := distribution.stdDev mean
  let estimate : Estimate := { confidenceInterval, pointEstimate, stdErr }
  (distribution, estimate)

def BenchGroup.getChange (bg : BenchGroup) (baseData : Estimates) (newData : Estimates) : IO Estimates := do
  let change ← if baseData.mean.pointEstimate == 0
  then
    IO.println s!"Percent change is infinite, `baseData` mean is 0"
    pure 0.0
  else
    let change := percentChange baseData.mean.pointEstimate newData.mean.pointEstimate
    IO.println s!"Percent change: {change.floatPretty 2}%"
    pure change
  let nT := bg.config.noiseThreshold * 100
  --IO.println s!"Noise threshold: {nT}%"
  if change.abs > nT
  then
    if change > 0
    then IO.println "Performance has regressed"
    else IO.println "Performance has improved"
  else IO.println "Change within noise threshold"
  return baseData -- TODO: Get actual change
  --let changeData : Estimates := { mean := change , stdDev := 1.0 }
  --return changeData

-- Store `Estimates` values as ixon on disk
-- Compare performance against prior run
-- TODO: Factor out into helper functions
def BenchGroup.comparePrev (bg : BenchGroup) (name : String) (benchData : Estimates) : IO Unit := do
  let ixon := Ixon.Serialize.put benchData
  let benchPath := System.mkFilePath [".", ".lake", "benches", name]
  let benchDir := benchPath.toString
  let _out ← IO.Process.run {cmd := "mkdir", args := #["-p", benchDir] }
  let basePath := benchPath / "base"
  let baseDir := basePath.toString
  -- If the user has already run the benchmark at least once, then write the new data to disk
  if (← System.FilePath.pathExists basePath)
  then
    let newPath := benchPath / "new"
    let newDir := newPath.toString
    -- If there have been 2 or more prior runs, overwrite old `base` with old `new`, then write latest data to `new`
    if (← System.FilePath.pathExists newPath) then
      let _out ← IO.Process.run {cmd := "rm", args := #["-r", baseDir] }
      let _out ← IO.Process.run {cmd := "mv", args := #[newDir, baseDir] }
    let _out ← IO.Process.run {cmd := "mkdir", args := #["-p", newDir] }
    IO.FS.writeBinFile (newPath / "estimates") ixon
    -- Get `base` data for comparison
    let baseBytes ← IO.FS.readBinFile (basePath / "estimates")
    let baseData ← match (Ixon.Serialize.get baseBytes : Except String Estimates) with
    | .ok bd' => pure bd'
    | e => throw $ IO.userError s!"expected `Estimates`, got {repr e}"
    -- Then do statistical analysis and write changes to disk
    let changeData ← bg.getChange baseData benchData
    let changeIxon := Ixon.Serialize.put changeData
    let changePath := benchPath / "change"
    let _out ← IO.Process.run {cmd := "mkdir", args := #["-p", changePath.toString ] }
    IO.FS.writeBinFile (changePath / "estimates") changeIxon
  else
    let _out ← IO.Process.run {cmd := "mkdir", args := #["-p", baseDir] }
    IO.FS.writeBinFile (basePath / "estimates") ixon

-- TODO: Make sure compiler isn't caching partial evaluation result for future runs of the same function (measure first vs subsequent runs)
-- Runs each benchmark in a `BenchGroup` and analyzes the results
def bgroup {α β : Type} (name: String) (benches : List (Benchmarkable α β)) (config : Config := {}) : IO Unit := do
  let bg : BenchGroup := { name, config }
  IO.println s!"Running bench group {name}\n"
  for b in benches do
    let warmupMean ← bg.warmup b
    IO.println s!"Running {b.name}"
    let (iters, times) ← bg.sample b warmupMean
    let data := iters.zip times
    let avgTimes : Distribution := { d := data.map (fun (x,y) => Float.ofNat y / Float.ofNat x) }
    avgTimes.tukey
    let gen ← IO.stdGenRef.get
    let mut (distributions, estimates) := avgTimes.estimates bg.config gen
    IO.println estimates.mean.pointEstimate
    if bg.config.samplingMode == .linear
    then
      let data' : Data := { d := data }
      let (distribution, slope) := data'.regression bg.config gen
      estimates := { estimates with slope := .some slope }
      distributions := { distributions with slope := .some distribution }
    IO.println s!"Mean: {estimates.mean.pointEstimate.formatNanos}"
    --IO.println s!"Results: {repr estimates}"
    --bg.comparePrev b.name bd
    --IO.println ""
