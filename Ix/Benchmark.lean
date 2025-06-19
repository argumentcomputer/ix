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

-- Compute the result and then discard the result
@[never_extract, noinline]
def blackBoxIO (f : α → β) (a : α) : IO β := do
  pure $ f a

def Float.toNanos (f : Float) : Float := f * 10 ^ 9

def Float.toSeconds (f : Float) : Float := f / 10 ^ 9

def Nat.toSeconds (n : Nat) : Float := Float.ofNat n / 10 ^ 9

def Nat.natPretty (n : Nat) : String :=
  if n ≥ 10 ^ 9
  then
    toString (n / 10 ^ 9) ++ "B"
  else if n ≥ 10 ^ 6
  then
    toString (n / 10 ^ 6 ) ++ "M"
  else
    toString n

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
  -- Significance level for hypothesis testing when comparing two benchmark runs for significant difference
  significanceLevel : Float := 0.05
  -- Noise threshold when comparing two benchmark means, if percent change is within this threshold then it's considered noise
  noiseThreshold : Float := 0.01 -- 1%
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

-- TODO: According to Criterion.rs docs the warmup iterations should increase linearly until the warmup time is reached, rather than one iteration per time check
def BenchGroup.warmup (bg : BenchGroup) (bench : Benchmarkable α β) : IO Float := do
  IO.println s!"Warming up for {bg.config.warmupTime.floatPretty 2}s"
  let mut count := 0
  let warmupNanos := Cronos.secToNano bg.config.warmupTime
  let mut elapsed := 0
  let startTime ← IO.monoNanosNow
  while elapsed < warmupNanos do
    let _res ← blackBoxIO bench.func bench.arg
    let now ← IO.monoNanosNow
    count := count + 1
    elapsed := now - startTime
  let mean := Float.ofNat elapsed / Float.ofNat count
  --IO.println s!"{bench.name} warmup avg: {mean}ns"
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
  IO.println s!"Running {bg.config.numSamples} samples in {expectedTime.floatPretty 2}s ({totalIters.natPretty} iterations)\n"
  --IO.println s!"Flat sample. Iters per sample: {itersPerSample}"
  let mut timings : Array Nat := #[]
  -- TODO: `mkArray` deprecated in favor of `replicate` in Lean v4.19
  let sampleIters := Array.mkArray bg.config.numSamples itersPerSample
  for iters in sampleIters do
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
  let mut timings : Array Nat := #[]
  for iters in sampleIters do
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

-- TODO: Ensure all array instances are used linearly for optimal performance
structure Distribution where
  d : Array Float := #[]
deriving Repr

-- TODO: ↑ coercion doesn't seem to work
instance : Coe Distribution (Array Float) where
  coe x := x.d

-- Gets the p value of the distribution, which is the likelihood of seeing the `t` value or a more extreme value in the distribution. Smaller p value => less likely
def Distribution.pValue (dist : Distribution) (t : Float) : Float :=
  let len := Float.ofNat dist.d.size
  let hits := Float.ofNat (dist.d.filter (· < t)).size
  (min len (len - hits)) / len * 2

def Distribution.percentile? (data : Distribution) (p : Float): Option Float :=
  if data.d.isEmpty || p > 100
  then .none
  else
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

-- Performs a one-sample bootstrap
-- Assumes `numSamples ≥ 2`
-- Gets `bootstrapSamples` resamples of the distribution and computes statistics for each
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
deriving Repr

def putNat (x : Nat) : Ixon.PutM := do
  let bytes := Ixon.natToBytesLE x
  Ixon.putBytes { data := bytes }

def putData' (xy : Nat × Nat) : Ixon.PutM := do
  Ixon.putNatl xy.fst
  Ixon.putNatl xy.snd

def putData (data : Data) : Ixon.PutM := do
  Ixon.putArray putData' data.d.toList

def getTupleNat : Ixon.GetM (Nat × Nat) := do
  return (← Ixon.getNatl, ← Ixon.getNatl)

def getData : Ixon.GetM Data := do
  let data ← Ixon.getArray getTupleNat
  return { d := data.toArray }

instance : Ixon.Serialize Data where
  put := Ixon.runPut ∘ putData
  get := Ixon.runGet getData

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

-- Performs a one-sample bootstrap of bivariate data
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

-- TODO: Use in `MeasurementData` and save outliers in `tukey.json`
structure LabeledSample where
  data : Array Float

structure ChangeEstimates where
  mean : Estimate
  median : Estimate

def putChangeEstimates (changeEst : ChangeEstimates) : Ixon.PutM := do
  putEstimate changeEst.mean
  putEstimate changeEst.median

def getChangeEstimates : Ixon.GetM ChangeEstimates := do
  let mean ← getEstimate
  let median ← getEstimate
  return { mean, median }

instance : Ixon.Serialize ChangeEstimates where
  put := Ixon.runPut ∘ putChangeEstimates
  get := Ixon.runGet getChangeEstimates

structure ChangeDistributions where
  mean : Distribution
  median : Distribution

structure ComparisonData where
  pValue : Float
  tDistribution : Distribution
  tValue : Float
  relativeEstimates : ChangeEstimates
  relativeDistributions : ChangeDistributions
  significanceThreshold : Float
  noiseThreshold : Float
  baseSample : Data
  baseAvgTimes : Array Float
  baseEstimates : Estimates

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

def tScore (xs ys : Distribution) : Float :=
  let (xBar, yBar) := (xs.mean, ys.mean)
  let (s2X, s2Y) := (xs.variance xBar, ys.variance yBar)
  let (nX, nY) := (Float.ofNat xs.d.size, Float.ofNat ys.d.size)
  let num := xBar - yBar
  let den := (s2X / nX + s2Y / nY).sqrt
  num / den

def Array.splitAt {α} (a : Array α) (n : Nat) : Array α × Array α :=
  (a.extract 0 n, a.extract n a.size)

-- Performs a mixed two-sample bootstrap
def tBootstrap (newAvgTimes baseAvgTimes : Distribution) (bootstrapSamples : Nat) : StateM StdGen Distribution := do
  let allTimes : Distribution := { d := newAvgTimes.d ++ baseAvgTimes.d }
  let newLen := newAvgTimes.d.size
  let mut tDistribution := #[]
  for _ in Array.range bootstrapSamples do
    let resample ← allTimes.resampleM allTimes.d.size
    let (xs, ys) := resample.d.splitAt newLen
    let t := tScore { d := xs } { d := ys }
    tDistribution := tDistribution.push t
  return { d := tDistribution }

def tTest (newAvgTimes baseAvgTimes : Distribution) (config : Config) (gen : StdGen) :(Float × Distribution) :=
  let tStatistic := tScore newAvgTimes baseAvgTimes
  let tDistribution := (tBootstrap newAvgTimes baseAvgTimes config.numSamples gen).run.fst
  -- Hack to filter out non-finite numbers from https://github.com/bheisler/criterion.rs/blob/ccccbcc15237233af22af4c76751a7aa184609b3/src/analysis/compare.rs#L86
  let tDistribution : Distribution := { d := tDistribution.d.filter (fun x => x.isFinite && !x.isNaN ) }
  (tStatistic, tDistribution)

def changeStats (xs ys : Distribution) : (Float × Float) :=
  (xs.mean / ys.mean - 1, xs.median / ys.median - 1)

-- TODO: Genericize bootstrap functions
-- Performs a two-sample bootstrap
def changeBootstrap (xs ys : Distribution) (numSamples bootstrapSamples : Nat) : StateM StdGen ChangeDistributions := do
  let mut means := #[]
  let mut medians := #[]
  for _ in Array.range bootstrapSamples do
    let resampleX ← xs.resampleM numSamples
    let resampleY ← ys.resampleM numSamples
    let (mean, median) := changeStats resampleX resampleY
    means := means.push mean
    medians := medians.push median
  return ⟨ { d := means }, { d := medians } ⟩

def buildChangeEstimates (changeDist : ChangeDistributions) (mean median confidenceLevel : Float) : ChangeEstimates :=
  let mean := changeDist.mean.toEstimate mean confidenceLevel
  let median := changeDist.median.toEstimate median confidenceLevel
  { mean, median }

def changeEstimates (newAvgTimes baseAvgTimes : Distribution) (config : Config) (gen : StdGen) : (ChangeEstimates × ChangeDistributions) :=
  let changeDistributions := (changeBootstrap newAvgTimes baseAvgTimes config.numSamples config.bootstrapSamples gen).run.fst
  let (mean, median) := changeStats newAvgTimes baseAvgTimes
  let changeEstimates := buildChangeEstimates changeDistributions mean median config.confidenceLevel
  (changeEstimates, changeDistributions)

-- Store `Estimates` and `Data` sample as Ixon on disk
-- Compare performance against prior run
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
