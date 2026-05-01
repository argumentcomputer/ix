module
public import Ix.Benchmark.Data

public section

-- TODO: Use in `MeasurementData` and save outliers in `tukey.json`
structure LabeledSample where
  data : Array Float

structure ChangeEstimates where
  mean : Estimate
  median : Estimate
  deriving Lean.ToJson, Lean.FromJson, Repr

structure ChangeDistributions where
  mean : Distribution
  median : Distribution
  deriving Repr

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
  deriving Repr

def tScore (xs ys : Distribution) : Float :=
  let (xBar, yBar) := (xs.mean, ys.mean)
  let (s2X, s2Y) := (xs.variance xBar, ys.variance yBar)
  let (nX, nY) := (Float.ofNat xs.d.size, Float.ofNat ys.d.size)
  let num := xBar - yBar
  let den := (s2X / nX + s2Y / nY).sqrt
  if den == 0 then 0.0 else num / den

def Array.splitAt {α} (a : Array α) (n : Nat) : Array α × Array α :=
  (a.extract 0 n, a.extract n a.size)

/-- Performs a mixed two-sample bootstrap -/
def tBootstrap (newAvgTimes baseAvgTimes : Distribution) (bootstrapSamples : Nat) : StateM StdGen Distribution := do
  let allTimes : Distribution := { d := newAvgTimes.d ++ baseAvgTimes.d }
  let newLen := newAvgTimes.d.size
  let mut tDistribution := Array.mkEmpty bootstrapSamples
  for _ in [:bootstrapSamples] do
    let resample ← allTimes.resampleM allTimes.d.size
    let (xs, ys) := resample.d.splitAt newLen
    tDistribution := tDistribution.push (tScore { d := xs } { d := ys })
  return { d := tDistribution }

def tTest (newAvgTimes baseAvgTimes : Distribution) (config : Config) (gen : StdGen) : (Float × Distribution) :=
  let tStatistic := tScore newAvgTimes baseAvgTimes
  let tDistribution := (tBootstrap newAvgTimes baseAvgTimes config.bootstrapSamples gen).run.fst
  -- Hack to filter out non-finite numbers from https://github.com/bheisler/criterion.rs/blob/ccccbcc15237233af22af4c76751a7aa184609b3/src/analysis/compare.rs#L86
  let tDistribution : Distribution := { d := tDistribution.d.filter (fun x => x.isFinite && !x.isNaN ) }
  (tStatistic, tDistribution)

def changeStats (xs ys : Distribution) : (Float × Float) :=
  (xs.mean / ys.mean - 1, xs.median / ys.median - 1)

/-- Performs a two-sample bootstrap for change estimation -/
def changeBootstrap (xs ys : Distribution) (numSamples bootstrapSamples : Nat) : StateM StdGen ChangeDistributions := do
  let mut means := Array.mkEmpty bootstrapSamples
  let mut medians := Array.mkEmpty bootstrapSamples
  for _ in [:bootstrapSamples] do
    let resampleX ← xs.resampleM numSamples
    let resampleY ← ys.resampleM numSamples
    means := means.push (resampleX.mean / resampleY.mean - 1)
    medians := medians.push (resampleX.median / resampleY.median - 1)
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

end
