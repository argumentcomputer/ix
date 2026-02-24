module
public import Ix.Benchmark.Common
public import Ix.Benchmark.Estimate

public section

-- TODO: Ensure all array instances are used linearly for optimal performance
structure Distribution where
  d : Array Float
  deriving Repr, Inhabited, Lean.ToJson, Lean.FromJson

-- TODO: ↑ coercion doesn't seem to work
instance : Coe Distribution (Array Float) where
  coe x := x.d

/-- Gets the p value of the distribution, which is the likelihood of seeing the `t` value or a more extreme value in the distribution. Smaller p value => less likely -/
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

structure Distributions where
  means: Distribution
  medians: Distribution
  medianAbsDevs : Distribution
  slope : Option (Distribution)
  stdDevs : Distribution
  deriving Inhabited, Repr

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

/-- Returns the data point in the distribution at a random index -/
def Distribution.randDistM (dist : Distribution) : StateM StdGen Float := do
  let gen ← get
  let (n, gen') := randNat gen 0 (dist.d.size - 1)
  set gen'
  return dist.d[n]!

/-- Creates a random permutation of the distribution with replacement (i.e. duplicates are permitted) -/
def Distribution.resampleM (dist : Distribution) (numSamples : Nat) : StateM StdGen Distribution := do
  let mut rands := #[]
  for _ in Array.range numSamples do
    let res ← dist.randDistM
    rands := rands.push res
  return { d := rands }

/--
Performs a one-sample bootstrap, gets `bootstrapSamples` resamples of the distribution and computes statistics for each.

Assumes `numSamples ≥ 2`
-/
def Distribution.bootstrap (dist : Distribution) (numSamples bootstrapSamples : Nat) : StateM StdGen Distributions := do
  let mut means : Distribution := default
  let mut stdDevs : Distribution := default
  let mut medians : Distribution := default
  let mut medianAbsDevs : Distribution := default
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

def Distributions.buildEstimates (dists : Distributions) (points : PointEstimates) (confidenceLevel : Float) : Estimates :=
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
  let est := dists.buildEstimates points config.confidenceLevel
  (dists, est)

end
