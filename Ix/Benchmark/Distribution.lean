module
public import Ix.Benchmark.Common
public import Ix.Benchmark.Estimate

public section

structure Distribution where
  d : Array Float
  deriving Repr, Inhabited, Lean.ToJson, Lean.FromJson

-- TODO: ↑ coercion doesn't seem to work
instance : Coe Distribution (Array Float) where
  coe x := x.d

/-- Two-sided p-value: the probability of observing a test statistic at least
as extreme as `t` under the null distribution `dist`. Returns a value in
`[0, 1]`; smaller means the observed `t` is more extreme (less consistent with
the null hypothesis). -/
def Distribution.pValue (dist : Distribution) (t : Float) : Float :=
  if dist.d.isEmpty then 1.0 else
  let len := Float.ofNat dist.d.size
  let hits := Float.ofNat (dist.d.filter (· < t)).size
  2 * (min hits (len - hits)) / len

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
  if dist.d.isEmpty then 0.0 else
  dist.d.sum / Float.ofNat dist.d.size

def Distribution.median (dist : Distribution) : Float :=
  (dist.percentile? 50).get!

def Distribution.variance (dist : Distribution) (mean : Float) : Float :=
  if dist.d.size ≤ 1 then 0.0 else
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
  let mut rands := Array.mkEmpty numSamples
  for _ in [:numSamples] do
    let res ← dist.randDistM
    rands := rands.push res
  return { d := rands }


/--
Performs a one-sample bootstrap: resamples the distribution `bootstrapSamples`
times and computes mean, stdDev, median, and medianAbsDev for each resample.

Assumes `numSamples ≥ 2`
-/
def Distribution.bootstrap (dist : Distribution) (numSamples bootstrapSamples : Nat) : StateM StdGen Distributions := do
  let mut means := Array.mkEmpty bootstrapSamples
  let mut stdDevs := Array.mkEmpty bootstrapSamples
  let mut medians := Array.mkEmpty bootstrapSamples
  let mut medianAbsDevs := Array.mkEmpty bootstrapSamples
  for _ in [:bootstrapSamples] do
    let resample ← dist.resampleM numSamples
    let m := resample.mean
    means := means.push m
    stdDevs := stdDevs.push (resample.stdDev m)
    let med := resample.median
    medians := medians.push med
    medianAbsDevs := medianAbsDevs.push (resample.medianAbsDev med)
  return { means := ⟨means⟩, medians := ⟨medians⟩, medianAbsDevs := ⟨medianAbsDevs⟩, slope := none, stdDevs := ⟨stdDevs⟩ }

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

/--
Qualitative classification of how much outliers are inflating the sample's
std-dev estimate, ported from Haskell criterion's `OutlierEffect`.
-/
inductive OutlierEffect where
  /-- < 1% of the variance can be blamed on outliers — numbers are trustworthy. -/
  | unaffected
  /-- 1%–10% — minor but noticeable. -/
  | slight
  /-- 10%–50% — take the reported CI with a grain of salt. -/
  | moderate
  /-- ≥ 50% — measurements are essentially useless. -/
  | severe
  deriving Repr, BEq, Ord, Lean.ToJson, Lean.FromJson

/-- Summary of the outlier-variance analysis for a sample. -/
structure OutlierVariance where
  effect : OutlierEffect
  /-- English description slotted into the `variance attributable to outliers:
      N% ({desc})` message — one of `"unaffected"`, `"slightly inflated"`,
      `"moderately inflated"`, or `"severely inflated"`. -/
  desc : String
  /-- Quantitative fraction in `[0, 1]`. -/
  fraction : Float
  deriving Repr, Lean.ToJson, Lean.FromJson

/--
Computes the fraction of the sample std-dev estimate that is attributable to
outliers, following Haskell criterion's `outlierVariance` (`Analysis.hs:85-112`).

Takes the bootstrap point estimates of the sample mean and std-dev plus the
original iteration count `numSamples` (e.g. `100` for a default `bgroup`).
-/
def outlierVariance (meanEst stdDevEst : Estimate) (numSamples : Float) : OutlierVariance :=
  -- Names from Haskell criterion's implementation:
  --   sb  = bootstrap point estimate of std dev          (σ_b)
  --   ua  = mean point estimate divided by `numSamples`  (µ_a)
  --   ugMin = ua / 2                                     (µ_{g,min})
  --   sg  = contributed std dev from the outlier model   (σ_g)
  let sb  := stdDevEst.pointEstimate
  let sb2 := sb * sb
  let ua  := meanEst.pointEstimate / numSamples
  let ugMin := ua / 2
  let sg  := min (ugMin / 4) (sb / numSamples.sqrt)
  let sg2 := sg * sg
  let varOut (c : Float) : Float :=
    let ac := numSamples - c
    (ac / numSamples) * (sb2 - ac * sg2)
  let cMax (x : Float) : Float :=
    let k := ua - x
    let d := k * k
    let ad := numSamples * d
    let k0 := -numSamples * ad
    let k1 := sb2 - numSamples * sg2 + ad
    let det := max (k1 * k1 - 4 * sg2 * k0) 0
    (-2 * k0 / (k1 + det.sqrt)).floor
  let minBy (f : Float → Float) (q r : Float) : Float := min (f q) (f r)
  let varOutMin := (minBy varOut 1 (minBy cMax 0 ugMin)) / sb2
  let (effect, desc) :=
    if varOutMin < 0.01 then (OutlierEffect.unaffected, "unaffected")
    else if varOutMin < 0.1 then (OutlierEffect.slight, "slightly inflated")
    else if varOutMin < 0.5 then (OutlierEffect.moderate, "moderately inflated")
    else (OutlierEffect.severe, "severely inflated")
  { effect, desc, fraction := varOutMin }

end
