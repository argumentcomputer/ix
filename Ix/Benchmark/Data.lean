module
public import Ix.Benchmark.Distribution

public section

structure Data where
  d : Array (Nat × Nat)
  deriving Repr, Inhabited, Lean.ToJson, Lean.FromJson

def dots (acc xys : Nat × Nat) : (Nat × Nat) :=
  let xy := acc.fst + xys.fst * xys.snd
  let xs := acc.snd + xys.fst * xys.fst
  (xy, xs)

def Data.slope (data : Data) : Float :=
  let (xy, x2) := data.d.foldl dots (0, 0)
  Float.ofNat xy / Float.ofNat x2

/-- Returns the data point in the distribution at a random index -/
def Data.randDataM (data : Data) : StateM StdGen (Nat × Nat) := do
  let gen ← get
  let (n, gen') := randNat gen 0 (data.d.size - 1)
  set gen'
  return data.d[n]!

/-- Creates a random permutation of the distribution with replacement (i.e. duplicates are permitted) -/
def Data.resampleM (data : Data) (numSamples : Nat) : StateM StdGen Data := do
  let mut rands := #[]
  for _ in Array.range numSamples do
    let res ← data.randDataM
    rands := rands.push res
  return { d := rands }

/-- Performs a one-sample bootstrap of bivariate data -/
def Data.bootstrap (data : Data) (numSamples bootstrapSamples : Nat): StateM StdGen Distribution := do
  let mut slopes : Array Float := #[]
  for _ in Array.range bootstrapSamples do
    let resample ← Data.resampleM data numSamples
    let slope := resample.slope
    slopes := slopes.push slope
  return { d := slopes }

/--
Performs a linear regression on a sample, returning a pair of the bootstrap samples and the estimated slope by fitting the data to a straight line.

Used only with linear sampling mode.
-/
def Data.regression (data : Data) (config : Config) (gen : StdGen) : (Distribution × Estimate) :=
  let distribution := ((data.bootstrap config.numSamples config.bootstrapSamples).run gen).fst
  let pointEstimate := data.slope
  let confidenceInterval := distribution.confidenceInterval config.confidenceLevel
  let mean := distribution.mean
  let stdErr := distribution.stdDev mean
  let estimate : Estimate := { confidenceInterval, pointEstimate, stdErr }
  (distribution, estimate)

end
