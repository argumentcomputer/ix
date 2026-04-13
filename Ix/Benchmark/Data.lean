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

/-- Creates a random permutation of the distribution with replacement -/
def Data.resampleM (data : Data) (numSamples : Nat) : StateM StdGen Data := do
  let mut rands := Array.mkEmpty numSamples
  for _ in [:numSamples] do
    let res ← data.randDataM
    rands := rands.push res
  return { d := rands }

/-- Performs a one-sample bootstrap of bivariate data -/
def Data.bootstrap (data : Data) (numSamples bootstrapSamples : Nat) : StateM StdGen Distribution := do
  let mut slopes := Array.mkEmpty bootstrapSamples
  for _ in [:bootstrapSamples] do
    let resample ← data.resampleM numSamples
    slopes := slopes.push resample.slope
  return { d := slopes }

/--
Centered coefficient of determination (R²) for the no-intercept linear model
`y = slope * x`:

  R² = 1 − SS_res / SS_tot
  SS_res = Σ (yᵢ − slope·xᵢ)²
  SS_tot = Σ (yᵢ − ȳ)²         where ȳ = mean(y)

Clamped to `[0, 1]`. If the sample has zero total variance (all y values
equal), returns `1.0` — the model trivially fits. A high R² (e.g. > 0.98)
indicates the linear time-per-iteration model is a good fit for the sample;
a low R² means the bench is doing something nonlinear or is dominated by noise.
-/
def Data.rSquared (data : Data) (slope : Float) : Float :=
  let n := Float.ofNat data.d.size
  if n == 0 then 1.0 else
  let ySum := data.d.foldl (fun acc (_, y) => acc + Float.ofNat y) 0.0
  let yMean := ySum / n
  let (ssRes, ssTot) := data.d.foldl (fun (r, t) (x, y) =>
    let yF := Float.ofNat y
    let residual := yF - slope * Float.ofNat x
    let centered := yF - yMean
    (r + residual * residual, t + centered * centered)) (0.0, 0.0)
  if ssTot == 0 then 1.0
  else max 0.0 (1.0 - ssRes / ssTot)

/--
Performs a linear regression on a sample, returning the bootstrap distribution,
the estimated slope, and the R² goodness-of-fit.

Used only with linear sampling mode.
-/
def Data.regression (data : Data) (config : Config) (gen : StdGen) :
    (Distribution × Estimate × Float) :=
  let distribution := ((data.bootstrap config.numSamples config.bootstrapSamples).run gen).fst
  let pointEstimate := data.slope
  let confidenceInterval := distribution.confidenceInterval config.confidenceLevel
  let mean := distribution.mean
  let stdErr := distribution.stdDev mean
  let estimate : Estimate := { confidenceInterval, pointEstimate, stdErr }
  let r2 := data.rSquared pointEstimate
  (distribution, estimate, r2)

end
