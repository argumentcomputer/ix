import Ix.Benchmark.Distribution

/-- Outliers are classified per https://bheisler.github.io/criterion.rs/book/analysis.html#outlier-classification -/
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
def Distribution.runTukey (data : Distribution) : IO Unit := do
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
    IO.println <| yellow s!"Found {outLength} outliers among {samples} measurements"
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
