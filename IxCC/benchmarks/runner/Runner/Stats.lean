/-! Statistics shared by the process and entry reports: medians, the
percentile bootstrap of a median paired ratio, and a hierarchical bootstrap
of a geometric mean over fixtures (blocks resampled within each fixture).
Resampling is deterministic (xorshift), so a report is reproducible from its
samples. -/

namespace Runner

def median (values : Array Float) : Float :=
  let sorted := values.qsort (· < ·)
  if sorted.isEmpty then 0
  else if sorted.size % 2 == 1 then sorted[sorted.size / 2]!
  else (sorted[sorted.size / 2 - 1]! + sorted[sorted.size / 2]!) / 2

/-- One xorshift step. -/
def xorshift (state : UInt64) : UInt64 :=
  let s := state ^^^ (state <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

/-- Percentile bootstrap of the median paired ratio (deterministic resampling). -/
def bootstrap (ratios : Array Float) (rounds : Nat := 2000) : Float × Float := Id.run do
  if ratios.isEmpty then return (0, 0)
  let mut state : UInt64 := 0x243f6a8885a308d3
  let mut estimates : Array Float := #[]
  for _ in [:rounds] do
    let mut resample : Array Float := #[]
    for _ in [:ratios.size] do
      state := xorshift state
      resample := resample.push ratios[state.toNat % ratios.size]!
    estimates := estimates.push (median resample)
  let sorted := estimates.qsort (· < ·)
  return (sorted[rounds * 25 / 1000]!, sorted[rounds * 975 / 1000]!)

def geomean (values : Array Float) : Float :=
  if values.isEmpty then 0
  else Float.exp ((values.foldl (fun acc v => acc + Float.log v) 0) / values.size.toFloat)

/-- The geometric mean over fixtures of each fixture's median paired ratio,
with a 95% interval from a hierarchical bootstrap: each round resamples the
blocks of every fixture independently, takes each fixture's median, and
forms the geometric mean. -/
def geomeanBootstrap (perFixture : Array (Array Float)) (rounds : Nat := 2000) :
    Float × Float × Float := Id.run do
  let groups := perFixture.filter (!·.isEmpty)
  if groups.isEmpty then return (0, 0, 0)
  let point := geomean (groups.map median)
  let mut state : UInt64 := 0x13198a2e03707344
  let mut estimates : Array Float := #[]
  for _ in [:rounds] do
    let mut medians : Array Float := #[]
    for ratios in groups do
      let mut resample : Array Float := #[]
      for _ in [:ratios.size] do
        state := xorshift state
        resample := resample.push ratios[state.toNat % ratios.size]!
      medians := medians.push (median resample)
    estimates := estimates.push (geomean medians)
  let sorted := estimates.qsort (· < ·)
  return (point, sorted[rounds * 25 / 1000]!, sorted[rounds * 975 / 1000]!)

/-- Fixed-point decimal text with `digits` fractional digits. -/
def fmt (value : Float) (digits : Nat := 3) : String :=
  let scaled := (value.abs * (10 : Float) ^ digits.toFloat).round.toUInt64.toNat
  let whole := scaled / 10 ^ digits
  let frac := toString (scaled % 10 ^ digits)
  let sign := if value < 0 then "-" else ""
  if digits == 0 then s!"{sign}{whole}"
  else s!"{sign}{whole}.{"".pushn '0' (digits - frac.length)}{frac}"

/-- A ratio with its interval, `r [lo, hi]`. -/
def fmtInterval (point low high : Float) (digits : Nat := 3) : String :=
  s!"{fmt point digits} [{fmt low digits}, {fmt high digits}]"

/-- A ratio in scientific notation when it is too small or large to read at
three decimals (a folded twin). -/
def fmtRatio (value : Float) : String :=
  if value == 0 then "0"
  else if value.abs < 0.001 || value.abs >= 100000 then
    let exponent := (Float.log10 value.abs).floor
    let mantissa := value / (10 : Float) ^ exponent
    s!"{fmt mantissa 2}e{if exponent < 0 then "-" else ""}{fmt exponent.abs 0}"
  else fmt value

end Runner
