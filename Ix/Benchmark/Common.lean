inductive SamplingMode where
  | flat : SamplingMode
  | linear : SamplingMode
  deriving Repr, BEq

inductive SerdeFormat where
  | json
  | ixon
  deriving Repr, BEq

instance : ToString SerdeFormat where
  toString sf := match sf with
  | .json => "json"
  | .ixon => "ixon"

inductive ThroughputUnit where
| bytes (bytes : Nat)
| elements (elems : Nat)
  deriving Repr

structure Config where
  /-- Warmup time in seconds -/
  warmupTime : Float := 3.0
  /-- Target sample time in seconds. If the time per iteration is too long then the actual sample time will run longer and print a warning -/
  sampleTime : Float := 5.0
  /-- Number of data points to collect per sample -/
  numSamples : Nat := 100
  /-- Sample in flat or linear mode -/
  samplingMode : SamplingMode := .flat
  /-- Number of bootstrap samples (with replacement) to run -/
  bootstrapSamples : Nat := 100000
  /-- Confidence level for estimates -/
  confidenceLevel : Float := 0.95
  /-- Significance level for hypothesis testing when comparing two benchmark runs for significant difference -/
  significanceLevel : Float := 0.05
  /-- Noise threshold when comparing two benchmark means, if percent change is within this threshold then it's considered noise -/
  noiseThreshold : Float := 0.01
  /-- Serde format for bench report written to disk, defaults to JSON for human readability -/
  serde : SerdeFormat := .json
  /-- Throughput -/
  throughput : Option ThroughputUnit := .none
  /-- Whether to skip sampling altogether and only collect a single data point. Takes precedence over all sampling settings. Used for expensive benchmarks -/
  oneShot : Bool := false
  /-- Whether to generate a Markdown report of all timings including comparison to disk if possible-/
  report : Bool := false
  deriving Repr

-- TODO: Integrate this with a `lake bench` CLI to set config options via flags
/-- Overrides config values with the corresponding `BENCH_<SETTING>` env vars if they are set -/
def getConfigEnv (config : Config) : IO Config := do
  let serde : SerdeFormat := if (← IO.getEnv "BENCH_SERDE") == some "ixon" then .ixon else config.serde
  let report := if let some val := (← IO.getEnv "BENCH_REPORT") then val == "1" else config.report
  return { config with serde, report }

@[inline] def Float.toNanos (f : Float) : Float := f * 10 ^ 9

@[inline] def Float.toSeconds (f : Float) : Float := f / 10 ^ 9

@[inline] def Nat.toSeconds (n : Nat) : Float := Float.ofNat n / 10 ^ 9

def Nat.natPretty (n : Nat) : String :=
  if n ≥ 10 ^ 9
  then
    toString (n / 10 ^ 9) ++ "B"
  else if n ≥ 10 ^ 6
  then
    toString (n / 10 ^ 6 ) ++ "M"
  else
    toString n

def percentChange (old : Float) (new : Float) : Float :=
  (new - old) / old.abs * 100

def Float.variablePrecision (float : Float) (precision : Nat) : Float :=
  let moveDecimal := Float.ofNat $ 10 ^ precision
  -- Move the decimal right to the desired precision, round to the nearest integer, then move the decimal back
  (float * moveDecimal).round / moveDecimal

/--
Rounds a `Float` to the desired number of decimal places, then prints it with trailing zeros removed.

E.g. `10.012345.floatPretty 5` => `"10.01235"`

Panics if float is a NaN.
-/
def Float.floatPretty (float : Float) (precision : Nat): String :=
  let precise := float.variablePrecision precision
  let parts := precise.toString.splitOn "."
  let integer := parts[0]!
  let fractional := parts[1]!.take precision
  if !fractional.isEmpty
  then integer ++ "." ++ fractional
  else integer

/--
Formats a time in ns as an xx.yy string with time units.

Examples:

`10.1234.formatNanos` => `"10.12ns"`

`(10.0 ^ 9) + 0.123` => `"1.00s"`
-/
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

def color (code : String) (s : String) : String :=
  s!"\x1b[{code}m{s}\x1b[0m"

def red := color "31"

def green := color "32"

def yellow := color "33"

def bold := color "1"

def formatPercent (p : Float) : String :=
  let percent := (p * 100).floatPretty 4 ++ "%"
  if p > 0 then
    s!"+{percent}"
  else
    percent
