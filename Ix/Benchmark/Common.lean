module
public import Lean.Data.Json

public section

inductive SamplingMode where
  /-- Every sample runs the same number of iterations. Best for expensive
      benches where linear's `[d, 2d, ..., Nd]` schedule would exceed the
      target sample time. -/
  | flat : SamplingMode
  /-- Iteration counts grow linearly `[d, 2d, ..., Nd]`; the per-iteration time
      is recovered by regression, which is more robust to single-sample outliers
      but 50× more total work for `N = 100`. -/
  | linear : SamplingMode
  /-- Pick flat or linear based on warmup timing: choose linear if its expected total time is at
      most 2× the target sample time, otherwise flat. -/
  | auto : SamplingMode
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

inductive SerdeFormat where
  | json
  | ixon
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

instance : ToString SerdeFormat where
  toString sf := match sf with
  | .json => "json"
  | .ixon => "ixon"

/--
Controls how much diagnostic output the benchmark harness prints. Can be overridden per-run via the
`BENCH_VERBOSITY` env var (see `getConfigEnv`).
-/
inductive Verbosity where
  /-- Only per-bench summary lines (time/thrpt/change/perf note). Suppresses
      warmup banners, "Running N samples" lines, and the
      outlier-variance/breakdown output. -/
  | quiet
  /-- Default output. Warmup + running lines print. Outlier-variance warning
      and Tukey breakdown print only when the outliers are moderately or
      severely inflating the std-dev estimate. -/
  | normal
  /-- Everything in `normal` plus R² always printed next to the time line,
      full Tukey outlier breakdown always printed, and the outlier-variance
      warning always printed regardless of severity. -/
  | verbose
  deriving Repr, BEq, Ord, Lean.ToJson, Lean.FromJson

/--
Describes the work performed by one iteration of a benchmark, for rate
computations in the report.

- `Bits`: bits processed per iteration; formatted with decimal (1000-based) units (`b/s`, `Kb/s`, ..).
- `Bytes`: bytes processed per iteration; formatted with binary (1024-based) units (`B/s`, `KiB/s`, ..).
- `BytesDecimal`: bytes processed per iteration; formatted with decimal (1000-based) units (`B/s`, `KB/s`, ..).
- `Elements`: generic elements per iteration; formatted with decimal units using the
  `label` (defaults to `elem`, e.g. `elem/s`, `Kelem/s`, .., or with label "hashes": `hashes/s`, `Khashes/s`, ..).
- `ElementsAndBytes`: reports both elements/s and bytes/s in the same cell. The
  elements side accepts a custom `elementsLabel` with the same semantics as
  `Elements`; the bytes side always uses the binary `B` scheme.
-/
inductive Throughput where
  | Bits (n : UInt64)
  | Bytes (n : UInt64)
  | BytesDecimal (n : UInt64)
  | Elements (n : UInt64) (label : String := "elem")
  | ElementsAndBytes (elements : UInt64) (bytes : UInt64) (elementsLabel : String := "elem")
  deriving Repr, Lean.ToJson, Lean.FromJson

structure Config where
  /-- Warmup time in seconds -/
  warmupTime : Float := 3.0
  /-- Target sample time in seconds. If the time per iteration is too long then the actual sample time will run longer and print a warning -/
  sampleTime : Float := 5.0
  /-- Number of data points to collect per sample -/
  numSamples : Nat := 100
  /-- Sample in flat, linear, or auto mode. Defaults to `.auto`.
      Linear is more robust to per-sample outliers but runs 50×
      more total iterations than flat for `numSamples = 100`, so it's unusable
      for expensive benches. Auto picks linear when it fits in ~2× the target
      sample time and falls back to flat otherwise. -/
  samplingMode : SamplingMode := .auto
  /-- Number of bootstrap samples (with replacement) to run.
      Defaults to 10K rather than criterion.rs's 100K because Lean's
      runtime has ~10x per-operation overhead for many operations vs native Rust,
      making 100K bootstrap iterations take ~5s per bench. 10K produces
      statistically indistinguishable confidence intervals for typical Lean benchmarks
      (µs–s scale) where execution variance already dwarfs bootstrap
      estimation noise. -/
  bootstrapSamples : Nat := 10000
  /-- Confidence level for estimates -/
  confidenceLevel : Float := 0.95
  /-- Significance level for hypothesis testing when comparing two benchmark runs for significant difference -/
  significanceLevel : Float := 0.05
  /-- Noise threshold when comparing two benchmark means, if percent change is within this threshold then it's considered noise -/
  noiseThreshold : Float := 0.01
  /-- Serde format for bench report written to disk, defaults to JSON for human readability -/
  serde : SerdeFormat := .json
  /--
  Whether to skip sampling altogether and only collect a single data point.
  Takes precedence over all sampling settings (`samplingMode`, `numSamples`,
  `sampleTime`, `warmupTime`).

  Rule of thumb (based on the mean per-iteration time `μ` of the bench, as
  estimated during warmup): enable `oneShot := true` when a single iteration
  takes longer than ~1s. At that point even flat-mode sampling
  (`numSamples × μ`) exceeds 100s per bench, and the statistical estimates
  gained from a full sample run rarely justify the wall-clock cost.

  Concretely:
  - μ < ~50ms   ⇒ leave `.auto`: linear sampling, full statistics
  - μ ~ 50ms–1s ⇒ leave `.auto`: falls back to flat sampling automatically
  - μ > ~1s     ⇒ set `oneShot := true` (total group time stays bounded
                  by `numBenches × μ`, not `numBenches × numSamples × μ`)
  -/
  oneShot : Bool := false
  /-- Whether to generate a Markdown report of all timings including comparison to disk if possible-/
  report : Bool := false
  /--
  Throughput for the next benchmark registered in a `bgroup` do-block. Each
  `bench`/`benchIO` call inside a `bgroup` captures a snapshot of this field
  at registration time, so we can set it once and register several benches,
  or mutate it between registrations via the monadic `throughput` helper.
  -/
  throughput : Option Throughput := none
  /--
  If `true`, `bgroup` prints a weighted-average throughput across all benches
  in the group at the end of the run. The average is weighted by the primary
  quantity of each bench (e.g. bytes processed). Requires every bench in the group to use the same
  `Throughput` variant; otherwise the average is skipped with a warning.
  -/
  avgThroughput : Bool := false
  /-- Diagnostic output level. Overridable via `BENCH_VERBOSITY` env var
      (see `getConfigEnv`). -/
  verbosity : Verbosity := .normal
  deriving Repr, Lean.ToJson, Lean.FromJson


/--
Overrides config values with the corresponding `BENCH_*` env vars.

- `BENCH_SERDE`: `"ixon"` to use Ixon format, otherwise JSON (default)
- `BENCH_REPORT`: `"1"` to generate a Markdown report
- `BENCH_VERBOSITY`: `q` (quiet) | `v` (verbose); omit for normal

Example: `BENCH_VERBOSITY=v lake exe bench-shardmap`
-/
def getConfigEnv (config : Config) : IO Config := do
  let serde : SerdeFormat := if (← IO.getEnv "BENCH_SERDE") == some "ixon" then .ixon else config.serde
  let report := if let some val := (← IO.getEnv "BENCH_REPORT") then val == "1" else config.report
  let verbosity : Verbosity ← do
    match (← IO.getEnv "BENCH_VERBOSITY") with
    | some "q" => pure .quiet
    | some "v" => pure .verbose
    | _ => pure config.verbosity
  return { config with serde, report, verbosity }

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

Returns the raw `.toString` representation for non-finite values (NaN, Inf).
-/
def Float.floatPretty (float : Float) (precision : Nat): String :=
  if !float.isFinite then float.toString
  else
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

/-- Formats a bytes-per-second `rate` with binary (1024-based) unit suffixes:
    `B/s`, `KiB/s`, `MiB/s`, `GiB/s`. -/
def Float.formatBytesRate (rate : Float) : String :=
  if rate ≥ 1024.0 * 1024.0 * 1024.0
  then (rate / (1024.0 * 1024.0 * 1024.0)).floatPretty 2 ++ " GiB/s"
  else if rate ≥ 1024.0 * 1024.0
  then (rate / (1024.0 * 1024.0)).floatPretty 2 ++ " MiB/s"
  else if rate ≥ 1024.0
  then (rate / 1024.0).floatPretty 2 ++ " KiB/s"
  else
    rate.floatPretty 2 ++ " B/s"

/-- Formats a per-second `rate` with decimal (1000-based) unit prefixes
    and the given `unit` label (e.g. `"elem"`, `"b"`, `"B"`, `"hashes"`). -/
def Float.formatRate (rate : Float) (unit : String) : String :=
  if rate ≥ 1e9
  then (rate / 1e9).floatPretty 2 ++ " G" ++ unit ++ "/s"
  else if rate ≥ 1e6
  then (rate / 1e6).floatPretty 2 ++ " M" ++ unit ++ "/s"
  else if rate ≥ 1e3
  then (rate / 1e3).floatPretty 2 ++ " K" ++ unit ++ "/s"
  else
    rate.floatPretty 2 ++ " " ++ unit ++ "/s"

/--
Extracts the primary quantity of work per iteration from a `Throughput`.
For `ElementsAndBytes`, the elements count is considered the primary quantity.
-/
def Throughput.quantity (t : Throughput) : UInt64 :=
  match t with
  | .Bits n => n
  | .Bytes n => n
  | .BytesDecimal n => n
  | .Elements n _ => n
  | .ElementsAndBytes e _ _ => e

/--
True iff two `Throughput` values use the same variant (regardless of numeric
payload or custom label). Used to decide whether a weighted-average rate
across a group of benches is meaningful.
-/
def Throughput.sameVariant (a b : Throughput) : Bool :=
  match a, b with
  | .Bits _,             .Bits _             => true
  | .Bytes _,            .Bytes _            => true
  | .BytesDecimal _,     .BytesDecimal _     => true
  | .Elements _ _,       .Elements _ _       => true
  | .ElementsAndBytes _ _ _, .ElementsAndBytes _ _ _ => true
  | _, _ => false

/--
Formats an already-computed primary per-second `rate` using the unit scheme
of the given `Throughput` variant (binary vs decimal, bytes vs elements, ..).
The numeric payload of `t` is ignored — only the variant and (for
`Elements`/`ElementsAndBytes`) the custom label are consulted.
-/
def Throughput.formatRateValue (t : Throughput) (rate : Float) : String :=
  match t with
  | .Bits _ => Float.formatRate rate "b"
  | .Bytes _ => Float.formatBytesRate rate
  | .BytesDecimal _ => Float.formatRate rate "B"
  | .Elements _ label => Float.formatRate rate label
  | .ElementsAndBytes _ _ label => Float.formatRate rate label

/--
Computes the per-second rate (primary quantity per iteration divided by
iteration time) of a `Throughput` given a typical iteration time in
nanoseconds. Returns `0` if `timeNs ≤ 0`.
-/
def Throughput.rate (t : Throughput) (timeNs : Float) : Float :=
  if timeNs ≤ 0 then 0.0 else
  t.quantity.toNat.toFloat * 1e9 / timeNs

/--
Formats a `Throughput` value and a typical iteration time `timeNs` as a
human-readable rate string.
-/
def Throughput.formatRate (t : Throughput) (timeNs : Float) : String :=
  if timeNs ≤ 0 then "—" else
  match t with
  | .ElementsAndBytes e b label =>
    let eRate := e.toNat.toFloat * 1e9 / timeNs
    let bRate := b.toNat.toFloat * 1e9 / timeNs
    let eStr := Float.formatRate eRate label
    let bStr := Float.formatBytesRate bRate
    s!"{eStr} / {bStr}"
  | _ => t.formatRateValue (t.rate timeNs)

end
