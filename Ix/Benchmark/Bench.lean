module
public import Ix.Address
public import Ix.Meta
public import Ix.Cronos
public import Ix.Address
public import Batteries

public import Ix.Benchmark.Serde
public import Ix.Benchmark.Tukey

public section

open Batteries (RBMap)

/-!
# Benchmarking library modeled after Criterion in Haskell and Rust

## Verbosity

Three levels controlled by `Config.verbosity`, the `BENCH_VERBOSITY` env var,
or the `-q` / `--quiet` / `-v` / `--verbose` command-line flags
(CLI > env var > `Config` default). See `getConfigEnv` for the precedence
rules, and the `Verbosity` enum doc comments for what each level prints.

- `quiet`   — only per-bench summary lines (time / thrpt / change / perf note)
- `normal`  — default; adds warmup + running lines, plus the variance-introduced-by-outliers warning and Tukey breakdown *only* when the outlier effect is moderate or severe
- `verbose` — adds R² alongside the time line, and always prints the variance warning + Tukey breakdown regardless of severity

Bench files wanting to pick up the CLI flags should call `setBenchArgs args`
at the top of `main (args : List String) : IO Unit`. Skipping this only
disables CLI flags — `Config.verbosity` and `BENCH_VERBOSITY` still work.

## Limitations
- Measures time in nanoseconds using `IO.monoNanosNow`, which is less precise than the picoseconds used in Criterion.rs
-/

/--
Computes the result and then wraps the return type in IO. This prevents Lean from optimizing away the function call due to an unused return value.
-/
@[never_extract, noinline]
def blackBoxIO (f : α → β) (a : α) : IO β := do
  pure $ f a

/--
A benchmark group defines a collection of related benchmarks that share a configuration, such as number of samples and noise threshold
-/
structure BenchGroup where
  name : String
  config : Config

inductive BenchFn ( α β : Type) where
| pure (fn : α → β)
| io (fn : α → IO β)

structure Benchmarkable (α β : Type) where
  name : String
  func : BenchFn α β
  arg : α

/-- If the function is pure, we need to wrap it in `blackBoxIO` so that Lean doesn't optimize away the result -/
def Benchmarkable.getFn (b : Benchmarkable α β) : α → IO β :=
  match b.func with
  | .pure f => blackBoxIO f
  | .io f => f

-- TODO: According to Criterion.rs docs the warmup iterations should increase linearly until the warmup time is reached, rather than one iteration per time check
def BenchGroup.warmup (bg : BenchGroup) (bench : Benchmarkable α β) : IO Float := do
  if bg.config.verbosity != .quiet then
    IO.println s!"Warming up for {bg.config.warmupTime.floatPretty 2}s"
  let mut count := 0
  let warmupNanos := Cronos.secToNano bg.config.warmupTime
  let mut elapsed := 0
  let func := bench.getFn
  let startTime ← IO.monoNanosNow
  while elapsed < warmupNanos do
    let _res ← func bench.arg
    let now ← IO.monoNanosNow
    count := count + 1
    elapsed := now - startTime
  let mean := Float.ofNat elapsed / Float.ofNat count
  return mean

def printRunning (config : Config) (expectedTime : Float) (numIters : Nat) (warningFactor : Nat) : IO Unit := do
  -- The "Unable to complete" warning is always shown — it's actionable at any verbosity.
  if warningFactor == 1 then
    IO.eprintln s!"Warning: Unable to complete {config.numSamples} samples in {config.sampleTime.floatPretty 2}s. You may wish to increase target time to {expectedTime.floatPretty 2}s"
  if config.verbosity != .quiet then
    IO.println s!"Running {config.numSamples} samples in {expectedTime.floatPretty 2}s ({numIters.natPretty} iterations)\n"

-- Core sampling loop that runs the benchmark function and returns the array of measured timings
def runSample (sampleIters : Array Nat) (bench : Benchmarkable α β) : IO (Array Nat) := do
  let func := bench.getFn
  let mut timings : Array Nat := #[]
  for iters in sampleIters do
    let start ← IO.monoNanosNow
    for _i in Array.range iters do
      let _res ← func bench.arg
    let finish ← IO.monoNanosNow
    timings := timings.push (finish - start)
  return timings

-- TODO: Recommend sample count if expectedTime >>> bg.config.sampleTime (i.e. itersPerSample == 1)
/--
Runs the sample as a sequence of constant iterations per data point, where the iteration count attempts to fit into the configurable `sampleTime` but cannot be less than 1.

Returns the iteration counts and elapsed time per data point.
-/
def BenchGroup.sampleFlat (bg : BenchGroup) (bench : Benchmarkable α β)
(warmupMean : Float) : IO (Array Nat × Array Nat) := do
  let targetTime := bg.config.sampleTime.toNanos
  let timePerSample := targetTime / (Float.ofNat bg.config.numSamples)
  let itersPerSample := (timePerSample / warmupMean).ceil.toUInt64.toNat.max 1
  let totalIters := itersPerSample * bg.config.numSamples
  let expectedTime := warmupMean * Float.ofNat itersPerSample * bg.config.numSamples.toSeconds
  printRunning bg.config expectedTime totalIters itersPerSample
  --IO.println s!"Flat sample. Iters per sample: {itersPerSample}"
  let sampleIters := Array.replicate bg.config.numSamples itersPerSample
  let timings ← runSample sampleIters bench
  return (sampleIters, timings)

/--
Runs the sample as a sequence of linearly increasing iterations [d, 2d, 3d, ..., Nd] where `N` is the total number of samples and `d` is a factor derived from the warmup iteration time.

The sum of this series should be roughly equivalent to the total `sampleTime`.

Returns the iteration counts and elapsed time per sample.
-/
def BenchGroup.sampleLinear (bg : BenchGroup) (bench : Benchmarkable α β) (warmupMean : Float) : IO (Array Nat × Array Nat) := do
  let totalRuns := bg.config.numSamples * (bg.config.numSamples + 1) / 2
  let targetTime := bg.config.sampleTime.toNanos
  -- `d` has a minimum value of 1 if the `warmupMean` is sufficiently large
  -- If so, that likely means the benchmark takes too long and target time should be increased, as well as considering other config options like flat sampling mode
  let d := (targetTime / warmupMean / (Float.ofNat totalRuns)).ceil.toUInt64.toNat.max 1
  let expectedTime := (Float.ofNat totalRuns) * (Float.ofNat d) * warmupMean.toSeconds
  let sampleIters := (Array.range bg.config.numSamples).map (fun x => (x + 1) * d)
  printRunning bg.config expectedTime sampleIters.sum d
  --IO.println s!"Linear sample. Iters increase by a factor of {d} per sample"
  let timings ← runSample sampleIters bench
  return (sampleIters, timings)

/-- Picks a concrete sampling mode for `.auto`, matching criterion.rs's
    `SamplingMode::choose_sampling_mode`: choose linear iff the expected total
    linear-mode time is at most 2× the target sample time, else fall back to
    flat. For `.flat` / `.linear` this returns the user's explicit choice. -/
def chooseSamplingMode (config : Config) (warmupMean : Float) : SamplingMode :=
  match config.samplingMode with
  | .flat => .flat
  | .linear => .linear
  | .auto =>
    let targetTime := config.sampleTime.toNanos
    let totalRuns := config.numSamples * (config.numSamples + 1) / 2
    let d := (targetTime / warmupMean / (Float.ofNat totalRuns)).ceil.toUInt64.toNat.max 1
    let expectedNs := (Float.ofNat totalRuns) * (Float.ofNat d) * warmupMean
    if expectedNs > 2 * targetTime then .flat else .linear

def BenchGroup.sample (bg : BenchGroup) (bench : Benchmarkable α β) (warmupMean : Float) : IO (Array Nat × Array Nat) := do
  match chooseSamplingMode bg.config warmupMean with
  | .flat => bg.sampleFlat bench warmupMean
  | .linear => bg.sampleLinear bench warmupMean
  | .auto => bg.sampleFlat bench warmupMean  -- unreachable after chooseSamplingMode

structure MeasurementData where
  data : Data
  avgTimes : Distribution
  absoluteEstimates : Estimates
  distributions : Distributions
  comparison : Option ComparisonData
  throughput : Option Throughput
  /-- R² goodness-of-fit for the linear regression, populated only in linear
      sampling mode. `none` for flat sampling. -/
  rSquared : Option Float := none
  /-- Outlier-variance analysis — how much the outliers inflate the sample
      std-dev estimate. `none` if the analysis was skipped (e.g. degenerate
      bench). -/
  outlierVariance : Option OutlierVariance := none
  /-- Tukey-fence outlier breakdown over the per-sample averaged times. -/
  outliers : Option Outliers := none
  deriving Repr

/--
On-disk payload for `sample.{fmt}`. Carries the raw `(iters, time)` data plus
a snapshot of the `Config` used to collect this run, so that a later run can
decide whether it's statistically comparable.

`config.samplingMode` is always the resolved mode (`.flat` or `.linear`);
`.auto` is resolved in `bgroup` before the `SampleRun` is constructed, and the
`Serialize SamplingMode` instance panics if `.auto` ever reaches disk.
-/
structure SampleRun where
  data : Data
  config : Config
  deriving Repr, Lean.ToJson, Lean.FromJson

def putSampleRun (r : SampleRun) : Ixon.PutM Unit := do
  Ixon.Serialize.put r.data
  Ixon.Serialize.put r.config

def getSampleRun : Ixon.GetM SampleRun := do
  let data ← Ixon.Serialize.get
  let config ← Ixon.Serialize.get
  return { data, config }

instance : Ixon.Serialize SampleRun where
  put := putSampleRun
  get := getSampleRun

/-- Compares bench results against prior run, using T-test to determine statistical significance -/
def BenchGroup.compare (bg : BenchGroup) (baseSample : Data) (baseEstimates : Estimates) (avgTimes : Distribution) (gen : StdGen) : ComparisonData :=
  -- Gets `base` data for comparison
  let baseAvgTimes : Distribution := { d := baseSample.d.map (fun (x,y) => Float.ofNat y / Float.ofNat x) }
  -- Then performs statistical analysis
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

/-- Retrieves prior bench result from disk and runs the comparison. Refuses
    to compare if the base was collected with a different resolved sampling
    mode (flat vs linear), since mixing the two through the same bootstrap
    gives misleading confidence intervals. -/
def BenchGroup.getComparison (bg : BenchGroup) (benchName : String)
    (avgTimes : Distribution) (config : Config) (resolvedMode : SamplingMode) :
    IO (Option ComparisonData) := do
  let benchPath := System.mkFilePath [".", ".lake", "benches", bg.name, benchName]
  let fileExt := toString config.serde
  -- Base data is at `new` since we haven't written the latest result to disk yet, which moves the prior data to `base`
  let basePath := benchPath / "new"
  if !(← System.FilePath.pathExists (basePath / s!"estimates.{fileExt}")) then
    return none
  let baseRun? : Option SampleRun ← try
    let r : SampleRun ← loadFile config.serde (basePath / s!"sample.{fileExt}")
    pure (some r)
  catch _ =>
    IO.eprintln s!"Skipping comparison for {benchName}: failed to parse base sample.{fileExt}"
    pure none
  let some baseRun := baseRun? | return none
  if baseRun.config.samplingMode != resolvedMode then
    IO.eprintln s!"Skipping comparison for {benchName}: base ran in {repr baseRun.config.samplingMode} mode, current run is {repr resolvedMode}"
    return none
  let baseEstimates : Estimates ← loadFile config.serde (basePath / s!"estimates.{fileExt}")
  let gen ← IO.stdGenRef.get
  return some $ bg.compare baseRun.data baseEstimates avgTimes gen

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


/-- Right-pads `s` with spaces to reach at least `width` characters. -/
def padLabel (s : String) (width : Nat) : String :=
  if s.length ≥ width then s
  else s ++ String.ofList (List.replicate (width - s.length) ' ')

/-- Criterion.rs-style label column width: minimum 24 chars, grows to fit the longest bench name in a group. -/
def minLabelWidth : Nat := 24

def BenchGroup.printResults (bg : BenchGroup) (benchName : String)
    (m : MeasurementData) (labelWidth : Nat) : IO Unit := do
  let estimates := m.absoluteEstimates
  let typicalEstimate := estimates.slope.getD estimates.mean
  let fullName := s!"{bg.name}/{benchName}"
  let label := padLabel fullName labelWidth
  let indent := padLabel "" labelWidth
  let verbosity := bg.config.verbosity
  let ciLb := typicalEstimate.confidenceInterval.lowerBound
  let ciUb := typicalEstimate.confidenceInterval.upperBound
  let lb := ciLb.formatNanos
  let pointEst := typicalEstimate.pointEstimate.formatNanos
  let ub := ciUb.formatNanos
  -- Append R² to the time line when linear-mode regression data is available.
  let r2Suffix := match m.rSquared with
    | some r2 => s!" R²={r2.floatPretty 3}"
    | none => ""
  IO.println s!"{label}time:   [{lb} {pointEst} {ub}]{r2Suffix}"
  if let some t := m.throughput then
    -- Higher time ⇒ lower throughput, so the low rate corresponds to the time CI upper bound.
    let thrptLow := t.formatRate ciUb
    let thrptPt := t.formatRate typicalEstimate.pointEstimate
    let thrptHigh := t.formatRate ciLb
    IO.println s!"{indent}thrpt:  [{thrptLow} {thrptPt} {thrptHigh}]"
  if let some comp := m.comparison
  then
    -- `p > significanceThreshold` means we fail to reject the null hypothesis
    -- that the two samples come from the same distribution — i.e. no
    -- statistically significant change.
    let notSignificant := comp.pValue > comp.significanceThreshold
    let meanEst := comp.relativeEstimates.mean
    let fmtSigned (f : Float) : String :=
      let body := (f * 100).floatPretty 4
      if f ≥ 0 then s!"+{body}" else body
    let pointEst := fmtSigned meanEst.pointEstimate
    let lb := fmtSigned meanEst.confidenceInterval.lowerBound
    let ub := fmtSigned meanEst.confidenceInterval.upperBound
    let symbol := if notSignificant then ">" else "<"
    IO.println s!"{indent}change: [{lb}% {pointEst}% {ub}%] (p = {comp.pValue.floatPretty 2} {symbol} {comp.significanceThreshold.floatPretty 2})"
    let explanation := if notSignificant
    then
      "No change in performance detected"
    else
      match compareToThreshold meanEst comp.noiseThreshold with
      | ComparisonResult.Improved => "Performance has improved"
      | ComparisonResult.Regressed => "Performance has regressed"
      | ComparisonResult.NonSignificant => "Change within noise threshold"
    IO.println s!"{indent}{explanation}"
  IO.println ""
  -- Outlier-variance warning + Tukey breakdown. Verbosity gating matches
  -- Haskell criterion's `Internal.hs:89-92`:
  --   • verbose             → always print the variance line AND breakdown
  --   • normal + > slight   → print the variance line AND breakdown
  --   • normal + ≤ slight   → silent
  --   • quiet               → silent regardless
  if let some ov := m.outlierVariance then
    -- `effect > .slight` means moderate or severe.
    let effectAboveSlight :=
      match ov.effect with
      | .moderate | .severe => true
      | _ => false
    let showVariance :=
      verbosity == .verbose
        || (effectAboveSlight && verbosity != .quiet)
    if showVariance then
      if let some outs := m.outliers then
        Outliers.note outs m.avgTimes.d.size indent
      let pct := (ov.fraction * 100).floatPretty 0
      IO.println s!"{indent}variance introduced by outliers: {pct}% ({ov.desc})"
      IO.println ""

-- TODO: Write sampling mode and config in `sample.json` for comparison
def saveComparison (groupName : String) (benchName : String) (comparison : ComparisonData) (config : Config) : IO Unit := do
  let changePath := System.mkFilePath [".", ".lake", "benches", groupName, benchName, "change"]
  storeFile config.serde comparison.relativeEstimates (changePath / s!"estimates.{toString config.serde}")

def mkDirs (groupName : String) (benchName : String) : IO (System.FilePath × System.FilePath) := do
  let benchPath := System.mkFilePath [".", ".lake", "benches", groupName, benchName]
  let (basePath, changePath, newPath) := (benchPath / "base", benchPath / "change", benchPath / "new")
  let (baseDir, changeDir, newDir) := (basePath.toString, changePath.toString, newPath.toString)
  let _out ← IO.Process.run {cmd := "mkdir", args := #["-p", baseDir, changeDir, newDir] }
  return (basePath, newPath)

def moveBaseFile (file : System.FilePath) (baseDir : String) : IO Unit := do
  if (← System.FilePath.pathExists file) then do
    -- Move prior bench from `new` to `base`
    let _ ← IO.Process.run { cmd := "mv", args := #[file.toString, baseDir] }

-- Results are always saved to `.lake/benches/<benchName>/new`. If files of the same serde format already exist from a prior run, move them to `base`.
-- `config.samplingMode` must be the resolved mode (`.flat` / `.linear`) — callers must never pass `.auto` here.
def saveMeasurement (groupName : String) (benchName : String) (mData : MeasurementData) (config : Config) : IO Unit := do
  let (basePath, newPath) ← mkDirs groupName benchName
  let baseDir := basePath.toString
  let fileExt := toString config.serde
  if let some compData := mData.comparison then
    saveComparison groupName benchName compData config
  let (newEstimatesFile, newSampleFile) := (newPath / s!"estimates.{fileExt}", newPath / s!"sample.{fileExt}")
  let newThroughputFile := newPath / s!"throughput.{fileExt}"
  moveBaseFile newSampleFile baseDir
  moveBaseFile newEstimatesFile baseDir
  moveBaseFile newThroughputFile baseDir
  let sampleRun : SampleRun := { data := mData.data, config }
  storeFile config.serde sampleRun newSampleFile
  storeFile config.serde mData.absoluteEstimates newEstimatesFile
  if let some t := mData.throughput then
    storeFile config.serde t newThroughputFile

inductive BenchResult where
| oneShot : OneShot → BenchResult
| sample : Estimates → BenchResult
  deriving Repr

def BenchResult.getTime (bench: BenchResult) : Float :=
  match bench with
  | oneShot o => o.benchTime.toFloat
  | sample s => s.mean.pointEstimate

-- TODO: Include input parameters if specified for post-processing
-- E.g. Blake3 bench wants to have `dataSize` and `numHashes`
-- Currently has to parse this from the `function` string
structure BenchReport where
  function: String
  newBench : BenchResult
  baseBench : Option BenchResult
  percentChange : Option Float
  throughput : Option Throughput := none

/-- Rendered display string for a report's throughput, or `"N/A"` if `none`. -/
def BenchReport.throughputStr (r : BenchReport) : String :=
  match r.throughput with
  | some t => t.formatRate r.newBench.getTime
  | none => "N/A"

/--
Computes the weighted-average primary throughput rate across a collection of
reports, weighted by each bench's primary quantity. Returns `none` if no
report has throughput set, or if the reports use more than one `Throughput`
variant (averaging across variants — e.g. bytes/s and elements/s — would be
meaningless). On success, returns the variant of the first throughput-bearing
report (used to pick display units) together with the averaged rate.
-/
def weightedAverageThroughput (reports : Array BenchReport) : Option (Throughput × Float) := Id.run do
  let mut representative : Option Throughput := none
  let mut sumQty : Float := 0.0
  let mut weightedSum : Float := 0.0
  for r in reports do
    match r.throughput with
    | none => pure ()
    | some t =>
      match representative with
      | none => representative := some t
      | some t0 =>
        unless t.sameVariant t0 do
          return none
      let qty := t.quantity.toNat.toFloat
      let rate := t.rate r.newBench.getTime
      sumQty := sumQty + qty
      weightedSum := weightedSum + qty * rate
  match representative with
  | none => return none
  | some t =>
    if sumQty == 0 then return none
    return some (t, weightedSum / sumQty)

def percentChangeToString (pc : Float) : String :=
  let rounded := (100 * pc).floatPretty 2
  if pc < 0 then s!"{rounded.drop 1}% faster"
  else if pc > 0 then s!"{rounded}% slower"
  else "No change"

structure ColumnWidths where
  function : Nat
  newBench : Nat
  baseBench : Nat
  percentChange : Nat
  /-- `none` ⇒ the Throughput column is not rendered for this group. -/
  throughput : Option Nat

def getColumnWidths' (maxWidths : ColumnWidths) (row: BenchReport) : ColumnWidths :=
  let fnLen := row.function.length
  let function := if fnLen > maxWidths.function then fnLen else maxWidths.function
  let newBenchLen := row.newBench.getTime.formatNanos.length
  let newBench := if newBenchLen > maxWidths.newBench then newBenchLen else maxWidths.newBench
  let baseBench := if let some baseBench := row.baseBench then
    let baseBenchLen := baseBench.getTime.formatNanos.length
    if baseBenchLen > maxWidths.baseBench then baseBenchLen
    else maxWidths.baseBench
  else maxWidths.baseBench
  let percentChange := if let some percentChange := row.percentChange then
    let percentChangeStr := percentChangeToString percentChange
    let percentLen := percentChangeStr.length
    if percentLen > maxWidths.percentChange then percentLen
    else maxWidths.percentChange
  else maxWidths.percentChange
  let throughput := match maxWidths.throughput with
    | none => none
    | some w =>
      let tStr := row.throughputStr
      let tLen := tStr.length
      some (if tLen > w then tLen else w)
  { function, newBench, baseBench, percentChange, throughput }

-- Gets the max lengths of each data type for pretty-printing columns
def getColumnWidths (report : Array BenchReport) : ColumnWidths :=
  let hasThroughput := report.any (·.throughput.isSome)
  let maxWidths : ColumnWidths := {
    function := "Function".length
    newBench := "New Benchmark".length
    baseBench := "Base Benchmark".length
    percentChange := "% change".length
    throughput := if hasThroughput then some "Throughput".length else none
  }
  report.foldl getColumnWidths' maxWidths

-- Centers a string with padded whitespace given the total width
def padWhitespace (input : String) (width : Nat) : String :=
  let padWidth := width - input.length
  let leftPad := padWidth / 2
  let rightPad := padWidth - leftPad
  String.ofList (List.replicate leftPad ' ') ++ input ++ (String.ofList (List.replicate rightPad ' '))

def padDashes (width : Nat) : String :=
  String.ofList (List.replicate width '-')

def mkReportPretty' (columnWidths : ColumnWidths) (reportPretty : String) (row : BenchReport) : String :=
  let functionStr := padWhitespace row.function columnWidths.function
  let newBenchStr := row.newBench.getTime.formatNanos
  let newBenchStr := padWhitespace newBenchStr columnWidths.newBench
  let baseBenchStr := if let some baseBench := row.baseBench then
    baseBench.getTime.formatNanos
  else "None"
  let baseBenchStr := padWhitespace baseBenchStr columnWidths.baseBench
  let percentChangeStr := if let some percentChange := row.percentChange then
    percentChangeToString percentChange
  else "N/A"
  let percentChangeStr := padWhitespace percentChangeStr columnWidths.percentChange
  let throughputCell := match columnWidths.throughput with
    | none => ""
    | some w => s!" {padWhitespace row.throughputStr w} |"
  let rowPretty :=
    s!"| {functionStr} | {newBenchStr} | {baseBenchStr} | {percentChangeStr} |{throughputCell}\n"
  reportPretty ++ rowPretty

-- TODO: Bold the faster result and faster/slower % change
/--
Generates a Markdown table with comparative benchmark timings based on the results on disk.
Each table row contains the benchmark function name, the new timing, the base timing, the percent change between the two, and (optionally) a throughput rate.
-/
def mkReportPretty (groupName : String) (report : Array BenchReport) : String :=
  let columnWidths := getColumnWidths report
  let title := s!"## {groupName}\n\n"
  let (fn, new, base, percent) := (
    padWhitespace "Function" columnWidths.function,
    padWhitespace "New Benchmark" columnWidths.newBench,
    padWhitespace "Base Benchmark" columnWidths.baseBench,
    padWhitespace "% change" columnWidths.percentChange
  )
  let (d1, d2, d3, d4) := (
    padDashes columnWidths.function,
    padDashes columnWidths.newBench,
    padDashes columnWidths.baseBench,
    padDashes columnWidths.percentChange
  )
  let (throughputHeader, throughputDashes) := match columnWidths.throughput with
    | none => ("", "")
    | some w => (s!" {padWhitespace "Throughput" w} |", s!"-{padDashes w}-|")
  let header := s!"| {fn} | {new} | {base} | {percent} |{throughputHeader}\n"
  let dashes := s!"|-{d1}-|-{d2}-|-{d3}-|-{d4}-|{throughputDashes}\n"
  let reportPretty := title ++ header ++ dashes
  report.foldl (mkReportPretty' columnWidths) reportPretty

def oneShotBench {α β : Type} (groupName : String) (b : Benchmarkable α β)
    (tput : Option Throughput) (config : Config) (labelWidth : Nat) : IO BenchReport := do
  let start ← IO.monoNanosNow
  let _res ← b.getFn b.arg
  let finish ← IO.monoNanosNow
  let benchTime := finish - start
  let fullName := s!"{groupName}/{b.name}"
  let label := padLabel fullName labelWidth
  let indent := padLabel "" labelWidth
  IO.println s!"{label}time:   {benchTime.toFloat.formatNanos}"
  if let some t := tput then
    IO.println s!"{indent}thrpt:  {t.formatRate benchTime.toFloat}"
  let (basePath, newPath) ← mkDirs groupName b.name
  let fileExt := toString config.serde
  let newFile := newPath / s!"one-shot.{fileExt}"
  let (baseBench, percentChange) ← if (← System.FilePath.pathExists newFile) then do
    let baseBench : OneShot ← loadFile config.serde newFile
    let baseTime := baseBench.benchTime.toFloat
    let percentChange := (benchTime.toFloat - baseTime) / baseTime
    IO.println s!"{indent}change: {percentChangeToString percentChange}"
    let _ ← IO.Process.run { cmd := "mv", args := #[newFile.toString, basePath.toString] }
    pure (some baseBench, some percentChange)
  else
    let _ ← IO.Process.run { cmd := "mkdir", args := #["-p", newPath.toString] }
    pure (.none, .none)
  -- One-shot mode embeds throughput inside the OneShot record so there is no
  -- separate throughput file on disk — switching between sample and one-shot
  -- modes never overlaps on the same filename.
  let newBench : OneShot := { benchTime, throughput := tput }
  IO.println ""
  storeFile config.serde newBench newFile
  let benchReport : BenchReport := {
    function := b.name,
    newBench := (.oneShot newBench),
    baseBench := baseBench.map .oneShot,
    percentChange,
    throughput := tput
  }
  return benchReport

/-!
## Monadic bgroup builder

`bgroup` takes a `BgroupM` do-block instead of a list of pre-built benches so
the user can interleave `throughput` (which updates the current group config's
throughput field) with `bench` / `benchIO` registrations. Each registration
captures a snapshot of `config.throughput` at that moment, mirroring
criterion.rs's `BenchmarkGroup::throughput` + `bench_function` pattern.
-/

/-- Internal state threaded through a `bgroup` do-block. -/
structure GroupState (α β : Type) where
  config : Config
  /-- Registered benches paired with the `config.throughput` snapshot taken at registration time. -/
  benches : Array (Benchmarkable α β × Option Throughput) := #[]

/-- Monad used inside a `bgroup` do-block. -/
abbrev BgroupM (α β : Type) := StateT (GroupState α β) IO

namespace BgroupM

/--
Sets the throughput for subsequent `bench`/`benchIO` calls in the current
`bgroup`. Prior registrations keep the value they captured at registration time.
-/
def throughput (t : Throughput) : BgroupM α β Unit :=
  modify fun s => { s with config := { s.config with throughput := some t } }

/-- Clears the current throughput so subsequent registrations capture `none`. -/
def clearThroughput : BgroupM α β Unit :=
  modify fun s => { s with config := { s.config with throughput := none } }

/--
Registers a pure benchmark with the current `bgroup`. The pure `fn` is wrapped
in `blackBoxIO` internally so the compiler cannot optimize its result away.
-/
def bench (name : String) (fn : α → β) (arg : α) : BgroupM α β Unit :=
  modify fun s =>
    let b : Benchmarkable α β := { name, func := BenchFn.pure fn, arg }
    { s with benches := s.benches.push (b, s.config.throughput) }

/--
Registers an `IO`-returning benchmark with the current `bgroup`. `IO` benches are
not black-boxed because the `IO` return already prevents the optimizer from
eliminating the call.
-/
def benchIO (name : String) (fn : α → IO β) (arg : α) : BgroupM α β Unit :=
  modify fun s =>
    let b : Benchmarkable α β := { name, func := BenchFn.io fn, arg }
    { s with benches := s.benches.push (b, s.config.throughput) }

end BgroupM

-- TODO: Make sure compiler isn't caching partial evaluation result for future runs of the same function (measure first vs subsequent runs)
/-- Runs each benchmark registered by `action` and analyzes the results. -/
def bgroup {α β : Type} (name: String) (config : Config := {})
    (action : BgroupM α β Unit) : IO $ Array BenchReport := do
  let config ← getConfigEnv config
  let (_, state) ← action.run { config, benches := #[] }
  -- The action may have mutated `config.throughput`; re-read it from state but
  -- keep the rest of `config` fixed.
  let bg : BenchGroup := { name, config }
  -- Criterion-style label column: max fullName length across the group, at least 24 + 1 pad.
  let labelWidth := state.benches.foldl
    (fun w (b, _) => max w s!"{name}/{b.name}".length) minLabelWidth + 1
  if config.verbosity != .quiet then
    IO.println s!"Running bench group {name}\n"
  let mut reports : Array BenchReport := #[]
  for (b, tput) in state.benches do
    let report : BenchReport ← if config.oneShot then do
      oneShotBench name b tput config labelWidth
    else
      let warmupMean ← bg.warmup b
      if bg.config.verbosity != .quiet then
        IO.println s!"Running {b.name}"
      -- Resolve `.auto` to a concrete mode now so both sampling and the
      -- downstream regression-vs-mean choice see the same decision.
      let resolvedMode := chooseSamplingMode bg.config warmupMean
      if bg.config.verbosity == .verbose then
        let modeName := match resolvedMode with
          | .flat => "flat"
          | .linear => "linear"
          | .auto => "auto" -- unreachable
        let picked := if bg.config.samplingMode == .auto then " (picked by auto)" else ""
        IO.println s!"Sampling mode: {modeName}{picked}"
      -- From here on we use `resolvedConfig` (never `.auto`) so that both the
      -- regression branch below and the `SampleRun` persisted to disk agree on
      -- exactly which mode this run used.
      let resolvedConfig := { bg.config with samplingMode := resolvedMode }
      -- Inner bg needs the resolved config too so its .printResults uses the
      -- right verbosity, labels, etc.
      let resolvedBg : BenchGroup := { name, config := resolvedConfig }
      let (iters, times) ← match resolvedMode with
        | .flat => bg.sampleFlat b warmupMean
        | .linear => bg.sampleLinear b warmupMean
        | .auto => bg.sampleFlat b warmupMean -- unreachable
      let data := iters.zip times
      let avgTimes : Distribution := { d := data.map (fun (x,y) => Float.ofNat y / Float.ofNat x) }
      let gen ← IO.stdGenRef.get
      let mut (distributions, estimates) := avgTimes.estimates resolvedConfig gen
      let mut rSquared : Option Float := none
      if resolvedMode == .linear
      then
        let data' : Data := { d := data }
        let (distribution, slope, r2) := data'.regression resolvedConfig gen
        estimates := { estimates with slope := .some slope }
        distributions := { distributions with slope := .some distribution }
        rSquared := some r2
      -- Outlier analysis: classify per-sample average times and compute the
      -- variance-inflation metric. Both are consumed by `printResults` under
      -- the verbosity gate.
      let outliers := avgTimes.classifyOutliers
      let ov := outlierVariance estimates.mean estimates.stdDev (Float.ofNat resolvedConfig.numSamples)
      let comparisonData : Option ComparisonData ← bg.getComparison b.name avgTimes resolvedConfig resolvedMode
      let measurement : MeasurementData :=  {
        data := { d := data },
        avgTimes,
        absoluteEstimates := estimates,
        distributions,
        comparison := comparisonData
        throughput := tput
        rSquared,
        outlierVariance := some ov,
        outliers := some outliers
      }
      resolvedBg.printResults b.name measurement labelWidth
      IO.println ""
      saveMeasurement name b.name measurement resolvedConfig
      let benchReport : BenchReport := {
        function := b.name,
        newBench := (.sample estimates),
        baseBench := (comparisonData.map (.sample ·.baseEstimates)),
        percentChange := comparisonData.map (·.relativeEstimates.mean.pointEstimate),
        throughput := tput
      }
      pure benchReport
    reports := reports.push report
  if config.avgThroughput then
    match weightedAverageThroughput reports with
    | some (t, avgRate) =>
      IO.println s!"Average throughput: {t.formatRateValue avgRate}"
    | none =>
      IO.eprintln "Average throughput: skipped (no throughput set, or mixed Throughput variants across benches)"
  if config.report then
    let table := mkReportPretty name reports
    IO.println table
    let reportDir := System.mkFilePath [".", ".lake", "benches", name]
    let _ ← IO.Process.run { cmd := "mkdir", args := #["-p", reportDir.toString] }
    IO.FS.writeFile (reportDir / "report.md") table
  return reports

end
