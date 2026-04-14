module
public import Ix.Benchmark.Serde
public import Ix.Benchmark.Tukey
public import Ix.Benchmark.Ansi

public section

/-! # Benchmark report output — console (ANSI) and Markdown table

This module contains display logic and the data types that form the interface
between measurement and display (`MeasurementData`, `BenchResult`,
`BenchReport`). These types are constructed by `Bench.lean` and consumed by
the formatting functions here.
-/

structure MeasurementData where
  data : Data
  avgTimes : Distribution
  absoluteEstimates : Estimates
  distributions : Distributions
  comparison : Option ComparisonData
  throughput : Option Throughput
  rSquared : Option Float := none
  outlierVariance : Option OutlierVariance := none
  outliers : Option Outliers := none
  deriving Repr

inductive BenchResult where
| oneShot : OneShot → BenchResult
| sample : Estimates → BenchResult
  deriving Repr

def BenchResult.getTime (bench: BenchResult) : Float :=
  match bench with
  | oneShot o => o.benchTime.toFloat
  | sample s => s.mean.pointEstimate

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
Computes weighted-average throughput rate(s) across a collection of reports.
For `ElementsAndBytes`, also returns the secondary bytes-weighted-average rate.
-/
def weightedAverageThroughput (reports : Array BenchReport) :
    Option (Throughput × Float × Option Float) := Id.run do
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
    let primaryAvg := weightedSum / sumQty
    let secondaryAvg ← match t with
      | .ElementsAndBytes _ _ _ => do
        let mut sumBytes : Float := 0.0
        let mut weightedBytesSum : Float := 0.0
        for r in reports do
          if let some (.ElementsAndBytes _ b _) := r.throughput then
            let bytes := b.toNat.toFloat
            let bytesRate := bytes * 1e9 / r.newBench.getTime
            sumBytes := sumBytes + bytes
            weightedBytesSum := weightedBytesSum + bytes * bytesRate
        pure (if sumBytes > 0 then some (weightedBytesSum / sumBytes) else none)
      | _ => pure none
    return some (t, primaryAvg, secondaryAvg)

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

/-- Criterion.rs uses a fixed 24-char column for the time/thrpt labels. -/
def indent24 : String := String.ofList (List.replicate 24 ' ')

def printRunning (config : Config) (style : CliStyle) (benchId : String) (expectedTime : Float) (numIters : Nat) (warningFactor : Nat) : IO Unit := do
  if warningFactor == 1 then
    -- Clear the ephemeral line before printing the permanent warning
    style.overwrite
    IO.eprintln s!"Warning: Unable to complete {config.numSamples} samples in {config.sampleTime.floatPretty 2}s. You may wish to increase target time to {expectedTime.floatPretty 2}s"
  style.printEphemeral s!"Benchmarking {benchId}: Collecting {config.numSamples} samples in estimated {expectedTime.floatPretty 2}s ({numIters.natPretty} iterations)"

/-- Prints the results of a single sampled benchmark to stdout, matching
    criterion.rs's layout with ANSI colors.

    `groupName` and `config` are used for the bench label and verbosity gating
    (replaces the old `BenchGroup.printResults` method so that Report.lean
    doesn't need to know about `BenchGroup`). -/
def printResults (groupName : String) (config : Config) (benchName : String)
    (m : MeasurementData) : IO Unit := do
  let estimates := m.absoluteEstimates
  let typicalEstimate := estimates.slope.getD estimates.mean
  let fullName := s!"{groupName}/{benchName}"
  let verbosity := config.verbosity
  let ciLb := typicalEstimate.confidenceInterval.lowerBound
  let ciUb := typicalEstimate.confidenceInterval.upperBound

  -- Name line + time, matching criterion.rs's 24-char column layout:
  -- Short name (≤ 23 chars): name + pad + time on one line
  -- Long name (> 23 chars): name on its own line, time on the next
  let r2Suffix := match m.rSquared with
    | some r2 => s!" R²={r2.floatPretty 3}"
    | none => ""
  let timeLine := s!"time:   [{Ansi.faint ciLb.formatNanos} {Ansi.bold typicalEstimate.pointEstimate.formatNanos} {Ansi.faint ciUb.formatNanos}]{r2Suffix}"
  if fullName.length > 23 then
    IO.println (Ansi.green fullName)
    IO.println s!"{indent24}{timeLine}"
  else
    let pad := String.ofList (List.replicate (24 - fullName.length) ' ')
    IO.println s!"{Ansi.green fullName}{pad}{timeLine}"

  -- Throughput line (if present)
  if let some t := m.throughput then
    -- Higher time ⇒ lower throughput, so bounds are inverted
    IO.println s!"{indent24}thrpt:  [{Ansi.faint (t.formatRate ciUb)} {Ansi.bold (t.formatRate typicalEstimate.pointEstimate)} {Ansi.faint (t.formatRate ciLb)}]"

  -- Change section (gated by verbosity, not shown in quiet)
  if verbosity != .quiet then
    if let some comp := m.comparison then
      -- `p > significanceThreshold` means we fail to reject the null hypothesis
      -- that the two samples come from the same distribution — i.e. no
      -- statistically significant change.
      let notSignificant := comp.pValue > comp.significanceThreshold
      let meanEst := comp.relativeEstimates.mean
      let fmtSigned (f : Float) : String :=
        let body := (f * 100).floatPretty 4
        if f ≥ 0 then s!"+{body}" else body

      -- Determine coloring for point estimate based on comparison result
      let comparison := if notSignificant then ComparisonResult.NonSignificant
        else compareToThreshold meanEst comp.noiseThreshold
      let colorPointEst (s : String) : String := match comparison with
        | .Improved => Ansi.green (Ansi.bold s)
        | .Regressed => Ansi.red (Ansi.bold s)
        | .NonSignificant => s

      let pointEstStr := colorPointEst (fmtSigned meanEst.pointEstimate)
      let lbStr := Ansi.faint (fmtSigned meanEst.confidenceInterval.lowerBound)
      let ubStr := Ansi.faint (fmtSigned meanEst.confidenceInterval.upperBound)
      let pStr := s!"(p = {comp.pValue.floatPretty 2} {if notSignificant then ">" else "<"} {comp.significanceThreshold.floatPretty 2})"

      -- Layout differs depending on whether throughput is present
      if m.throughput.isSome then
        -- Throughput present: separate "change:" header, then time: and thrpt: sub-lines
        let toThrptEst (ratio : Float) : Float := 1.0 / (1.0 + ratio) - 1.0
        let thrptPointStr := colorPointEst (fmtSigned (toThrptEst meanEst.pointEstimate))
        let thrptLbStr := Ansi.faint (fmtSigned (toThrptEst meanEst.confidenceInterval.upperBound))
        let thrptUbStr := Ansi.faint (fmtSigned (toThrptEst meanEst.confidenceInterval.lowerBound))
        IO.println s!"{String.ofList (List.replicate 17 ' ')}change:"
        IO.println s!"{indent24}time:   [{lbStr}% {pointEstStr}% {ubStr}%] {pStr}"
        IO.println s!"{indent24}thrpt:  [{thrptLbStr}% {thrptPointStr}% {thrptUbStr}%]"
      else
        -- No throughput: inline change
        IO.println s!"{indent24}change: [{lbStr}% {pointEstStr}% {ubStr}%] {pStr}"

      -- Explanation line
      let explanation := if notSignificant then
        "No change in performance detected."
      else match comparison with
        | .Improved => s!"Performance has {Ansi.green "improved"}."
        | .Regressed => s!"Performance has {Ansi.red "regressed"}."
        | .NonSignificant => "Change within noise threshold."
      IO.println s!"{indent24}{explanation}"

  -- Outlier-variance warning + Tukey breakdown. Verbosity gating matches
  -- Haskell criterion's `Internal.hs:89-92`:
  --   • verbose             → always print the variance line AND breakdown
  --   • normal + > slight   → print the variance line AND breakdown
  --   • normal + ≤ slight   → silent
  --   • quiet               → silent regardless
  if verbosity != .quiet then
    if let some ov := m.outlierVariance then
      let effectAboveSlight := match ov.effect with
        | .moderate | .severe => true
        | _ => false
      let showVariance := verbosity == .verbose || (effectAboveSlight && verbosity != .quiet)
      if showVariance then
        if let some outs := m.outliers then
          Outliers.note outs m.avgTimes.d.size
        let pct := (ov.fraction * 100).floatPretty 0
        IO.println s!"variance introduced by outliers: {pct}% ({ov.desc})"

/-! ## Markdown table -/

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

/--
Generates a Markdown table with comparative benchmark timings.
Each table row contains the benchmark function name, the new timing, the base
timing, the percent change between the two, and (optionally) a throughput rate.
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

end
