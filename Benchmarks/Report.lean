import Cli
import Ix.Benchmark.Bench

-- TODO: Support multiple functions in one report (depends on JSON file)

structure Comparison where
  benchName : String
  new : Estimates
  base : Estimates

def mkRow (acc : String) (comp : Comparison) : String :=
    let newMean := comp.new.mean.pointEstimate
    let baseMean := comp.base.mean.pointEstimate
    let percentDiff := 100 * (baseMean - newMean) / baseMean
    let percentDiffStr := percentDiff.floatPretty 2
    let percentDiffStr :=
      if percentDiff > 0 then s!"{percentDiffStr}% faster"
      else if percentDiff < 0 then s!"{percentDiffStr}% slower"
      else "No change"
    acc ++ s!"| {comp.benchName} | {newMean.formatNanos} | {baseMean.formatNanos } | {percentDiffStr} |\n"

def mkTable (results: List Comparison) : String :=
  let rows := results.foldl mkRow ""

  "| Function | New Benchmark | Base Benchmark | % diff |\n"
  ++
  "|----------|---------------|----------------|--------|\n"
  ++ rows ++
  "|----------|---------------|----------------|--------|"

def runReport (p : Cli.Parsed) : IO UInt32 := do
  if !p.hasFlag "new" || !p.hasFlag "base" then
    p.printError "error: must specify --new, --base"
    return 1
  let new : String := p.flag! "new" |>.as! String
  let newPath := System.mkFilePath [".", new]
  let base : String := p.flag! "base" |>.as! String
  let basePath := System.mkFilePath [".", base]

  let newEstimates ← loadJson Estimates newPath
  let baseEstimates ← loadJson Estimates basePath

  let comp : Comparison := { benchName := "prove", new := newEstimates, base := baseEstimates }
  let output := mkTable [comp]
  IO.println output
  return 0

def reportCmd : Cli.Cmd := `[Cli|
  report VIA runReport;
  "A tool for generating a Markdown comparison report of JSON benchmark data"

  FLAGS:
    new : String; "New benchmark result to compare with base"
    base : String; "Base benchmark result to compare with new"
]

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    reportCmd.printHelp
    return 0
  reportCmd.validate args

