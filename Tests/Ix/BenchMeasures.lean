/-
  Tests for the benchmark registry's row kinds: a backend's constant rows
  are the shared constants, each in its own env, and its env rows are the
  registry envs; both kinds plot on the backend's one testbed. The
  PR-comment renderer marks each cell past ±3% and groups a cell's rows
  under its env.
-/

module
public import Ix.Cli.BenchCmd
public import Ix.Cli.BenchReport
public import LSpec

public section

open LSpec Ix.Cli.BenchCmd

namespace Tests.Ix.BenchMeasures

def envNames : Array String := (envSpecs.map (·.name)).toArray

def constantNames : Array String :=
  Ix.BenchConstants.benchConstants.map (·.name)

def testRows : TestSeq :=
  test "every shared constant's env is a registry env"
    (Ix.BenchConstants.benchConstants.all (envNames.contains ·.env))
  ++ test "every backend has env rows"
    (backendSpecs.all (!·.envMetrics.isEmpty))
  ++ test "an env-row measure plots every env"
    (backendSpecs.all fun b => b.envMetrics.all fun m =>
      envNames.all (b.benchmarkNames m).contains)
  ++ test "a constant-row measure plots every shared constant"
    (backendSpecs.all fun b => b.constantMetrics.all fun m =>
      constantNames.all (b.benchmarkNames m).contains)
  ++ test "a measure no row kind carries plots nothing"
    (backendSpecs.all fun b => (b.benchmarkNames "no-such-measure").isEmpty)
  ++ test "ixvm and ixvm-ooc have constant rows"
    (["ixvm", "ixvm-ooc"].all fun n => ((findBackend n).map (·.hasConstants)).getD false)
  ++ test "compile and decompile have only env rows"
    (["compile", "decompile"].all fun n => ((findBackend n).map (!·.hasConstants)).getD false)
  ++ test "a stage measure plots only the shared constants"
    (backendSpecs.all fun b => b.stages.all fun (_, ms) => ms.all fun m =>
      b.benchmarkNames m == constantNames)
  ++ test "stage measures are tracked"
    (backendSpecs.all fun b => b.stages.all fun (_, ms) => ms.all b.trackedMetrics.contains)
  ++ test "backend testbeds are distinct"
    ((backendSpecs.map (·.testbed)).eraseDups.length == backendSpecs.length)

/-- Results rows: each `(name, fields)` is one row of numeric fields, with
    `status` set when given. -/
def rowsOf (rows : List (String × List (String × Nat)) ) (status : List (String × String) := []) :
    Lean.Json :=
  Lean.Json.mkObj <| rows.map fun (name, fields) =>
    let base := fields.map fun (k, v) => (k, Lean.toJson v)
    let extra := (status.filter (·.1 == name)).map fun (_, s) => ("status", Lean.Json.str s)
    (name, Lean.Json.mkObj (base ++ extra))

open Ix.Cli.BenchReport in
def testCells : TestSeq :=
  let cell := fun (b p : Nat) (metric : String) =>
    metricCell (rowsOf [("Nat.add_comm", [(metric, b)])])
      (rowsOf [("Nat.add_comm", [(metric, p)])]) "Nat.add_comm" metric 3.0
  test "a slower run past 3% is a regression"
    (let (text, bad, good) := cell 100 110 "check-time"
     text.endsWith "(+10.0%) ⚠️" && bad && !good)
  ++ test "a faster run past 3% is an improvement"
    (let (text, bad, good) := cell 100 96 "check-time"
     text.endsWith "(-4.0%) 🟢" && !bad && good)
  ++ test "a change within 3% is unmarked"
    (let (text, bad, good) := cell 100 102 "check-time"
     text.endsWith "(+2.0%)" && !bad && !good)
  ++ test "higher throughput is an improvement"
    ((cell 100 110 "throughput").2.2)
  ++ test "a rejected row renders ❌"
    ((metricCell (rowsOf [("Nat.add_comm", [("check-time", 1)])])
      (rowsOf [("Nat.add_comm", [])] [("Nat.add_comm", "rejected")])
      "Nat.add_comm" "check-time" 3.0).1.endsWith "→ ❌")
  ++ test "the env row leads, then its constants in registry order"
    ({ backend := "ixvm", env := "InitStd"
       base := rowsOf [("Std.HashMap", []), ("InitStd", []), ("Nat.add_comm", [])] : Cell }.rows
      == #[("InitStd", true), ("Nat.add_comm", false), ("Std.HashMap", false)])
  ++ test "constants without an env row still get their env's label row"
    ({ backend := "ixvm", env := "InitStd", pr := rowsOf [("Nat.add_comm", [])] : Cell }.rows
      == #[("InitStd", true), ("Nat.add_comm", false)])

open Ix.Cli.BenchReport in
def testReport : TestSeq := .individualIO "ixvm report: one table, env row first, stages on demand" none (do
  let some spec := findBackend "ixvm" | return (false, 0, 0, none)
  let base := rowsOf [("InitStd", [("check-time", 50), ("execute-time", 40)]),
    ("Nat.add_comm", [("check-time", 3), ("execute-time", 1)])]
  let pr := rowsOf [("InitStd", [("check-time", 60), ("execute-time", 41)]),
    ("Nat.add_comm", [("check-time", 3), ("execute-time", 1)])]
  let plain ← renderBackend spec #[{ backend := "ixvm", env := "InitStd", base, pr }] 3.0 "main"
  let lines := plain.splitOn "\n"
  let envAt := lines.findIdx? (·.startsWith "| **InitStd** |")
  let constAt := lines.findIdx? (·.startsWith "| `Nat.add_comm` |")
  let proved := rowsOf [("Nat.add_comm", [("check-time", 3), ("prove-time", 30)])]
  let staged ← renderBackend spec
    #[{ backend := "ixvm", env := "InitStd", base := proved, pr := proved }] 3.0 "main"
  let ok := plain.startsWith "### `ixvm`"
    && (match envAt, constAt with | some e, some c => e < c | _, _ => false)
    && (plain.splitOn "· prove").length == 1
    && (staged.splitOn "#### `ixvm` · prove").length == 2
  return (ok, 0, 0, if ok then none else some plain)) .done

open Ix.Cli.BenchReport in
def testRowKinds : TestSeq := .individualIO "a row shows and compares only its kind's measures" none (do
  let some ooc := findBackend "ixvm-ooc" | return (false, 0, 0, none)
  -- The constant rows share one process's peak RSS, which ixvm-ooc does not
  -- compare per constant.
  let shared := rowsOf [("Nat.add_comm", [("check-time", 5), ("peak-rss", 100)])]
  let grew := rowsOf [("Nat.add_comm", [("check-time", 5), ("peak-rss", 200)])]
  let oocText ← renderBackend ooc
    #[{ backend := "ixvm-ooc", env := "InitStd", base := shared, pr := grew }] 3.0 "main"
  let some ixvm := findBackend "ixvm" | return (false, 0, 0, none)
  let consts := rowsOf [("Nat.add_comm", [("check-time", 3), ("execute-time", 1)])]
  let ixvmText ← renderBackend ixvm
    #[{ backend := "ixvm", env := "InitStd", base := consts, pr := consts }] 3.0 "main"
  let ok := (oocText.splitOn "0 with regressions").length == 2
    && (oocText.splitOn "peak-ram").length == 1
    && (ixvmText.splitOn "shards").length == 1
  return (ok, 0, 0, if ok then none else some (oocText ++ "\n" ++ ixvmText))) .done

def suite : List TestSeq := [testRows, testCells, testReport, testRowKinds]

end Tests.Ix.BenchMeasures
