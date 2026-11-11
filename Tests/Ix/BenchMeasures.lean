/-
  Tests for the benchmark registry's row kinds: a backend's constant rows
  are the shared constants, each in its own env, and its env rows are the
  registry envs; both kinds plot on the backend's one testbed. The
  PR-comment renderer marks each cell past ±3% and tables env rows and
  constant rows separately.
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
    metricCells (rowsOf [("Nat.add_comm", [(metric, b)])])
      (rowsOf [("Nat.add_comm", [(metric, p)])]) "Nat.add_comm" metric 3.0
  test "a slower run past 3% is a regression"
    (let (text, bad, good) := cell 100 110 "check-time"
     text == #["1m 40.0s", "1m 50.0s", "+10.0% (1.10× slower) ⚠️"] && bad && !good)
  ++ test "a faster run past 3% is an improvement"
    (let (text, bad, good) := cell 100 96 "check-time"
     text[2]! == "-4.0% 🟢" && !bad && good)
  ++ test "a change within 3% is unmarked"
    (let (text, bad, good) := cell 100 102 "check-time"
     text[2]! == "+2.0%" && !bad && !good)
  ++ test "a change of 5% or more names its factor in the metric's terms"
    ((cell 100 50 "check-time").1[2]! == "-50.0% (2.00× faster) 🟢"
      && (metricCells (rowsOf [("Nat.add_comm", [("prove-proof-size", 100)])])
        (rowsOf [("Nat.add_comm", [("prove-proof-size", 120)])])
        "Nat.add_comm" "prove-proof-size" 3.0).1[2]! == "+20.0% (1.20× larger) ⚠️")
  ++ test "trace shards render as counts and more of them is a regression"
    ((metricCells (rowsOf [("Nat.add_comm", [("prove-trace-shards", 4)])])
      (rowsOf [("Nat.add_comm", [("prove-trace-shards", 6)])])
      "Nat.add_comm" "prove-trace-shards" 3.0).1 == #["4", "6", "+50.0% (1.50× more) ⚠️"])
  ++ test "higher throughput is an improvement"
    ((cell 100 110 "throughput").2.2)
  ++ test "a rejected row renders ❌"
    ((metricCells (rowsOf [("Nat.add_comm", [("check-time", 1)])])
      (rowsOf [("Nat.add_comm", [])] [("Nat.add_comm", "rejected")])
      "Nat.add_comm" "check-time" 3.0).1 == #["1.000 s", "❌", "n/a"])
  ++ test "a crashed row renders a generic failure"
    ((metricCells (rowsOf [("Nat.add_comm", [("check-time", 1)])])
      (rowsOf [("Nat.add_comm", [])] [("Nat.add_comm", "crash")])
      "Nat.add_comm" "check-time" 3.0).1 == #["1.000 s", "❌ failed", "n/a"])
  ++ test "an OOM row keeps its measured stages and marks the ones it lost"
    (let base := rowsOf [("Nat.add_comm", [("execute-time", 1), ("prove-time", 30)])]
     let pr := rowsOf [("Nat.add_comm", [("execute-time", 1)])] [("Nat.add_comm", "oom")]
     (metricCells base pr "Nat.add_comm" "execute-time" 3.0).1[2]! == "+0.0%"
       && (metricCells base pr "Nat.add_comm" "prove-time" 3.0).1 == #["30.000 s", "❌ OOM", "n/a"])
  ++ test "the env row leads, then its constants in registry order"
    ({ backend := "ixvm", env := "InitStd"
       base := rowsOf [("Std.HashMap", []), ("InitStd", []), ("Nat.add_comm", [])] : Cell }.rows
      == #[("InitStd", true), ("Nat.add_comm", false), ("Std.HashMap", false)])
  ++ test "constants without an env row get no env label row"
    ({ backend := "ixvm", env := "InitStd", pr := rowsOf [("Nat.add_comm", [])] : Cell }.rows
      == #[("Nat.add_comm", false)])

open Ix.Cli.BenchReport in
def testReport : TestSeq := .individualIO "ixvm report: an env table, then a constant table, stages on demand" none (do
  let some spec := findBackend "ixvm" | return (false, 0, 0, none)
  let base := rowsOf [("InitStd", [("execute-time", 40)]), ("Nat.add_comm", [("execute-time", 1)])]
  let pr := rowsOf [("InitStd", [("execute-time", 41)]), ("Nat.add_comm", [("execute-time", 1)])]
  let plain ← renderBackend spec #[{ backend := "ixvm", env := "InitStd", base, pr }] 3.0 "main"
  let lines := plain.splitOn "\n"
  let envAt := lines.findIdx? (·.startsWith "| InitStd |")
  let constAt := lines.findIdx? (·.startsWith "| `Nat.add_comm` |")
  let envHead := lines.findIdx? (· == "#### `ixvm` · envs")
  let constHead := lines.findIdx? (· == "#### `ixvm` · constants")
  let proved := rowsOf [("Nat.add_comm", [("execute-time", 1), ("prove-time", 30)])]
  let staged ← renderBackend spec
    #[{ backend := "ixvm", env := "InitStd", base := proved, pr := proved }] 3.0 "main"
  let ok := plain.startsWith "### `ixvm`"
    && (match envHead, envAt, constHead, constAt with
      | some eh, some e, some ch, some c => eh < e && e < ch && ch < c
      | _, _, _, _ => false)
    && (plain.splitOn "| env | execute-time (main)").length == 2
    && (plain.splitOn "| constant | execute-time (main)").length == 2
    && (plain.splitOn "· prove").length == 1
    && (staged.splitOn "#### `ixvm` · prove").length == 2
    && (staged.splitOn "| constant | prove-time (main) | prove-time (PR) | Δ% |\n").length == 2
    && (plain.splitOn "check-time").length == 1
  return (ok, 0, 0, if ok then none else some plain)) .done

open Ix.Cli.BenchReport in
def testFftCost : TestSeq := .individualIO "ixvm tables show the FFT cost on both row kinds" none (do
  let some spec := findBackend "ixvm" | return (false, 0, 0, none)
  let rows := fun (env c : Nat) => rowsOf [
    ("InitStd", [("execute-time", 40), ("peak-rss", 1), ("shards", 12), ("fft-cost", env)]),
    ("Nat.add_comm", [("execute-time", 1), ("peak-rss", 1), ("fft-cost", c)])]
  let text ← renderBackend spec
    #[{ backend := "ixvm", env := "InitStd", base := rows 100000000000 390000000, pr := rows 100000000000 400000000 }]
    3.0 "main"
  let ok := (text.splitOn "| env-shards (main) | env-shards (PR) | Δ% | fft-cost (main) |").length == 2
    && (text.splitOn "| `Nat.add_comm` | 1.000 s | 1.000 s | +0.0% | 1 B | 1 B | +0.0% | 390.00M | 400.00M | +2.6% |").length == 2
  return (ok, 0, 0, if ok then none else some text)) .done

open Ix.Cli.BenchReport in
def testThroughput : TestSeq := .individualIO "every measure gets columns, throughputs improve upward" none (do
  let some spec := findBackend "ixvm" | return (false, 0, 0, none)
  let rows := fun (t : Nat) => rowsOf [
    ("InitStd", [("execute-time", 40), ("throughput", t), ("peak-rss", 1), ("shards", 12),
      ("fft-cost", 100)]),
    ("Nat.add_comm", [("execute-time", 1), ("prove-time", 30), ("prove-throughput", t)])]
  let text ← renderBackend spec
    #[{ backend := "ixvm", env := "InitStd", base := rows 100, pr := rows 110 }] 3.0 "main"
  let ok := (text.splitOn "| env | execute-time (main) | execute-time (PR) | Δ% | throughput (const/s) (main) | throughput (const/s) (PR) | Δ% | peak-ram (main) | peak-ram (PR) | Δ% | env-shards (main) | env-shards (PR) | Δ% | fft-cost (main) | fft-cost (PR) | Δ% |").length == 2
    && (text.splitOn "more metrics").length == 1
    && (text.splitOn "| prove-throughput (const/s) (main) |").length == 2
    && (text.splitOn "+10.0% (1.10× faster) 🟢").length == 3
  return (ok, 0, 0, if ok then none else some text)) .done

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
  let consts := rowsOf [("Nat.add_comm", [("execute-time", 1)])]
  let ixvmText ← renderBackend ixvm
    #[{ backend := "ixvm", env := "InitStd", base := consts, pr := consts }] 3.0 "main"
  let ok := (oocText.splitOn "0 with regressions").length == 2
    && (oocText.splitOn "peak-ram").length == 1
    && (ixvmText.splitOn "shards").length == 1
  return (ok, 0, 0, if ok then none else some (oocText ++ "\n" ++ ixvmText))) .done

open Ix.Cli.BenchReport in
def testCommands : TestSeq :=
  let modes := fun command => (parseCommand command).toOption.map fun parsed =>
    parsed.matrix.map fun cell =>
      let field := fun key => (cell.getObjValAs? String key).toOption.getD ""
      (field "backend", field "env", field "mode")
  let selected := " BENCH_CONSTANTS=Nat.add_comm BENCH_ENVS=none"
  let rejects := fun command => (parseCommand command).toOption.isNone
  test "bare ixvm defaults to execution"
    (modes ("!benchmark ixvm" ++ selected) == some #[ ("ixvm", "InitStd", "execute") ])
  ++ test "ixvm execute selects execution"
    (modes ("!benchmark ixvm execute" ++ selected) == some #[ ("ixvm", "InitStd", "execute") ])
  ++ test "ixvm prove selects proving"
    (modes ("!benchmark ixvm prove" ++ selected) == some #[ ("ixvm", "InitStd", "prove") ])
  ++ test "ixvm compress selects compression"
    (modes ("!benchmark ixvm compress" ++ selected) == some #[ ("ixvm", "InitStd", "compress") ])
  ++ test "the ixvm mode does not apply to other backends"
    (modes ("!benchmark ixvm compress ixvm-ooc" ++ selected) ==
      some #[ ("ixvm", "InitStd", "compress"), ("ixvm-ooc", "InitStd", "execute") ])
  ++ test "env-only ixvm cells stay execution-only"
    (modes "!benchmark ixvm prove BENCH_CONSTANTS=Nat.add_comm BENCH_ENVS=Mathlib" ==
      some #[ ("ixvm", "InitStd", "prove"), ("ixvm", "Mathlib", "execute") ])
  ++ test "all defaults every cell to execution"
    ((modes "!benchmark all").any (·.all fun (_, _, mode) => mode == "execute"))
  ++ test "all can include an explicit ixvm mode"
    ((modes "!benchmark all ixvm compress").any fun cells =>
      cells.any (fun (backend, _, mode) => backend == "ixvm" && mode == "compress") &&
      cells.all (fun (backend, _, mode) => backend == "ixvm" || mode == "execute"))
  ++ test "backend and subcommand names are case-insensitive"
    (modes ("!benchmark IXVM PROVE" ++ selected) == some #[ ("ixvm", "InitStd", "prove") ])
  ++ test "a mode must follow ixvm"
    (["!benchmark prove ixvm", "!benchmark ixvm-ooc prove", "!benchmark all compress"].all rejects)
  ++ test "conflicting or repeated modes are rejected"
    (["!benchmark ixvm prove compress", "!benchmark ixvm prove ixvm compress"].all rejects)
  ++ test "a misspelled mode is rejected"
    (rejects "!benchmark ixvm proev")
  ++ test "proving and compression require constant rows"
    (["!benchmark ixvm prove BENCH_CONSTANTS=none",
      "!benchmark ixvm compress BENCH_CONSTANTS=none"].all rejects)
  ++ test "stage environment settings are rejected inline and on later lines"
    (["!benchmark ixvm BENCH_PROVE=1", "!benchmark ixvm BENCH_COMPRESS=kzg",
      "!benchmark ixvm\nBENCH_PROVE=1", "!benchmark ixvm\nBENCH_COMPRESS=kzg"].all rejects)
  ++ test "compress reports the complete pipeline and only forwards unrelated settings"
    ((parseCommand "!benchmark ixvm compress RUST_LOG=debug").toOption.any fun parsed =>
      (parsed.summary.splitOn "stages `execute+prove+compress`").length == 2 &&
      parsed.passthrough == #["RUST_LOG=debug"])
  ++ test "fresh applies to every backend and retains the ixvm mode"
    ((parseCommand "!benchmark ixvm compress ixvm-ooc fresh").toOption.any fun parsed =>
      parsed.fresh && parsed.passthrough.isEmpty &&
      (parsed.summary.splitOn "baseline `fresh`").length == 2 &&
      parsed.matrix.all (fun cell =>
        (cell.getObjValAs? String "mode").toOption ==
          some (if (cell.getObjValAs? String "backend").toOption == some "ixvm"
            then "compress" else "execute")))
  ++ test "fresh is case-insensitive and works with all"
    ((parseCommand "!benchmark all FRESH").toOption.any (·.fresh))
  ++ test "ordinary requests retain cache reuse"
    ((parseCommand "!benchmark ixvm execute").toOption.any (!·.fresh))
  ++ test "fresh alone does not select a backend"
    (rejects "!benchmark fresh")
  ++ test "with neither key set, every shared constant and the InitStd env row run"
    ((parseCommand "!benchmark ixvm").toOption.any fun parsed =>
      parsed.matrix.any (fun cell => (cell.getObjValAs? String "env-row").toOption == some "1")
      && parsed.matrix.size == 2)
  ++ test "BENCH_CONSTANTS alone selects no env rows"
    ((parseCommand "!benchmark ixvm BENCH_CONSTANTS=Nat.add_comm").toOption.any fun parsed =>
      parsed.matrix.size == 1 &&
      parsed.matrix.all (fun cell => (cell.getObjValAs? String "env-row").toOption == some "0"))
  ++ test "BENCH_ENVS alone selects no constant rows"
    ((parseCommand "!benchmark ixvm\nBENCH_ENVS=Mathlib").toOption.any fun parsed =>
      parsed.matrix.size == 1 &&
      parsed.matrix.all (fun cell => (cell.getObjValAs? String "constants").toOption == some "none"))
  ++ test "proving with only env rows selected is rejected"
    (rejects "!benchmark ixvm prove BENCH_ENVS=InitStd")
  ++ test "proving with neither key set selects only Nat.add_comm"
    (["!benchmark ixvm prove", "!benchmark ixvm compress"].all fun c =>
      modes c == some #[ ("ixvm", "InitStd", c.splitOn " " |>.getLast!) ] &&
      (parseCommand c).toOption.any fun parsed =>
        parsed.matrix.all (fun cell =>
          (cell.getObjValAs? String "constants").toOption == some "Nat.add_comm" &&
          (cell.getObjValAs? String "env-row").toOption == some "0"))

def testRunMode : TestSeq := .individualIO "invalid run modes fail before starting measured tools" none (do
  let mut ok := true
  for args in [["--backend", "ixvm", "--mode", "unknown"],
               ["--backend", "ixvm-ooc", "--mode", "prove"],
               ["--backend", "ixvm", "--mode", "compress", "--constants", "none"]] do
    let (_, code) ← IO.FS.withIsolatedStreams (benchRunCmd.validate args)
    ok := ok && code == 2
  return (ok, 0, 0, none)) .done

def suite : List TestSeq :=
  [testRows, testCells, testReport, testFftCost, testThroughput, testRowKinds, testCommands, testRunMode]

end Tests.Ix.BenchMeasures
