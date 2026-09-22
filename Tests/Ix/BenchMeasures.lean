/-
  Tests for the benchmark measure-naming convention
  (`Ix.Cli.BenchCmd.stagePrefixOf` / `dropStagePrefix`): the string
  parsing that measure formatting kinds, units, improvement direction,
  and stage-table column labels all key off.
-/

module
public import Ix.Cli.BenchCmd
public import Ix.Cli.BenchReport
public import LSpec

public section

open LSpec Ix.Cli.BenchCmd

namespace Tests.Ix.BenchMeasures

def testStagePrefix : TestSeq :=
  test "ixvm- strips" (dropStagePrefix "ixvm-prove-time" == "prove-time")
  ++ test "fri-verifier- strips"
      (dropStagePrefix "fri-verifier-peak-rss" == "peak-rss")
  ++ test "pipeline- strips"
      (dropStagePrefix "pipeline-throughput" == "throughput")
  ++ test "ixvm- prefix identified"
      (stagePrefixOf "ixvm-verify-time" == some "ixvm-")
  ++ test "fri-verifier- prefix identified"
      (stagePrefixOf "fri-verifier-fft-cost" == some "fri-verifier-")
  ++ test "join- strips" (dropStagePrefix "join-proof-size" == "proof-size")
  ++ test "join- prefix identified"
      (stagePrefixOf "join-execute-time" == some "join-")
  ++ test "unqualified name passes through"
      (dropStagePrefix "execute-time" == "execute-time")
  ++ test "prefix without dash is not a qualifier"
      (stagePrefixOf "ixvmtime" == none)
  ++ test "fri- alone is not a qualifier"
      (stagePrefixOf "fri-fold-time" == none)
  ++ test "phase spans pass through"
      (dropStagePrefix "phase-stark-stage1-commit"
        == "phase-stark-stage1-commit")
  ++ test "aiur join pair is registered for dashboard filtering"
      ((backendSpecs.find? (·.name == "aiur")).any fun backend =>
        (backend.benchmarkNames "prove").contains
          "Nat.add_comm + String.append")

def testJoinSelection : TestSeq :=
  test "scheduled InitStd prove includes the aggregation pair"
    (aiurJoinNames "InitStd" "prove"
      ((selectNames "InitStd" "aiur" "prove").map (·.name)) == aiurJoinBenchmarkNames)
  ++ test "execute does not schedule proving"
    ((aiurJoinNames "InitStd" "execute" aiurJoinConstants).isEmpty)
  ++ test "other envs do not duplicate the pair"
    ((aiurJoinNames "Mathlib" "prove" aiurJoinConstants).isEmpty)
  ++ test "single-constant override does not schedule a pair"
    ((aiurJoinNames "InitStd" "prove" #["Nat.add_comm"]).isEmpty)
  ++ test "pair ordering is stable across selection order"
    (aiurJoinNames "InitStd" "prove" #["String.append", "Nat.add_comm"]
      == aiurJoinBenchmarkNames)

open Ix.Cli.BenchReport in
def testJoinReport : TestSeq := Id.run do
  let pair := aiurJoinBenchmarkNames[0]!
  let names := aiurJoinConstants.push pair
  let joinSection := scopeAiurSection names
    { heading := "Aggregate flat join", metrics := #["join-prove-time"] }
  let ixvmSection := scopeAiurSection names
    { heading := "IxVM on FRI", metrics := #["ixvm-prove-time"] }
  let rows := Lean.Json.mkObj [
    ("Nat.add_comm", Lean.Json.mkObj [("ixvm-prove-time", Lean.toJson (1 : Nat))]),
    (pair, Lean.Json.mkObj [("status", Lean.Json.str "oom")])]
  let table := renderCompare {
    mainRows := Lean.Json.mkObj [], prRows := rows
    sections := #[joinSection], threshold := 3, title := "join" }
  let oldTable := renderCompare {
    mainRows := rows, prRows := rows
    sections := #[scopeAiurSection aiurJoinConstants joinSection]
    threshold := 3, title := "old" }
  return test "join table selects only the pair"
      (joinSection.names == some #[pair])
    ++ test "pipeline tables exclude the pair"
      (ixvmSection.names == some aiurJoinConstants)
    ++ test "failed pair stays visible without metrics"
      ((table.splitOn "OOM").length == 2)
    ++ test "join table does not fabricate per-constant rows"
      ((table.splitOn "| `Nat.add_comm` |").length == 1)
    ++ test "old per-constant results do not render an empty join table"
      ((oldTable.splitOn "Aggregate flat join").length == 1)

/-- Exercise the real orchestration with small JSON fixtures instead of
    allocating a prover. Child rows deliberately collide with existing rows. -/
def testJoinRun : TestSeq := .individualIO "join result isolation and failures" none (do
  let dir ← IO.FS.createTempDir
  try
    let out := (dir / "bench.json").toString
    let pair := aiurJoinBenchmarkNames[0]!
    let child := aiurJoinConstants[0]!
    let fields := ["join-execute-time", "join-prove-time", "join-peak-rss",
                   "join-proof-size", "join-verify-time", "join-fft-cost"].map
      fun k => (k, Lean.toJson (1 : Nat))
    let write := Ix.Benchmark.Results.writeRow
    let read := Ix.Benchmark.Results.readRows
    write out child "ok" [("ixvm-prove-time", Lean.toJson (42 : Nat))]
    runAiurJoin out fun path => do
      write path child "ok" [("ixvm-prove-time", Lean.toJson (999 : Nat))]
      write path pair "ok" fields
      return 0
    let rows ← read out
    let isolated := Ix.Cli.BenchReport.rowNum rows child "ixvm-prove-time" == some 42
      && Ix.Cli.BenchReport.rowNum rows pair "join-prove-time" == some 1
    runAiurJoin out fun path => do
      write path pair "ok" [("join-execute-time", Lean.toJson (2 : Nat))]
      return 137
    let rows ← read out
    let keptPartial := Ix.Cli.BenchReport.rowStatus rows pair == "oom"
      && Ix.Cli.BenchReport.rowNum rows pair "join-execute-time" == some 2
      && (Ix.Cli.BenchReport.rowNum rows pair "join-prove-time").isNone
    runAiurJoin out fun path => do
      write path pair "ok" fields
      return 137
    let teardown := Ix.Cli.BenchReport.rowStatus (← read out) pair == "ok"
    runAiurJoin out fun _ => pure Ix.Benchmark.Results.exitRejected
    let rejected := Ix.Cli.BenchReport.rowStatus (← read out) pair == "rejected"
    let mut errors := 0
    for code in [0, 1, 255] do
      try runAiurJoin out fun _ => pure code
      catch _ => errors := errors + 1
    try
      runAiurJoin out fun path => do
        write path pair "ok" [("join-execute-time", Lean.toJson (2 : Nat))]
        return 0
    catch _ => errors := errors + 1
    return (isolated && keptPartial && teardown && rejected && errors == 4, 0, 0, none)
  finally
    IO.FS.removeDirAll dir) .done

def suite : List TestSeq := [testStagePrefix, testJoinSelection, testJoinReport, testJoinRun]

end Tests.Ix.BenchMeasures
