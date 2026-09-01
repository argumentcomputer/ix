/-
  Tests for the benchmark measure-naming convention
  (`Ix.Cli.BenchCmd.stagePrefixOf` / `dropStagePrefix`): the string
  parsing that measure formatting kinds, units, improvement direction,
  and stage-table column labels all key off.
-/

module
public import Ix.Cli.BenchCmd
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

def suite : List TestSeq := [testStagePrefix]

end Tests.Ix.BenchMeasures
