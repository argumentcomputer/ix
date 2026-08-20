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
  test "stage1- strips" (dropStagePrefix "stage1-prove-time" == "prove-time")
  ++ test "stage2- strips" (dropStagePrefix "stage2-peak-rss" == "peak-rss")
  ++ test "multi-digit stage strips"
      (dropStagePrefix "stage12-fft-cost" == "fft-cost")
  ++ test "pipeline- strips"
      (dropStagePrefix "pipeline-throughput" == "throughput")
  ++ test "stage1- prefix identified"
      (stagePrefixOf "stage1-verify-time" == some "stage1-")
  ++ test "unqualified name passes through"
      (dropStagePrefix "execute-time" == "execute-time")
  ++ test "stage without digits is not a qualifier"
      (stagePrefixOf "stage-time" == none)
  ++ test "stage digits without dash is not a qualifier"
      (stagePrefixOf "stage1time" == none)
  ++ test "stage prefix inside a word is not a qualifier"
      (stagePrefixOf "stagehand-time" == none)
  ++ test "bare stage name passes through"
      (dropStagePrefix "stages" == "stages")

def suite : List TestSeq := [testStagePrefix]

end Tests.Ix.BenchMeasures
