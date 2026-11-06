/-
  Tests for the benchmark registry's row kinds: a backend's constant rows
  are the shared constants, each in its own env, and its env rows are the
  registry envs; both kinds plot on the backend's one testbed.
-/

module
public import Ix.Cli.BenchCmd
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
  ++ test "backend testbeds are distinct"
    ((backendSpecs.map (·.testbed)).eraseDups.length == backendSpecs.length)

def suite : List TestSeq := [testRows]

end Tests.Ix.BenchMeasures
