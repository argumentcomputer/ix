/-
  The twins fixtures, as one module: the root of the `TwinsFixtures` library
  (`lakefile.lean`), which `IxTests` needs.

  `IxTests` does not import it. The `twins` suite imports it at run time
  (`Tests.Ix.Compile.Twins.fixturesEnv`, through `getCompileEnv`), so these
  presentations stay out of the environment every other suite reads with
  `get_env!`. Some of them are refused by both compilers on purpose (the
  call-site surgery's safety refusals, `Tests.Ix.Compile.NonCanonical.
  expectedRefusals`), and the whole-environment suites (`rust-compile`,
  `decompile`, `rust-decompile`, `ixon-corpus`, …) count a refused constant
  as a failure.

  It also carries the clique library's fixtures
  (`Tests.Ix.Compile.Clique.Fixtures`), which the suites `clique-recognition`
  and `clique-transport` load with the twins, for the same reason: some of
  them are named like encoding constants on purpose.
-/
import Tests.Ix.Compile.Twins.Cliques
import Tests.Ix.Compile.Twins.Repro
import Tests.Ix.Compile.Twins.Proto
import Tests.Ix.Compile.Oracle.Lib
import Tests.Ix.Compile.Fixtures.LetNonDep
import Tests.Ix.Compile.Fixtures.NestedLevels
import Tests.Ix.Compile.Clique.Fixtures
