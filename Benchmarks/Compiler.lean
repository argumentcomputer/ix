import Benchmarks.Compiler.Reproduce
import Benchmarks.Compiler.CounterFold

open Ix.Compiler.Tools.Check

def main (args : List String) : IO UInt32 := cli "benchmark failed" do
  match args with
  | "counter-fold-build" :: output :: options =>
    let options ← checked (parseArgs ["--gcc", "--time"] options)
    Benchmarks.Compiler.CounterFold.buildSuite output (option options "--gcc" "gcc") (option options "--time" "time")
  | ["counter-fold-verify", build, output] => Benchmarks.Compiler.CounterFold.verifySuite build output
  | ["counter-fold-smoke", build, output, core] =>
    Benchmarks.Compiler.CounterFold.smokeSuite build output (← present core.toNat? "core must be a natural number")
  | ["counter-fold-smoke", build, output] => Benchmarks.Compiler.CounterFold.smokeSuite build output (← Benchmarks.Compiler.firstCore)
  | ["counter-fold-pilot", build, correctness, output, core] =>
    Benchmarks.Compiler.CounterFold.pilotSuite build correctness output (← present core.toNat? "core must be a natural number")
  | ["counter-fold-measure", build, correctness, pilot, output, core] =>
    Benchmarks.Compiler.CounterFold.measureSuite build correctness pilot output (← present core.toNat? "core must be a natural number")
  | ["counter-fold-analyze", build, measured, output] => Benchmarks.Compiler.CounterFold.analyzeSuite build measured output
  | ["counter-fold-reproduce", build, measured, output] => Benchmarks.Compiler.CounterFold.reproduceSuite build measured output
  | ["datasets", output] =>
    Benchmarks.Compiler.writeDatasets output
    IO.println "benchmark datasets: 585 inputs, 19305 arena capacity cases, 38 timing rows"
  | "build" :: output :: options =>
    let options ← checked (parseArgs ["--gcc", "--clang", "--compcert", "--cakeml", "--time"] options)
    Benchmarks.Compiler.buildSuite output {
      gcc := option options "--gcc" "gcc", clang := option options "--clang" "clang",
      compcert := option options "--compcert" "ccomp", cakeml := option options "--cakeml" "cake",
      timerTool := option options "--time" "time" }
  | ["check-matrix", implementation, path] =>
    let rows ← Benchmarks.Compiler.readLines path
    let result ← Benchmarks.Compiler.inspectMatrix implementation rows
    Benchmarks.Compiler.checkerRegressions implementation rows
    IO.println result.compress
  | ["verify", build, output] => Benchmarks.Compiler.verifySuite build output
  | ["smoke", build, output, core] =>
    Benchmarks.Compiler.smokeSuite build output (← present core.toNat? "core must be a natural number")
  | ["smoke", build, output] => Benchmarks.Compiler.smokeSuite build output (← Benchmarks.Compiler.firstCore)
  | ["gc-smoke", build, output, core] =>
    Benchmarks.Compiler.gcSmokeSuite build output (← present core.toNat? "core must be a natural number")
  | ["gc-smoke", build, output] => Benchmarks.Compiler.gcSmokeSuite build output (← Benchmarks.Compiler.firstCore)
  | ["pilot", build, correctness, output, core] =>
    Benchmarks.Compiler.pilotSuite build correctness output (← present core.toNat? "core must be a natural number")
  | ["measure", build, correctness, pilot, output, core] =>
    Benchmarks.Compiler.measureSuite build correctness pilot output (← present core.toNat? "core must be a natural number")
  | ["analyze", build, measured, output] => Benchmarks.Compiler.analyzeSuite build measured output
  | ["analysis-self-check"] => Benchmarks.Compiler.analysisSelfCheck
  | ["diagnose", build, pilot, output, core] =>
    Benchmarks.Compiler.diagnoseSuite build pilot output (← present core.toNat? "core must be a natural number")
  | ["reproduce", build, measured, output] => Benchmarks.Compiler.reproduceSuite build measured output
  | ["rebuild-check", build, output] => let _ ← Benchmarks.Compiler.rebuildArtifacts build output; pure ()
  | _ => throw (IO.userError "usage: benchmark datasets OUT | build OUT [--gcc PATH --clang PATH --compcert PATH --cakeml PATH --time PATH] | verify BUILD OUT | smoke BUILD OUT [CORE] | gc-smoke BUILD OUT [CORE] | pilot BUILD VERIFY OUT CORE | measure BUILD VERIFY PILOT OUT CORE | diagnose BUILD PILOT OUT CORE | analyze BUILD MEASURED OUT | reproduce BUILD MEASURED OUT | analysis-self-check")
