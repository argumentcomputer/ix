import Comparisons.Reproduce
import Comparisons.CounterFold
import Comparisons.ScalingReproduce

open Compilatrix.Tools.Check

def main (args : List String) : IO UInt32 := cli "benchmark failed" do
  match args with
  | "compiler-scaling-build" :: output :: options =>
    let options ← checked (parseArgs ["--profile", "--worker", "--gcc", "--time"] options)
    Benchmark.CompilerScaling.buildSuite output (option options "--profile" "full")
      (option options "--worker" (← Benchmark.scalingWorker).toString) (option options "--gcc" "gcc") (option options "--time" "time")
  | ["compiler-scaling-golden", build, output] =>
    Benchmark.writeJson output (← Benchmark.CompilerScaling.golden (← Benchmark.CompilerScaling.inspectBuild build))
  | ["compiler-scaling-verify", build, output] => Benchmark.CompilerScaling.verifySuite build output
  | ["compiler-scaling-measure", build, correctness, output, core] =>
    Benchmark.CompilerScaling.measureSuite build correctness output (← present core.toNat? "core must be a natural number")
  | ["compiler-scaling-analyze", build, measured, output] => Benchmark.CompilerScaling.analyzeSuite build measured output
  | ["compiler-scaling-measurement-regressions", build, measured, output] => Benchmark.CompilerScaling.measurementRegressions build measured output
  | ["compiler-scaling-reproduce", build, measured, output] => Benchmark.CompilerScaling.reproduceSuite build measured output
  | "compiler-scaling-smoke" :: output :: options =>
    let options ← checked (parseArgs ["--gcc", "--time"] options)
    Benchmark.CompilerScaling.smokeSuite output (option options "--gcc" "gcc") (option options "--time" "time")
  | "counter-fold-build" :: output :: options =>
    let options ← checked (parseArgs ["--gcc", "--time"] options)
    Benchmark.CounterFold.buildSuite output (option options "--gcc" "gcc") (option options "--time" "time")
  | ["counter-fold-verify", build, output] => Benchmark.CounterFold.verifySuite build output
  | ["counter-fold-smoke", build, output, core] =>
    Benchmark.CounterFold.smokeSuite build output (← present core.toNat? "core must be a natural number")
  | ["counter-fold-smoke", build, output] => Benchmark.CounterFold.smokeSuite build output (← Benchmark.firstCore)
  | ["counter-fold-pilot", build, correctness, output, core] =>
    Benchmark.CounterFold.pilotSuite build correctness output (← present core.toNat? "core must be a natural number")
  | ["counter-fold-measure", build, correctness, pilot, output, core] =>
    Benchmark.CounterFold.measureSuite build correctness pilot output (← present core.toNat? "core must be a natural number")
  | ["counter-fold-analyze", build, measured, output] => Benchmark.CounterFold.analyzeSuite build measured output
  | ["counter-fold-reproduce", build, measured, output] => Benchmark.CounterFold.reproduceSuite build measured output
  | ["datasets", output] =>
    Benchmark.writeDatasets output
    IO.println "benchmark datasets: 585 inputs, 19305 arena capacity cases, 38 timing rows"
  | "build" :: output :: options =>
    let options ← checked (parseArgs ["--gcc", "--clang", "--compcert", "--cakeml", "--time"] options)
    Benchmark.buildSuite output {
      gcc := option options "--gcc" "gcc", clang := option options "--clang" "clang",
      compcert := option options "--compcert" "ccomp", cakeml := option options "--cakeml" "cake",
      timerTool := option options "--time" "time" }
  | ["check-matrix", implementation, path] =>
    let rows ← Benchmark.readLines path
    let result ← Benchmark.inspectMatrix implementation rows
    Benchmark.checkerRegressions implementation rows
    IO.println result.compress
  | ["verify", build, output] => Benchmark.verifySuite build output
  | ["smoke", build, output, core] =>
    Benchmark.smokeSuite build output (← present core.toNat? "core must be a natural number")
  | ["smoke", build, output] => Benchmark.smokeSuite build output (← Benchmark.firstCore)
  | ["gc-smoke", build, output, core] =>
    Benchmark.gcSmokeSuite build output (← present core.toNat? "core must be a natural number")
  | ["gc-smoke", build, output] => Benchmark.gcSmokeSuite build output (← Benchmark.firstCore)
  | ["pilot", build, correctness, output, core] =>
    Benchmark.pilotSuite build correctness output (← present core.toNat? "core must be a natural number")
  | ["measure", build, correctness, pilot, output, core] =>
    Benchmark.measureSuite build correctness pilot output (← present core.toNat? "core must be a natural number")
  | ["analyze", build, measured, output] => Benchmark.analyzeSuite build measured output
  | ["analysis-self-check"] => Benchmark.analysisSelfCheck
  | ["diagnose", build, pilot, output, core] =>
    Benchmark.diagnoseSuite build pilot output (← present core.toNat? "core must be a natural number")
  | ["reproduce", build, measured, output] => Benchmark.reproduceSuite build measured output
  | ["rebuild-check", build, output] => let _ ← Benchmark.rebuildArtifacts build output; pure ()
  | _ => throw (IO.userError "usage: benchmark datasets OUT | build OUT [--gcc PATH --clang PATH --compcert PATH --cakeml PATH --time PATH] | verify BUILD OUT | smoke BUILD OUT [CORE] | gc-smoke BUILD OUT [CORE] | pilot BUILD VERIFY OUT CORE | measure BUILD VERIFY PILOT OUT CORE | diagnose BUILD PILOT OUT CORE | analyze BUILD MEASURED OUT | reproduce BUILD MEASURED OUT | analysis-self-check | compiler-scaling-build OUT [--profile smoke|full --worker PATH --gcc PATH --time PATH] | compiler-scaling-verify BUILD OUT | compiler-scaling-measure BUILD VERIFY OUT CORE | compiler-scaling-analyze BUILD MEASURED OUT | compiler-scaling-reproduce BUILD MEASURED OUT | compiler-scaling-smoke OUT [--gcc PATH --time PATH] | compiler-scaling-golden BUILD OUTPUT")
