import Benchmark.ScalingVerify

open Compilatrix.Tools.Check

def main (args : List String) : IO UInt32 := cli "compiler scaling failed" do
  match args with
  | ["generate", "joins", count, "0", output] =>
    Benchmark.Scaling.generateJoins (← present count.toNat? "size must be a natural number") output
  | ["generate", family, count, edited, output] =>
    need (["0", "1"].contains edited) "edited must be 0 or 1"
    Benchmark.Scaling.generate family (← present count.toNat? "size must be a natural number") (edited == "1") output
  | ["compile", input, output] =>
    let metadata ← readJson input
    if (← strField metadata "format") == "compilatrix/compiler-scaling-rejected-input/1" then Benchmark.Scaling.compileRejectedInput input output
    else if (← strField metadata "family") == "joins" then Benchmark.Scaling.compileJoins input output
    else Benchmark.Scaling.compile input output none
  | ["compile", input, output, cache] => Benchmark.Scaling.compile input output (some cache)
  | ["verify", directory, output] => Benchmark.Scaling.verify directory output
  | _ => throw (IO.userError "usage: compiler-scaling generate FAMILY SIZE EDITED INPUT | compile INPUT OUTPUT [CACHE] | verify DIRECTORY REPORT")
