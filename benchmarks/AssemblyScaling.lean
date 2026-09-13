import Benchmark.Assembly

def main (args : List String) : IO UInt32 := Compilatrix.Tools.Check.cli "assembly-scaling" do
  match args with
  | ["run", directory, profile] => Benchmark.Assembly.produce directory profile
  | ["replay", input, output] => Benchmark.Assembly.replay input output
  | _ => throw (IO.userError "usage: assembly-scaling run NEW-DIRECTORY smoke|reference | replay INPUT NEW-DIRECTORY")
