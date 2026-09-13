import Benchmark.SourceEvidence

def main (args : List String) : IO UInt32 := Compilatrix.Tools.Check.cli "source-evidence" do
  match args with
  | ["run", directory, profile] => Benchmark.SourceEvidence.produce directory profile
  | ["replay", input, output] => Benchmark.SourceEvidence.replay input output
  | _ => throw (IO.userError "usage: source-evidence run NEWDIR smoke|reference | replay INPUT NEWDIR")
