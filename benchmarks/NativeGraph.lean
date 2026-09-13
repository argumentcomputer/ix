import Benchmark.NativeGraph

open Compilatrix.Tools.Check

def main (args : List String) : IO UInt32 := cli "native graph failed" do
  let [directory, profile] := args
    | throw (IO.userError "usage: native-graph NEW-OUTPUT-DIRECTORY smoke|reference")
  Benchmark.NativeGraph.produce directory profile
