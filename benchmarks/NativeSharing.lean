import Benchmark.NativeSharing

open Compilatrix.Tools.Check

def main (args : List String) : IO UInt32 := cli "native sharing failed" do
  let [directory, profile] := args
    | throw (IO.userError "usage: native-sharing NEW-OUTPUT-DIRECTORY smoke|reference")
  Benchmark.NativeSharing.produce directory profile
