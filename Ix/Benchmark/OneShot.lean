module
public import Lean.Data.Json.FromToJson
public import Ix.Benchmark.Common

public section

structure OneShot where
  benchTime : Nat
  throughput : Option Throughput := none
  deriving Lean.ToJson, Lean.FromJson, Repr

end
