module
public import Lean.Data.Json.FromToJson
public import Ix.Benchmark.Common

public section

structure OneShot where
  benchTime : Nat
  throughput : Option Throughput := none
  deriving Lean.ToJson, Lean.FromJson, Repr

/-- Group-level end-to-end total: the sum of per-stage mean/one-shot times
    for every bench in a group. Persisted to disk so successive runs can
    report a percent change against the previous total. -/
structure E2ETotal where
  totalNs : Float
  deriving Lean.ToJson, Lean.FromJson, Repr

end
