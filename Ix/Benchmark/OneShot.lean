module
public import Lean.Data.Json.FromToJson
public import Ix.Benchmark.Common

public section

structure OneShot where
  benchTime : Nat
  /-- Optional throughput metadata captured at registration time. Embedded
      directly in the one-shot result so one-shot mode doesn't need a separate
      throughput file on disk. -/
  throughput : Option Throughput := none
  deriving Lean.ToJson, Lean.FromJson, Repr

end
