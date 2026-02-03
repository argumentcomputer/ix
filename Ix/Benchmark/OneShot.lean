import Lean.Data.Json.FromToJson

structure OneShot where
  benchTime : Nat
  throughput : Option Float
  deriving Lean.ToJson, Lean.FromJson, Repr

structure OneShots where
  base : Option OneShot
  new : OneShot
  deriving Repr

