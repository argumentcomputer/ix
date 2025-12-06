import Lean.Data.Json.FromToJson

structure OneShot where
  benchTime : Nat
  deriving Lean.ToJson, Lean.FromJson, Repr

