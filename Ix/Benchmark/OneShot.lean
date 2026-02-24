module
public import Lean.Data.Json.FromToJson

public section

structure OneShot where
  benchTime : Nat
  deriving Lean.ToJson, Lean.FromJson, Repr

end
