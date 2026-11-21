import Aiur.Generic.Runtime

namespace Aiur.Generic.SourceSemantics

theorem constant_evaluates [Field F] [DecidableEq F] (world : World F) (value : Constant F)
    (types : Types) (locals : Environment F Nat) (heap : Heap F) :
    EvalExpr world types locals (constantExpr value) heap value.toValue heap := by
  have children (values : List (Constant F))
      (smaller : ∀ v ∈ values, sizeOf v < sizeOf value) :
      EvalArgs world types locals (values.map constantExpr) heap (values.map (Value.mapAddress Empty.elim)) heap := by
    induction values with
    | nil => exact .nil
    | cons v vs ih =>
        exact .cons (constant_evaluates world v types locals heap)
          (ih (fun x hx => smaller x (by simp [hx])))
  cases value with
  | field => simp only [constantExpr, Constant.toValue, Value.mapAddress]; exact .literal
  | ptr _ address => exact Empty.elim address
  | tuple values =>
      simpa only [constantExpr, Constant.toValue, Value.mapAddress] using
        EvalExpr.tuple (children values (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega))
  | construct name ctor values =>
      simpa only [constantExpr, Constant.toValue, Value.mapAddress, instanceName,
        Option.getD_some, List.map_nil, Instance.symbol, List.isEmpty_nil, ↓reduceIte] using
        EvalExpr.construct (name := name) (args := some []) (ctor := ctor)
          (children values (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega))
termination_by sizeOf value
decreasing_by exact smaller _ (by simp)

end Aiur.Generic.SourceSemantics
