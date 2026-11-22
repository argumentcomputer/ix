import IxCC.Cfg.Rc.Lower
import IxCC.Cfg.Rc.Proof.Prefix

set_option autoImplicit false
namespace IxCC.Cfg.Rc


theorem checkFunction_intercepts {limit first : Nat} {fd : Cfg.Fun} {table : ActionTable}
    {i : Instr} {rest : List Instr}
    (hcode : instructions fd = i :: rest)
    (hcheck : checkFunction limit first fd table = true)
    (hreserved : reserved limit i = true) :
    ∃ slot a, decode limit i = some (slot, a) ∧ first ≤ slot ∧ table.get? slot = some a := by
  unfold checkFunction at hcheck
  rw [hcode] at hcheck
  exact checked_head_intercepts hcheck hreserved

theorem skeleton_action (limit first : Nat) (a : Action) (k : Own.Plain.Code) :
    skeleton limit first (.act a k) =
      .bind first (markerRhs limit a) (skeleton limit (first + 1) k) := rfl

theorem markerRhs_eq (limit first : Nat) (a : Action) :
    Instr.bind first (markerRhs limit a) = marker limit first a := by cases a <;> rfl

/-- The actual existing block builder emits exactly the action prefix whose
small-step execution is proved in `prefix_reach`; this is not a separate toy
instruction translation. Its reversed accumulator convention is preserved. -/
theorem lower_actionPrefix (limit first self : Nat) (J : Cfg.Lower.JScope)
    (cur : BlockId) (params : List (Fir.Var × Own.PSig)) (acc : List Instr)
    (next : BlockId) (out : Cfg.Lower.Out) (as : List Action) (k : Own.Plain.Code) :
    Cfg.Lower.code self J cur params acc next out
      (skeleton limit first (Own.Plain.actionPrefix as k)) =
    Cfg.Lower.code self J cur params ((encodePrefix limit first as).reverse ++ acc) next out
      (skeleton limit (first + as.length) k) := by
  induction as generalizing first acc with
  | nil => simp [Own.Plain.actionPrefix, encodePrefix]
  | cons a as ih =>
    simp only [Own.Plain.actionPrefix, skeleton, Cfg.Lower.code]
    rw [ih, markerRhs_eq]
    simp [encodePrefix, List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

end IxCC.Cfg.Rc
