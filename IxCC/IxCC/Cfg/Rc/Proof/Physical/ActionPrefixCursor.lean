import IxCC.Cfg.Rc.Proof.State

set_option autoImplicit false
namespace IxCC.Cfg.Rc
open Cfg.Proof (Impl spine)

theorem spine_actionPrefix (limit first : Nat) (actions : List Action) (code : Own.Plain.Code) :
    spine (skeleton limit first (Own.Plain.actionPrefix actions code)) =
      encodePrefix limit first actions ++ spine (skeleton limit (first+actions.length) code) := by
  induction actions generalizing first with
  | nil => simp [Own.Plain.actionPrefix, encodePrefix]
  | cons action actions ih =>
    simp only [Own.Plain.actionPrefix, skeleton, spine, markerRhs_eq, encodePrefix,
      List.cons_append, List.length_cons]
    rw [ih]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem names_actionPrefix (lower : Nat) (actions : List Action) (code : Own.Plain.Code) :
    names lower (Own.Plain.actionPrefix actions code) = names lower code := by
  induction actions with
  | nil => rfl
  | cons action actions ih => exact ih

theorem impl_after_prefix {fd : Cfg.Fun} {limit self cur next first : Nat}
    {J : Cfg.Lower.JScope} {params : List (Fir.Var × Own.PSig)} {acc : List Instr}
    {actions : List Action} {code : Own.Plain.Code}
    (layout : Impl fd.block? self J cur params acc next
      (skeleton limit first (Own.Plain.actionPrefix actions code))) :
    Impl fd.block? self J cur params ((encodePrefix limit first actions).reverse ++ acc) next
      (skeleton limit (first+actions.length) code) := by
  induction actions generalizing first acc with
  | nil => simpa [Own.Plain.actionPrefix, encodePrefix] using layout
  | cons action actions ih =>
    have after := impl_after_action (show Impl fd.block? self J cur params acc next
      (skeleton limit first (.act action (Own.Plain.actionPrefix actions code))) from layout)
    simpa [encodePrefix, List.reverse_cons, List.append_assoc, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using ih after

/-- The actual canonical source cursor identifies its complete emitted
marker prefix and the continuation layout. This is syntax transport only;
physical prefix traversal proves the intervening execution separately. -/
theorem At.action_prefix_cursor {F : Fir.Program} {P : Program} {source : Frame}
    {ρ : Own.Env} {saved : List Own.Plain.JEntry} {actions : List Action} {code : Own.Plain.Code}
    (before : At F P source ρ saved (Own.Plain.actionPrefix actions code)) :
    ∃ first, source.rest = encodePrefix P.base.size first actions ++
        spine (skeleton P.base.size (first+actions.length) code) ∧
      At F P {source with rest := spine (skeleton P.base.size (first+actions.length) code)}
        ρ saved code := by
  obtain ⟨fd, scope, params, acc, next, first, lower, lookup, range, layout, cursor,
    env, bounded, names, joins⟩ := before
  refine ⟨first, ?_, fd, scope, params, (encodePrefix P.base.size first actions).reverse ++ acc,
    next, first+actions.length, lower, lookup, range, impl_after_prefix layout, rfl,
    env, bounded, ?_, joins⟩
  · rw [cursor, spine_actionPrefix]
  · simpa only [names_actionPrefix] using names




end IxCC.Cfg.Rc
