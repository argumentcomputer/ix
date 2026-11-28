import IxCC.Cfg.Rc.Proof.State

set_option autoImplicit false
namespace IxCC.Cfg.Rc
open Cfg.Proof (Impl spine)

theorem spine_actionPrefix (limit first : Nat) (actions : List Action) (code : Own.Plain.Code)
    (ctors : List Lam.CtorInfo := []) (slotBase : Nat := first) :
    spine (skeleton limit first (Own.Plain.actionPrefix actions code) ctors slotBase) =
      encodePrefix limit first actions ++ spine (skeleton limit (first+actions.length) code ctors slotBase) := by
  induction actions generalizing first with
  | nil => simp [Own.Plain.actionPrefix, encodePrefix]
  | cons action actions ih =>
    simp only [Own.Plain.actionPrefix, skeleton, spine, markerRhs_eq, encodePrefix,
      List.cons_append, List.length_cons]
    rw [ih]
    rw [Nat.add_assoc first 1 actions.length, Nat.add_comm 1 actions.length]

theorem names_actionPrefix (lower : Nat) (actions : List Action) (code : Own.Plain.Code) :
    names lower (Own.Plain.actionPrefix actions code) = names lower code := by
  induction actions with
  | nil => rfl
  | cons action actions ih => exact ih

theorem varsBelow_actionPrefix (hi : Nat) (actions : List Action) (code : Own.Plain.Code) :
    varsBelow hi (Own.Plain.actionPrefix actions code) = varsBelow hi code := by
  induction actions with
  | nil => rfl
  | cons action actions ih => exact ih

theorem reuseCtorsOk_actionPrefix (ctors : List Lam.CtorInfo) (actions : List Action) (code : Own.Plain.Code) :
    reuseCtorsOk ctors (Own.Plain.actionPrefix actions code) = reuseCtorsOk ctors code := by
  induction actions with
  | nil => rfl
  | cons action actions ih => exact ih

theorem impl_after_prefix {fd : Cfg.Fun} {limit self cur next first : Nat}
    {J : Cfg.Lower.JScope} {params : List (Fir.Var × Own.PSig)} {acc : List Instr}
    {actions : List Action} {code : Own.Plain.Code}
    {ctors : List Lam.CtorInfo} {slotBase : Nat}
    (layout : Impl fd.block? self J cur params acc next
      (skeleton limit first (Own.Plain.actionPrefix actions code) ctors slotBase)) :
    Impl fd.block? self J cur params ((encodePrefix limit first actions).reverse ++ acc) next
      (skeleton limit (first+actions.length) code ctors slotBase) := by
  induction actions generalizing first acc with
  | nil => simpa [Own.Plain.actionPrefix, encodePrefix] using layout
  | cons action actions ih =>
    have after := impl_after_action (show Impl fd.block? self J cur params acc next
      (skeleton limit first (.act action (Own.Plain.actionPrefix actions code)) ctors slotBase) from layout)
    have h := ih after
    simp only [encodePrefix, List.reverse_cons, List.append_assoc, List.singleton_append,
      List.length_cons] at h ⊢
    rwa [Nat.add_assoc first 1 actions.length, Nat.add_comm 1 actions.length] at h

/-- The actual canonical source cursor identifies its complete emitted
marker prefix and the continuation layout. This is syntax transport only;
physical prefix traversal proves the intervening execution separately. -/
theorem At.action_prefix_cursor {F : Fir.Program} {P : Program} {source : Frame}
    {ρ : Own.Env} {saved : List Own.Plain.JEntry} {actions : List Action} {code : Own.Plain.Code}
    {slots : Src.NatMap Own.RVal}
    (before : At F P source ρ saved (Own.Plain.actionPrefix actions code) slots) :
    ∃ first slotBase, source.rest = encodePrefix P.base.size first actions ++
        spine (skeleton P.base.size (first+actions.length) code F.ctors slotBase) ∧
      At F P {source with rest := spine (skeleton P.base.size (first+actions.length) code F.ctors slotBase)}
        ρ saved code slots := by
  obtain ⟨fd, scope, params, acc, next, first, lower, slotBase, lookup, range, layout, cursor,
    env, bounded, loSlot, slotSub, names, vb, rc, joins⟩ := before
  refine ⟨first, slotBase, ?_, fd, scope, params, (encodePrefix P.base.size first actions).reverse ++ acc,
    next, first+actions.length, lower, slotBase, lookup, range, impl_after_prefix layout, rfl,
    env, bounded, loSlot, slotSub, ?_, ?_, ?_, joins⟩
  · rw [cursor, spine_actionPrefix P.base.size first actions code F.ctors slotBase]
  · simpa only [names_actionPrefix] using names
  · simpa only [varsBelow_actionPrefix] using vb
  · simpa only [reuseCtorsOk_actionPrefix] using rc




end IxCC.Cfg.Rc
