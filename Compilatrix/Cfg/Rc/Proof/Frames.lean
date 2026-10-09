import Compilatrix.Cfg.Rc.Proof.Coverage
import Compilatrix.Cfg.Rc.Proof.Lower
import Compilatrix.Cfg.Proof.Sim

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc
open Compilatrix.Cfg.Proof (Impl spine)

/-- Existing layout witnesses place the actual marker in the complete checked
instruction inventory, even after arbitrary earlier bindings in the block. -/
theorem impl_marker_member {fd : Cfg.Fun} {limit self cur next first : Nat}
    {J : Cfg.Lower.JScope} {params : List (Fir.Var × Own.PSig)} {acc : List Instr}
    {a : Action} {k : Own.Plain.Code}
    (h : Impl fd.block? self J cur params acc next (skeleton limit first (.act a k))) :
    marker limit first a ∈ instructions fd := by
  obtain ⟨term, hb⟩ := Cfg.Proof.impl_head h
  apply List.mem_flatMap.mpr
  refine ⟨_, List.mem_of_getElem? hb, ?_⟩
  simp [spine, skeleton, markerRhs_eq]

/-- The checked complete function table and actual block layout derive the
action lookup. No caller-supplied per-marker interpretation is assumed. -/
theorem checked_frame_action {P : Program} {fd : Cfg.Fun} {fr : Frame}
    {stk : List (Frame × Fir.Var)} {H H' : Own.Heap} {first lower next : Nat}
    {J : Cfg.Lower.JScope} {params : List (Fir.Var × Own.PSig)} {acc : List Instr}
    {a : Action} {k : Own.Plain.Code} {table : ActionTable}
    (layout : Impl fd.block? fr.fn J fr.blk params acc next
      (skeleton P.base.size first (.act a k)))
    (cursor : fr.rest = spine (skeleton P.base.size first (.act a k)))
    (checked : checkFunction P.base.size lower fd table = true)
    (tableLookup : P.actions.get? fr.fn = some table)
    (effect : Own.Plain.evalAction fr.env H a = .ok H') :
    step P (.run fr stk H) =
      .next (.run { fr with rest := spine (skeleton P.base.size (first + 1) k) } stk H') false := by
  have member := impl_marker_member layout
  obtain ⟨slot, action, decoded, _, found⟩ := collect_member
    ((checkMarkers_iff ..).mp checked) member (reserved_marker ..)
  simp only [decode_marker, Option.some.injEq, Prod.mk.injEq] at decoded
  rcases decoded with ⟨rfl, rfl⟩
  apply step_action_success ?_ tableLookup found effect
  simpa only [skeleton, spine, markerRhs_eq] using cursor

theorem impl_after_action {fd : Cfg.Fun} {limit self cur next first : Nat}
    {J : Cfg.Lower.JScope} {params : List (Fir.Var × Own.PSig)} {acc : List Instr}
    {a : Action} {k : Own.Plain.Code}
    (h : Impl fd.block? self J cur params acc next (skeleton limit first (.act a k))) :
    Impl fd.block? self J cur params (marker limit first a :: acc) next
      (skeleton limit (first + 1) k) := by
  simpa only [skeleton, Impl, markerRhs_eq] using h


end Compilatrix.Cfg.Rc
