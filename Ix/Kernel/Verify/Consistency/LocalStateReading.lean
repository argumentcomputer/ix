/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.RecursiveLocalState
import Ix.Kernel.Verify.Consistency.IngressLocalState

/-! Connect the maintained structural invariant to the model's local reader.
Observable scope restoration preserves that reader, and the allocation bound
proves freshness for every registered model local. These facts hold for the
actual recursive checker, including its installed production loader. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model
universe u

theorem LocalContextReading.congr {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {context : Model.Context β} {left right : LocalContext .anon}
    (agreement : LocalContextReading resolve locals left context) (same : left.Equiv right) :
    LocalContextReading resolve locals right context := by
  refine ⟨agreement.distinct, agreement.length, ?_⟩
  intro id index registered
  obtain ⟨decl, type, found, position, reading⟩ := agreement.lookup id index registered
  exact ⟨decl, type, (same.find? id).symm.trans found, position, reading⟩

theorem localIndex?_of_mem {locals : List FVarId} {id : FVarId} (member : id ∈ locals) :
    ∃ index, localIndex? locals id = some index := by
  induction locals with
  | nil => contradiction
  | cons head rest ih =>
      by_cases equal : id = head
      · exact ⟨0, by simp [localIndex?, equal]⟩
      · obtain ⟨index, found⟩ := ih ((List.mem_cons.mp member).resolve_left equal)
        exact ⟨index + 1, by simp [localIndex?, equal, found]⟩

/-- Freshness comes from the maintained production counter, even when the
reader registers only part of the concrete context. -/
theorem LocalStateInvariant.freshReading {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {context : Model.Context β} {state : TcState .anon}
    (valid : LocalStateInvariant state)
    (agreement : LocalContextReading resolve locals state.lctx context) :
    (⟨state.env.nextFVarId⟩ : FVarId) ∉ locals := by
  intro member
  obtain ⟨index, registered⟩ := localIndex?_of_mem member
  obtain ⟨decl, _, found, _, _⟩ := agreement.lookup _ index registered
  simp [LocalContext.find?, valid.allocated.fresh] at found

theorem FramesLocalState.ok {action : TcM .anon α}
    (framed : FramesLocalState action) {before after : TcState .anon} {value : α}
    (valid : LocalStateInvariant before) (run : action before = .ok value after) :
    LocalStateFrame before after := by
  have frame := framed before valid
  rw [run] at frame
  exact frame

theorem FramesLocalState.error {action : TcM .anon α}
    (framed : FramesLocalState action) {before after : TcState .anon} {error : TcError .anon}
    (valid : LocalStateInvariant before) (run : action before = .error error after) :
    LocalStateFrame before after := by
  have frame := framed before valid
  rw [run] at frame
  exact frame

theorem infer_methodsN_framesLocalState (fuel : Nat) (term : KExpr .anon) :
    FramesLocalState (RecM.infer term (methodsN fuel)) :=
  infer_framesLocalState_of_whnf (MethodsLocalState.methodsN fuel).infer
    (FramesLocalState.whnf (MethodsLocalState.methodsN fuel))
    (MethodsLocalState.methodsN fuel).isDefEq term

theorem isDefEq_methodsN_framesLocalState (fuel : Nat) (left right : KExpr .anon) :
    FramesLocalState (RecM.isDefEq left right (methodsN fuel)) :=
  FramesLocalState.isDefEq (MethodsLocalState.methodsN fuel) left right

/-- A caller's model context survives the complete public inference entry. -/
theorem infer_localReading {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {context : Model.Context β} {before after : TcState .anon}
    {term type : KExpr .anon} (valid : LocalStateInvariant before)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (run : TcM.infer term before = .ok type after) :
    LocalStateInvariant after ∧ LocalContextReading resolve locals after.lctx context := by
  have frame := (TcM.infer_framesLocalState term).ok valid run
  exact ⟨frame.invariant valid, agreement.congr frame.context.symm⟩

end Ix.Kernel.Consistency
