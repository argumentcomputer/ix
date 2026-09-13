/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CompilerAllocation
import Ix.Aiur.Proofs.Relayout

/-! Branch layout restores the incoming logical degrees and retains the maximum
physical allocation, including the inverse columns of a default branch. -/

namespace Aiur.Concrete.Bytecode
open Aiur.Bytecode

def allocationBranchStep (shared : SharedData) (degrees : Array Nat) (acc : SharedData)
    (block : Block) : LayoutM SharedData := do
  setSharedData shared
  blockLayout block
  let used ← getSharedData
  setDegrees degrees
  return acc.maximals used

theorem allocationBranchStep_degrees (shared : SharedData) (degrees : Array Nat) (acc : SharedData)
    (block : Block) (initial : LayoutMState) :
    ((allocationBranchStep shared degrees acc block).run initial).2.degrees = degrees := rfl

theorem allocationBranchStep_callRanks (shared : SharedData) (degrees : Array Nat)
    (acc : SharedData) (block : Block) (initial : LayoutMState) :
    ((allocationBranchStep shared degrees acc block).run initial).2.callRanks = initial.callRanks :=
  blockLayout_callRanks block ((setSharedData shared).run initial).2

theorem allocationBranchFold_callRanks {α : Type} (items : List α) (blockOf : α → Block)
    (shared : SharedData) (degrees : Array Nat) (acc : SharedData) (initial : LayoutMState) :
    ((items.foldlM (fun acc item => allocationBranchStep shared degrees acc (blockOf item)) acc).run initial).2.callRanks =
      initial.callRanks := by
  induction items generalizing acc initial with
  | nil => rfl
  | cons item items ih =>
    rw [List.foldlM_cons]
    exact (ih ((allocationBranchStep shared degrees acc (blockOf item)).run initial).1
      ((allocationBranchStep shared degrees acc (blockOf item)).run initial).2).trans
      (allocationBranchStep_callRanks shared degrees acc (blockOf item) initial)

theorem allocationBranchStep_column (shared : SharedData) (degrees : Array Nat) (acc : SharedData)
    (block : Block) (initial : LayoutMState) (base column : Nat) (aligned : initial.degrees = degrees)
    (generic : initial.callRanks = #[])
    (effect : ∀ state : LayoutMState, state.callRanks = #[] → state.degrees = degrees →
      state.functionLayout.auxiliaries = shared.auxiliaries →
      column = base + ((blockLayout block).run state).2.functionLayout.auxiliaries) :
    base + ((allocationBranchStep shared degrees acc block).run initial).1.auxiliaries =
      max (base + acc.auxiliaries) column := by
  have body := effect ((setSharedData shared).run initial).2 generic aligned rfl
  change base + max acc.auxiliaries
    ((blockLayout block).run ((setSharedData shared).run initial).2).2.functionLayout.auxiliaries = _
  rw [← Nat.add_max_add_left, ← body]

theorem allocationBranchFold {α β : Type} {items : List α} {emissions : List β}
    (blockOf : α → Block) (measure : β → Nat) (shared : SharedData) (degrees : Array Nat) (base : Nat)
    (related : List.Forall₂ (fun item emission => ∀ state : LayoutMState,
      state.callRanks = #[] → state.degrees = degrees → state.functionLayout.auxiliaries = shared.auxiliaries →
      measure emission = base + ((blockLayout (blockOf item)).run state).2.functionLayout.auxiliaries)
      items emissions)
    (acc : SharedData) (initial : LayoutMState) (aligned : initial.degrees = degrees)
    (generic : initial.callRanks = #[]) :
    ((items.foldlM (fun acc item => allocationBranchStep shared degrees acc (blockOf item)) acc).run initial).2.degrees =
      degrees ∧
    base + ((items.foldlM (fun acc item => allocationBranchStep shared degrees acc (blockOf item)) acc).run initial).1.auxiliaries =
      emissions.foldl (fun current emission => max current (measure emission)) (base + acc.auxiliaries) := by
  induction related generalizing acc initial with
  | nil => exact ⟨aligned, rfl⟩
  | @cons item emission items emissions effect related ih =>
    rw [List.foldlM_cons]
    have next := ih ((allocationBranchStep shared degrees acc (blockOf item)).run initial).1
      ((allocationBranchStep shared degrees acc (blockOf item)).run initial).2
      (allocationBranchStep_degrees ..)
      ((allocationBranchStep_callRanks shared degrees acc (blockOf item) initial).trans generic)
    rw [allocationBranchStep_column shared degrees acc (blockOf item) initial base
      (measure emission) aligned generic effect] at next
    exact next

theorem allocationBranchLoop (branches : Array (G × Block)) (shared : SharedData) (degrees : Array Nat) :
    branches.attach.foldlM (fun acc pair => allocationBranchStep shared degrees acc pair.val.2) shared =
      branches.toList.foldlM (fun acc pair => allocationBranchStep shared degrees acc pair.2) shared := by
  rw [← Array.foldlM_toList, Array.toList_attach, ← List.foldlM_map,
    List.attachWith_map_val, List.foldlM_map]

theorem matchLayout_allocation {β : Type} (index : ValIdx) (branches : Array (G × Block))
    (fallback : Option Block) (initial : LayoutMState) (base : Nat) (measure : β → Nat)
    {cases defaults : List β}
    (generic : initial.callRanks = #[])
    (caseEffects : List.Forall₂ (fun pair emission => ∀ state : LayoutMState,
      state.callRanks = #[] → state.degrees = initial.degrees → state.functionLayout.auxiliaries = initial.functionLayout.auxiliaries →
      measure emission = base + ((blockLayout pair.2).run state).2.functionLayout.auxiliaries)
      branches.toList cases)
    (defaultEffects : List.Forall₂ (fun block emission => ∀ state : LayoutMState,
      state.callRanks = #[] → state.degrees = initial.degrees →
      state.functionLayout.auxiliaries = initial.functionLayout.auxiliaries + branches.size →
      measure emission = base + ((blockLayout block).run state).2.functionLayout.auxiliaries)
      fallback.toList defaults) :
    ((ctrlLayout (.match index branches fallback)).run initial).2.degrees = initial.degrees ∧
    base + ((ctrlLayout (.match index branches fallback)).run initial).2.functionLayout.auxiliaries =
      (cases ++ defaults).foldl (fun current emission => max current (measure emission))
        (base + initial.functionLayout.auxiliaries) := by
  let shared : SharedData := ⟨initial.functionLayout.auxiliaries, initial.functionLayout.lookups⟩
  let loop : LayoutM SharedData := branches.attach.foldlM
    (fun acc pair => allocationBranchStep shared initial.degrees acc pair.val.2) shared
  have loopResult : (loop.run initial).2.degrees = initial.degrees ∧
      base + (loop.run initial).1.auxiliaries =
        cases.foldl (fun current emission => max current (measure emission))
          (base + initial.functionLayout.auxiliaries) := by
    dsimp only [loop]
    rw [allocationBranchLoop]
    exact allocationBranchFold Prod.snd measure shared initial.degrees base caseEffects shared initial rfl generic
  have loopRanks : (loop.run initial).2.callRanks = #[] := by
    dsimp only [loop]
    rw [allocationBranchLoop]
    exact (allocationBranchFold_callRanks branches.toList Prod.snd shared initial.degrees shared initial).trans generic
  rw [ctrlLayout_eq_def]
  cases fallback with
  | none =>
    cases defaultEffects
    change (loop.run initial).2.degrees = initial.degrees ∧
      base + (loop.run initial).1.auxiliaries = _
    simpa only [List.append_nil] using loopResult
  | some block =>
    cases defaultEffects with
    | cons effect tail =>
      cases tail
      let before := ((bumpAuxiliaries branches.size).run
        ((setSharedData shared).run (loop.run initial).2).2).2
      have body := effect before loopRanks loopResult.1 rfl
      change initial.degrees = initial.degrees ∧
        base + max (loop.run initial).1.auxiliaries
          ((blockLayout block).run before).2.functionLayout.auxiliaries = _
      constructor
      · rfl
      · rw [← Nat.add_max_add_left, ← body, loopResult.2]
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem ctrlLayout_continue (index : ValIdx) (branches : Array (G × Block))
    (fallback : Option Block) (size aux slots : Nat) (continuation : Block) :
    ctrlLayout (.matchContinue index branches fallback size aux slots continuation) = (do
      ctrlLayout (.match index branches fallback)
      bumpAuxiliaries size
      pushDegrees (.replicate size 1)
      blockLayout continuation) := by
  exact ctrlLayout_eq_def _

end Aiur.Concrete.Bytecode
