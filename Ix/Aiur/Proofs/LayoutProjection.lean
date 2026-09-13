/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.LayoutState

/-! The state projection of the actual layout pass. Constructing revised
continuations preserves the same degree, column, selector and lookup state
as folding just those state effects. -/

namespace Aiur.Concrete.Bytecode
open Aiur.Bytecode

theorem blockLayout_eq_discard_relayout (block : Block) :
    blockLayout block = discard (relayoutBlock block) := by
  funext initial
  rw [relayoutBlock.eq_def]
  rfl

private theorem fold_project {α β γ σ : Type} (items : List α)
    (step : β → α → StateM σ β) (summary : γ → α → StateM σ γ)
    (project : β → γ)
    (effect : ∀ acc item state,
      (project ((step acc item).run state).1, ((step acc item).run state).2) =
        (summary (project acc) item).run state)
    (acc : β) (initial : σ) :
    (project ((items.foldlM step acc).run initial).1, ((items.foldlM step acc).run initial).2) =
      (items.foldlM summary (project acc)).run initial := by
  induction items generalizing acc initial with
  | nil => rfl
  | cons item items ih =>
    simp only [List.foldlM_cons]
    change (project ((items.foldlM step ((step acc item).run initial).1).run
        ((step acc item).run initial).2).1,
      ((items.foldlM step ((step acc item).run initial).1).run
        ((step acc item).run initial).2).2) =
      (items.foldlM summary ((summary (project acc) item).run initial).1).run
        ((summary (project acc) item).run initial).2
    rw [← effect acc item initial]
    exact ih _ _

private def fullStep (shared : SharedData) (degrees : Array Nat)
    (acc : Array (G × Block) × SharedData) (pair : G × Block) :
    LayoutM (Array (G × Block) × SharedData) := do
  setSharedData shared
  let body ← relayoutBlock pair.2
  let used ← getSharedData
  setDegrees degrees
  return (acc.1.push (pair.1, body), acc.2.maximals used)

private def summaryStep (shared : SharedData) (degrees : Array Nat)
    (acc : SharedData) (pair : G × Block) : LayoutM SharedData := do
  setSharedData shared
  blockLayout pair.2
  let used ← getSharedData
  setDegrees degrees
  return acc.maximals used

private theorem branch_projection (branches : Array (G × Block))
    (shared : SharedData) (degrees : Array Nat) (initial : LayoutMState) :
    let full := (branches.attach.foldlM
      (fun acc pair => fullStep shared degrees acc pair.val) (#[], shared)).run initial
    (full.1.2, full.2) = (branches.attach.foldlM
      (fun acc pair => summaryStep shared degrees acc pair.val) shared).run initial := by
  simp only
  rw [← Array.foldlM_toList, ← Array.foldlM_toList]
  apply fold_project (project := Prod.snd)
  intro acc pair state
  simp only [summaryStep, fullStep, blockLayout_eq_discard_relayout]
  rfl

private theorem fullFold_size {α : Type} (items : List α) (pairOf : α → G × Block)
    (shared : SharedData) (degrees : Array Nat)
    (acc : Array (G × Block) × SharedData) (initial : LayoutMState) :
    ((items.foldlM (fun acc item => fullStep shared degrees acc (pairOf item)) acc).run initial).1.1.size =
      acc.1.size + items.length := by
  induction items generalizing acc initial with
  | nil => simp only [List.foldlM_nil, List.length_nil, Nat.add_zero]; rfl
  | cons item items ih =>
    rw [List.foldlM_cons]
    have rest := ih ((fullStep shared degrees acc (pairOf item)).run initial).1
      ((fullStep shared degrees acc (pairOf item)).run initial).2
    change ((items.foldlM (fun acc item => fullStep shared degrees acc (pairOf item))
      ((fullStep shared degrees acc (pairOf item)).run initial).1).run
      ((fullStep shared degrees acc (pairOf item)).run initial).2).1.1.size = _
    rw [rest]
    change (acc.1.push _).size + items.length = _
    simp only [Array.size_push, List.length_cons]
    omega

private theorem branch_size (branches : Array (G × Block))
    (shared : SharedData) (degrees : Array Nat) (initial : LayoutMState) :
    ((branches.attach.foldlM (fun acc pair => fullStep shared degrees acc pair.val)
      (#[], shared)).run initial).1.1.size = branches.size := by
  rw [← Array.foldlM_toList]
  simpa only [Array.size_empty, Nat.zero_add, Array.length_toList, Array.size_attach] using
    fullFold_size branches.attach.toList Subtype.val shared degrees (#[], shared) initial

theorem ctrlLayout_eq_def (ctrl : Ctrl) : ctrlLayout ctrl = (match ctrl with
  | .match _ branches fallback => do
    let shared ← getSharedData
    let degrees ← getDegrees
    let maximal ← branches.attach.foldlM
      (fun acc pair => summaryStep shared degrees acc pair.val) shared
    let final ← match fallback with
      | none => pure maximal
      | some block => do
        setSharedData shared
        bumpAuxiliaries branches.size
        blockLayout block
        let used ← getSharedData
        setDegrees degrees
        pure (maximal.maximals used)
    setSharedData final
  | .return .. | .yield .. => bumpSelectors
  | .matchContinue index branches fallback outputs _ _ cont => do
    ctrlLayout (.match index branches fallback)
    bumpAuxiliaries outputs
    pushDegrees (.replicate outputs 1)
    blockLayout cont) := by
  cases ctrl with
  | «return» sel outs => funext initial; rw [ctrlLayout, relayoutCtrl.eq_def]; rfl
  | «yield» sel outs => funext initial; rw [ctrlLayout, relayoutCtrl.eq_def]; rfl
  | «match» index branches fallback =>
    funext initial
    let shared : SharedData := ⟨initial.functionLayout.auxiliaries, initial.functionLayout.lookups⟩
    let full := branches.attach.foldlM
      (fun acc pair => fullStep shared initial.degrees acc pair.val) (#[], shared)
    let summary := branches.attach.foldlM
      (fun acc pair => summaryStep shared initial.degrees acc pair.val) shared
    have projected := branch_projection branches shared initial.degrees initial
    have sized := branch_size branches shared initial.degrees initial
    have valueEq : (full.run initial).1.2 = (summary.run initial).1 := congrArg Prod.fst projected
    have stateEq : (full.run initial).2 = (summary.run initial).2 := congrArg Prod.snd projected
    rw [ctrlLayout, relayoutCtrl.eq_def]
    cases fallback with
    | none =>
      change (setSharedData (full.run initial).1.2).run (full.run initial).2 =
        (setSharedData (summary.run initial).1).run (summary.run initial).2
      rw [valueEq, stateEq]
    | some block =>
      simp only [blockLayout_eq_discard_relayout]
      change (do
        setSharedData shared
        bumpAuxiliaries (full.run initial).1.1.size
        discard (relayoutBlock block)
        let used ← getSharedData
        setDegrees initial.degrees
        setSharedData ((full.run initial).1.2.maximals used)).run (full.run initial).2 =
        (do
        setSharedData shared
        bumpAuxiliaries branches.size
        discard (relayoutBlock block)
        let used ← getSharedData
        setDegrees initial.degrees
        setSharedData ((summary.run initial).1.maximals used)).run (summary.run initial).2
      rw [valueEq, stateEq, sized]
  | matchContinue index branches fallback outputs aux slots cont =>
    funext initial
    rw [ctrlLayout, relayoutCtrl.eq_def]
    simp only [ctrlLayout, relayoutCtrl.eq_def, blockLayout_eq_discard_relayout]
    cases fallback <;> rfl

end Aiur.Concrete.Bytecode
