/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.BlockDegrees
import Ix.Aiur.Proofs.EmissionAllocation
import Ix.Aiur.Proofs.CompilerBranches

/-! Recursive block emission has the logical degree map and physical column
cursor calculated by the actual compiler layout pass. -/

namespace Aiur.NativeAIR.BlockEmitter
open OpEmitter Aiur.Bytecode Concrete.Bytecode

theorem branchRows_layout {selectors : Array Expr} {context : Context} {matched : RowExpr}
    {rows : Array RowExpr} {column lookup : Nat} {branches : Array (G × Block)}
    {fallback : Option Block} {emission : Emission} (index : Nat) (initial : LayoutMState) (base : Nat)
    (generic : initial.callRanks = context.callRanks)
    (aligned : rowDegrees rows = initial.degrees) (cursor : column = base + initial.functionLayout.auxiliaries)
    (emitted : branchRows selectors context matched rows column lookup branches fallback = some emission)
    (caseSound : ∀ pair ∈ branches.toList, ∀ entry result state,
      state.callRanks = context.callRanks → rowDegrees rows = state.degrees → column = base + state.functionLayout.auxiliaries →
      emitBlock selectors context entry rows column lookup pair.2 = some result →
      result.column = base + ((blockLayout pair.2).run state).2.functionLayout.auxiliaries)
    (defaultSound : ∀ block, fallback = some block → ∀ entry result state,
      state.callRanks = context.callRanks → rowDegrees rows = state.degrees → column + branches.size = base + state.functionLayout.auxiliaries →
      emitBlock selectors context entry rows (column + branches.size) lookup block = some result →
      result.column = base + ((blockLayout block).run state).2.functionLayout.auxiliaries) :
    ((ctrlLayout (.match index branches fallback)).run initial).2.degrees = rowDegrees emission.values ∧
    emission.column = base + ((ctrlLayout (.match index branches fallback)).run initial).2.functionLayout.auxiliaries := by
  simp only [branchRows, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  rename_i cases casesEmitted
  dsimp only at emitted
  split at emitted
  · cases emitted
  rename_i defaults defaultsEmitted
  cases emitted
  have caseEffects : List.Forall₂ (fun pair result => ∀ state : LayoutMState,
      state.callRanks = context.callRanks → state.degrees = initial.degrees → state.functionLayout.auxiliaries = initial.functionLayout.auxiliaries →
      result.column = base + ((blockLayout pair.2).run state).2.functionLayout.auxiliaries)
      branches.toList cases := by
    apply AIR.mapM_forall₂ casesEmitted
    intro pair member result resultEmitted
    simp only [caseRow, bind, Option.bind] at resultEmitted
    split at resultEmitted
    · cases resultEmitted
    rename_i entry entryRead
    dsimp only at resultEmitted
    split at resultEmitted
    · cases resultEmitted
    rename_i body bodyEmitted
    cases resultEmitted
    intro state stateGeneric degrees auxiliaries
    exact caseSound pair member entry body state stateGeneric (aligned.trans degrees.symm)
      (by rw [auxiliaries]; exact cursor) bodyEmitted
  have defaultEffects : List.Forall₂ (fun block result => ∀ state : LayoutMState,
      state.callRanks = context.callRanks → state.degrees = initial.degrees →
      state.functionLayout.auxiliaries = initial.functionLayout.auxiliaries + branches.size →
      result.column = base + ((blockLayout block).run state).2.functionLayout.auxiliaries)
      fallback.toList defaults := by
    cases present : fallback with
    | none =>
      simp only [defaultRow, present, Option.some.injEq] at defaultsEmitted
      subst defaults
      exact .nil
    | some block =>
      simp only [defaultRow, present, bind, Option.bind] at defaultsEmitted
      split at defaultsEmitted
      · cases defaultsEmitted
      rename_i entry entryRead
      dsimp only at defaultsEmitted
      split at defaultsEmitted
      · cases defaultsEmitted
      rename_i body bodyEmitted
      cases defaultsEmitted
      refine .cons ?_ .nil
      intro state stateGeneric degrees auxiliaries
      exact defaultSound block present entry body state stateGeneric (aligned.trans degrees.symm)
        (by rw [cursor, auxiliaries, Nat.add_assoc]) bodyEmitted
  have layout := matchLayout_allocation index branches fallback initial base Emission.column generic caseEffects defaultEffects
  rw [← cursor] at layout
  exact ⟨layout.1.trans aligned.symm, layout.2.symm⟩

private theorem case_allocation_smaller {branches : Array (G × Block)} {pair : G × Block}
    (member : pair ∈ branches.toList) : sizeOf pair.2 < sizeOf branches := by
  have bound := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp member)
  cases pair
  simp at bound ⊢
  omega

private theorem default_allocation_smaller {fallback : Option Block} {block : Block}
    (present : fallback = some block) : sizeOf block < sizeOf fallback := by
  rw [present]
  simp

mutual

theorem emitCtrl_layout {selectors : Array Expr} {context : Context} {incoming : Expr}
    {rows : Array RowExpr} {column lookup : Nat} (ctrl : Ctrl) {emission : Emission}
    (initial : LayoutMState) (base : Nat) (valid : DegreeValid rows)
    (generic : initial.callRanks = context.callRanks)
    (aligned : rowDegrees rows = initial.degrees) (cursor : column = base + initial.functionLayout.auxiliaries)
    (emitted : emitCtrl selectors context incoming rows column lookup ctrl = some emission) :
    ((ctrlLayout ctrl).run initial).2.degrees = rowDegrees emission.values ∧
    emission.column = base + ((ctrlLayout ctrl).run initial).2.functionLayout.auxiliaries := by
  cases ctrl with
  | «return» index indices | yield index indices =>
    simp only [emitCtrl, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    cases emitted
    rw [ctrlLayout_eq_def]
    exact ⟨aligned.symm, cursor⟩
  | «match» index branches fallback =>
    rw [emitCtrl_match] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    dsimp only at emitted
    apply branchRows_layout index initial base generic aligned cursor emitted
    · intro pair member entry result state stateGeneric degrees column emitted
      exact (emitBlock_layout pair.2 state base valid stateGeneric degrees column emitted).2
    · intro block present entry result state stateGeneric degrees column emitted
      exact (emitBlock_layout block state base valid stateGeneric degrees column emitted).2
  | matchContinue index branches fallback size aux slots continuation =>
    rw [emitCtrl_matchContinue] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i joined joinedEmitted
    have joinedLayout := branchRows_layout index initial base generic aligned cursor joinedEmitted
      (fun pair member entry result state stateGeneric degrees column emitted =>
        (emitBlock_layout pair.2 state base valid stateGeneric degrees column emitted).2)
      (fun block present entry result state stateGeneric degrees column emitted =>
        (emitBlock_layout block state base valid stateGeneric degrees column emitted).2)
    rw [branchRows_values joinedEmitted] at joinedLayout
    simp only [continueRow] at emitted
    split at emitted
    · simp only [bind, Option.bind] at emitted
      split at emitted
      · cases emitted
      dsimp only at emitted
      split at emitted
      · cases emitted
      rename_i continued continuedEmitted
      cases emitted
      let before := ((pushDegrees (.replicate size 1)).run
        ((bumpAuxiliaries size).run ((ctrlLayout (.match index branches fallback)).run initial).2).2).2
      have beforeDegrees : rowDegrees (rows ++ advice joined.column size) = before.degrees := by
        change _ = ((ctrlLayout (.match index branches fallback)).run initial).2.degrees ++ .replicate size 1
        rw [rowDegrees_append, advice_degrees, joinedLayout.1]
      have beforeColumn : joined.column + size = base + before.functionLayout.auxiliaries := by
        change _ = base + (((ctrlLayout (.match index branches fallback)).run initial).2.functionLayout.auxiliaries + size)
        rw [joinedLayout.2, Nat.add_assoc]
      have result := emitBlock_layout continuation before base (valid.append (advice_degreeValid _ _))
        ((ctrlLayout_callRanks (.match index branches fallback) initial).trans generic)
        beforeDegrees beforeColumn continuedEmitted
      rw [ctrlLayout_continue]
      exact result
    · cases emitted
termination_by sizeOf ctrl
decreasing_by
  all_goals subst ctrl
  all_goals first
    | (have bound := case_allocation_smaller ‹_ ∈ _›; simp; omega)
    | (have bound := default_allocation_smaller ‹_ = some _›; simp; omega)
    | decreasing_tactic

theorem emitBlock_layout {selectors : Array Expr} {context : Context} {incoming : Expr}
    {rows : Array RowExpr} {column lookup : Nat} (block : Block) {emission : Emission}
    (initial : LayoutMState) (base : Nat) (valid : DegreeValid rows)
    (generic : initial.callRanks = context.callRanks)
    (aligned : rowDegrees rows = initial.degrees) (cursor : column = base + initial.functionLayout.auxiliaries)
    (emitted : emitBlock selectors context incoming rows column lookup block = some emission) :
    ((blockLayout block).run initial).2.degrees = rowDegrees emission.values ∧
    emission.column = base + ((blockLayout block).run initial).2.functionLayout.auxiliaries := by
  simp only [emitBlock, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  dsimp only at emitted
  split at emitted
  · cases emitted
  rename_i operations operationsEmitted
  dsimp only at emitted
  split at emitted
  · cases emitted
  rename_i control controlEmitted
  cases emitted
  have operationsLayout := emitOps_layout initial base generic valid aligned cursor operationsEmitted
  have result := emitCtrl_layout block.ctrl ((block.ops.forM opLayout).run initial).2 base
    (emitOps_degreeValid valid operationsEmitted)
    ((congrArg Prod.snd (opsLayout_context block.ops initial)).trans generic)
    operationsLayout.1.symm operationsLayout.2 controlEmitted
  rw [blockLayout]
  exact result
termination_by sizeOf block
decreasing_by cases block; simp; omega

end

end Aiur.NativeAIR.BlockEmitter
