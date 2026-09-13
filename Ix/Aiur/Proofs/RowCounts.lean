/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.RowCounts
import Ix.Aiur.Proofs.CircuitRowExecution

/-! Control counts bound the selector flow of every field assignment.
The node count also bounds all branch arities and nested continuation joins.
Consumed yields contribute to the leaf count even after leaving the flow. -/

namespace Aiur.Bytecode
open Aiur.AIR

structure ControlCounts.Describes (counts : ControlCounts) (flow : SelectorFlow) : Prop where
  returned : flow.returns.length = counts.returns
  yielded : flow.yields.length = counts.yields
  terminals : counts.returns + counts.yields ≤ counts.leaves
  leaves : counts.leaves ≤ counts.nodes

theorem ControlCounts.Describes.unguard {counts : ControlCounts} {flow : SelectorFlow}
    (describes : counts.Describes flow.guard) : counts.Describes flow :=
  ⟨describes.returned, describes.yielded, describes.terminals, describes.leaves⟩

theorem ControlCounts.sum_describes {counts : List ControlCounts} {flows : List SelectorFlow}
    (related : List.Forall₂ Describes counts flows) :
    (sum counts).Describes (SelectorFlow.join flows) := by
  induction related with
  | nil => exact ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
  | @cons first firstFlow rest restFlows head tail ih =>
    obtain ⟨hr, hy, ht, hl⟩ := head
    obtain ⟨tr, ty, tt, tl⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      dsimp only [sum, SelectorFlow.join] at * <;>
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append] at * <;> omega

theorem ControlCounts.branch_describes {counts : List ControlCounts} {flows : List SelectorFlow}
    (related : List.Forall₂ Describes counts flows) :
    (branch counts).Describes (SelectorFlow.join flows).guard := by
  obtain ⟨returned, yielded, terminals, leaves⟩ := sum_describes related
  exact ⟨returned, yielded, terminals, by change (sum counts).leaves ≤ (sum counts).nodes + 1; omega⟩

theorem ControlCounts.continue_describes {branches continuation : ControlCounts}
    {branchFlow contFlow : SelectorFlow} (first : branches.Describes branchFlow)
    (last : continuation.Describes contFlow) :
    (branches.continue continuation).Describes (branchFlow.continue contFlow).guard := by
  obtain ⟨fr, fy, ft, fl⟩ := first
  obtain ⟨lr, ly, lt, ll⟩ := last
  refine ⟨?_, ly, ?_, ?_⟩
  · change (branchFlow.returns ++ contFlow.returns).length = _
    rw [List.length_append, fr, lr]
    rfl
  · change branches.returns + continuation.returns + continuation.yields ≤ branches.leaves + continuation.leaves
    omega
  · change branches.leaves + continuation.leaves ≤ branches.nodes + continuation.nodes
    omega

theorem ControlCounts.member_nodes_le {items : List ControlCounts} {item : ControlCounts}
    (member : item ∈ items) : item.nodes ≤ (sum items).nodes := by
  induction items with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with equal | member
    · subst item
      change first.nodes ≤ first.nodes + (sum rest).nodes
      omega
    · have bounded := ih member
      change item.nodes ≤ first.nodes + (sum rest).nodes
      omega

theorem ControlCounts.length_le_nodes {items : List ControlCounts}
    (positive : ∀ item ∈ items, 0 < item.nodes) : items.length ≤ (sum items).nodes := by
  induction items with
  | nil => exact Nat.le_refl _
  | cons first rest ih =>
    have head := positive first List.mem_cons_self
    have tail := ih (fun item member => positive item (List.mem_cons_of_mem _ member))
    change rest.length + 1 ≤ first.nodes + (sum rest).nodes
    omega

theorem branchControlCounts_all {branches : Array (G × Block)} {fallback : Option Block}
    (property : ControlCounts → Prop)
    (casesValid : ∀ pair ∈ branches.toList, property pair.2.controlCounts)
    (fallbackValid : ∀ block, fallback = some block → property block.controlCounts) :
    ∀ counts ∈ branchControlCounts branches fallback, property counts := by
  intro counts member
  rcases List.mem_append.mp member with first | last
  · obtain ⟨pair, pairMember, equal⟩ := List.mem_map.mp first
    subst counts
    exact casesValid pair pairMember
  · obtain ⟨block, blockMember, equal⟩ := List.mem_map.mp last
    subst counts
    exact fallbackValid block (by simpa using blockMember)

theorem branchControlCounts_describes (selector : SelIdx → G)
    (branches : Array (G × Block)) (fallback : Option Block)
    (casesValid : ∀ pair ∈ branches.toList, pair.2.controlCounts.Describes (pair.2.selectorFlow selector))
    (fallbackValid : ∀ block, fallback = some block →
      block.controlCounts.Describes (block.selectorFlow selector)) :
    List.Forall₂ ControlCounts.Describes (branchControlCounts branches fallback)
      (branchSelectorFlows selector branches fallback) := by
  apply forall₂_append
  · apply forall₂_map_left
    exact forall₂_self_map _ _ _ casesValid
  · apply forall₂_map_left
    apply forall₂_self_map
    intro block member
    exact fallbackValid block (by simpa using member)

theorem branchControlCounts_case_le (branches : Array (G × Block)) (fallback : Option Block)
    {pair : G × Block} (member : pair ∈ branches.toList) :
    pair.2.controlCounts.nodes ≤ (ControlCounts.sum (branchControlCounts branches fallback)).nodes :=
  ControlCounts.member_nodes_le (List.mem_append_left _ (List.mem_map.mpr ⟨pair, member, rfl⟩))

theorem branchControlCounts_default_le (branches : Array (G × Block)) (fallback : Option Block)
    {block : Block} (present : fallback = some block) :
    block.controlCounts.nodes ≤ (ControlCounts.sum (branchControlCounts branches fallback)).nodes := by
  apply ControlCounts.member_nodes_le
  apply List.mem_append_right
  rw [present]
  exact List.mem_cons_self

private theorem counts_spec_block_smaller (block : Block) : sizeOf block.ctrl < sizeOf block := by
  cases block
  simp
  omega

mutual

theorem Ctrl.controlCounts_spec (selector : SelIdx → G) (ctrl : Ctrl) :
    ctrl.controlCounts.Describes (ctrl.selectorFlow selector) ∧
      0 < ctrl.controlCounts.nodes ∧
      (ctrl.controlCounts.nodes < gSize.toNat → ctrl.rowBounds selector) := by
  cases ctrl with
  | «return» index values =>
    rw [Ctrl.controlCounts.eq_def, Ctrl.selectorFlow.eq_def, Ctrl.rowBounds.eq_def]
    exact ⟨⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩, Nat.zero_lt_succ 0, fun _ => True.intro⟩
  | yield index values =>
    rw [Ctrl.controlCounts.eq_def, Ctrl.selectorFlow.eq_def, Ctrl.rowBounds.eq_def]
    exact ⟨⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩, Nat.zero_lt_succ 0, fun _ => True.intro⟩
  | «match» index branches fallback =>
    have casesSpec := fun pair (_ : pair ∈ branches.toList) => Block.controlCounts_spec selector pair.2
    have defaultSpec := fun block (_ : fallback = some block) => Block.controlCounts_spec selector block
    have related := branchControlCounts_describes selector branches fallback
      (fun pair member => (casesSpec pair member).1) (fun block present => (defaultSpec block present).1)
    have positive := branchControlCounts_all (fun counts => 0 < counts.nodes)
      (fun pair member => (casesSpec pair member).2.1) (fun block present => (defaultSpec block present).2.1)
    have arity : branches.size + fallback.toList.length ≤
        (ControlCounts.sum (branchControlCounts branches fallback)).nodes := by
      simpa only [branchControlCounts, List.length_append, List.length_map, Array.length_toList]
        using ControlCounts.length_le_nodes positive
    rw [Ctrl.controlCounts_match, Ctrl.selectorFlow_match, Ctrl.rowBounds.eq_def]
    refine ⟨ControlCounts.branch_describes related, by change 0 < _ + 1; omega, ?_⟩
    intro bounded
    change (ControlCounts.sum (branchControlCounts branches fallback)).nodes + 1 < gSize.toNat at bounded
    refine ⟨?_, ?_, ?_⟩
    · omega
    · intro pair member
      apply (casesSpec pair member).2.2
      have le := branchControlCounts_case_le branches fallback member
      omega
    · cases fallback with
      | none => exact True.intro
      | some block =>
        apply (defaultSpec block rfl).2.2
        have le := branchControlCounts_default_le branches (some block) rfl
        omega
  | matchContinue index branches fallback outputs aux lookups continuation =>
    have casesSpec := fun pair (_ : pair ∈ branches.toList) => Block.controlCounts_spec selector pair.2
    have defaultSpec := fun block (_ : fallback = some block) => Block.controlCounts_spec selector block
    have continued := Block.controlCounts_spec selector continuation
    have related := branchControlCounts_describes selector branches fallback
      (fun pair member => (casesSpec pair member).1) (fun block present => (defaultSpec block present).1)
    have positive := branchControlCounts_all (fun counts => 0 < counts.nodes)
      (fun pair member => (casesSpec pair member).2.1) (fun block present => (defaultSpec block present).2.1)
    have arity : branches.size + fallback.toList.length ≤
        (ControlCounts.sum (branchControlCounts branches fallback)).nodes := by
      simpa only [branchControlCounts, List.length_append, List.length_map, Array.length_toList]
        using ControlCounts.length_le_nodes positive
    rw [Ctrl.controlCounts_matchContinue, Ctrl.selectorFlow_matchContinue, Ctrl.rowBounds.eq_def]
    refine ⟨ControlCounts.continue_describes (ControlCounts.branch_describes related).unguard continued.1,
      by change 0 < _ + 1 + _; omega, ?_⟩
    intro bounded
    change (ControlCounts.sum (branchControlCounts branches fallback)).nodes + 1 +
      continuation.controlCounts.nodes < gSize.toNat at bounded
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · omega
    · obtain ⟨returned, yielded, terminals, leaves⟩ := ControlCounts.sum_describes related
      rw [returned, yielded]
      omega
    · intro pair member
      apply (casesSpec pair member).2.2
      have le := branchControlCounts_case_le branches fallback member
      omega
    · cases fallback with
      | none => exact True.intro
      | some block =>
        apply (defaultSpec block rfl).2.2
        have le := branchControlCounts_default_le branches (some block) rfl
        omega
    · apply continued.2.2
      omega
termination_by sizeOf ctrl
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem (Array.mem_def.mpr ‹_ ∈ _›); grind)

theorem Block.controlCounts_spec (selector : SelIdx → G) (block : Block) :
    block.controlCounts.Describes (block.selectorFlow selector) ∧
      0 < block.controlCounts.nodes ∧
      (block.controlCounts.nodes < gSize.toNat → block.rowBounds selector) := by
  rw [Block.controlCounts, Block.selectorFlow, Block.rowBounds]
  exact Ctrl.controlCounts_spec selector block.ctrl
termination_by sizeOf block
decreasing_by exact counts_spec_block_smaller block

end

theorem Block.rowBounds_of_controlCounts (selector : SelIdx → G) (block : Block)
    (bounded : block.controlCounts.nodes < gSize.toNat) : block.rowBounds selector :=
  (block.controlCounts_spec selector).2.2 bounded

theorem Block.return_bound_of_controlCounts (selector : SelIdx → G) (block : Block)
    (bounded : block.controlCounts.nodes < gSize.toNat) :
    (block.selectorFlow selector).returns.length < gSize.toNat := by
  obtain ⟨returned, _, terminals, leaves⟩ := (block.controlCounts_spec selector).1
  omega

theorem Block.returns_le_selectors (selector : SelIdx → G) (block : Block) :
    (block.selectorFlow selector).returns.length ≤ block.controlCounts.leaves := by
  obtain ⟨returned, _, terminals, _⟩ := (block.controlCounts_spec selector).1
  omega

end Aiur.Bytecode
