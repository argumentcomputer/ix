/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.SelectorControl

/-!
The emitter gates a continuation with its yield sum. Its continuation-link
equation identifies that sum with the continuation block's selector. These
definitions retain the distinction on arbitrary field assignments and prove
that satisfying selector equations identify all return gates with their leaf
selectors. A nonzero provider's combined message then recovers one return.

Reflection of native argument values and layout remains an obligation. The
branchless single-writer property and terminal-count bound are explicit.
-/

namespace Aiur.Bytecode
open Aiur.AIR

private theorem return_gate_block_smaller (block : Block) : sizeOf block.ctrl < sizeOf block := by
  cases block
  simp
  omega

mutual

/-- Return arguments are gated by the selector passed to the emitter. At a
continuation this is the yield sum, equal to the block selector only when
the emitted continuation-link equation is satisfied. -/
def Ctrl.returnGates (selector : SelIdx → G) (incoming : G) : Ctrl → List G
  | .return .. => [incoming]
  | .yield .. => []
  | .match _ branches fallback =>
    (branches.attach.toList.flatMap fun ⟨pair, _⟩ =>
      pair.2.returnGates selector (pair.2.selectorFlow selector).entry) ++
      (match fallback with
      | none => []
      | some block => block.returnGates selector (block.selectorFlow selector).entry)
  | .matchContinue _ branches fallback _ _ _ continuation =>
    (branches.attach.toList.flatMap fun ⟨pair, _⟩ =>
      pair.2.returnGates selector (pair.2.selectorFlow selector).entry) ++
      (match fallback with
      | none => []
      | some block => block.returnGates selector (block.selectorFlow selector).entry) ++
      continuation.returnGates selector
        (selectorSum (SelectorFlow.join (branchSelectorFlows selector branches fallback)).yields)
termination_by ctrl => sizeOf ctrl
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

def Block.returnGates (selector : SelIdx → G) (incoming : G) (block : Block) : List G :=
  block.ctrl.returnGates selector incoming
termination_by sizeOf block
decreasing_by exact return_gate_block_smaller block

end

def branchReturnGates (selector : SelIdx → G) (branches : Array (G × Block))
    (fallback : Option Block) : List G :=
  branches.toList.flatMap (fun pair => pair.2.returnGates selector (pair.2.selectorFlow selector).entry) ++
    fallback.toList.flatMap (fun block => block.returnGates selector (block.selectorFlow selector).entry)

private theorem flatMap_attachWith_val {α β : Type} (items : List α) (p : α → Prop)
    (h : ∀ item ∈ items, p item) (f : α → List β) :
    (items.attachWith p h).flatMap (fun item => f item.val) = items.flatMap f := by
  rw [List.flatMap, List.flatMap, List.attachWith_map_val]

theorem Ctrl.returnGates_match (selector : SelIdx → G) (incoming : G) (index : ValIdx)
    (branches : Array (G × Block)) (fallback : Option Block) :
    (Ctrl.match index branches fallback).returnGates selector incoming =
      branchReturnGates selector branches fallback := by
  rw [Ctrl.returnGates.eq_def]
  simp only [branchReturnGates, Array.toList_attach]
  rw [flatMap_attachWith_val _ _ _ (fun pair : G × Block =>
    pair.2.returnGates selector (pair.2.selectorFlow selector).entry)]
  cases fallback <;> simp

theorem Ctrl.returnGates_matchContinue (selector : SelIdx → G) (incoming : G) (index : ValIdx)
    (branches : Array (G × Block)) (fallback : Option Block)
    (outputs aux lookups : Nat) (continuation : Block) :
    (Ctrl.matchContinue index branches fallback outputs aux lookups continuation).returnGates selector incoming =
      branchReturnGates selector branches fallback ++ continuation.returnGates selector
        (selectorSum (SelectorFlow.join (branchSelectorFlows selector branches fallback)).yields) := by
  rw [Ctrl.returnGates.eq_def]
  simp only [branchReturnGates, Array.toList_attach]
  rw [flatMap_attachWith_val _ _ _ (fun pair : G × Block =>
    pair.2.returnGates selector (pair.2.selectorFlow selector).entry)]
  cases fallback <;> simp

private theorem flatMap_congr_mem {α β : Type} (items : List α) (left right : α → List β)
    (equal : ∀ item ∈ items, left item = right item) : items.flatMap left = items.flatMap right := by
  rw [List.flatMap, List.flatMap]
  exact congrArg List.flatten (List.map_congr_left equal)

theorem branchReturnGates_reflects (selector : SelIdx → G) (branches : Array (G × Block))
    (fallback : Option Block)
    (casesEqual : ∀ pair ∈ branches.toList,
      pair.2.returnGates selector (pair.2.selectorFlow selector).entry =
        (pair.2.selectorFlow selector).returns)
    (fallbackEqual : ∀ block, fallback = some block →
      block.returnGates selector (block.selectorFlow selector).entry =
        (block.selectorFlow selector).returns) :
    branchReturnGates selector branches fallback =
      (SelectorFlow.join (branchSelectorFlows selector branches fallback)).returns := by
  simp only [branchReturnGates, branchSelectorFlows, SelectorFlow.join,
    List.flatMap_append, List.flatMap_map]
  congr 1
  · exact flatMap_congr_mem _ _ _ casesEqual
  · apply flatMap_congr_mem
    intro block member
    exact fallbackEqual block (by simpa using member)

theorem branchSelectorFlows_satisfied (selector : SelIdx → G) (branches : Array (G × Block))
    (fallback : Option Block)
    (valid : (SelectorFlow.join (branchSelectorFlows selector branches fallback)).Satisfied) :
    (∀ pair ∈ branches.toList, (pair.2.selectorFlow selector).Satisfied) ∧
      (∀ block, fallback = some block → (block.selectorFlow selector).Satisfied) := by
  refine ⟨?_, ?_⟩
  · intro pair member
    apply SelectorFlow.join_satisfied valid
    exact List.mem_append_left _ (List.mem_map.mpr ⟨pair, member, rfl⟩)
  · intro block present
    apply SelectorFlow.join_satisfied valid
    apply List.mem_append_right
    rw [present]
    exact List.mem_cons_self

mutual

theorem Ctrl.returnGates_reflects (selector : SelIdx → G) (incoming : G) (ctrl : Ctrl)
    (valid : (ctrl.selectorFlow selector).Satisfied)
    (linked : incoming = (ctrl.selectorFlow selector).entry) :
    ctrl.returnGates selector incoming = (ctrl.selectorFlow selector).returns := by
  cases ctrl with
  | «return» index values =>
    rw [Ctrl.returnGates.eq_def, linked, Ctrl.selectorFlow.eq_def]
    rfl
  | yield index values => rw [Ctrl.returnGates.eq_def, Ctrl.selectorFlow.eq_def]; rfl
  | «match» index branches fallback =>
    rw [Ctrl.selectorFlow_match] at valid ⊢
    rw [Ctrl.returnGates_match]
    obtain ⟨casesValid, fallbackValid⟩ :=
      branchSelectorFlows_satisfied selector branches fallback (SelectorFlow.guard_satisfied valid)
    apply branchReturnGates_reflects
    · intro pair member
      exact Block.returnGates_reflects selector _ pair.2 (casesValid pair member) rfl
    · intro block present
      exact Block.returnGates_reflects selector _ block (fallbackValid block present) rfl
  | matchContinue index branches fallback outputs aux lookups continuation =>
    rw [Ctrl.selectorFlow_matchContinue] at valid ⊢
    rw [Ctrl.returnGates_matchContinue]
    obtain ⟨branchesValid, contValid, link⟩ :=
      SelectorFlow.continue_satisfied (SelectorFlow.guard_satisfied valid)
    obtain ⟨casesValid, fallbackValid⟩ := branchSelectorFlows_satisfied selector branches fallback branchesValid
    change _ ++ _ = _ ++ _
    congr 1
    · apply branchReturnGates_reflects
      · intro pair member
        exact Block.returnGates_reflects selector _ pair.2 (casesValid pair member) rfl
      · intro block present
        exact Block.returnGates_reflects selector _ block (fallbackValid block present) rfl
    · exact Block.returnGates_reflects selector _ continuation contValid link.symm
termination_by sizeOf ctrl
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem (Array.mem_def.mpr member); grind)

theorem Block.returnGates_reflects (selector : SelIdx → G) (incoming : G) (block : Block)
    (valid : (block.selectorFlow selector).Satisfied)
    (linked : incoming = (block.selectorFlow selector).entry) :
    block.returnGates selector incoming = (block.selectorFlow selector).returns := by
  rw [Block.returnGates, Block.selectorFlow] at *
  exact Ctrl.returnGates_reflects selector incoming block.ctrl valid linked
termination_by sizeOf block
decreasing_by exact return_gate_block_smaller block

end

theorem Block.return_message (selector : SelIdx → G) (block : Block) (program : Toplevel)
    (shape : block.lookupShapes program none = true)
    (valid : (block.selectorFlow selector).Satisfied)
    (bounded : (block.selectorFlow selector).returns.length < gSize.toNat)
    (multiplicity : G) (nonzero : multiplicity ≠ 0)
    (activity : activityConstraint multiplicity (block.selectorFlow selector).entry = 0)
    (width : Nat) (branchless : Bool) (parts : List (G × List G))
    (gates : parts.map Prod.fst = block.returnGates selector (block.selectorFlow selector).entry)
    (single : branchless = true → parts.length = 1) :
    ∃ chosen ∈ parts, chosen.1 = 1 ∧
      padMessage width (slotMessage branchless parts) = padMessage width chosen.2 := by
  have reflected := block.returnGates_reflects selector _ valid rfl
  rw [reflected] at gates
  have empty := block.selectorFlow_yields_empty selector program shape
  have conservation := (block.selectorFlow_sound selector valid).conservation
  have active := nonzero_multiplicity_selector_one activity nonzero
  rw [empty] at conservation
  change _ = selectorSum (block.selectorFlow selector).returns + 0 at conservation
  rw [G.add_zero, active] at conservation
  apply slotMessage_active width branchless single
  · intro part member
    apply (block.selectorFlow_sound selector valid).returned part.1
    rw [← gates]
    exact List.mem_map.mpr ⟨part, member, rfl⟩
  · have lengths := congrArg List.length gates
    simp only [List.length_map] at lengths
    omega
  · rw [gates]
    exact conservation.symm

end Aiur.Bytecode
