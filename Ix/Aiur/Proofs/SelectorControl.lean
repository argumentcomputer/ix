/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.SelectorMessages
import Ix.Aiur.Proofs.LookupShapes

/-!
Conservation and exclusivity for the selector portion of native control
constraints, computed over the actual bytecode tree. A continuation consumes
only its branches' escaping yields; early returns remain function returns.
The existing shape validator excludes yields escaping an entire function.

Native-expression reflection, value-index and layout correctness, branch
matching and operation extraction remain separate obligations. The terminal
count bound is explicit; this module does not assume it follows from syntax.
-/

namespace Aiur.AIR

/-- Selector-only projection of the native control emitter. `yields` lists
only yields escaping this block to its nearest enclosing continuation. -/
structure SelectorFlow where
  entry : G
  returns : List G
  yields : List G
  equations : List G
  deriving Repr

def SelectorFlow.guard (flow : SelectorFlow) : SelectorFlow :=
  { flow with equations := oneSubBooleanConstraint flow.entry :: flow.equations }

def SelectorFlow.join (flows : List SelectorFlow) : SelectorFlow :=
  ⟨selectorSum (flows.map (·.entry)), flows.flatMap (·.returns),
    flows.flatMap (·.yields), flows.flatMap (·.equations)⟩

def SelectorFlow.continue (branches continuation : SelectorFlow) : SelectorFlow :=
  ⟨branches.entry, branches.returns ++ continuation.returns, continuation.yields,
    branches.equations ++
      (continuation.entry - selectorSum branches.yields) :: continuation.equations⟩

def SelectorFlow.Satisfied (flow : SelectorFlow) : Prop :=
  ∀ equation ∈ flow.equations, equation = 0

structure SelectorFlow.Sound (flow : SelectorFlow) : Prop where
  conservation : flow.entry = selectorSum flow.returns + selectorSum flow.yields
  returned : ∀ value ∈ flow.returns, booleanConstraint value = 0
  yielded : ∀ value ∈ flow.yields, booleanConstraint value = 0

theorem SelectorFlow.guard_sound {flow : SelectorFlow} (sound : flow.Sound) : flow.guard.Sound :=
  ⟨sound.conservation, sound.returned, sound.yielded⟩

theorem SelectorFlow.guard_satisfied {flow : SelectorFlow} (valid : flow.guard.Satisfied) :
    flow.Satisfied := fun equation member => valid equation (List.mem_cons_of_mem _ member)

theorem SelectorFlow.guard_boolean {flow : SelectorFlow} (valid : flow.guard.Satisfied) :
    booleanConstraint flow.entry = 0 := by
  have boolean := G.boolean_of_one_sub_constraint (valid _ List.mem_cons_self)
  rcases boolean with zero | one
  · rw [zero]; rfl
  · rw [one]; rfl

theorem SelectorFlow.join_satisfied {flows : List SelectorFlow} (valid : (join flows).Satisfied) :
    ∀ flow ∈ flows, flow.Satisfied := by
  intro flow member equation equationMember
  exact valid equation (List.mem_flatMap.mpr ⟨flow, member, equationMember⟩)

theorem SelectorFlow.continue_satisfied {branches continuation : SelectorFlow}
    (valid : (branches.continue continuation).Satisfied) :
    branches.Satisfied ∧ continuation.Satisfied ∧
      continuation.entry = selectorSum branches.yields := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun equation member => valid _ (List.mem_append_left _ member)
  · exact fun equation member =>
      valid _ (List.mem_append_right _ (List.mem_cons_of_mem _ member))
  · exact (G.sub_eq_zero_iff _ _).mp
      (valid _ (List.mem_append_right _ List.mem_cons_self))

theorem SelectorFlow.join_sound {flows : List SelectorFlow}
    (sound : ∀ flow ∈ flows, flow.Sound) : (join flows).Sound := by
  induction flows with
  | nil => exact ⟨rfl, by simp [join], by simp [join]⟩
  | cons flow flows ih =>
    have head := sound flow List.mem_cons_self
    have tail := ih (fun flow member => sound flow (List.mem_cons_of_mem _ member))
    have tailEq := tail.conservation
    dsimp only [join] at tailEq
    refine ⟨?_, ?_, ?_⟩
    · change selectorSum (flow.entry :: flows.map (·.entry)) =
        selectorSum (flow.returns ++ flows.flatMap (·.returns)) +
        selectorSum (flow.yields ++ flows.flatMap (·.yields))
      rw [selectorSum_cons, selectorSum_append, selectorSum_append,
        head.conservation, tailEq]
      simp only [G.add_assoc]
      apply congrArg (selectorSum flow.returns + ·)
      rw [← G.add_assoc, G.add_comm (selectorSum flow.yields)
        (selectorSum (flows.flatMap (·.returns))), G.add_assoc]
    · intro value member
      change value ∈ flow.returns ++ flows.flatMap (·.returns) at member
      rcases List.mem_append.mp member with first | last
      · exact head.returned _ first
      · exact tail.returned _ last
    · intro value member
      change value ∈ flow.yields ++ flows.flatMap (·.yields) at member
      rcases List.mem_append.mp member with first | last
      · exact head.yielded _ first
      · exact tail.yielded _ last

theorem SelectorFlow.continue_sound {branches continuation : SelectorFlow}
    (first : branches.Sound) (last : continuation.Sound)
    (link : continuation.entry = selectorSum branches.yields) :
    (branches.continue continuation).Sound := by
  refine ⟨?_, ?_, last.yielded⟩
  · change branches.entry = selectorSum (branches.returns ++ continuation.returns) +
      selectorSum continuation.yields
    rw [selectorSum_append, G.add_assoc, ← last.conservation, link, ← first.conservation]
  · intro value member
    rcases List.mem_append.mp member with firstMember | lastMember
    · exact first.returned _ firstMember
    · exact last.returned _ lastMember

theorem SelectorFlow.Sound.terminal_boolean {flow : SelectorFlow} (sound : flow.Sound) :
    ∀ value ∈ flow.returns ++ flow.yields, booleanConstraint value = 0 := by
  intro value member
  rcases List.mem_append.mp member with returned | yielded
  · exact sound.returned value returned
  · exact sound.yielded value yielded

theorem SelectorFlow.Sound.active_terminal {flow : SelectorFlow} (sound : flow.Sound)
    (bounded : flow.returns.length + flow.yields.length < gSize.toNat)
    (active : flow.entry = 1) :
    ∃ before after, flow.returns ++ flow.yields = before ++ 1 :: after ∧
      ∀ value ∈ before ++ after, value = 0 := by
  apply selectorSum_active_split sound.terminal_boolean
    (by simpa only [List.length_append] using bounded)
  rw [selectorSum_append, ← sound.conservation, active]

theorem SelectorFlow.Sound.inactive_terminal {flow : SelectorFlow} (sound : flow.Sound)
    (bounded : flow.returns.length + flow.yields.length < gSize.toNat)
    (inactive : flow.entry = 0) :
    ∀ value ∈ flow.returns ++ flow.yields, value = 0 := by
  apply selectorSum_inactive sound.terminal_boolean
    (by simpa only [List.length_append] using bounded)
  rw [selectorSum_append, ← sound.conservation, inactive]

theorem SelectorFlow.Sound.return_stops_continuation {flow : SelectorFlow} (sound : flow.Sound)
    (bounded : flow.returns.length + flow.yields.length < gSize.toNat)
    (active : flow.entry = 1) (returned : (1 : G) ∈ flow.returns) :
    selectorSum flow.yields = 0 := by
  have count := selectorSum_active_count sound.terminal_boolean
    (by simpa only [List.length_append] using bounded)
    (show selectorSum (flow.returns ++ flow.yields) = 1 by
      rw [selectorSum_append, ← sound.conservation, active])
  have positive := List.count_pos_iff.mpr returned
  rw [List.count_append] at count
  have noYields : flow.yields.count 1 = 0 := by omega
  rw [selectorSum_eq_count _ (fun value member =>
    G.boolean_of_constraint (sound.yielded value member)), noYields]
  rfl

theorem SelectorFlow.Sound.yield_starts_continuation {flow : SelectorFlow} (sound : flow.Sound)
    (bounded : flow.returns.length + flow.yields.length < gSize.toNat)
    (active : flow.entry = 1) (yielded : (1 : G) ∈ flow.yields) :
    selectorSum flow.yields = 1 := by
  have count := selectorSum_active_count sound.terminal_boolean
    (by simpa only [List.length_append] using bounded)
    (show selectorSum (flow.returns ++ flow.yields) = 1 by
      rw [selectorSum_append, ← sound.conservation, active])
  have positive := List.count_pos_iff.mpr yielded
  rw [List.count_append] at count
  have oneYield : flow.yields.count 1 = 1 := by omega
  rw [selectorSum_eq_count _ (fun value member =>
    G.boolean_of_constraint (sound.yielded value member)), oneYield]
  rfl

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

private theorem selector_block_smaller (block : Block) : sizeOf block.ctrl < sizeOf block := by
  cases block
  simp
  omega

mutual

def Ctrl.selectorFlow (selector : SelIdx → G) : Ctrl → SelectorFlow
  | .return index _ => (⟨selector index, [selector index], [], []⟩ : SelectorFlow).guard
  | .yield index _ => (⟨selector index, [], [selector index], []⟩ : SelectorFlow).guard
  | .match _ branches fallback =>
    (SelectorFlow.join (
      (branches.attach.toList.map fun ⟨pair, _⟩ => pair.2.selectorFlow selector) ++
      (match fallback with | none => [] | some block => [block.selectorFlow selector]))).guard
  | .matchContinue _ branches fallback _ _ _ continuation =>
    ((SelectorFlow.join (
      (branches.attach.toList.map fun ⟨pair, _⟩ => pair.2.selectorFlow selector) ++
      (match fallback with | none => [] | some block => [block.selectorFlow selector]))).continue
        (continuation.selectorFlow selector)).guard
termination_by ctrl => sizeOf ctrl
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

def Block.selectorFlow (selector : SelIdx → G) (block : Block) : SelectorFlow :=
  block.ctrl.selectorFlow selector
termination_by sizeOf block
decreasing_by exact selector_block_smaller block

end

def branchSelectorFlows (selector : SelIdx → G) (branches : Array (G × Block))
    (fallback : Option Block) : List SelectorFlow :=
  branches.toList.map (fun pair => pair.2.selectorFlow selector) ++
    fallback.toList.map (fun block => block.selectorFlow selector)

theorem Ctrl.selectorFlow_match (selector : SelIdx → G) (index : ValIdx)
    (branches : Array (G × Block)) (fallback : Option Block) :
    (Ctrl.match index branches fallback).selectorFlow selector =
      (SelectorFlow.join (branchSelectorFlows selector branches fallback)).guard := by
  rw [Ctrl.selectorFlow.eq_def]
  simp only [branchSelectorFlows, Array.toList_attach]
  rw [List.attachWith_map_val (f := fun pair : G × Block => pair.2.selectorFlow selector)]
  cases fallback <;> rfl

theorem Ctrl.selectorFlow_matchContinue (selector : SelIdx → G) (index : ValIdx)
    (branches : Array (G × Block)) (fallback : Option Block)
    (outputs aux lookups : Nat) (continuation : Block) :
    (Ctrl.matchContinue index branches fallback outputs aux lookups continuation).selectorFlow selector =
      ((SelectorFlow.join (branchSelectorFlows selector branches fallback)).continue
        (continuation.selectorFlow selector)).guard := by
  rw [Ctrl.selectorFlow.eq_def]
  simp only [branchSelectorFlows, Array.toList_attach]
  rw [List.attachWith_map_val (f := fun pair : G × Block => pair.2.selectorFlow selector)]
  cases fallback <;> rfl

theorem branchSelectorFlows_sound (selector : SelIdx → G) (branches : Array (G × Block))
    (fallback : Option Block)
    (valid : (SelectorFlow.join (branchSelectorFlows selector branches fallback)).Satisfied)
    (casesSound : ∀ pair ∈ branches.toList,
      (pair.2.selectorFlow selector).Satisfied → (pair.2.selectorFlow selector).Sound)
    (fallbackSound : ∀ block, fallback = some block →
      (block.selectorFlow selector).Satisfied → (block.selectorFlow selector).Sound) :
    (SelectorFlow.join (branchSelectorFlows selector branches fallback)).Sound := by
  apply SelectorFlow.join_sound
  intro flow member
  have flowValid := SelectorFlow.join_satisfied valid flow member
  rcases List.mem_append.mp member with caseMember | defaultMember
  · obtain ⟨pair, pairMember, equal⟩ := List.mem_map.mp caseMember
    subst flow
    exact casesSound pair pairMember flowValid
  · obtain ⟨block, blockMember, equal⟩ := List.mem_map.mp defaultMember
    subst flow
    exact fallbackSound block (by simpa using blockMember) flowValid

mutual

theorem Ctrl.selectorFlow_sound (selector : SelIdx → G) (ctrl : Ctrl)
    (valid : (ctrl.selectorFlow selector).Satisfied) : (ctrl.selectorFlow selector).Sound := by
  cases ctrl with
  | «return» index values =>
    rw [Ctrl.selectorFlow.eq_def] at valid ⊢
    have boolean := SelectorFlow.guard_boolean valid
    exact ⟨by simp only [SelectorFlow.guard,
        selectorSum, List.foldl_nil, List.foldl_cons, G.add_zero, G.zero_add],
      fun value member => (List.mem_singleton.mp member).symm ▸ boolean,
      by simp [SelectorFlow.guard]⟩
  | yield index values =>
    rw [Ctrl.selectorFlow.eq_def] at valid ⊢
    have boolean := SelectorFlow.guard_boolean valid
    exact ⟨by simp only [SelectorFlow.guard,
        selectorSum, List.foldl_nil, List.foldl_cons, G.zero_add],
      by simp [SelectorFlow.guard],
      fun value member => (List.mem_singleton.mp member).symm ▸ boolean⟩
  | «match» index branches fallback =>
    rw [Ctrl.selectorFlow_match] at valid ⊢
    apply SelectorFlow.guard_sound
    apply branchSelectorFlows_sound selector branches fallback (SelectorFlow.guard_satisfied valid)
    · intro pair member satisfied
      exact Block.selectorFlow_sound selector pair.2 satisfied
    · intro block present satisfied
      exact Block.selectorFlow_sound selector block satisfied
  | matchContinue index branches fallback outputs aux lookups continuation =>
    rw [Ctrl.selectorFlow_matchContinue] at valid ⊢
    obtain ⟨branchesValid, continuationValid, link⟩ :=
      SelectorFlow.continue_satisfied (SelectorFlow.guard_satisfied valid)
    apply SelectorFlow.guard_sound
    apply SelectorFlow.continue_sound _ (Block.selectorFlow_sound selector continuation continuationValid) link
    apply branchSelectorFlows_sound selector branches fallback branchesValid
    · intro pair member satisfied
      exact Block.selectorFlow_sound selector pair.2 satisfied
    · intro block present satisfied
      exact Block.selectorFlow_sound selector block satisfied
termination_by sizeOf ctrl
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem (Array.mem_def.mpr ‹_ ∈ _›); grind)

theorem Block.selectorFlow_sound (selector : SelIdx → G) (block : Block)
    (valid : (block.selectorFlow selector).Satisfied) : (block.selectorFlow selector).Sound := by
  rw [Block.selectorFlow] at valid ⊢
  exact Ctrl.selectorFlow_sound selector block.ctrl valid
termination_by sizeOf block
decreasing_by exact selector_block_smaller block

end

mutual

theorem Ctrl.selectorFlow_yields_empty (selector : SelIdx → G) (ctrl : Ctrl)
    (program : Toplevel) (valid : ctrl.lookupShapes program none = true) :
    (ctrl.selectorFlow selector).yields = [] := by
  cases ctrl with
  | «return» index values => rw [Ctrl.selectorFlow.eq_def]; rfl
  | yield index values => simp only [Ctrl.lookupShapes, reduceCtorEq, beq_iff_eq] at valid
  | «match» index branches fallback =>
    obtain ⟨casesValid, fallbackValid⟩ := (lookupShapes_match _ _ _ _ _).mp valid
    rw [Ctrl.selectorFlow_match]
    change (branchSelectorFlows selector branches fallback).flatMap (·.yields) = []
    apply List.flatMap_eq_nil_iff.mpr
    intro flow member
    rcases List.mem_append.mp member with caseMember | defaultMember
    · obtain ⟨pair, pairMember, equal⟩ := List.mem_map.mp caseMember
      subst flow
      exact Block.selectorFlow_yields_empty selector pair.2 program (casesValid pair pairMember)
    · obtain ⟨block, blockMember, equal⟩ := List.mem_map.mp defaultMember
      subst flow
      have present : fallback = some block := by simpa using blockMember
      exact Block.selectorFlow_yields_empty selector block program (fallbackValid block present)
  | matchContinue index branches fallback outputs aux lookups continuation =>
    obtain ⟨_, _, contValid⟩ := (lookupShapes_matchContinue _ _ _ _ _ _ _ _ _).mp valid
    rw [Ctrl.selectorFlow_matchContinue]
    exact Block.selectorFlow_yields_empty selector continuation program contValid
termination_by sizeOf ctrl
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem (Array.mem_def.mpr pairMember); grind)

theorem Block.selectorFlow_yields_empty (selector : SelIdx → G) (block : Block)
    (program : Toplevel) (valid : block.lookupShapes program none = true) :
    (block.selectorFlow selector).yields = [] := by
  rw [Block.selectorFlow]
  rw [Block.lookupShapes, Bool.and_eq_true] at valid
  exact Ctrl.selectorFlow_yields_empty selector block.ctrl program valid.2
termination_by sizeOf block
decreasing_by exact selector_block_smaller block

end

theorem Block.selectorFlow_active_return (selector : SelIdx → G) (block : Block)
    (program : Toplevel) (shape : block.lookupShapes program none = true)
    (valid : (block.selectorFlow selector).Satisfied)
    (bounded : (block.selectorFlow selector).returns.length < gSize.toNat)
    (active : (block.selectorFlow selector).entry = 1) :
    ∃ before after, (block.selectorFlow selector).returns = before ++ 1 :: after ∧
      ∀ value ∈ before ++ after, value = 0 := by
  have empty := block.selectorFlow_yields_empty selector program shape
  have sound := block.selectorFlow_sound selector valid
  have result := sound.active_terminal (by simpa only [empty, List.length_nil, Nat.add_zero] using bounded) active
  simpa only [empty, List.append_nil] using result

theorem Block.selectorFlow_provider_return (selector : SelIdx → G) (block : Block)
    (program : Toplevel) (shape : block.lookupShapes program none = true)
    (valid : (block.selectorFlow selector).Satisfied)
    (bounded : (block.selectorFlow selector).returns.length < gSize.toNat)
    (multiplicity : G) (nonzero : multiplicity ≠ 0)
    (activity : activityConstraint multiplicity (block.selectorFlow selector).entry = 0) :
    ∃ before after, (block.selectorFlow selector).returns = before ++ 1 :: after ∧
      ∀ value ∈ before ++ after, value = 0 :=
  block.selectorFlow_active_return selector program shape valid bounded
    (nonzero_multiplicity_selector_one activity nonzero)

end Aiur.Bytecode
