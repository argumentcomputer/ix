/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ReturnGates

/-! Active case/default polynomial equations recover a branch of the actual
bytecode and its selector constraints. The branch-count bound and decoding
of the matched expression and default inverse columns remain explicit. -/

namespace Aiur.Bytecode
open Aiur.AIR

theorem Ctrl.selectorFlow_boolean (selector : SelIdx → G) (ctrl : Ctrl)
    (valid : (ctrl.selectorFlow selector).Satisfied) :
    booleanConstraint (ctrl.selectorFlow selector).entry = 0 := by
  cases ctrl <;> rw [Ctrl.selectorFlow.eq_def] at valid ⊢
  all_goals
    have boolean := SelectorFlow.guard_boolean valid
    exact boolean

theorem Block.selectorFlow_boolean (selector : SelIdx → G) (block : Block)
    (valid : (block.selectorFlow selector).Satisfied) :
    booleanConstraint (block.selectorFlow selector).entry = 0 := by
  rw [Block.selectorFlow] at valid ⊢
  exact Ctrl.selectorFlow_boolean selector block.ctrl valid

/-- Case and default polynomial forms after reading the matched expression.
Default inverse advice is arbitrary; its equation establishes disequality. -/
structure MatchPolynomials (selector : SelIdx → G) (scrutinee : G)
    (branches : Array (G × Block)) (fallback : Option Block) : Prop where
  cases : ∀ pair ∈ branches.toList,
    (pair.2.selectorFlow selector).entry * (scrutinee - pair.1) = 0
  default : ∀ block, fallback = some block → ∀ pair ∈ branches.toList,
    ∃ inverse : G,
      (block.selectorFlow selector).entry * ((scrutinee - pair.1) * inverse - 1) = 0

theorem branchSelectorFlows_boolean (selector : SelIdx → G) (branches : Array (G × Block))
    (fallback : Option Block)
    (valid : (SelectorFlow.join (branchSelectorFlows selector branches fallback)).Satisfied) :
    ∀ flow ∈ branchSelectorFlows selector branches fallback, booleanConstraint flow.entry = 0 := by
  intro flow member
  have satisfied := SelectorFlow.join_satisfied valid flow member
  rcases List.mem_append.mp member with caseMember | defaultMember
  · obtain ⟨pair, pairMember, equal⟩ := List.mem_map.mp caseMember
    subst flow
    exact pair.2.selectorFlow_boolean selector satisfied
  · obtain ⟨block, blockMember, equal⟩ := List.mem_map.mp defaultMember
    subst flow
    exact block.selectorFlow_boolean selector satisfied

/-- An active sum selects a branch that matches the scrutinee, with its own
selector equations available for recursive local execution extraction. -/
theorem MatchPolynomials.active_branch {selector : SelIdx → G} {scrutinee : G}
    {branches : Array (G × Block)} {fallback : Option Block}
    (polynomials : MatchPolynomials selector scrutinee branches fallback)
    (valid : (SelectorFlow.join (branchSelectorFlows selector branches fallback)).Satisfied)
    (bounded : branches.size + fallback.toList.length < gSize.toNat)
    (active : (SelectorFlow.join (branchSelectorFlows selector branches fallback)).entry = 1) :
    ∃ block, AIR.SelectArm scrutinee branches fallback block ∧
      (block.selectorFlow selector).Satisfied ∧ (block.selectorFlow selector).entry = 1 := by
  have individual := branchSelectorFlows_boolean selector branches fallback valid
  change selectorSum ((branchSelectorFlows selector branches fallback).map SelectorFlow.entry) = 1 at active
  have count := selectorSum_active_count
    (selectors := (branchSelectorFlows selector branches fallback).map SelectorFlow.entry)
    (fun value member => by
      obtain ⟨flow, flowMember, equal⟩ := List.mem_map.mp member
      subst value
      exact individual flow flowMember)
    (by simpa only [List.length_map, branchSelectorFlows, List.length_append,
      Array.length_toList] using bounded) active
  have oneMember : (1 : G) ∈ (branchSelectorFlows selector branches fallback).map SelectorFlow.entry :=
    List.count_pos_iff.mp (Nat.lt_of_lt_of_eq (by decide : 0 < 1) count.symm)
  obtain ⟨flow, flowMember, selected⟩ := List.mem_map.mp oneMember
  have satisfied := SelectorFlow.join_satisfied valid flow flowMember
  rcases List.mem_append.mp flowMember with caseMember | defaultMember
  · obtain ⟨pair, pairMember, equal⟩ := List.mem_map.mp caseMember
    subst flow
    refine ⟨pair.2, ?_, satisfied, selected⟩
    apply AIR.SelectArm.case
    have matchesEq := active_case selected (polynomials.cases pair pairMember)
    rw [matchesEq]
    exact pairMember
  · obtain ⟨block, blockMember, equal⟩ := List.mem_map.mp defaultMember
    subst flow
    have present : fallback = some block := by simpa using blockMember
    refine ⟨block, AIR.SelectArm.fallback present ?_, satisfied, selected⟩
    intro pair pairMember
    obtain ⟨inverse, equation⟩ := polynomials.default block present pair pairMember
    exact (active_default selected equation).symm

theorem MatchPolynomials.active_match {selector : SelIdx → G} {scrutinee : G}
    {index : ValIdx} {branches : Array (G × Block)} {fallback : Option Block}
    (polynomials : MatchPolynomials selector scrutinee branches fallback)
    (valid : ((Ctrl.match index branches fallback).selectorFlow selector).Satisfied)
    (bounded : branches.size + fallback.toList.length < gSize.toNat)
    (active : ((Ctrl.match index branches fallback).selectorFlow selector).entry = 1) :
    ∃ block, AIR.SelectArm scrutinee branches fallback block ∧
      (block.selectorFlow selector).Satisfied ∧ (block.selectorFlow selector).entry = 1 := by
  rw [Ctrl.selectorFlow_match] at valid active
  exact polynomials.active_branch (SelectorFlow.guard_satisfied valid) bounded active

theorem MatchPolynomials.active_matchContinue {selector : SelIdx → G} {scrutinee : G}
    {index : ValIdx} {branches : Array (G × Block)} {fallback : Option Block}
    {outputs aux lookups : Nat} {continuation : Block}
    (polynomials : MatchPolynomials selector scrutinee branches fallback)
    (valid : ((Ctrl.matchContinue index branches fallback outputs aux lookups continuation).selectorFlow selector).Satisfied)
    (bounded : branches.size + fallback.toList.length < gSize.toNat)
    (active : ((Ctrl.matchContinue index branches fallback outputs aux lookups continuation).selectorFlow selector).entry = 1) :
    ∃ block, AIR.SelectArm scrutinee branches fallback block ∧
      (block.selectorFlow selector).Satisfied ∧ (block.selectorFlow selector).entry = 1 := by
  rw [Ctrl.selectorFlow_matchContinue] at valid active
  exact polynomials.active_branch
    (SelectorFlow.continue_satisfied (SelectorFlow.guard_satisfied valid)).1 bounded active

end Aiur.Bytecode
