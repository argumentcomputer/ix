/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.QuerySlots

/-!
The valued block emitter respects lookup-slot intervals and has at most
one active query in each slot. Branch exclusivity follows from the emitted
selector equations; continuations resume after the maximum branch cursor.
An inactive parent also disables its continuation under the terminal bound.

Only the selector equations and explicit syntax count bounds are needed.
Native expression/layout reflection remains separate.
-/

namespace Aiur.AIR

theorem selectorSum_all_zero {gates : List G} (zero : ∀ gate ∈ gates, gate = 0) :
    selectorSum gates = 0 := by
  induction gates with
  | nil => rfl
  | cons gate gates ih =>
    rw [selectorSum_cons, zero gate List.mem_cons_self, G.zero_add]
    exact ih (fun gate member => zero gate (List.mem_cons_of_mem _ member))

theorem SelectorFlow.Sound.yield_gateCount {flow : SelectorFlow} (sound : flow.Sound)
    (bounded : flow.returns.length + flow.yields.length < gSize.toNat)
    (boolean : booleanConstraint flow.entry = 0) :
    gateCount (selectorSum flow.yields) ≤ gateCount flow.entry := by
  rcases G.boolean_of_constraint boolean with inactive | active
  · have zero := sound.inactive_terminal bounded inactive
    have yieldsZero := selectorSum_all_zero (fun gate member => zero gate (List.mem_append_right _ member))
    rw [inactive, yieldsZero]
    exact Nat.le_refl _
  · rw [active]
    exact gateCount_le_one _

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

theorem branchSelectorFlows_case_satisfied {selector : SelIdx → G}
    {branches : Array (G × Block)} {fallback : Option Block}
    (valid : (SelectorFlow.join (branchSelectorFlows selector branches fallback)).Satisfied)
    {pair : G × Block} (member : pair ∈ branches.toList) :
    (pair.2.selectorFlow selector).Satisfied :=
  SelectorFlow.join_satisfied valid _ (List.mem_append_left _ (List.mem_map.mpr ⟨pair, member, rfl⟩))

theorem branchSelectorFlows_default_satisfied {selector : SelIdx → G}
    {branches : Array (G × Block)} {fallback : Option Block}
    (valid : (SelectorFlow.join (branchSelectorFlows selector branches fallback)).Satisfied)
    {block : Block} (present : fallback = some block) : (block.selectorFlow selector).Satisfied := by
  apply SelectorFlow.join_satisfied valid _
  apply List.mem_append_right
  rw [present]
  exact List.mem_cons_self

theorem branchRows_querySlots (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (matched : G) (values : Array RowValue) (column lookup : Nat)
    (branches : Array (G × Block)) (fallback : Option Block) {emission : BlockEmission}
    (emitted : branchRows row selector context matched values column lookup branches fallback = some emission)
    (valid : (SelectorFlow.join (branchSelectorFlows selector branches fallback)).Satisfied)
    (bounded : branches.size + fallback.toList.length < gSize.toNat)
    (boolean : booleanConstraint (SelectorFlow.join (branchSelectorFlows selector branches fallback)).entry = 0)
    (caseSound : ∀ pair ∈ branches.toList, ∀ emission,
      pair.2.emitRow row selector context (pair.2.selectorFlow selector).entry values column lookup = some emission →
      QuerySlots (pair.2.selectorFlow selector).entry lookup emission.lookup emission.queries)
    (defaultSound : ∀ block, fallback = some block → ∀ emission,
      block.emitRow row selector context (block.selectorFlow selector).entry values
        (column + branches.size) lookup = some emission →
      QuerySlots (block.selectorFlow selector).entry lookup emission.lookup emission.queries) :
    QuerySlots (SelectorFlow.join (branchSelectorFlows selector branches fallback)).entry
      lookup emission.lookup emission.queries := by
  simp only [branchRows, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  · rename_i cases casesEmitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    · rename_i default defaultEmitted
      have equal := Option.some.inj emitted
      subst emission
      have casesRelated : List.Forall₂ (fun block emission =>
          QuerySlots (block.selectorFlow selector).entry lookup emission.lookup emission.queries)
          (branches.toList.map Prod.snd) cases := by
        apply forall₂_map_left
        apply mapM_forall₂ casesEmitted
        intro pair member emission emitted
        simp only [caseRow, bind, Option.bind] at emitted
        split at emitted
        · cases emitted
        · rename_i body bodyEmitted
          have equal := Option.some.inj emitted
          subst emission
          exact caseSound pair member body bodyEmitted
      have defaultRelated : List.Forall₂ (fun block emission =>
          QuerySlots (block.selectorFlow selector).entry lookup emission.lookup emission.queries)
          fallback.toList default := by
        cases fallback with
        | none =>
          have equal := Option.some.inj defaultEmitted
          subst default
          exact .nil
        | some block =>
          simp only [defaultRow, bind, Option.bind] at defaultEmitted
          split at defaultEmitted
          · cases defaultEmitted
          · rename_i body bodyEmitted
            have equal := Option.some.inj defaultEmitted
            subst default
            exact .cons (defaultSound block rfl body bodyEmitted) .nil
      have individual := branchSelectorFlows_boolean selector branches fallback valid
      have count := selector_gateCount
        (gates := (branchSelectorFlows selector branches fallback).map SelectorFlow.entry)
        (fun gate member => by
          obtain ⟨flow, flowMember, equal⟩ := List.mem_map.mp member
          subst gate
          exact individual flow flowMember)
        (by simpa only [branchSelectorFlows, List.length_map, List.length_append, Array.length_toList] using bounded)
        boolean
      apply QuerySlots.join (fun block : Block => (block.selectorFlow selector).entry)
        _ values column lookup (forall₂_append casesRelated defaultRelated)
      apply Nat.le_of_eq
      simpa only [SelectorFlow.join, branchSelectorFlows, List.map_append, List.map_map, Function.comp_def] using count

private theorem block_query_smaller (block : Block) : sizeOf block.ctrl < sizeOf block := by
  cases block
  simp
  omega

private theorem block_query_pair_smaller (pair : G × Block) : sizeOf pair.2 < sizeOf pair := by
  cases pair
  simp
  omega

private theorem block_query_option_smaller {block : Block} {fallback : Option Block}
    (present : fallback = some block) : sizeOf block < sizeOf fallback := by
  rw [present]
  simp

mutual

theorem Ctrl.emitRow_querySlots (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (incoming : G) (values : Array RowValue) (column lookup : Nat) (ctrl : Ctrl)
    (bounds : ctrl.rowBounds selector) {emission : BlockEmission}
    (emitted : ctrl.emitRow row selector context incoming values column lookup = some emission)
    (linked : incoming = (ctrl.selectorFlow selector).entry)
    (valid : (ctrl.selectorFlow selector).Satisfied) :
    QuerySlots incoming lookup emission.lookup emission.queries := by
  cases ctrlEq : ctrl with
  | «return» index indices =>
    rw [ctrlEq] at bounds emitted linked valid
    rw [Ctrl.emitRow.eq_def] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · dsimp only at emitted
      split at emitted
      · cases emitted
      · have equal := Option.some.inj emitted
        subst emission
        exact QuerySlots.empty incoming lookup
  | yield index indices =>
    rw [ctrlEq] at bounds emitted linked valid
    rw [Ctrl.emitRow.eq_def] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · have equal := Option.some.inj emitted
      subst emission
      exact QuerySlots.empty incoming lookup
  | «match» index branches fallback =>
    rw [ctrlEq] at bounds emitted linked valid
    have boolean := (Ctrl.match index branches fallback).selectorFlow_boolean selector valid
    rw [Ctrl.emitRow_match] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i matched read
      rw [Ctrl.rowBounds.eq_def] at bounds
      obtain ⟨branchBound, casesBounded, fallbackBounded⟩ := bounds
      rw [Ctrl.selectorFlow_match] at valid boolean linked
      have joinedValid := SelectorFlow.guard_satisfied valid
      rw [linked]
      apply branchRows_querySlots row selector context matched.value values column lookup branches fallback
        emitted joinedValid branchBound boolean
      · intro pair member body bodyEmitted
        exact Block.emitRow_querySlots row selector context _ values column lookup pair.2
          (casesBounded pair member) bodyEmitted rfl (branchSelectorFlows_case_satisfied joinedValid member)
      · intro block present body bodyEmitted
        have bounded : block.rowBounds selector := by rw [present] at fallbackBounded; exact fallbackBounded
        exact Block.emitRow_querySlots row selector context _ values _ lookup block bounded bodyEmitted rfl
          (branchSelectorFlows_default_satisfied joinedValid present)
  | matchContinue index branches fallback size aux slots continuation =>
    rw [ctrlEq] at bounds emitted linked valid
    have boolean := (Ctrl.matchContinue index branches fallback size aux slots continuation).selectorFlow_boolean selector valid
    rw [Ctrl.emitRow_matchContinue] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i matched read
      dsimp only at emitted
      split at emitted
      · cases emitted
      · rename_i joined branchesEmitted
        simp only [continueRow] at emitted
        split at emitted
        · simp only [bind, Option.bind] at emitted
          split at emitted
          · cases emitted
          · rename_i continued contEmitted
            have equal := Option.some.inj emitted
            subst emission
            rw [Ctrl.rowBounds.eq_def] at bounds
            obtain ⟨branchBound, terminalBound, casesBounded, fallbackBounded, contBounded⟩ := bounds
            rw [Ctrl.selectorFlow_matchContinue] at valid boolean linked
            obtain ⟨joinedValid, contValid, link⟩ :=
              SelectorFlow.continue_satisfied (SelectorFlow.guard_satisfied valid)
            have joinedSlots := branchRows_querySlots row selector context matched.value values column lookup
              branches fallback branchesEmitted joinedValid branchBound boolean
              (fun pair member body bodyEmitted =>
                Block.emitRow_querySlots row selector context _ values column lookup pair.2
                  (casesBounded pair member) bodyEmitted rfl (branchSelectorFlows_case_satisfied joinedValid member))
              (fun block present body bodyEmitted =>
                Block.emitRow_querySlots row selector context _ values _ lookup block
                  (by rw [present] at fallbackBounded; exact fallbackBounded) bodyEmitted rfl
                  (branchSelectorFlows_default_satisfied joinedValid present))
            have projected := branchRows_selector_projection row selector context matched.value values column lookup
              branches fallback branchesEmitted
            have contLinked : selectorSum (joined.yields.map Prod.fst) =
                (continuation.selectorFlow selector).entry := by
              rw [projected.yielded]
              exact link.symm
            have continuedSlots := Block.emitRow_querySlots row selector context _ _ _ _ continuation
              contBounded contEmitted contLinked contValid
            have joinedSound := branchSelectorFlows_sound selector branches fallback joinedValid
              (fun pair _ valid => pair.2.selectorFlow_sound selector valid)
              (fun block _ valid => block.selectorFlow_sound selector valid)
            have countBound := joinedSound.yield_gateCount terminalBound boolean
            rw [← projected.yielded] at countBound
            rw [linked]
            exact joinedSlots.append (continuedSlots.weaken countBound)
        · cases emitted
termination_by sizeOf ctrl
decreasing_by
  all_goals
    try rw [ctrlEq]
    first
    | (have bound := Array.sizeOf_lt_of_mem (Array.mem_def.mpr member)
       have pairBound := block_query_pair_smaller pair
       first | simp only [Ctrl.match.sizeOf_spec] | simp only [Ctrl.matchContinue.sizeOf_spec]
       omega)
    | (have optionBound := block_query_option_smaller present
       first | simp only [Ctrl.match.sizeOf_spec] | simp only [Ctrl.matchContinue.sizeOf_spec]
       omega)
    | (simp only [Ctrl.matchContinue.sizeOf_spec]; omega)

theorem Block.emitRow_querySlots (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (incoming : G) (values : Array RowValue) (column lookup : Nat) (block : Block)
    (bounds : block.rowBounds selector) {emission : BlockEmission}
    (emitted : block.emitRow row selector context incoming values column lookup = some emission)
    (linked : incoming = (block.selectorFlow selector).entry)
    (valid : (block.selectorFlow selector).Satisfied) :
    QuerySlots incoming lookup emission.lookup emission.queries := by
  rw [Block.rowBounds] at bounds
  have boolean : booleanConstraint incoming = 0 := by
    rw [linked]
    exact block.selectorFlow_boolean selector valid
  rw [Block.selectorFlow] at linked valid
  rw [Block.emitRow] at emitted
  simp only [bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  · rename_i operations opsEmitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    · rename_i control ctrlEmitted
      have controlSlots := Ctrl.emitRow_querySlots row selector context incoming _ _ _ block.ctrl
        bounds ctrlEmitted linked valid
      have equal := Option.some.inj emitted
      subst emission
      exact (QuerySlots.indexed incoming lookup operations.queries boolean).append controlSlots
termination_by sizeOf block
decreasing_by exact block_query_smaller block

end

theorem Block.emitRow_equation_querySlots (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (incoming : G) (values : Array RowValue) (column lookup : Nat) (block : Block)
    (bounds : block.rowBounds selector) {emission : BlockEmission}
    (emitted : block.emitRow row selector context incoming values column lookup = some emission)
    (linked : incoming = (block.selectorFlow selector).entry)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0) :
    QuerySlots incoming lookup emission.lookup emission.queries :=
  block.emitRow_querySlots row selector context incoming values column lookup bounds emitted linked
    (block.emitRow_selectors row selector context incoming values column lookup emitted satisfied)

end Aiur.Bytecode
