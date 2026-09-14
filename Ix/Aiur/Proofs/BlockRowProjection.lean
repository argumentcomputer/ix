/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.BlockRows
import Batteries.Data.List.Basic

/-!
The selector and return-gate projections of the valued block emitter.
Successful emission suffices for the projection equalities; no satisfying
assignment is assumed. Its equations therefore imply the previously checked
selector-flow equations.
-/

namespace Aiur.AIR
open Bytecode

theorem mapM_forall₂ {α β : Type} {relation : α → β → Prop} {source : List α}
    {emissions : List β} {emit : α → Option β}
    (emitted : source.mapM emit = some emissions)
    (each : ∀ item ∈ source, ∀ emission, emit item = some emission → relation item emission) :
    List.Forall₂ relation source emissions := by
  induction source generalizing emissions with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at emitted
    subst emissions
    exact .nil
  | cons item items ih =>
    simp only [List.mapM_cons, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i first firstEmitted
      dsimp only at emitted
      split at emitted
      · cases emitted
      · rename_i rest restEmitted
        have equal := Option.some.inj emitted
        subst emissions
        exact .cons (each item List.mem_cons_self first firstEmitted)
          (ih restEmitted (fun item member => each item (List.mem_cons_of_mem _ member)))

theorem attachWith_mapM_val {α β : Type} (items : List α) (predicate : α → Prop)
    (holds : ∀ item ∈ items, predicate item) (emit : α → Option β) :
    (items.attachWith predicate holds).mapM (fun item => emit item.val) = items.mapM emit := by
  have result := List.mapM_map (m := Option) (l := items.attachWith predicate holds)
    (f := Subtype.val) (g := emit)
  rw [List.attachWith_map_subtype_val] at result
  exact result.symm

theorem forall₂_map_left {α β γ : Type} {relation : β → γ → Prop} {map : α → β}
    {left : List α} {right : List γ}
    (related : List.Forall₂ (fun item result => relation (map item) result) left right) :
    List.Forall₂ relation (left.map map) right := by
  induction related with
  | nil => exact .nil
  | cons first _ ih => exact .cons first ih

theorem forall₂_append {α β : Type} {relation : α → β → Prop}
    {firstLeft restLeft : List α} {firstRight restRight : List β}
    (first : List.Forall₂ relation firstLeft firstRight)
    (rest : List.Forall₂ relation restLeft restRight) :
    List.Forall₂ relation (firstLeft ++ restLeft) (firstRight ++ restRight) := by
  induction first with
  | nil => exact rest
  | cons head _ ih => exact .cons head ih

def SelectorFlow.unguard (flow : SelectorFlow) : SelectorFlow :=
  { flow with equations := flow.equations.tail }

structure EmissionProjection (flow : SelectorFlow) (gates : List G)
    (emission : BlockEmission) : Prop where
  returned : emission.returns.map Prod.fst = gates
  yielded : emission.yields.map Prod.fst = flow.yields
  equations : flow.equations ⊆ emission.equations

theorem EmissionProjection.prefix {flow : SelectorFlow} {gates : List G}
    {emission : BlockEmission} (projection : EmissionProjection flow gates emission)
    (equations : List G) : EmissionProjection flow gates (emission.prefix equations) :=
  ⟨projection.returned, projection.yielded,
    fun _ member => List.mem_append_right _ (projection.equations member)⟩

theorem EmissionProjection.join {α : Type} {source : List α} {emissions : List BlockEmission}
    (flow : α → SelectorFlow) (gates : α → List G)
    (projections : List.Forall₂ (fun item emission => EmissionProjection (flow item) (gates item) emission)
      source emissions) (values : Array RowValue) (column lookup : Nat) :
    EmissionProjection (SelectorFlow.join (source.map flow)) (source.flatMap gates)
      (joinBlockEmissions values column lookup emissions) := by
  induction projections with
  | nil => exact ⟨rfl, rfl, by simp [SelectorFlow.join]⟩
  | @cons item emission items emissions first rest ih =>
    refine ⟨?_, ?_, ?_⟩
    · change (emission.returns ++ emissions.flatMap (·.returns)).map Prod.fst =
        gates item ++ items.flatMap gates
      rw [List.map_append, first.returned]
      exact congrArg (gates item ++ ·) ih.returned
    · change (emission.yields ++ emissions.flatMap (·.yields)).map Prod.fst =
        (flow item).yields ++ (items.map flow).flatMap (·.yields)
      rw [List.map_append, first.yielded]
      exact congrArg ((flow item).yields ++ ·) ih.yielded
    · intro equation member
      change equation ∈ (flow item).equations ++ (items.map flow).flatMap (·.equations) at member
      change equation ∈ emission.equations ++ emissions.flatMap (·.equations)
      rcases List.mem_append.mp member with left | right
      · exact List.mem_append_left _ (first.equations left)
      · exact List.mem_append_right _ (ih.equations right)

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

theorem Ctrl.selectorFlow_equations (selector : SelIdx → G) (ctrl : Ctrl) :
    (ctrl.selectorFlow selector).equations =
      oneSubBooleanConstraint (ctrl.selectorFlow selector).entry ::
        (ctrl.selectorFlow selector).equations.tail := by
  cases ctrl <;> rw [Ctrl.selectorFlow.eq_def]
  all_goals rfl

def caseRow (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (matched : G) (values : Array RowValue) (column lookup : Nat) (pair : G × Block) :
    Option BlockEmission := do
  let entry := (pair.2.selectorFlow selector).entry
  let emission ← pair.2.emitRow row selector context entry values column lookup
  return emission.prefix [entry * (matched - pair.1)]

def defaultRow (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (matched : G) (values : Array RowValue) (column lookup : Nat)
    (branches : Array (G × Block)) (fallback : Option Block) : Option (List BlockEmission) :=
  match fallback with
  | none => some []
  | some block => do
    let entry := (block.selectorFlow selector).entry
    let emission ← block.emitRow row selector context entry values (column + branches.size) lookup
    return [emission.prefix (branches.toList.mapIdx fun i pair =>
      entry * ((matched - pair.1) * row (column + i) - 1))]

def branchRows (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (matched : G) (values : Array RowValue) (column lookup : Nat)
    (branches : Array (G × Block)) (fallback : Option Block) : Option BlockEmission := do
  let cases ← branches.toList.mapM (caseRow row selector context matched values column lookup)
  let default ← defaultRow row selector context matched values column lookup branches fallback
  return joinBlockEmissions values column lookup (cases ++ default)

theorem Ctrl.emitRow_match (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (incoming : G) (values : Array RowValue) (column lookup : Nat)
    (index : ValIdx) (branches : Array (G × Block)) (fallback : Option Block) :
    (Ctrl.match index branches fallback).emitRow row selector context incoming values column lookup = (do
      let matched ← values[index]?
      branchRows row selector context matched.value values column lookup branches fallback) := by
  rw [Ctrl.emitRow.eq_def]
  simp only [branchRows, Array.toList_attach]
  cases read : values[index]? with
  | none => simp only [bind, Option.bind_none]
  | some matched =>
    simp only [bind, Option.bind_some]
    rw [attachWith_mapM_val _ _ _ (fun pair : G × Block =>
      (pair.2.emitRow row selector context (pair.2.selectorFlow selector).entry values column lookup).bind
        fun emission => pure (emission.prefix
          [(pair.2.selectorFlow selector).entry * (matched.value - pair.1)]))]
    change (branches.toList.mapM (caseRow row selector context matched.value values column lookup)).bind _ = _
    congr 1
    funext cases
    cases fallback with
    | none => rfl
    | some block => simp only [defaultRow, bind, Option.bind_assoc]

def continueRow (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (incoming : G) (values : Array RowValue) (size : Nat) (continuation : Block)
    (joined : BlockEmission) : Option BlockEmission :=
  if joined.yields.all (fun part => part.2.size == size) then do
    let gate := selectorSum (joined.yields.map Prod.fst)
    let merged := rowAdvice row joined.column size
    let equations := mergeEquations row incoming joined.column size joined.yields ++
      [(continuation.selectorFlow selector).entry - gate]
    let continued ← continuation.emitRow row selector context gate (values ++ merged)
      (joined.column + size) joined.lookup
    return joined.continued equations continued
  else none

theorem Ctrl.emitRow_matchContinue (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (incoming : G) (values : Array RowValue) (column lookup : Nat)
    (index : ValIdx) (branches : Array (G × Block)) (fallback : Option Block)
    (size aux slots : Nat) (continuation : Block) :
    (Ctrl.matchContinue index branches fallback size aux slots continuation).emitRow
      row selector context incoming values column lookup = (do
        let matched ← values[index]?
        let joined ← branchRows row selector context matched.value values column lookup branches fallback
        continueRow row selector context incoming values size continuation joined) := by
  rw [Ctrl.emitRow.eq_def]
  simp only [branchRows, Array.toList_attach]
  cases read : values[index]? with
  | none => simp only [bind, Option.bind_none]
  | some matched =>
    simp only [bind, Option.bind_some]
    rw [attachWith_mapM_val _ _ _ (fun pair : G × Block =>
      (pair.2.emitRow row selector context (pair.2.selectorFlow selector).entry values column lookup).bind
        fun emission => pure (emission.prefix
          [(pair.2.selectorFlow selector).entry * (matched.value - pair.1)]))]
    simp only [Option.bind_assoc]
    change (branches.toList.mapM (caseRow row selector context matched.value values column lookup)).bind _ = _
    congr 1
    funext cases
    cases fallback <;> simp only [defaultRow, continueRow, bind, pure,
      Option.bind_assoc, Option.bind_some]

theorem caseRows_projection (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (matched : G) (values : Array RowValue) (column lookup : Nat)
    (branches : Array (G × Block)) {emissions : List BlockEmission}
    (emitted : branches.toList.mapM (caseRow row selector context matched values column lookup) = some emissions)
    (sound : ∀ pair ∈ branches.toList, ∀ emission,
      pair.2.emitRow row selector context (pair.2.selectorFlow selector).entry values column lookup = some emission →
      EmissionProjection (pair.2.selectorFlow selector)
        (pair.2.returnGates selector (pair.2.selectorFlow selector).entry) emission) :
    List.Forall₂ (fun block emission => EmissionProjection (block.selectorFlow selector)
      (block.returnGates selector (block.selectorFlow selector).entry) emission)
      (branches.toList.map Prod.snd) emissions := by
  apply forall₂_map_left
  apply mapM_forall₂ emitted
  intro pair member emission emitted
  simp only [caseRow, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  · rename_i body bodyEmitted
    have equal := Option.some.inj emitted
    subst emission
    exact (sound pair member body bodyEmitted).prefix _

theorem defaultRow_projection (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (matched : G) (values : Array RowValue) (column lookup : Nat)
    (branches : Array (G × Block)) (fallback : Option Block) {emissions : List BlockEmission}
    (emitted : defaultRow row selector context matched values column lookup branches fallback = some emissions)
    (sound : ∀ block, fallback = some block → ∀ emission,
      block.emitRow row selector context (block.selectorFlow selector).entry values
        (column + branches.size) lookup = some emission →
      EmissionProjection (block.selectorFlow selector)
        (block.returnGates selector (block.selectorFlow selector).entry) emission) :
    List.Forall₂ (fun block emission => EmissionProjection (block.selectorFlow selector)
      (block.returnGates selector (block.selectorFlow selector).entry) emission)
      fallback.toList emissions := by
  cases fallback with
  | none =>
    simp only [defaultRow, Option.some.injEq] at emitted
    subst emissions
    exact .nil
  | some block =>
    simp only [defaultRow, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i body bodyEmitted
      have equal := Option.some.inj emitted
      subst emissions
      exact .cons ((sound block rfl body bodyEmitted).prefix _) .nil

theorem branchRows_projection (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (matched : G) (values : Array RowValue) (column lookup : Nat)
    (branches : Array (G × Block)) (fallback : Option Block) {emission : BlockEmission}
    (emitted : branchRows row selector context matched values column lookup branches fallback = some emission)
    (caseSound : ∀ pair ∈ branches.toList, ∀ emission,
      pair.2.emitRow row selector context (pair.2.selectorFlow selector).entry values column lookup = some emission →
      EmissionProjection (pair.2.selectorFlow selector)
        (pair.2.returnGates selector (pair.2.selectorFlow selector).entry) emission)
    (defaultSound : ∀ block, fallback = some block → ∀ emission,
      block.emitRow row selector context (block.selectorFlow selector).entry values
        (column + branches.size) lookup = some emission →
      EmissionProjection (block.selectorFlow selector)
        (block.returnGates selector (block.selectorFlow selector).entry) emission) :
    EmissionProjection (SelectorFlow.join (branchSelectorFlows selector branches fallback))
      (branchReturnGates selector branches fallback) emission := by
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
      have casesProjection := caseRows_projection row selector context matched values column lookup branches
        casesEmitted caseSound
      have defaultProjection := defaultRow_projection row selector context matched values column lookup
        branches fallback defaultEmitted defaultSound
      have result := EmissionProjection.join
        (fun block : Block => block.selectorFlow selector)
        (fun block : Block => block.returnGates selector (block.selectorFlow selector).entry)
        (forall₂_append casesProjection defaultProjection) values column lookup
      simpa only [branchSelectorFlows, branchReturnGates, List.map_append, List.map_map,
        List.flatMap_append, List.flatMap_map, Function.comp_def] using result

private theorem block_projection_smaller (block : Block) : sizeOf block.ctrl < sizeOf block := by
  cases block
  simp
  omega

mutual

theorem Ctrl.emitRow_projection (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (incoming : G) (values : Array RowValue) (column lookup : Nat) (ctrl : Ctrl)
    {emission : BlockEmission}
    (emitted : ctrl.emitRow row selector context incoming values column lookup = some emission) :
    EmissionProjection (ctrl.selectorFlow selector).unguard
      (ctrl.returnGates selector incoming) emission := by
  cases ctrl with
  | «return» index indices =>
    rw [Ctrl.emitRow.eq_def] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · dsimp only at emitted
      split at emitted
      · cases emitted
      · have equal := Option.some.inj emitted
        subst emission
        rw [Ctrl.selectorFlow.eq_def, Ctrl.returnGates.eq_def]
        exact ⟨rfl, rfl, by simp [SelectorFlow.unguard, SelectorFlow.guard]⟩
  | yield index indices =>
    rw [Ctrl.emitRow.eq_def] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · have equal := Option.some.inj emitted
      subst emission
      rw [Ctrl.selectorFlow.eq_def, Ctrl.returnGates.eq_def]
      exact ⟨rfl, rfl, by simp [SelectorFlow.unguard, SelectorFlow.guard]⟩
  | «match» index branches fallback =>
    rw [Ctrl.emitRow_match] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i matched read
      rw [Ctrl.selectorFlow_match, Ctrl.returnGates_match]
      apply branchRows_projection row selector context matched.value values column lookup branches fallback emitted
      · intro pair member body bodyEmitted
        exact Block.emitRow_projection row selector context _ values column lookup pair.2 bodyEmitted
      · intro block present body bodyEmitted
        exact Block.emitRow_projection row selector context _ values _ lookup block bodyEmitted
  | matchContinue index branches fallback size aux slots continuation =>
    rw [Ctrl.emitRow_matchContinue] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i matched read
      dsimp only at emitted
      split at emitted
      · cases emitted
      · rename_i joined branchesEmitted
        have branchesProjection := branchRows_projection row selector context matched.value values column lookup
          branches fallback branchesEmitted
          (fun pair member body bodyEmitted =>
            Block.emitRow_projection row selector context _ values column lookup pair.2 bodyEmitted)
          (fun block present body bodyEmitted =>
            Block.emitRow_projection row selector context _ values _ lookup block bodyEmitted)
        simp only [continueRow] at emitted
        split at emitted
        · simp only [bind, Option.bind] at emitted
          split at emitted
          · cases emitted
          · rename_i continued contEmitted
            have contProjection := Block.emitRow_projection row selector context _ _ _ _ continuation contEmitted
            have gate := congrArg selectorSum branchesProjection.yielded
            have equal := Option.some.inj emitted
            subst emission
            rw [Ctrl.selectorFlow_matchContinue, Ctrl.returnGates_matchContinue]
            refine ⟨?_, contProjection.yielded, ?_⟩
            · change (joined.returns ++ continued.returns).map Prod.fst = _
              rw [List.map_append, branchesProjection.returned, contProjection.returned, gate]
            · intro equation member
              change equation ∈
                (SelectorFlow.join (branchSelectorFlows selector branches fallback)).equations ++
                  ((continuation.selectorFlow selector).entry -
                    selectorSum (SelectorFlow.join (branchSelectorFlows selector branches fallback)).yields) ::
                    (continuation.selectorFlow selector).equations at member
              change equation ∈ (joined.equations ++
                (mergeEquations row incoming joined.column size joined.yields ++
                  [(continuation.selectorFlow selector).entry - selectorSum (joined.yields.map Prod.fst)])) ++
                continued.equations
              rcases List.mem_append.mp member with branchEquation | contEquation
              · exact List.mem_append_left _ (List.mem_append_left _
                  (branchesProjection.equations branchEquation))
              · rcases List.mem_cons.mp contEquation with link | contEquation
                · rw [link, ← gate]
                  exact List.mem_append_left _ (List.mem_append_right _
                    (List.mem_append_right _ List.mem_cons_self))
                · exact List.mem_append_right _ (contProjection.equations contEquation)
        · cases emitted
termination_by sizeOf ctrl
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem (Array.mem_def.mpr ‹_ ∈ _›); grind)

theorem Block.emitRow_projection (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (incoming : G) (values : Array RowValue) (column lookup : Nat) (block : Block)
    {emission : BlockEmission}
    (emitted : block.emitRow row selector context incoming values column lookup = some emission) :
    EmissionProjection (block.selectorFlow selector)
      (block.returnGates selector incoming) emission := by
  rw [Block.emitRow] at emitted
  simp only [bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  · rename_i operations opsEmitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    · rename_i control ctrlEmitted
      have projected := Ctrl.emitRow_projection row selector context incoming _ _ _ block.ctrl ctrlEmitted
      have equal := Option.some.inj emitted
      subst emission
      rw [Block.returnGates, Block.selectorFlow]
      refine ⟨projected.returned, projected.yielded, ?_⟩
      intro equation member
      change equation ∈ oneSubBooleanConstraint (block.ctrl.selectorFlow selector).entry ::
        (operations.equations ++ control.equations)
      change equation ∈ (block.ctrl.selectorFlow selector).equations at member
      rw [Ctrl.selectorFlow_equations] at member
      rcases List.mem_cons.mp member with guard | tail
      · rw [guard]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (projected.equations tail))
termination_by sizeOf block
decreasing_by exact block_projection_smaller block

end

theorem Block.emitRow_selectors (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (incoming : G) (values : Array RowValue) (column lookup : Nat) (block : Block)
    {emission : BlockEmission}
    (emitted : block.emitRow row selector context incoming values column lookup = some emission)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0) :
    (block.selectorFlow selector).Satisfied :=
  fun equation member => satisfied equation
    ((block.emitRow_projection row selector context incoming values column lookup emitted).equations member)

end Aiur.Bytecode
