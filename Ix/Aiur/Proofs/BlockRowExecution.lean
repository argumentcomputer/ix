/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.BlockRowProjection

/-!
Execution extraction from the valued block emitter, covering operations,
case and default selection, early returns, and continuation merges. The
proof follows the actual emitted equations and logical value map.

Active raw queries must belong to the global lookup pool, and the explicit
branch and terminal counts must fit the field characteristic. Deriving
these premises from shared slots and validated native layouts is separate.
-/

namespace Aiur.AIR
open Bytecode

theorem selector_pair_split {α : Type} {parts : List (G × α)}
    (individual : ∀ part ∈ parts, booleanConstraint part.1 = 0)
    (bounded : parts.length < gSize.toNat)
    (active : selectorSum (parts.map Prod.fst) = 1) :
    ∃ before chosen after, parts = before ++ chosen :: after ∧ chosen.1 = 1 ∧
      ∀ part ∈ before ++ after, part.1 = 0 := by
  obtain ⟨before, after, split, zero⟩ := selectorSum_active_split
    (fun value member => by
      obtain ⟨part, partMember, equal⟩ := List.mem_map.mp member
      subst value
      exact individual part partMember)
    (by simpa only [List.length_map] using bounded) active
  obtain ⟨first, rest, partsEq, firstEq, restEq⟩ := List.map_eq_append_iff.mp split
  obtain ⟨chosen, last, tailEq, activeChosen, lastEq⟩ := List.map_eq_cons_iff.mp restEq
  refine ⟨first, chosen, last, by rw [partsEq, tailEq], activeChosen, ?_⟩
  intro part member
  apply zero part.1
  rcases List.mem_append.mp member with firstMember | lastMember
  · apply List.mem_append_left
    rw [← firstEq]
    exact List.mem_map.mpr ⟨part, firstMember, rfl⟩
  · apply List.mem_append_right
    rw [← lastEq]
    exact List.mem_map.mpr ⟨part, lastMember, rfl⟩

theorem selector_pair_chosen {α : Type} {parts : List (G × α)}
    (individual : ∀ part ∈ parts, booleanConstraint part.1 = 0)
    (bounded : parts.length < gSize.toNat)
    (active : selectorSum (parts.map Prod.fst) = 1)
    {chosen : G × α} (member : chosen ∈ parts) (selected : chosen.1 = 1) :
    ∃ before after, parts = before ++ chosen :: after ∧
      ∀ part ∈ before ++ after, part.1 = 0 := by
  obtain ⟨before, other, after, equal, _, zero⟩ := selector_pair_split individual bounded active
  rw [equal] at member
  rcases List.mem_append.mp member with left | tail
  · have inactive := zero chosen (List.mem_append_left _ left)
    exact False.elim (G.one_ne_zero (selected.symm.trans inactive))
  · rcases List.mem_cons.mp tail with same | right
    · subst chosen
      exact ⟨before, after, equal, zero⟩
    · have inactive := zero chosen (List.mem_append_right _ right)
      exact False.elim (G.one_ne_zero (selected.symm.trans inactive))

theorem selector_weighted_zero {α : Type} (read : α → G) {parts : List (G × α)}
    (zero : ∀ part ∈ parts, part.1 = 0) :
    selectorSum (parts.map fun part => part.1 * read part.2) = 0 := by
  induction parts with
  | nil => rfl
  | cons part parts ih =>
    rw [List.map_cons, selectorSum_cons, zero part List.mem_cons_self,
      G.mul_comm 0, G.mul_zero, G.zero_add]
    exact ih (fun part member => zero part (List.mem_cons_of_mem _ member))

theorem selector_weighted_chosen {α : Type} (read : α → G) {parts : List (G × α)}
    (individual : ∀ part ∈ parts, booleanConstraint part.1 = 0)
    (bounded : parts.length < gSize.toNat)
    (active : selectorSum (parts.map Prod.fst) = 1)
    {chosen : G × α} (member : chosen ∈ parts) (selected : chosen.1 = 1) :
    selectorSum (parts.map fun part => part.1 * read part.2) = read chosen.2 := by
  obtain ⟨before, after, equal, zero⟩ := selector_pair_chosen individual bounded active member selected
  rw [equal, List.map_append, selectorSum_append,
    selector_weighted_zero read (fun part member => zero part (List.mem_append_left _ member)),
    G.zero_add, List.map_cons, selectorSum_cons,
    selector_weighted_zero read (fun part member => zero part (List.mem_append_right _ member)),
    G.add_zero, selected, G.mul_comm, G.mul_one]

theorem mergeEquations_chosen (row : Nat → G) {parent : G} {column size : Nat}
    {parts : List (G × Array RowValue)} (parentActive : parent = 1)
    (individual : ∀ part ∈ parts, booleanConstraint part.1 = 0)
    (bounded : parts.length < gSize.toNat)
    (active : selectorSum (parts.map Prod.fst) = 1)
    {chosen : Array RowValue} (member : (1, chosen) ∈ parts) (width : chosen.size = size)
    (equations : ∀ equation ∈ mergeEquations row parent column size parts, equation = 0) :
    rowValues (rowAdvice row column size) = rowValues chosen := by
  apply Array.ext (by
    rw [rowValues_advice_size]
    simpa only [rowValues, Array.size_map] using width.symm)
  intro index leftBound rightBound
  have bound : index < size := by simpa only [rowValues_advice_size] using leftBound
  have polynomial := equations _ (List.mem_map.mpr ⟨index, List.mem_range.mpr bound, rfl⟩)
  change parent * (row (column + index) - selectorSum
    (parts.map fun part => part.1 * (rowValues part.2)[index]?.getD 0)) = 0 at polynomial
  rw [selector_weighted_chosen (fun values => (rowValues values)[index]?.getD 0)
    individual bounded active member rfl] at polynomial
  have equal := active_case parentActive polynomial
  rw [Array.getElem?_eq_getElem rightBound, Option.getD_some] at equal
  simpa only [rowValues, rowAdvice, Array.getElem_map, Array.getElem_ofFn,
    RowValue.variable, Fin.getElem_fin] using equal

def BlockEmission.QueriesIn (emission : BlockEmission) (queries : List (List G)) : Prop :=
  ∀ part ∈ emission.queries, part.selector = 1 → part.message ∈ queries

def BlockEmission.CallsAt (emission : BlockEmission)
    (calls : List (Bytecode.AIR.Call × (Fin 6 → G))) : Prop :=
  ∀ edge ∈ calls, (1, edge) ∈ emission.calls

def BlockEmission.TerminalAt (emission : BlockEmission) : Bytecode.AIR.Outcome → Prop
  | .returned outputs => ∃ request, (1, request) ∈ emission.returns ∧ request.outputs = outputs
  | .yielded outputs => ∃ yielded, (1, yielded) ∈ emission.yields ∧ rowValues yielded = outputs

structure EmissionIncluded (part whole : BlockEmission) : Prop where
  equations : part.equations ⊆ whole.equations
  queries : part.queries ⊆ whole.queries
  returns : part.returns ⊆ whole.returns
  yields : part.yields ⊆ whole.yields
  calls : part.calls ⊆ whole.calls

theorem EmissionIncluded.refl (emission : BlockEmission) : EmissionIncluded emission emission :=
  ⟨List.Subset.refl _, List.Subset.refl _, List.Subset.refl _, List.Subset.refl _, List.Subset.refl _⟩

theorem EmissionIncluded.trans {first middle last : BlockEmission}
    (left : EmissionIncluded first middle) (right : EmissionIncluded middle last) :
    EmissionIncluded first last :=
  ⟨left.equations.trans right.equations, left.queries.trans right.queries,
    left.returns.trans right.returns, left.yields.trans right.yields, left.calls.trans right.calls⟩

theorem EmissionIncluded.prefix (emission : BlockEmission) (equations : List G) :
    EmissionIncluded emission (emission.prefix equations) :=
  ⟨fun _ member => List.mem_append_right _ member, List.Subset.refl _,
    List.Subset.refl _, List.Subset.refl _, List.Subset.refl _⟩

theorem EmissionIncluded.join (values : Array RowValue) (column lookup : Nat)
    {emissions : List BlockEmission} {emission : BlockEmission} (member : emission ∈ emissions) :
    EmissionIncluded emission (joinBlockEmissions values column lookup emissions) := by
  constructor <;> exact fun _ present => List.mem_flatMap.mpr ⟨emission, member, present⟩

theorem EmissionIncluded.satisfied {part whole : BlockEmission} (included : EmissionIncluded part whole)
    (satisfied : ∀ equation ∈ whole.equations, equation = 0) :
    ∀ equation ∈ part.equations, equation = 0 :=
  fun equation member => satisfied equation (included.equations member)

theorem EmissionIncluded.queried {part whole : BlockEmission} (included : EmissionIncluded part whole)
    {queries : List (List G)} (queried : whole.QueriesIn queries) : part.QueriesIn queries :=
  fun query member active => queried query (included.queries member) active

theorem EmissionIncluded.terminal {part whole : BlockEmission} (included : EmissionIncluded part whole)
    {outcome : Bytecode.AIR.Outcome} (terminal : part.TerminalAt outcome) : whole.TerminalAt outcome := by
  cases outcome with
  | returned outputs =>
    obtain ⟨request, member, equal⟩ := terminal
    exact ⟨request, included.returns member, equal⟩
  | yielded outputs =>
    obtain ⟨values, member, equal⟩ := terminal
    exact ⟨values, included.yields member, equal⟩

theorem EmissionIncluded.called {part whole : BlockEmission} (included : EmissionIncluded part whole)
    {calls : List (Bytecode.AIR.Call × (Fin 6 → G))} (called : part.CallsAt calls) : whole.CallsAt calls :=
  fun edge member => included.calls (called edge member)

theorem forall₂_left_member {α β : Type} {relation : α → β → Prop} {source : List α}
    {emissions : List β} (related : List.Forall₂ relation source emissions) {item : α}
    (member : item ∈ source) : ∃ emission ∈ emissions, relation item emission := by
  induction related with
  | nil => cases member
  | @cons head emission heads emissions first rest ih =>
    rcases List.mem_cons.mp member with equal | tail
    · subst item
      exact ⟨emission, List.mem_cons_self, first⟩
    · obtain ⟨body, bodyMember, correct⟩ := ih tail
      exact ⟨body, List.mem_cons_of_mem _ bodyMember, correct⟩

theorem mapM_member {α β : Type} {source : List α} {emissions : List β} {emit : α → Option β}
    (emitted : source.mapM emit = some emissions) {item : α} (member : item ∈ source) :
    ∃ emission ∈ emissions, emit item = some emission :=
  forall₂_left_member (mapM_forall₂ emitted (fun _ _ _ equal => equal)) member

theorem mapM_of_forall₂ {α β : Type} {source : List α} {emissions : List β} {emit : α → Option β}
    (related : List.Forall₂ (fun item emission => emit item = some emission) source emissions) :
    source.mapM emit = some emissions := by
  induction related with
  | nil => rfl
  | cons first _ ih => rw [List.mapM_cons, first, ih]; rfl

theorem readRowValues (values : Array RowValue) (indices : Array ValIdx) (outputs : List RowValue)
    (read : indices.toList.mapM (fun index => values[index]?) = some outputs) :
    Bytecode.AIR.readValues (rowValues values) indices = some (rowValues outputs.toArray) := by
  have related := mapM_forall₂ read (fun _ _ _ equal => equal)
  have mapped : List.Forall₂ (fun index value => (rowValues values)[index]? = some value)
      indices.toList (outputs.map RowValue.value) := by
    generalize sourceEq : indices.toList = source at related ⊢
    clear read sourceEq
    induction related with
    | nil => exact .nil
    | cons first _ ih => exact .cons (rowValues_read first) ih
  have result := mapM_of_forall₂ mapped
  have listResult : (Array.toList <$> Bytecode.AIR.readValues (rowValues values) indices) =
      some (rowValues outputs.toArray).toList := by
    rw [Bytecode.AIR.readValues, Array.toList_mapM]
    simpa only [rowValues, Array.toList_map, List.toList_toArray] using result
  cases emitted : Bytecode.AIR.readValues (rowValues values) indices with
  | none => rw [emitted] at listResult; cases listResult
  | some array =>
    rw [emitted] at listResult
    have equal := Array.toList_inj.mp (Option.some.inj listResult)
    exact congrArg some equal

theorem queryParts_member (slot : Nat) (selector : G) {queries : List (List G)} {message : List G}
    (member : message ∈ queries) :
    ∃ part ∈ queryParts slot selector queries, part.selector = selector ∧ part.message = message := by
  obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp member
  refine ⟨⟨slot + index, selector, message⟩, ?_, rfl, rfl⟩
  exact List.mem_mapIdx.mpr ⟨index, bound, by rw [equal]⟩

theorem EmissionIncluded.afterOps (incoming : G) (lookup : Nat) (operations : OpsEmission)
    (control : BlockEmission) : EmissionIncluded control (control.afterOps incoming lookup operations) :=
  ⟨fun _ member => List.mem_append_right _ member,
    fun _ member => List.mem_append_right _ member, List.Subset.refl _, List.Subset.refl _,
    fun _ member => List.mem_append_right _ member⟩

theorem BlockEmission.afterOps_queried {incoming : G} {lookup : Nat} {operations : OpsEmission}
    {control : BlockEmission} {queries : List (List G)} (active : incoming = 1)
    (queried : (control.afterOps incoming lookup operations).QueriesIn queries) :
    operations.queries ⊆ queries := by
  intro message member
  obtain ⟨part, partMember, gate, equal⟩ := queryParts_member lookup incoming member
  rw [← equal]
  exact queried part (List.mem_append_left _ partMember) (gate.trans active)

theorem BlockEmission.afterOps_called {incoming : G} {lookup : Nat} {operations : OpsEmission}
    {control : BlockEmission} {calls : List (Bytecode.AIR.Call × (Fin 6 → G))}
    (active : incoming = 1) (called : control.CallsAt calls) :
    (control.afterOps incoming lookup operations).CallsAt (operations.calls ++ calls) := by
  intro edge member
  rcases List.mem_append.mp member with first | rest
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨edge, first, by rw [active]⟩)
  · exact List.mem_append_right _ (called edge rest)

theorem EmissionIncluded.continued (branches : BlockEmission) (equations : List G)
    (continuation : BlockEmission) : EmissionIncluded continuation (branches.continued equations continuation) :=
  ⟨fun _ member => List.mem_append_right _ member,
    fun _ member => List.mem_append_right _ member,
    fun _ member => List.mem_append_right _ member, List.Subset.refl _,
    fun _ member => List.mem_append_right _ member⟩

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

private theorem row_bounds_smaller (block : Block) : sizeOf block.ctrl < sizeOf block := by
  cases block
  simp
  omega

mutual

def Ctrl.rowBounds (selector : SelIdx → G) : Ctrl → Prop
  | .return .. | .yield .. => True
  | .match _ branches fallback =>
    branches.size + fallback.toList.length < gSize.toNat ∧
      (∀ pair ∈ branches.toList, pair.2.rowBounds selector) ∧
      (match fallback with | none => True | some block => block.rowBounds selector)
  | .matchContinue _ branches fallback _ _ _ continuation =>
    let flow := SelectorFlow.join (branchSelectorFlows selector branches fallback)
    branches.size + fallback.toList.length < gSize.toNat ∧
      flow.returns.length + flow.yields.length < gSize.toNat ∧
      (∀ pair ∈ branches.toList, pair.2.rowBounds selector) ∧
      (match fallback with | none => True | some block => block.rowBounds selector) ∧
      continuation.rowBounds selector
termination_by ctrl => sizeOf ctrl
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem (Array.mem_def.mpr ‹_ ∈ _›); grind)

def Block.rowBounds (selector : SelIdx → G) (block : Block) : Prop :=
  block.ctrl.rowBounds selector
termination_by sizeOf block
decreasing_by exact row_bounds_smaller block

end

theorem AIR.SelectArm.rowBounds {selector : SelIdx → G} {matched : G}
    {branches : Array (G × Block)} {fallback : Option Block} {block : Block}
    (selected : SelectArm matched branches fallback block)
    (casesBounded : ∀ pair ∈ branches.toList, pair.2.rowBounds selector)
    (fallbackBounded : ∀ block, fallback = some block → block.rowBounds selector) :
    block.rowBounds selector := by
  cases selected with
  | case member => exact casesBounded _ member
  | fallback present unmatched => exact fallbackBounded block present

theorem AIR.SelectArm.smaller_match {matched : G} {branches : Array (G × Block)}
    {fallback : Option Block} {block : Block} (selected : SelectArm matched branches fallback block)
    (index : ValIdx) : sizeOf block < sizeOf (Ctrl.match index branches fallback) := by
  cases selected with
  | case member =>
    have bound := Array.sizeOf_lt_of_mem (Array.mem_def.mpr member)
    simp only [Prod.mk.sizeOf_spec, Ctrl.match.sizeOf_spec] at *
    omega
  | fallback present unmatched => rw [present]; simp; omega

theorem AIR.SelectArm.smaller_matchContinue {matched : G} {branches : Array (G × Block)}
    {fallback : Option Block} {block : Block} (selected : SelectArm matched branches fallback block)
    (index : ValIdx) (size aux slots : Nat) (continuation : Block) :
    sizeOf block < sizeOf (Ctrl.matchContinue index branches fallback size aux slots continuation) := by
  cases selected with
  | case member =>
    have bound := Array.sizeOf_lt_of_mem (Array.mem_def.mpr member)
    simp only [Prod.mk.sizeOf_spec, Ctrl.matchContinue.sizeOf_spec] at *
    omega
  | fallback present unmatched => rw [present]; simp; omega

theorem branchRows_polynomials (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (matched : G) (values : Array RowValue) (column lookup : Nat)
    (branches : Array (G × Block)) (fallback : Option Block) {emission : BlockEmission}
    (emitted : branchRows row selector context matched values column lookup branches fallback = some emission)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0) :
    MatchPolynomials selector matched branches fallback := by
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
      constructor
      · intro pair member
        obtain ⟨result, resultMember, resultEmitted⟩ := mapM_member casesEmitted member
        simp only [caseRow, bind, Option.bind] at resultEmitted
        split at resultEmitted
        · cases resultEmitted
        · rename_i body bodyEmitted
          have equal := Option.some.inj resultEmitted
          subst result
          exact satisfied _ ((EmissionIncluded.join values column lookup
            (List.mem_append_left _ resultMember)).equations List.mem_cons_self)
      · intro block present pair member
        rw [present] at defaultEmitted
        simp only [defaultRow, bind, Option.bind] at defaultEmitted
        split at defaultEmitted
        · cases defaultEmitted
        · rename_i body bodyEmitted
          have equal := Option.some.inj defaultEmitted
          subst default
          obtain ⟨index, bound, selected⟩ := List.mem_iff_getElem.mp member
          refine ⟨row (column + index), ?_⟩
          apply satisfied
          apply (EmissionIncluded.join values column lookup
            (List.mem_append_right cases List.mem_cons_self)).equations
          apply List.mem_append_left
          exact List.mem_mapIdx.mpr ⟨index, bound, by rw [selected]⟩

theorem branchRows_body (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (matched : G) (values : Array RowValue) (column lookup : Nat)
    (branches : Array (G × Block)) (fallback : Option Block) {emission : BlockEmission}
    (emitted : branchRows row selector context matched values column lookup branches fallback = some emission)
    {block : Block} (selected : AIR.SelectArm matched branches fallback block) :
    ∃ bodyColumn body,
      block.emitRow row selector context (block.selectorFlow selector).entry values bodyColumn lookup = some body ∧
      EmissionIncluded body emission := by
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
      cases selected with
      | case member =>
        obtain ⟨result, resultMember, resultEmitted⟩ := mapM_member casesEmitted member
        simp only [caseRow, bind, Option.bind] at resultEmitted
        split at resultEmitted
        · cases resultEmitted
        · rename_i body bodyEmitted
          have equal := Option.some.inj resultEmitted
          subst result
          exact ⟨column, body, bodyEmitted,
            (EmissionIncluded.prefix body _).trans
              (EmissionIncluded.join values column lookup (List.mem_append_left _ resultMember))⟩
      | fallback present unmatched =>
        rw [present] at defaultEmitted
        simp only [defaultRow, bind, Option.bind] at defaultEmitted
        split at defaultEmitted
        · cases defaultEmitted
        · rename_i body bodyEmitted
          have equal := Option.some.inj defaultEmitted
          subst default
          exact ⟨column + branches.size, body, bodyEmitted,
            (EmissionIncluded.prefix body _).trans
              (EmissionIncluded.join values column lookup
                (List.mem_append_right _ List.mem_cons_self))⟩

theorem branchRows_selector_projection (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (matched : G) (values : Array RowValue) (column lookup : Nat)
    (branches : Array (G × Block)) (fallback : Option Block) {emission : BlockEmission}
    (emitted : branchRows row selector context matched values column lookup branches fallback = some emission) :
    EmissionProjection (SelectorFlow.join (branchSelectorFlows selector branches fallback))
      (branchReturnGates selector branches fallback) emission :=
  branchRows_projection row selector context matched values column lookup branches fallback emitted
    (fun pair _ _ bodyEmitted => pair.2.emitRow_projection row selector context _ _ _ _ bodyEmitted)
    (fun block _ _ bodyEmitted => block.emitRow_projection row selector context _ _ _ _ bodyEmitted)

theorem branchRows_selected (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (matched : G) (values : Array RowValue) (column lookup : Nat)
    (branches : Array (G × Block)) (fallback : Option Block) {emission : BlockEmission}
    (emitted : branchRows row selector context matched values column lookup branches fallback = some emission)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0)
    (bounded : branches.size + fallback.toList.length < gSize.toNat)
    (active : (SelectorFlow.join (branchSelectorFlows selector branches fallback)).entry = 1) :
    ∃ block bodyColumn body, AIR.SelectArm matched branches fallback block ∧
      (block.selectorFlow selector).entry = 1 ∧
      block.emitRow row selector context (block.selectorFlow selector).entry values bodyColumn lookup = some body ∧
      EmissionIncluded body emission := by
  have projected := branchRows_selector_projection row selector context matched values column lookup
    branches fallback emitted
  have polynomials := branchRows_polynomials row selector context matched values column lookup
    branches fallback emitted satisfied
  obtain ⟨block, selected, _, blockActive⟩ := polynomials.active_branch
    (fun equation member => satisfied equation (projected.equations member)) bounded active
  obtain ⟨bodyColumn, body, bodyEmitted, included⟩ := branchRows_body row selector context matched values
    column lookup branches fallback emitted selected
  exact ⟨block, bodyColumn, body, selected, blockActive, bodyEmitted, included⟩

mutual

theorem Ctrl.emitRow_run {tables : LookupTables} {width : Nat} {queries : List (List G)}
    (global : GlobalLookups tables width queries)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    (program : Toplevel) (yieldSize : Option Nat)
    (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (incoming : G) (values : Array RowValue) (column lookup : Nat) (ctrl : Ctrl)
    (shape : ctrl.lookupShapes program yieldSize = true) (bounds : ctrl.rowBounds selector)
    {emission : BlockEmission}
    (emitted : ctrl.emitRow row selector context incoming values column lookup = some emission)
    (active : incoming = 1) (linked : incoming = (ctrl.selectorFlow selector).entry)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0) (queried : emission.QueriesIn queries) :
    ∃ outcome calls,
      AIR.RunCtrl (memoryFacts tables.memory) ctrl (rowValues values) outcome (calls.map Prod.fst) ∧
      emission.TerminalAt outcome ∧ emission.CallsAt calls := by
  cases ctrl with
  | «return» index indices =>
    rw [Ctrl.emitRow.eq_def] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i inputs readInputs
      dsimp only at emitted
      split at emitted
      · cases emitted
      · rename_i outputs readOutputs
        have equal := Option.some.inj emitted
        subst emission
        refine ⟨.returned outputs, [], AIR.RunCtrl.returned readOutputs, ?_, by simp [BlockEmission.CallsAt]⟩
        refine ⟨⟨context.function, inputs, outputs, context.rank⟩, ?_, rfl⟩
        change (1, _) ∈ [(incoming, _)]
        rw [active]
        exact List.mem_cons_self
  | yield index indices =>
    rw [Ctrl.emitRow.eq_def] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i outputs readOutputs
      have equal := Option.some.inj emitted
      subst emission
      rw [Ctrl.selectorFlow.eq_def] at linked
      have selected : selector index = 1 := linked.symm.trans active
      refine ⟨.yielded (rowValues outputs.toArray), [],
        AIR.RunCtrl.yielded (readRowValues values indices outputs readOutputs), ?_,
        by simp [BlockEmission.CallsAt]⟩
      exact ⟨outputs.toArray, by change (1, _) ∈ [(selector index, _)]; rw [selected]; exact List.mem_cons_self, rfl⟩
  | «match» index branches fallback =>
    rw [Ctrl.emitRow_match] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i matched read
      rw [Ctrl.rowBounds.eq_def] at bounds
      obtain ⟨branchBound, casesBounded, fallbackBounded⟩ := bounds
      obtain ⟨casesShape, fallbackShape⟩ := (lookupShapes_match _ _ _ _ _).mp shape
      rw [Ctrl.selectorFlow_match] at linked
      obtain ⟨arm, bodyColumn, body, selected, armActive, bodyEmitted, included⟩ :=
        branchRows_selected row selector context matched.value values column lookup branches fallback
          emitted satisfied branchBound (linked.symm.trans active)
      have smaller := selected.smaller_match index
      obtain ⟨outcome, calls, execution, terminal, called⟩ := Block.emitRow_run global memoryValid canonical
        program yieldSize row selector context _ values bodyColumn lookup arm
        (selected.lookupShapes program yieldSize casesShape fallbackShape)
        (selected.rowBounds casesBounded (fun block present => by
          rw [present] at fallbackBounded; exact fallbackBounded)) bodyEmitted armActive rfl
        (included.satisfied satisfied) (included.queried queried)
      exact ⟨outcome, calls, AIR.RunCtrl.match (rowValues_read read) selected execution,
        included.terminal terminal, included.called called⟩
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
        simp only [continueRow] at emitted
        split at emitted
        · rename_i sizes
          simp only [bind, Option.bind] at emitted
          split at emitted
          · cases emitted
          · rename_i continued contEmitted
            have equal := Option.some.inj emitted
            subst emission
            rw [Ctrl.rowBounds.eq_def] at bounds
            obtain ⟨branchBound, terminalBound, casesBounded, fallbackBounded, contBounded⟩ := bounds
            obtain ⟨casesShape, fallbackShape, contShape⟩ :=
              (lookupShapes_matchContinue _ _ _ _ _ _ _ _ _).mp shape
            rw [Ctrl.selectorFlow_matchContinue] at linked
            have joinedActive : (SelectorFlow.join (branchSelectorFlows selector branches fallback)).entry = 1 :=
              linked.symm.trans active
            have joinedSatisfied : ∀ equation ∈ joined.equations, equation = 0 :=
              fun equation member => satisfied equation
                (List.mem_append_left _ (List.mem_append_left _ member))
            have joinedQueried : joined.QueriesIn queries :=
              fun part member gate => queried part (List.mem_append_left _ member) gate
            obtain ⟨arm, bodyColumn, body, selected, armActive, bodyEmitted, included⟩ :=
              branchRows_selected row selector context matched.value values column lookup branches fallback
                branchesEmitted joinedSatisfied branchBound joinedActive
            have smaller := selected.smaller_matchContinue index size aux slots continuation
            obtain ⟨outcome, calls, execution, terminal, called⟩ := Block.emitRow_run global memoryValid canonical
              program (some size) row selector context _ values bodyColumn lookup arm
              (selected.lookupShapes program (some size) casesShape fallbackShape)
              (selected.rowBounds casesBounded (fun block present => by
                rw [present] at fallbackBounded; exact fallbackBounded)) bodyEmitted armActive rfl
              (included.satisfied joinedSatisfied) (included.queried joinedQueried)
            have joinedTerminal := included.terminal terminal
            have joinedCalls := included.called called
            cases outcome with
            | returned outputs =>
              refine ⟨.returned outputs, calls,
                AIR.RunCtrl.matchContinueReturn (rowValues_read read) selected execution, ?_, ?_⟩
              · obtain ⟨request, member, equal⟩ := joinedTerminal
                exact ⟨request, List.mem_append_left _ member, equal⟩
              · exact fun edge member => List.mem_append_left _ (joinedCalls edge member)
            | yielded outputs =>
              obtain ⟨yielded, yieldMember, yieldEqual⟩ := joinedTerminal
              have projected := branchRows_selector_projection row selector context matched.value values column lookup
                branches fallback branchesEmitted
              have flowValid : (SelectorFlow.join (branchSelectorFlows selector branches fallback)).Satisfied :=
                fun equation member => joinedSatisfied equation (projected.equations member)
              have flowSound := branchSelectorFlows_sound selector branches fallback flowValid
                (fun pair _ valid => pair.2.selectorFlow_sound selector valid)
                (fun block _ valid => block.selectorFlow_sound selector valid)
              have oneYield : (1 : G) ∈ (SelectorFlow.join (branchSelectorFlows selector branches fallback)).yields := by
                rw [← projected.yielded]
                exact List.mem_map.mpr ⟨(1, yielded), yieldMember, rfl⟩
              have gateOne : selectorSum (joined.yields.map Prod.fst) = 1 := by
                rw [projected.yielded]
                exact flowSound.yield_starts_continuation terminalBound joinedActive oneYield
              have link : (continuation.selectorFlow selector).entry = selectorSum (joined.yields.map Prod.fst) := by
                apply (G.sub_eq_zero_iff _ _).mp
                apply satisfied
                exact List.mem_append_left _ (List.mem_append_right _
                  (List.mem_append_right _ List.mem_cons_self))
              have yieldWidth : yielded.size = size :=
                beq_iff_eq.mp ((List.all_eq_true.mp sizes) _ yieldMember)
              have yieldBound : joined.yields.length < gSize.toNat := by
                have lengths := congrArg List.length projected.yielded
                simp only [List.length_map] at lengths
                omega
              have yieldBoolean : ∀ part ∈ joined.yields, booleanConstraint part.1 = 0 := by
                intro part member
                apply flowSound.yielded
                rw [← projected.yielded]
                exact List.mem_map.mpr ⟨part, member, rfl⟩
              have mergeValues := mergeEquations_chosen row active yieldBoolean yieldBound gateOne
                yieldMember yieldWidth (fun equation member => satisfied equation
                  (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ member))))
              have contIncluded := EmissionIncluded.continued joined
                (mergeEquations row incoming joined.column size joined.yields ++
                  [(continuation.selectorFlow selector).entry - selectorSum (joined.yields.map Prod.fst)]) continued
              obtain ⟨result, contCalls, contRun, contTerminal, contCallsAt⟩ :=
                Block.emitRow_run global memoryValid canonical program yieldSize row selector context _ _ _ _
                  continuation contShape contBounded contEmitted gateOne link.symm
                  (contIncluded.satisfied satisfied) (contIncluded.queried queried)
              rw [rowValues_append, mergeValues, yieldEqual] at contRun
              have outputSize : outputs.size = size := by
                rw [← yieldEqual]
                simpa only [rowValues, Array.size_map] using yieldWidth
              refine ⟨result, calls ++ contCalls, ?_, contIncluded.terminal contTerminal, ?_⟩
              · simpa only [List.map_append] using
                  AIR.RunCtrl.matchContinueYield (rowValues_read read) selected execution outputSize contRun
              · intro edge member
                rcases List.mem_append.mp member with first | last
                · exact List.mem_append_left _ (joinedCalls edge first)
                · exact List.mem_append_right _ (contCallsAt edge last)
        · cases emitted
termination_by sizeOf ctrl
decreasing_by all_goals first | decreasing_tactic | omega

theorem Block.emitRow_run {tables : LookupTables} {width : Nat} {queries : List (List G)}
    (global : GlobalLookups tables width queries)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    (program : Toplevel) (yieldSize : Option Nat)
    (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (incoming : G) (values : Array RowValue) (column lookup : Nat) (block : Block)
    (shape : block.lookupShapes program yieldSize = true) (bounds : block.rowBounds selector)
    {emission : BlockEmission}
    (emitted : block.emitRow row selector context incoming values column lookup = some emission)
    (active : incoming = 1) (linked : incoming = (block.selectorFlow selector).entry)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0) (queried : emission.QueriesIn queries) :
    ∃ outcome calls,
      AIR.RunBlock (memoryFacts tables.memory) block (rowValues values) outcome (calls.map Prod.fst) ∧
      emission.TerminalAt outcome ∧ emission.CallsAt calls := by
  rw [Block.emitRow] at emitted
  simp only [bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  · rename_i operations opsEmitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    · rename_i control ctrlEmitted
      have equal := Option.some.inj emitted
      subst emission
      have tailIncluded := EmissionIncluded.prefix (control.afterOps incoming lookup operations)
        [oneSubBooleanConstraint (block.selectorFlow selector).entry]
      have controlIncluded := (EmissionIncluded.afterOps incoming lookup operations control).trans tailIncluded
      rw [Block.lookupShapes, Bool.and_eq_true] at shape
      have opsRun := emitOps_run global memoryValid canonical
        (fun op member => (Array.all_eq_true'.mp shape.1) op (Array.mem_def.mpr member))
        opsEmitted active
        (fun equation member => (tailIncluded.satisfied satisfied) equation (List.mem_append_left _ member))
        (BlockEmission.afterOps_queried active (tailIncluded.queried queried))
      obtain ⟨outcome, calls, ctrlRun, terminal, called⟩ := Ctrl.emitRow_run global memoryValid canonical
        program yieldSize row selector context incoming _ _ _ block.ctrl shape.2
        (by rwa [Block.rowBounds] at bounds) ctrlEmitted active
        (by simpa only [Block.selectorFlow] using linked)
        (controlIncluded.satisfied satisfied) (controlIncluded.queried queried)
      refine ⟨outcome, operations.calls ++ calls, ?_, controlIncluded.terminal terminal, ?_⟩
      · simpa only [List.map_append] using AIR.RunBlock.block opsRun ctrlRun
      · exact tailIncluded.called (BlockEmission.afterOps_called active called)
termination_by sizeOf block
decreasing_by exact row_bounds_smaller block

end

end Aiur.Bytecode
