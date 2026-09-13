/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.BlockQuerySlots

/-!
Decode the unique active query in each valued lookup slot. Its message
equals the native-style combined message after padding, and its multiplicity
is zero or one. The decoded list preserves exact padded lookup balance and
has at most one query per allocated slot.

The single-writer premise for ungated branchless slots remains explicit.
The model-to-native and randomized-compression reductions are separate.
-/

namespace Aiur.AIR

def activeQuerySlot (queries : List QueryPart) (slot : Nat) : List QueryPart :=
  queries.filter fun query => query.slot == slot && query.selector == 1

def querySlotParts (queries : List QueryPart) (slot : Nat) : List (G × List G) :=
  (queries.filter fun query => query.slot == slot).map fun query => (query.selector, query.message)

def querySlotMultiplicity (queries : List QueryPart) (slot : Nat) : G :=
  selectorSum ((querySlotParts queries slot).map Prod.fst)

def decodedQuery (queries : List QueryPart) (slot : Nat) : Option (List G) :=
  (activeQuerySlot queries slot).head?.map (·.message)

def encodedQuery (branchless : Bool) (queries : List QueryPart) (slot : Nat) : Option (List G) :=
  if querySlotMultiplicity queries slot = 1 then some (slotMessage branchless (querySlotParts queries slot))
  else none

def decodedQueries (queries : List QueryPart) (limit : Nat) : List (List G) :=
  (List.range limit).filterMap (decodedQuery queries)

def encodedQueries (branchless : Bool) (queries : List QueryPart) (limit : Nat) : List (List G) :=
  (List.range limit).filterMap (encodedQuery branchless queries)

theorem singleton_of_member_length_le_one {α : Type} {items : List α} {item : α}
    (member : item ∈ items) (bound : items.length ≤ 1) : items = [item] := by
  cases items with
  | nil => cases member
  | cons head tail =>
    have empty : tail = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at bound; omega)
    subst tail
    have equal := List.mem_singleton.mp member
    subst item
    rfl

theorem selector_pair_chosen_count {α : Type} {parts : List (G × α)}
    (individual : ∀ part ∈ parts, booleanConstraint part.1 = 0)
    (count : (parts.map Prod.fst).count 1 = 1)
    {chosen : G × α} (member : chosen ∈ parts) (active : chosen.1 = 1) :
    ∃ before after, parts = before ++ chosen :: after ∧
      ∀ part ∈ before ++ after, part.1 = 0 := by
  obtain ⟨before, after, equal⟩ := List.mem_iff_append.mp member
  have counts := count
  rw [equal, List.map_append, List.count_append, List.map_cons, active, List.count_cons_self] at counts
  have empty : ((before ++ after).map Prod.fst).count 1 = 0 := by
    rw [List.map_append, List.count_append]
    omega
  have absent := List.count_eq_zero.mp empty
  refine ⟨before, after, equal, ?_⟩
  intro part present
  have original : part ∈ parts := by
    rw [equal]
    rcases List.mem_append.mp present with left | right
    · exact List.mem_append_left _ left
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ right)
  rcases G.boolean_of_constraint (individual part original) with inactive | selected
  · exact inactive
  · exact False.elim (absent (List.mem_map.mpr ⟨part, present, selected⟩))

theorem slotMessage_chosen_count (width : Nat) (branchless : Bool) {parts : List (G × List G)}
    (single : branchless = true → parts.length ≤ 1)
    (individual : ∀ part ∈ parts, booleanConstraint part.1 = 0)
    (count : (parts.map Prod.fst).count 1 = 1)
    {chosen : G × List G} (member : chosen ∈ parts) (active : chosen.1 = 1) :
    padMessage width (slotMessage branchless parts) = padMessage width chosen.2 := by
  cases branchless with
  | false =>
    obtain ⟨before, after, equal, zero⟩ := selector_pair_chosen_count individual count member active
    rw [equal]
    exact weightedMessage_split width before after chosen active zero
  | true =>
    rw [singleton_of_member_length_le_one member (single rfl)]
    rfl

theorem querySlotParts_count (queries : List QueryPart) (slot : Nat) :
    ((querySlotParts queries slot).map Prod.fst).count 1 = queryCount queries slot := by
  rw [querySlotParts, List.map_map, List.count_eq_countP, List.countP_map,
    List.countP_eq_length_filter, List.filter_filter]
  simp only [Function.comp_def, queryCount, Bool.and_comm]

theorem querySlotParts_member {queries : List QueryPart} {query : QueryPart}
    (member : query ∈ queries) : (query.selector, query.message) ∈ querySlotParts queries query.slot := by
  apply List.mem_map.mpr
  exact ⟨query, List.mem_filter.mpr ⟨member, by simp⟩, rfl⟩

theorem QuerySlots.slot_boolean {gate : G} {start finish : Nat} {queries : List QueryPart}
    (slots : QuerySlots gate start finish queries) (slot : Nat) :
    ∀ part ∈ querySlotParts queries slot, booleanConstraint part.1 = 0 := by
  intro part member
  obtain ⟨query, queryMember, equal⟩ := List.mem_map.mp member
  subst part
  exact slots.boolean query (List.mem_filter.mp queryMember).1

theorem QuerySlots.slot_multiplicity {gate : G} {start finish : Nat} {queries : List QueryPart}
    (slots : QuerySlots gate start finish queries) (slot : Nat) :
    querySlotMultiplicity queries slot = G.ofNat (queryCount queries slot) := by
  rw [querySlotMultiplicity, selectorSum_eq_count]
  · rw [querySlotParts_count]
  · intro value member
    obtain ⟨part, partMember, equal⟩ := List.mem_map.mp member
    subst value
    exact G.boolean_of_constraint (slots.slot_boolean slot part partMember)

theorem QuerySlots.multiplicity_boolean {gate : G} {start finish : Nat} {queries : List QueryPart}
    (slots : QuerySlots gate start finish queries) (slot : Nat) :
    querySlotMultiplicity queries slot = 0 ∨ querySlotMultiplicity queries slot = 1 := by
  have bound := Nat.le_trans (slots.count slot) (gateCount_le_one gate)
  have count : queryCount queries slot = 0 ∨ queryCount queries slot = 1 := by omega
  rw [slots.slot_multiplicity slot]
  rcases count with zero | one
  · rw [zero]
    exact Or.inl rfl
  · rw [one]
    exact Or.inr rfl

theorem QuerySlots.active_singleton {gate : G} {start finish : Nat} {queries : List QueryPart}
    (slots : QuerySlots gate start finish queries) {query : QueryPart}
    (member : query ∈ queries) (active : query.selector = 1) :
    activeQuerySlot queries query.slot = [query] := by
  apply singleton_of_member_length_le_one
  · exact List.mem_filter.mpr ⟨member, by simp only [Bool.and_eq_true, beq_iff_eq]; exact ⟨trivial, active⟩⟩
  · exact Nat.le_trans (slots.count _) (gateCount_le_one gate)

theorem QuerySlots.decoded {gate : G} {start finish : Nat} {queries : List QueryPart}
    (slots : QuerySlots gate start finish queries) {query : QueryPart}
    (member : query ∈ queries) (active : query.selector = 1) :
    decodedQuery queries query.slot = some query.message := by
  rw [decodedQuery, slots.active_singleton member active]
  rfl

theorem QuerySlots.decoded_member {gate : G} {start finish : Nat} {queries : List QueryPart}
    (slots : QuerySlots gate start finish queries) {query : QueryPart}
    (member : query ∈ queries) (active : query.selector = 1) :
    query.message ∈ decodedQueries queries finish := by
  apply List.mem_filterMap.mpr
  exact ⟨query.slot, List.mem_range.mpr (slots.range query member).2, slots.decoded member active⟩

theorem QuerySlots.slot_message {gate : G} {start finish : Nat} {queries : List QueryPart}
    (slots : QuerySlots gate start finish queries) (width : Nat) (branchless : Bool)
    (single : branchless = true → ∀ slot, (querySlotParts queries slot).length ≤ 1)
    {query : QueryPart} (member : query ∈ queries) (active : query.selector = 1) :
    padMessage width (slotMessage branchless (querySlotParts queries query.slot)) = padMessage width query.message := by
  have count : queryCount queries query.slot = 1 :=
    congrArg List.length (slots.active_singleton member active)
  exact slotMessage_chosen_count width branchless (fun enabled => single enabled query.slot)
    (slots.slot_boolean _) ((querySlotParts_count _ _).trans count)
    (querySlotParts_member member) active

theorem QuerySlots.slot_reflects {gate : G} {start finish : Nat} {queries : List QueryPart}
    (slots : QuerySlots gate start finish queries) (width : Nat) (branchless : Bool)
    (single : branchless = true → ∀ slot, (querySlotParts queries slot).length ≤ 1) (slot : Nat) :
    (encodedQuery branchless queries slot).map (padMessage width) =
      (decodedQuery queries slot).map (padMessage width) := by
  cases found : activeQuerySlot queries slot with
  | nil =>
    have count : queryCount queries slot = 0 := congrArg List.length found
    have inactive : querySlotMultiplicity queries slot = 0 := by rw [slots.slot_multiplicity slot, count]; rfl
    simp only [encodedQuery, decodedQuery, found, inactive, Ne.symm G.one_ne_zero, if_false,
      List.head?_nil, Option.map_none]
  | cons query rest =>
    have member : query ∈ activeQuerySlot queries slot := by rw [found]; exact List.mem_cons_self
    obtain ⟨original, same, active⟩ := by
      simpa only [activeQuerySlot, List.mem_filter, Bool.and_eq_true, beq_iff_eq] using member
    have singleton := slots.active_singleton original active
    rw [same] at singleton
    have count : queryCount queries slot = 1 := congrArg List.length singleton
    have multiplicity : querySlotMultiplicity queries slot = 1 := by rw [slots.slot_multiplicity slot, count]; rfl
    have message := slots.slot_message width branchless single original active
    rw [same] at message
    simp only [encodedQuery, decodedQuery, singleton, multiplicity, if_true,
      List.head?_cons, Option.map_some]
    exact congrArg some message

theorem QuerySlots.queries_reflect {gate : G} {start finish : Nat} {queries : List QueryPart}
    (slots : QuerySlots gate start finish queries) (width : Nat) (branchless : Bool)
    (single : branchless = true → ∀ slot, (querySlotParts queries slot).length ≤ 1) (limit : Nat) :
    (encodedQueries branchless queries limit).map (padMessage width) =
      (decodedQueries queries limit).map (padMessage width) := by
  simp only [encodedQueries, decodedQueries, List.map_filterMap]
  apply congrArg (fun read : Nat → Option (List G) => (List.range limit).filterMap read)
  funext slot
  exact slots.slot_reflects width branchless single slot

theorem QuerySlots.padded_balance {gate : G} {start finish : Nat} {queries : List QueryPart}
    (slots : QuerySlots gate start finish queries) (width : Nat) (branchless : Bool)
    (single : branchless = true → ∀ slot, (querySlotParts queries slot).length ≤ 1)
    (limit : Nat) (providers : List (Provider (List G)))
    (balanced : PaddedLookupBalance width (encodedQueries branchless queries limit) providers) :
    PaddedLookupBalance width (decodedQueries queries limit) providers := by
  unfold PaddedLookupBalance at balanced ⊢
  rw [← slots.queries_reflect width branchless single limit]
  exact balanced

theorem decodedQueries_length (queries : List QueryPart) (limit : Nat) :
    (decodedQueries queries limit).length ≤ limit := by
  simpa only [decodedQueries, List.length_range] using
    List.length_filterMap_le (decodedQuery queries) (List.range limit)

end Aiur.AIR
