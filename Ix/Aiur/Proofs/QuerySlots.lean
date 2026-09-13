/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.FunctionRows

/-!
Lookup-slot intervals and natural active-query counts. Sequential regions
are disjoint, while shared regions combine bounded selector families. The
count invariant excludes duplicate active contributions without requiring
the number of inactive writers in a slot to fit the field characteristic.
-/

namespace Aiur.AIR
open Bytecode

def gateCount (gate : G) : Nat := if gate = 1 then 1 else 0

def queryCount (queries : List QueryPart) (slot : Nat) : Nat :=
  (queries.filter fun query => query.slot == slot && query.selector == 1).length

structure QuerySlots (gate : G) (start finish : Nat) (queries : List QueryPart) : Prop where
  extent : start ≤ finish
  range : ∀ query ∈ queries, start ≤ query.slot ∧ query.slot < finish
  boolean : ∀ query ∈ queries, booleanConstraint query.selector = 0
  count : ∀ slot, queryCount queries slot ≤ gateCount gate

theorem gateCount_le_one (gate : G) : gateCount gate ≤ 1 := by
  simp only [gateCount]
  split <;> omega

theorem gateCount_zero : gateCount 0 = 0 := by
  simp [gateCount, Ne.symm G.one_ne_zero]

theorem queryCount_append (first rest : List QueryPart) (slot : Nat) :
    queryCount (first ++ rest) slot = queryCount first slot + queryCount rest slot := by
  simp only [queryCount, List.filter_append, List.length_append]

theorem QuerySlots.empty (gate : G) (start : Nat) : QuerySlots gate start start [] :=
  ⟨Nat.le_refl _, by simp, by simp, by simp [queryCount]⟩

theorem QuerySlots.outside {gate : G} {start finish : Nat} {queries : List QueryPart}
    (slots : QuerySlots gate start finish queries) (slot : Nat)
    (outside : slot < start ∨ finish ≤ slot) : queryCount queries slot = 0 := by
  apply List.length_eq_zero_iff.mpr
  apply List.filter_eq_nil_iff.mpr
  intro query member
  have range := slots.range query member
  simp only [Bool.and_eq_true, beq_iff_eq]
  intro same
  omega

theorem QuerySlots.weaken {first last : G} {start finish : Nat} {queries : List QueryPart}
    (slots : QuerySlots first start finish queries) (bound : gateCount first ≤ gateCount last) :
    QuerySlots last start finish queries :=
  ⟨slots.extent, slots.range, slots.boolean, fun slot => Nat.le_trans (slots.count slot) bound⟩

theorem QuerySlots.append {gate : G} {start middle finish : Nat} {first rest : List QueryPart}
    (left : QuerySlots gate start middle first) (right : QuerySlots gate middle finish rest) :
    QuerySlots gate start finish (first ++ rest) := by
  refine ⟨Nat.le_trans left.extent right.extent, ?_, ?_, ?_⟩
  · intro query member
    rcases List.mem_append.mp member with before | after
    · have range := left.range query before
      exact ⟨range.1, Nat.lt_of_lt_of_le range.2 right.extent⟩
    · have range := right.range query after
      exact ⟨Nat.le_trans left.extent range.1, range.2⟩
  · intro query member
    rcases List.mem_append.mp member with before | after
    · exact left.boolean query before
    · exact right.boolean query after
  · intro slot
    rw [queryCount_append]
    by_cases before : slot < middle
    · rw [right.outside slot (Or.inl before), Nat.add_zero]
      exact left.count slot
    · rw [left.outside slot (Or.inr (by omega)), Nat.zero_add]
      exact right.count slot

theorem QuerySlots.single (gate : G) (slot : Nat) (message : List G)
    (boolean : booleanConstraint gate = 0) :
    QuerySlots gate slot (slot + 1) [⟨slot, gate, message⟩] := by
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro query member
    have same := List.mem_singleton.mp member
    subst query
    exact ⟨Nat.le_refl _, Nat.lt_succ_self slot⟩
  · intro query member
    have same := List.mem_singleton.mp member
    subst query
    exact boolean
  · intro index
    simp only [queryCount, gateCount, List.filter_cons, List.filter_nil,
      Bool.and_eq_true, beq_iff_eq]
    split
    · rename_i selected
      rw [selected.2]
      exact Nat.le_refl 1
    · exact Nat.zero_le _

theorem queryParts_cons (slot : Nat) (gate : G) (message : List G) (queries : List (List G)) :
    queryParts slot gate (message :: queries) =
      ⟨slot, gate, message⟩ :: queryParts (slot + 1) gate queries := by
  simp [queryParts, List.mapIdx_cons, Nat.add_comm, Nat.add_left_comm]

theorem QuerySlots.indexed (gate : G) (slot : Nat) (queries : List (List G))
    (boolean : booleanConstraint gate = 0) :
    QuerySlots gate slot (slot + queries.length) (queryParts slot gate queries) := by
  induction queries generalizing slot with
  | nil => exact QuerySlots.empty gate slot
  | cons message queries ih =>
    rw [queryParts_cons]
    have result := (QuerySlots.single gate slot message boolean).append (ih (slot + 1))
    simpa only [List.singleton_append, List.length_cons, Nat.add_assoc,
      Nat.add_comm 1 queries.length] using result

theorem fold_lookup_start (emissions : List BlockEmission) (start : Nat) :
    start ≤ emissions.foldl (fun current emission => max current emission.lookup) start := by
  induction emissions generalizing start with
  | nil => exact Nat.le_refl _
  | cons emission emissions ih =>
    exact Nat.le_trans (Nat.le_max_left start emission.lookup) (ih _)

theorem fold_lookup_member {emissions : List BlockEmission} {emission : BlockEmission}
    (member : emission ∈ emissions) (start : Nat) :
    emission.lookup ≤ emissions.foldl (fun current emission => max current emission.lookup) start := by
  induction emissions generalizing start with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with equal | tail
    · subst emission
      exact Nat.le_trans (Nat.le_max_right start head.lookup) (fold_lookup_start rest _)
    · exact ih tail _

theorem gateCount_list (gates : List G) : (gates.map gateCount).sum = gates.count 1 := by
  induction gates with
  | nil => rfl
  | cons gate gates ih =>
    by_cases active : gate = 1
    · subst gate
      simp [gateCount, ih, List.count_cons_self, Nat.add_comm]
    · simp [gateCount, active, ih]

theorem selector_gateCount {gates : List G}
    (individual : ∀ gate ∈ gates, booleanConstraint gate = 0)
    (bounded : gates.length < gSize.toNat)
    (combined : booleanConstraint (selectorSum gates) = 0) :
    gates.count 1 = gateCount (selectorSum gates) := by
  have count := selectorSum_n_eq_count
    (fun gate member => G.boolean_of_constraint (individual gate member)) bounded
  rcases G.boolean_of_constraint combined with inactive | active
  · rw [inactive, gateCount_zero]
    exact count.symm.trans (congrArg G.n inactive)
  · rw [active]
    exact count.symm.trans (congrArg G.n active)

theorem queryCount_flatMap_le {α : Type} {source : List α} {emissions : List BlockEmission}
    (gate : α → G) (start : Nat)
    (related : List.Forall₂ (fun item emission =>
      QuerySlots (gate item) start emission.lookup emission.queries) source emissions) (slot : Nat) :
    queryCount (emissions.flatMap (·.queries)) slot ≤ ((source.map gate).map gateCount).sum := by
  induction related with
  | nil => exact Nat.le_refl 0
  | @cons item emission items emissions first rest ih =>
    simp only [List.flatMap_cons, queryCount_append, List.map_cons, List.sum_cons]
    exact Nat.add_le_add (first.count slot) ih

theorem forall₂_right_member {α β : Type} {source : List α} {target : List β}
    {relation : α → β → Prop} (related : List.Forall₂ relation source target)
    {item : β} (member : item ∈ target) : ∃ original ∈ source, relation original item := by
  induction related with
  | nil => cases member
  | @cons head result heads results first rest ih =>
    rcases List.mem_cons.mp member with equal | tail
    · subst item
      exact ⟨head, List.mem_cons_self, first⟩
    · obtain ⟨original, present, evidence⟩ := ih tail
      exact ⟨original, List.mem_cons_of_mem _ present, evidence⟩

theorem QuerySlots.join {α : Type} {source : List α} {emissions : List BlockEmission}
    (gate : α → G) (parent : G) (values : Array RowValue) (column lookup : Nat)
    (related : List.Forall₂ (fun item emission =>
      QuerySlots (gate item) lookup emission.lookup emission.queries) source emissions)
    (count : (source.map gate).count 1 ≤ gateCount parent) :
    QuerySlots parent lookup (joinBlockEmissions values column lookup emissions).lookup
      (joinBlockEmissions values column lookup emissions).queries := by
  refine ⟨fold_lookup_start emissions lookup, ?_, ?_, ?_⟩
  · intro query member
    obtain ⟨emission, emissionMember, queryMember⟩ := List.mem_flatMap.mp member
    obtain ⟨item, _, evidence⟩ := forall₂_right_member related emissionMember
    have range := evidence.range query queryMember
    exact ⟨range.1, Nat.lt_of_lt_of_le range.2 (fold_lookup_member emissionMember lookup)⟩
  · intro query member
    obtain ⟨emission, emissionMember, queryMember⟩ := List.mem_flatMap.mp member
    obtain ⟨item, _, evidence⟩ := forall₂_right_member related emissionMember
    exact evidence.boolean query queryMember
  · intro slot
    have bounded := queryCount_flatMap_le gate lookup related slot
    rw [gateCount_list] at bounded
    exact Nat.le_trans bounded count

end Aiur.AIR
