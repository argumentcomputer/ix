/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ComponentCircuitMembers

/-! Mixed circuits reuse rank slots for acyclic members. Distributing the
rank queries over their member selectors preserves natural active counts,
so member exclusivity still gives at most one active request per slot. -/

namespace Aiur.AIR
open Bytecode

theorem queryCount_singleton (query : QueryPart) (slot : Nat) :
    queryCount [query] slot = if query.slot = slot then gateCount query.selector else 0 := by
  simp only [queryCount, List.filter_cons, List.filter_nil, Bool.and_eq_true, beq_iff_eq, gateCount]
  by_cases equal : query.slot = slot <;> by_cases active : query.selector = 1 <;>
    simp only [equal, active, if_true, if_false, List.length_cons, List.length_nil,
      and_self, and_true, and_false]

theorem queryParts_boolean (gate : G) (messages : List (List G)) (start : Nat)
    (boolean : booleanConstraint gate = 0) :
    ∀ query ∈ queryParts start gate messages, booleanConstraint query.selector = 0 := by
  induction messages generalizing start with
  | nil => simp [queryParts]
  | cons message messages ih =>
    intro query present
    rw [queryParts_cons] at present
    rcases List.mem_cons.mp present with equal | later
    · subst query
      exact boolean
    · exact ih (start + 1) query later

theorem queryCount_queryParts (gate : G) (messages : List (List G)) (start slot : Nat) :
    queryCount (queryParts start gate messages) slot =
      gateCount gate * queryCount (queryParts start 1 messages) slot := by
  induction messages generalizing start with
  | nil => simp [queryParts, queryCount]
  | cons message messages ih =>
    rw [queryParts_cons, queryParts_cons]
    change queryCount ([⟨start, gate, message⟩] ++ queryParts (start + 1) gate messages) slot =
      gateCount gate * queryCount ([⟨start, 1, message⟩] ++ queryParts (start + 1) 1 messages) slot
    rw [queryCount_append, queryCount_append, queryCount_singleton, queryCount_singleton, ih, Nat.mul_add]
    by_cases equal : start = slot <;>
      simp only [equal, if_true, if_false, show gateCount (1 : G) = 1 from rfl, Nat.mul_one, Nat.mul_zero]

theorem queryCount_flatMap_indexed {α : Type} (items : List α) (gate : α → G)
    (messages : List (List G)) (start slot : Nat) :
    queryCount (items.flatMap fun item => queryParts start (gate item) messages) slot =
      ((items.map gate).map gateCount).sum * queryCount (queryParts start 1 messages) slot := by
  induction items with
  | nil => simp [queryCount]
  | cons item items ih =>
    rw [List.flatMap_cons, queryCount_append, queryCount_queryParts, ih]
    simp only [List.map_cons, List.sum_cons, Nat.add_mul]

theorem queryCount_flatMap_append {α : Type} (items : List α) (left right : α → List QueryPart) (slot : Nat) :
    queryCount (items.flatMap fun item => left item ++ right item) slot =
      queryCount (items.flatMap left) slot + queryCount (items.flatMap right) slot := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    simp only [List.flatMap_cons, queryCount_append, ih]
    omega

theorem flatMap_if_filter {α β : Type} (items : List α) (chosen : α → Bool) (parts : α → List β) :
    (items.flatMap fun item => if chosen item then parts item else []) =
      (items.filter chosen).flatMap parts := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    cases selected : chosen item <;>
      simp only [List.flatMap_cons, List.filter_cons, selected, Bool.false_eq_true,
        if_true, if_false, ih, List.nil_append]

theorem queryCount_flatMap_le_sum {α : Type} (items : List α) (parts : α → List QueryPart)
    (gate : α → G) (slot : Nat)
    (bounded : ∀ item ∈ items, queryCount (parts item) slot ≤ gateCount (gate item)) :
    queryCount (items.flatMap parts) slot ≤ ((items.map gate).map gateCount).sum := by
  induction items with
  | nil => exact Nat.le_refl 0
  | cons item items ih =>
    simp only [List.flatMap_cons, queryCount_append, List.map_cons, List.sum_cons]
    exact Nat.add_le_add (bounded item List.mem_cons_self)
      (ih (fun item present => bounded item (List.mem_cons_of_mem _ present)))

def MemberEmission.componentQueries (row : Nat → G) (rankBytes : Fin 6 → G)
    (program : Toplevel) (member : MemberEmission) : List QueryPart :=
  member.body.queries ++ if (program.componentFor member.functionIndex).ranked then
    queryParts 1 (member.entry row) ((rankByteQueries rankBytes).map rangeMessage) else []

theorem MemberEmission.FromComponent.querySlots {row : Nat → G} {rank : G} {base : Nat}
    {program : Toplevel} {member : MemberEmission} (source : member.FromComponent row rank base program)
    (rankBytes : Fin 6 → G) (bounds : member.function.body.rowBounds (member.selector row))
    (satisfied : ∀ equation ∈ member.body.equations, equation = 0) :
    QuerySlots (member.entry row) 1 member.body.lookup (member.componentQueries row rankBytes program) := by
  have bodySlots := MemberEmission.FromProgram.querySlots source bounds satisfied
  have boolean := member.function.body.selectorFlow_boolean (member.selector row)
    (MemberEmission.FromProgram.selector_satisfied source satisfied)
  cases ranked : (program.componentFor member.functionIndex).ranked with
  | false =>
    simpa only [MemberEmission.componentQueries, ranked, Bool.false_eq_true, if_false,
      List.append_nil, componentLookup, Nat.add_zero] using bodySlots
  | true =>
    have rankSlots : QuerySlots (member.entry row) 1 4
        (queryParts 1 (member.entry row) ((rankByteQueries rankBytes).map rangeMessage)) :=
      QuerySlots.indexed (member.entry row) 1 ((rankByteQueries rankBytes).map rangeMessage) boolean
    have combined := (rankSlots.append (by simpa only [componentLookup, ranked, if_true] using bodySlots)).permuted
      List.perm_append_comm
    simpa only [MemberEmission.componentQueries, ranked, if_true] using combined

theorem componentCircuitEmission_queries_count {row : Nat → G} {rank : G} {base : Nat}
    {program : Toplevel} {circuit : Circuit} {members : List MemberEmission}
    (source : ∀ member ∈ members, member.FromComponent row rank base program)
    (count : members.length = circuit.members.size) (bounded : circuit.members.size < gSize.toNat)
    (satisfied : ∀ equation ∈ (componentCircuitEmission row program circuit members).equations, equation = 0)
    (slot : Nat) :
    queryCount (componentCircuitEmission row program circuit members).queries slot =
      queryCount (members.flatMap fun member =>
        member.componentQueries row (circuitRankBytes row circuit.layout) program) slot := by
  unfold MemberEmission.componentQueries
  rw [queryCount_flatMap_append, flatMap_if_filter]
  change queryCount (members.flatMap (·.body.queries) ++
      (if (componentMembers program members).isEmpty then [] else
        queryParts 1 (selectorSum ((componentMembers program members).map (·.entry row)))
          ((rankByteQueries (circuitRankBytes row circuit.layout)).map rangeMessage))) slot = _
  rw [queryCount_append]
  congr 1
  change _ = queryCount ((componentMembers program members).flatMap fun member =>
    queryParts 1 (member.entry row) ((rankByteQueries (circuitRankBytes row circuit.layout)).map rangeMessage)) slot
  cases empty : (componentMembers program members).isEmpty with
  | true =>
    have absent : componentMembers program members = [] := List.isEmpty_iff.mp empty
    simp only [if_true, absent, List.flatMap_nil]
  | false =>
    simp only [Bool.false_eq_true, if_false]
    rw [queryCount_queryParts, queryCount_flatMap_indexed]
    exact congrArg (fun count => count * queryCount
      (queryParts 1 1 ((rankByteQueries (circuitRankBytes row circuit.layout)).map rangeMessage)) slot)
      (componentCircuitEmission_rank_count source count bounded satisfied).symm

theorem componentCircuitEmission_querySlots {row : Nat → G} {rank : G} {base : Nat}
    {program : Toplevel} {circuit : Circuit} {members : List MemberEmission}
    (source : ∀ member ∈ members, member.FromComponent row rank base program)
    (count : members.length = circuit.members.size) (bounded : circuit.members.size < gSize.toNat)
    (bounds : ∀ member ∈ members, member.function.body.rowBounds (member.selector row))
    (reserved : 0 < circuit.layout.lookups)
    (ranges : ∀ part ∈ (componentCircuitEmission row program circuit members).queries,
      0 < part.slot ∧ part.slot < circuit.layout.lookups)
    (satisfied : ∀ equation ∈ (componentCircuitEmission row program circuit members).equations, equation = 0) :
    QuerySlots (componentCircuitEmission row program circuit members).selector 1 circuit.layout.lookups
      (componentCircuitEmission row program circuit members).queries := by
  have each := fun member present => MemberEmission.FromComponent.querySlots (source member present)
    (circuitRankBytes row circuit.layout) (bounds member present) (circuitEmission_member_satisfied satisfied present)
  refine ⟨reserved, fun query present => ⟨(ranges query present).1, (ranges query present).2⟩, ?_, ?_⟩
  · intro query present
    change query ∈ members.flatMap (·.body.queries) ++ _ at present
    rcases List.mem_append.mp present with body | header
    · obtain ⟨member, memberPresent, queryPresent⟩ := List.mem_flatMap.mp body
      exact (each member memberPresent).boolean query (List.mem_append_left _ queryPresent)
    · have rankedBoolean := componentCircuitEmission_rank_boolean source count bounded satisfied
      split at header
      · cases header
      · exact queryParts_boolean _ _ _ rankedBoolean query header
  · intro slot
    rw [componentCircuitEmission_queries_count source count bounded satisfied]
    exact Nat.le_trans (queryCount_flatMap_le_sum members _ (fun member => member.entry row) slot
      (fun member present => (each member present).count slot))
      (Nat.le_of_eq (componentCircuitEmission_gateCount source count bounded satisfied))

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

theorem Circuit.emitComponentRow_querySlots (row : Nat → G) (program : Toplevel) (circuit : Circuit)
    {emission : CircuitEmission} (emitted : circuit.emitComponentRow row program = some emission)
    (bounded : circuit.members.size < gSize.toNat)
    (bounds : ∀ member ∈ emission.members, member.function.body.rowBounds (member.selector row))
    (reserved : 0 < emission.lookupCount)
    (ranges : ∀ part ∈ emission.queries, 0 < part.slot ∧ part.slot < emission.lookupCount)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0) :
    QuerySlots emission.selector 1 emission.lookupCount emission.queries := by
  obtain ⟨description, indices, source⟩ := circuit.emitComponentRow_spec row program emitted
  have count := congrArg List.length indices
  simp only [List.length_map, Array.length_toList] at count
  have lookupEq : emission.lookupCount = circuit.layout.lookups := congrArg CircuitEmission.lookupCount description
  have valid : ∀ equation ∈ (componentCircuitEmission row program circuit emission.members).equations, equation = 0 := by
    rw [← description]
    exact satisfied
  have slots := componentCircuitEmission_querySlots source count bounded bounds
    (lookupEq ▸ reserved) (by rw [← description, ← lookupEq]; exact ranges) valid
  rw [← description, ← lookupEq] at slots
  exact slots

end Aiur.Bytecode
