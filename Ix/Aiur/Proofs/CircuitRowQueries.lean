/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CircuitRowMembers

/-!
Shared-slot extraction across circuit members and the three reserved
rank-byte lookup slots. Validated body bounds and lookup cursor limits give
one active query per physical slot and a computed circuit query pool.
Native layout enforcement and verifier-to-valued-model reflection remain
separate.
-/

namespace Aiur.AIR
open Bytecode

theorem QuerySlots.extend {gate : G} {start finish limit : Nat} {queries : List QueryPart}
    (slots : QuerySlots gate start finish queries) (bound : finish ≤ limit) :
    QuerySlots gate start limit queries :=
  ⟨Nat.le_trans slots.extent bound,
    fun query member => ⟨(slots.range query member).1, Nat.lt_of_lt_of_le (slots.range query member).2 bound⟩,
    slots.boolean, slots.count⟩

theorem QuerySlots.permuted {gate : G} {start finish : Nat} {queries other : List QueryPart}
    (slots : QuerySlots gate start finish queries) (permutation : queries.Perm other) :
    QuerySlots gate start finish other := by
  refine ⟨slots.extent, ?_, ?_, ?_⟩
  · exact fun query member => slots.range query (permutation.mem_iff.mpr member)
  · exact fun query member => slots.boolean query (permutation.mem_iff.mpr member)
  · intro slot
    have counts : queryCount queries slot = queryCount other slot := (permutation.filter _).length_eq
    rw [← counts]
    exact slots.count slot

theorem fold_lookup_upper (emissions : List BlockEmission) (start limit : Nat)
    (initial : start ≤ limit) (bounded : ∀ emission ∈ emissions, emission.lookup ≤ limit) :
    emissions.foldl (fun current emission => max current emission.lookup) start ≤ limit := by
  induction emissions generalizing start with
  | nil => exact initial
  | cons emission rest ih =>
    apply ih
    · exact Nat.max_le.mpr ⟨initial, bounded emission List.mem_cons_self⟩
    · exact fun item member => bounded item (List.mem_cons_of_mem _ member)

theorem forall₂_self_map {α β : Type} (items : List α) (map : α → β) (relation : α → β → Prop)
    (related : ∀ item ∈ items, relation item (map item)) : List.Forall₂ relation items (items.map map) := by
  induction items with
  | nil => exact .nil
  | cons item rest ih =>
    exact .cons (related item List.mem_cons_self) (ih (fun item member => related item (List.mem_cons_of_mem _ member)))

theorem MemberEmission.FromProgram.querySlots {row : Nat → G} {rank : G} {column lookup : Nat}
    {program : Toplevel} {member : MemberEmission} (source : member.FromProgram row rank column lookup program)
    (bounds : member.function.body.rowBounds (member.selector row))
    (satisfied : ∀ equation ∈ member.body.equations, equation = 0) :
    QuerySlots (member.entry row) lookup member.body.lookup member.body.queries := by
  have emitted := source.emitted
  rw [Bytecode.Function.emitRow] at emitted
  exact member.function.body.emitRow_equation_querySlots row (member.selector row) _ _ _ _ _ bounds emitted rfl satisfied

theorem circuitEmission_querySlots {row : Nat → G} {rank : G} {column : Nat}
    {program : Toplevel} {circuit : Circuit} {members : List MemberEmission}
    (source : ∀ member ∈ members, member.FromProgram row rank column 4 program)
    (count : members.length = circuit.members.size)
    (bounded : circuit.members.size < gSize.toNat)
    (bounds : ∀ member ∈ members, member.function.body.rowBounds (member.selector row))
    (reserved : 4 ≤ circuit.layout.lookups)
    (limits : ∀ member ∈ members, member.body.lookup ≤ circuit.layout.lookups)
    (satisfied : ∀ equation ∈ (circuitEmission row circuit members).equations, equation = 0) :
    QuerySlots (circuitEmission row circuit members).selector 1 circuit.layout.lookups
      (circuitEmission row circuit members).queries := by
  by_cases empty : members = []
  · subst members
    exact (QuerySlots.empty 0 1).extend (by omega)
  have nonempty : members.isEmpty = false := by cases members <;> simp_all
  have boolean := circuitEmission_boolean source count satisfied
  have individual := circuitEmission_member_boolean source satisfied
  have slots : ∀ member ∈ members, QuerySlots (member.entry row) 4 member.body.lookup member.body.queries :=
    fun member present => (source member present).querySlots (bounds member present)
      (circuitEmission_member_satisfied satisfied present)
  have related := forall₂_self_map members MemberEmission.body
    (fun member body => QuerySlots (member.entry row) 4 body.lookup body.queries) slots
  have selectorCount := selector_gateCount
    (gates := members.map (fun member : MemberEmission => member.entry row))
    (fun gate member => by
      obtain ⟨part, partMember, equal⟩ := List.mem_map.mp member
      subst gate
      exact individual part partMember)
    (by simpa only [List.length_map, count] using bounded) boolean
  have joined := QuerySlots.join (fun member : MemberEmission => member.entry row)
    (circuitEmission row circuit members).selector #[] 0 4 related (Nat.le_of_eq selectorCount)
  have upper : (joinBlockEmissions #[] 0 4 (members.map MemberEmission.body)).lookup ≤ circuit.layout.lookups := by
    apply fold_lookup_upper _ _ _ reserved
    intro body member
    obtain ⟨part, partMember, equal⟩ := List.mem_map.mp member
    subst body
    exact limits part partMember
  have bodies := joined.extend upper
  have rankSlots : QuerySlots (circuitEmission row circuit members).selector 1 4
      (queryParts 1 (circuitEmission row circuit members).selector
        ((rankByteQueries (circuitRankBytes row circuit.layout)).map rangeMessage)) :=
    QuerySlots.indexed _ 1 ((rankByteQueries (circuitRankBytes row circuit.layout)).map rangeMessage) boolean
  have combined := (rankSlots.append bodies).permuted List.perm_append_comm
  simpa only [joinBlockEmissions, List.flatMap_map, Function.comp_def, circuitEmission,
    nonempty, Bool.false_eq_true, if_false] using combined

def CircuitEmission.QueriesIn (emission : CircuitEmission) (queries : List (List G)) : Prop :=
  ∀ part ∈ emission.queries, part.selector = 1 → part.message ∈ queries

def circuitQueryPool (emissions : List CircuitEmission) : List (List G) :=
  emissions.flatMap fun emission => decodedQueries emission.queries emission.lookupCount

theorem QuerySlots.circuit_pool {emission : CircuitEmission}
    (slots : QuerySlots emission.selector 1 emission.lookupCount emission.queries)
    {emissions : List CircuitEmission} (member : emission ∈ emissions) :
    emission.QueriesIn (circuitQueryPool emissions) := by
  intro query present active
  exact List.mem_flatMap.mpr ⟨emission, member, slots.decoded_member present active⟩

theorem circuitEmission_member_queried {row : Nat → G} {circuit : Circuit} {members : List MemberEmission}
    {queries : List (List G)} (queried : (circuitEmission row circuit members).QueriesIn queries)
    {member : MemberEmission} (present : member ∈ members) : member.body.QueriesIn queries := by
  intro query member active
  exact queried query (List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, present, member⟩)) active

theorem circuitEmission_rank_queried {row : Nat → G} {circuit : Circuit} {members : List MemberEmission}
    {queries : List (List G)} (queried : (circuitEmission row circuit members).QueriesIn queries)
    (active : (circuitEmission row circuit members).selector = 1) :
    (rankByteQueries (circuitEmission row circuit members).rankBytes).map rangeMessage ⊆ queries := by
  have nonempty : members.isEmpty = false := by
    cases members with
    | nil => exact False.elim (G.one_ne_zero active.symm)
    | cons => rfl
  simp only [CircuitEmission.QueriesIn, circuitEmission, nonempty, Bool.false_eq_true, if_false] at queried
  intro message member
  obtain ⟨part, partMember, selectorEq, messageEq⟩ :=
    queryParts_member 1 (circuitEmission row circuit members).selector member
  have result := queried part (List.mem_append_right _ partMember) (selectorEq.trans active)
  rw [messageEq] at result
  exact result

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

theorem Circuit.emitRow_querySlots (row : Nat → G) (program : Toplevel) (circuit : Circuit)
    {emission : CircuitEmission} (emitted : circuit.emitRow row program = some emission)
    (bounded : circuit.members.size < gSize.toNat)
    (bounds : ∀ member ∈ emission.members, member.function.body.rowBounds (member.selector row))
    (reserved : 4 ≤ circuit.layout.lookups)
    (limits : ∀ member ∈ emission.members, member.body.lookup ≤ circuit.layout.lookups)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0) :
    QuerySlots emission.selector 1 emission.lookupCount emission.queries := by
  obtain ⟨description, indices, source⟩ := circuit.emitRow_spec row program emitted
  have count := congrArg List.length indices
  simp only [List.length_map, Array.length_toList] at count
  have valid : ∀ equation ∈ (circuitEmission row circuit emission.members).equations, equation = 0 := by
    rw [← description]
    exact satisfied
  have slots := circuitEmission_querySlots source count bounded bounds reserved limits valid
  have lookupEq := congrArg CircuitEmission.lookupCount description
  change emission.lookupCount = circuit.layout.lookups at lookupEq
  rw [← lookupEq] at slots
  rw [← description] at slots
  exact slots

end Aiur.Bytecode
