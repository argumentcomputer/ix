/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ComponentCircuitCounts
import Ix.Aiur.Proofs.ComponentCircuitQueries

/-! A nonzero component circuit provider yields a locally valid function
row. Its actual call messages and precisely the rank ranges used by the
component order belong to the balanced physical query pool. -/

namespace Aiur.AIR
open Bytecode

theorem componentCircuitEmission_member_queried {row : Nat → G} {program : Toplevel}
    {circuit : Circuit} {members : List MemberEmission} {queries : List (List G)}
    (queried : (componentCircuitEmission row program circuit members).QueriesIn queries)
    {member : MemberEmission} (present : member ∈ members) : member.body.QueriesIn queries := by
  intro query queryPresent active
  exact queried query (List.mem_append_left _ (List.mem_flatMap.mpr ⟨member, present, queryPresent⟩)) active

theorem componentCircuitEmission_rank_active {row : Nat → G} {rank : G} {base : Nat}
    {program : Toplevel} {circuit : Circuit} {members : List MemberEmission}
    (source : ∀ member ∈ members, member.FromComponent row rank base program)
    (count : members.length = circuit.members.size) (bounded : circuit.members.size < gSize.toNat)
    (satisfied : ∀ equation ∈ (componentCircuitEmission row program circuit members).equations, equation = 0)
    {member : MemberEmission} (present : member ∈ members)
    (ranked : (program.componentFor member.functionIndex).ranked = true) (active : member.entry row = 1) :
    selectorSum ((componentMembers program members).map (·.entry row)) = 1 := by
  have individual : ∀ gate ∈ (componentMembers program members).map (·.entry row), gate = 0 ∨ gate = 1 := by
    intro gate gatePresent
    obtain ⟨part, partPresent, same⟩ := List.mem_map.mp gatePresent
    subst gate
    exact G.boolean_of_constraint
      (componentCircuitEmission_member_boolean source satisfied part (List.mem_filter.mp partPresent).1)
  have inside : (1 : G) ∈ (componentMembers program members).map (·.entry row) :=
    List.mem_map.mpr ⟨member, List.mem_filter.mpr ⟨present, ranked⟩, active⟩
  have counts := componentCircuitEmission_rank_count source count bounded satisfied
  rw [gateCount_list] at counts
  have positive := List.count_pos_iff.mpr inside
  have limit := gateCount_le_one (selectorSum ((componentMembers program members).map (·.entry row)))
  have one : ((componentMembers program members).map (·.entry row)).count 1 = 1 := by omega
  rw [selectorSum_eq_count _ individual, one]
  rfl

theorem componentCircuitEmission_rank_queried {row : Nat → G} {rank : G} {base : Nat}
    {program : Toplevel} {circuit : Circuit} {members : List MemberEmission} {queries : List (List G)}
    (source : ∀ member ∈ members, member.FromComponent row rank base program)
    (count : members.length = circuit.members.size) (bounded : circuit.members.size < gSize.toNat)
    (satisfied : ∀ equation ∈ (componentCircuitEmission row program circuit members).equations, equation = 0)
    (queried : (componentCircuitEmission row program circuit members).QueriesIn queries)
    {member : MemberEmission} (present : member ∈ members)
    (ranked : (program.componentFor member.functionIndex).ranked = true) (active : member.entry row = 1) :
    (rankByteQueries (componentCircuitEmission row program circuit members).rankBytes).map rangeMessage ⊆ queries := by
  have rankActive := componentCircuitEmission_rank_active source count bounded satisfied present ranked active
  have inside : member ∈ componentMembers program members := List.mem_filter.mpr ⟨present, ranked⟩
  have nonempty := List.isEmpty_eq_false_iff_exists_mem.mpr ⟨member, inside⟩
  simp only [componentCircuitEmission, nonempty, Bool.false_eq_true, if_false] at queried ⊢
  intro message messagePresent
  obtain ⟨part, partPresent, selectorEq, messageEq⟩ :=
    queryParts_member 1 (selectorSum ((componentMembers program members).map (·.entry row))) messagePresent
  have found := queried part (List.mem_append_right _ partPresent) (selectorEq.trans rankActive)
  rwa [messageEq] at found

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

theorem Circuit.emitComponentRow_valid_in_pool {tables : LookupTables} {width : Nat}
    {emissions : List CircuitEmission} {queries : List (List G)}
    (global : GlobalLookups tables width queries)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    (row : Nat → G) (program : Toplevel) (components : program.validCallComponents = true) (circuit : Circuit)
    {emission : CircuitEmission} (emitted : circuit.emitComponentRow row program = some emission)
    (member : emission ∈ emissions) (pooled : circuitQueryPool emissions ⊆ queries)
    (validated : circuit.validateRowCounts program = true)
    (shape : ∀ part ∈ emission.members, part.function.body.lookupShapes program none = true)
    (constrained : ∀ part ∈ emission.members, part.function.constrained = true)
    (reserved : 0 < emission.lookupCount)
    (ranges : ∀ part ∈ emission.queries, 0 < part.slot ∧ part.slot < emission.lookupCount)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0) (nonzero : emission.multiplicity ≠ 0) :
    ∃ selected ∈ emission.members, ∃ interpreted : FunctionRow,
      interpreted.ComponentValid program (memoryFacts tables.memory) ∧
      interpreted.request.function = selected.functionIndex ∧
      interpreted.request.inputs = rowValues (rowAdvice row 0 selected.function.layout.inputSize) ∧
      interpreted.request.rank = program.componentRowRank selected.functionIndex emission.rankBytes ∧
      interpreted.rankBytes = emission.rankBytes ∧
      interpreted.selector = emission.selector ∧ interpreted.multiplicity = emission.multiplicity ∧
      (1, interpreted.request) ∈ emission.returns ∧
      padMessage width (emission.lookup 0).2 = padMessage width (functionMessage interpreted.request) ∧
      selected.body.CallsAt interpreted.calls ∧
      (interpreted.requests.map functionMessage) ⊆ queries ∧
      ((interpreted.componentByteQueries program).map rangeMessage) ⊆ queries := by
  obtain ⟨bounded, bounds, returnBound, single⟩ := circuit.emitComponentRow_count_bounds row program emitted validated satisfied
  obtain ⟨description, indices, source⟩ := circuit.emitComponentRow_spec row program emitted
  have count := congrArg List.length indices
  simp only [List.length_map, Array.length_toList] at count
  have valid : ∀ equation ∈ (componentCircuitEmission row program circuit emission.members).equations, equation = 0 := by
    rw [← description]
    exact satisfied
  have slots := circuit.emitComponentRow_querySlots row program emitted bounded bounds reserved ranges satisfied
  have inCircuit := slots.circuit_pool member
  have queried : emission.QueriesIn queries := fun query present active => pooled (inCircuit query present active)
  have wholeQueried : (componentCircuitEmission row program circuit emission.members).QueriesIn queries := by
    rw [← description]
    exact queried
  have activity := circuitEmission_activity valid
  change activityConstraint (componentCircuitEmission row program circuit emission.members).multiplicity
    (componentCircuitEmission row program circuit emission.members).selector = 0 at activity
  rw [← description] at activity
  have active := nonzero_multiplicity_selector_one activity nonzero
  obtain ⟨selected, selectedMember, selectedActive, selectedSource⟩ :=
    circuit.emitComponentRow_active_member row program emitted satisfied bounded nonzero
  have bodySatisfied := circuitEmission_member_satisfied valid selectedMember
  have bodyQueried := componentCircuitEmission_member_queried wholeQueried selectedMember
  have selectedActivity : activityConstraint emission.multiplicity
      (selected.function.body.selectorFlow (selected.selector row)).entry = 0 := by
    change activityConstraint emission.multiplicity (selected.entry row) = 0
    rw [selectedActive]
    rw [active] at activity
    exact activity
  obtain ⟨interpreted, interpretedValid, returned, functionEq, inputsEq, rankEq,
      rankBytesEq, selectorEq, multiplicityEq, called, inventory⟩ :=
    selected.function.emitRow_componentValid global memoryValid canonical program components row (selected.selector row)
      selected.functionIndex emission.rankBytes (rowAdvice row 0 selected.function.layout.inputSize)
      _ _ selectedSource.present (constrained selected selectedMember) (by simp only [rowAdvice, Array.size_ofFn])
      (shape selected selectedMember) (bounds selected selectedMember) selectedSource.emitted
      emission.multiplicity nonzero selectedActivity bodySatisfied bodyQueried
  have interpretedActive : interpreted.selector = 1 := selectorEq.trans selectedActive
  have returnMember : (1, interpreted.request) ∈ emission.returns := by
    have returnsEq := congrArg CircuitEmission.returns description
    rw [returnsEq]
    exact List.mem_flatMap.mpr ⟨selected, selectedMember, returned⟩
  have message := componentCircuitEmission_return_message source shape (by omega) returnBound valid
    (by rw [← description]; exact active) width
    (by rw [← description]; exact single) (by rw [← description]; exact returnMember)
  rw [← description] at message
  refine ⟨selected, selectedMember, interpreted, interpretedValid, functionEq, inputsEq, rankEq,
    rankBytesEq, interpretedActive.trans active.symm, multiplicityEq, returnMember, message, called, ?_, ?_⟩
  · intro message present
    simp only [FunctionRow.requests, List.map_map, List.mem_map, Function.comp_def] at present
    obtain ⟨edge, edgeMember, same⟩ := present
    rw [← same]
    exact (inventory edge edgeMember).1
  · intro message present
    rw [FunctionRow.componentByteQueries, List.map_append] at present
    rcases List.mem_append.mp present with header | gap
    · cases ranked : (program.componentFor interpreted.request.function).ranked with
      | false => simp only [ranked, Bool.false_eq_true, if_false, List.map_nil, List.not_mem_nil] at header
      | true =>
        simp only [ranked, if_true, rankBytesEq] at header
        have selectedRanked : (program.componentFor selected.functionIndex).ranked = true := functionEq ▸ ranked
        have headers := componentCircuitEmission_rank_queried source count bounded valid wholeQueried
          selectedMember selectedRanked selectedActive
        rw [← description] at headers
        exact headers header
    · obtain ⟨pair, pairMember, messageEq⟩ := List.mem_map.mp gap
      obtain ⟨edge, edgeMember, pairMember⟩ := List.mem_flatMap.mp pairMember
      split at pairMember
      · rename_i same
        obtain ⟨function, present, functionConstrained⟩ := interpretedValid.constrained interpretedActive
        have componentEdge := (interpretedValid.execution interpretedActive).calls_components components
          present functionConstrained edge.1 (List.mem_map.mpr ⟨edge, edgeMember, rfl⟩)
        have mode := componentEdge.rankMode same
        rw [functionEq] at mode
        rw [← messageEq]
        exact ((inventory edge edgeMember).2.ordered mode).1 (List.mem_map.mpr ⟨pair, pairMember, rfl⟩)
      · cases pairMember

end Aiur.Bytecode
