/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CircuitRowReturns

/-!
A nonzero provider row of the valued circuit model yields a valid
function row from the same bytecode program. The interpreted inputs, rank
bytes and multiplicity agree with the circuit, and its padded provider
message names that same semantic call. All selected call and rank-byte
queries belong to any ambient pool containing the computed circuit pool.

Exact global lookup balance, memory validity, shape and count/layout bounds
remain explicit. This is not yet extraction from native public verification.
-/

namespace Aiur.Bytecode
open Aiur.AIR

theorem Circuit.emitRow_valid_in_pool {tables : LookupTables} {width : Nat} {emissions : List CircuitEmission} {queries : List (List G)}
    (global : GlobalLookups tables width queries)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    (row : Nat → G) (program : Toplevel) (circuit : Circuit)
    {emission : CircuitEmission} (emitted : circuit.emitRow row program = some emission)
    (member : emission ∈ emissions)
    (pooled : circuitQueryPool emissions ⊆ queries)
    (bounded : circuit.members.size < gSize.toNat)
    (bounds : ∀ part ∈ emission.members, part.function.body.rowBounds (part.selector row))
    (shape : ∀ part ∈ emission.members, part.function.body.lookupShapes program none = true)
    (returnBound : ∀ part ∈ emission.members,
      (part.function.body.selectorFlow (part.selector row)).returns.length < gSize.toNat)
    (reserved : 4 ≤ circuit.layout.lookups)
    (limits : ∀ part ∈ emission.members, part.body.lookup ≤ circuit.layout.lookups)
    (single : emission.branchless = true → emission.returns.length ≤ 1)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0)
    (nonzero : emission.multiplicity ≠ 0) :
    ∃ selected ∈ emission.members, ∃ interpreted : FunctionRow,
      interpreted.Valid program (memoryFacts tables.memory) ∧
      interpreted.request.function = selected.functionIndex ∧
      interpreted.request.inputs = rowValues (rowAdvice row 0 selected.function.layout.inputSize) ∧
      interpreted.request.rank = packRank emission.rankBytes ∧
      interpreted.rankBytes = emission.rankBytes ∧
      interpreted.selector = emission.selector ∧ interpreted.multiplicity = emission.multiplicity ∧
      (1, interpreted.request) ∈ emission.returns ∧
      padMessage width (emission.lookup 0).2 = padMessage width (functionMessage interpreted.request) ∧
      selected.body.CallsAt interpreted.calls ∧
      (interpreted.requests.map functionMessage) ⊆ queries ∧
      (interpreted.byteQueries.map rangeMessage) ⊆ queries := by
  obtain ⟨description, indices, source⟩ := circuit.emitRow_spec row program emitted
  have count := congrArg List.length indices
  simp only [List.length_map, Array.length_toList] at count
  have valid : ∀ equation ∈ (circuitEmission row circuit emission.members).equations, equation = 0 := by
    rw [← description]
    exact satisfied
  have slots := circuit.emitRow_querySlots row program emitted bounded bounds reserved limits satisfied
  have inCircuit := slots.circuit_pool member
  have queried : emission.QueriesIn queries := fun query present active =>
    pooled (inCircuit query present active)
  have wholeQueried : (circuitEmission row circuit emission.members).QueriesIn queries := by
    rw [← description]
    exact queried
  have activity := circuitEmission_activity valid
  rw [← description] at activity
  have active := nonzero_multiplicity_selector_one activity nonzero
  obtain ⟨selected, selectedMember, selectedActive, selectedSource⟩ :=
    circuit.emitRow_active_member row program emitted satisfied bounded nonzero
  have bodySatisfied := circuitEmission_member_satisfied valid selectedMember
  have bodyQueried := circuitEmission_member_queried wholeQueried selectedMember
  have selectedActivity : activityConstraint emission.multiplicity
      (selected.function.body.selectorFlow (selected.selector row)).entry = 0 := by
    change activityConstraint emission.multiplicity (selected.entry row) = 0
    rw [selectedActive]
    rw [active] at activity
    exact activity
  obtain ⟨interpreted, interpretedValid, returned, functionEq, inputsEq, rankEq,
      rankBytesEq, selectorEq, multiplicityEq, called, inventory⟩ :=
    selected.function.emitRow_valid global memoryValid canonical program row (selected.selector row)
      selected.functionIndex emission.rankBytes (rowAdvice row 0 selected.function.layout.inputSize)
      _ 4 selectedSource.present (by simp only [rowAdvice, Array.size_ofFn])
      (shape selected selectedMember) (bounds selected selectedMember) selectedSource.emitted
      emission.multiplicity nonzero selectedActivity bodySatisfied bodyQueried
  have returnMember : (1, interpreted.request) ∈ emission.returns := by
    have returnsEq := congrArg CircuitEmission.returns description
    rw [returnsEq]
    exact List.mem_flatMap.mpr ⟨selected, selectedMember, returned⟩
  have message := circuitEmission_return_message source shape (by omega) returnBound valid
    (by rw [← description]; exact active) width
    (by rw [← description]; exact single)
    (by rw [← description]; exact returnMember)
  rw [← description] at message
  have headers := circuitEmission_rank_queried wholeQueried (by rw [← description]; exact active)
  rw [← description] at headers
  refine ⟨selected, selectedMember, interpreted, interpretedValid, functionEq, inputsEq,
    rankEq, rankBytesEq, ?_, multiplicityEq, returnMember, message, called, ?_, ?_⟩
  · exact selectorEq.trans (selectedActive.trans active.symm)
  · intro message member
    simp only [FunctionRow.requests, List.map_map, List.mem_map, Function.comp_def] at member
    obtain ⟨edge, edgeMember, equal⟩ := member
    rw [← equal]
    exact (inventory edge edgeMember).1
  · intro message member
    rw [FunctionRow.byteQueries, List.map_append] at member
    rcases List.mem_append.mp member with header | gap
    · rw [rankBytesEq] at header
      exact headers header
    · obtain ⟨pair, pairMember, messageEq⟩ := List.mem_map.mp gap
      obtain ⟨edge, edgeMember, pairMember⟩ := List.mem_flatMap.mp pairMember
      rw [← messageEq]
      exact (inventory edge edgeMember).2.1 (List.mem_map.mpr ⟨pair, pairMember, rfl⟩)

end Aiur.Bytecode
