/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.BranchlessSlots
import Ix.Aiur.Proofs.PublicCircuitExecution

/-! Encoded circuit consumer messages give the same padded query pool
and query count as decoded active operations. Their physical message widths
bound the decoded widths. This connects valued slot balance to execution
of the selected public success call without a single-writer assumption.
Native trace extraction and the cryptographic reduction remain separate. -/

namespace Aiur.AIR
open Bytecode

theorem gateMessage_length (branchless : Bool) (gate : G) (message : List G) :
    (gateMessage branchless gate message).length = message.length := by
  cases branchless <;> simp only [gateMessage, Bool.false_eq_true, if_false,
    scaleMessage, List.length_map, if_true]

private theorem slotMessage_fold_start (branchless : Bool) (parts : List (G × List G)) (start : List G) :
    start.length ≤ (parts.foldl (fun combined part => addMessages combined
      (gateMessage branchless part.1 part.2)) start).length := by
  induction parts generalizing start with
  | nil => exact Nat.le_refl _
  | cons part rest ih =>
    have step := ih (addMessages start (gateMessage branchless part.1 part.2))
    simp only [List.foldl_cons]
    apply Nat.le_trans _ step
    rw [addMessages_length]
    exact Nat.le_max_left _ _

private theorem slotMessage_fold_member (branchless : Bool) {parts : List (G × List G)}
    {part : G × List G} (member : part ∈ parts) (start : List G) :
    part.2.length ≤ (parts.foldl (fun combined part => addMessages combined
      (gateMessage branchless part.1 part.2)) start).length := by
  induction parts generalizing start with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with equal | later
    · subst part
      apply Nat.le_trans _ (slotMessage_fold_start branchless rest _)
      rw [addMessages_length, gateMessage_length]
      exact Nat.le_max_right _ _
    · exact ih later _

theorem slotMessage_member_length (branchless : Bool) {parts : List (G × List G)}
    {part : G × List G} (member : part ∈ parts) : part.2.length ≤ (slotMessage branchless parts).length :=
  slotMessage_fold_member branchless member []

theorem QuerySlots.encoded_member {gate : G} {start finish : Nat} {queries : List QueryPart}
    (slots : QuerySlots gate start finish queries) (branchless : Bool)
    {query : QueryPart} (member : query ∈ queries) (active : query.selector = 1) :
    slotMessage branchless (querySlotParts queries query.slot) ∈ encodedQueries branchless queries finish := by
  have count : queryCount queries query.slot = 1 := congrArg List.length (slots.active_singleton member active)
  have multiplicity : querySlotMultiplicity queries query.slot = 1 := by
    rw [slots.slot_multiplicity, count]
    rfl
  apply List.mem_filterMap.mpr
  refine ⟨query.slot, List.mem_range.mpr (slots.range query member).2, ?_⟩
  simp only [encodedQuery, multiplicity, if_true]

theorem QuerySlots.decoded_widths {gate : G} {start finish : Nat} {queries : List QueryPart}
    (slots : QuerySlots gate start finish queries) (branchless : Bool) (width : Nat)
    (widths : ∀ message ∈ encodedQueries branchless queries finish, message.length ≤ width) :
    ∀ message ∈ decodedQueries queries finish, message.length ≤ width := by
  intro message present
  obtain ⟨slot, _, decoded⟩ := List.mem_filterMap.mp present
  cases found : activeQuerySlot queries slot with
  | nil => simp only [decodedQuery, found, List.head?_nil, Option.map_none, reduceCtorEq] at decoded
  | cons query rest =>
    have member : query ∈ activeQuerySlot queries slot := by rw [found]; exact List.mem_cons_self
    obtain ⟨original, _, active⟩ := by
      simpa only [activeQuerySlot, List.mem_filter, Bool.and_eq_true, beq_iff_eq] using member
    simp only [decodedQuery, found, List.head?_cons, Option.map_some, Option.some.injEq] at decoded
    rw [← decoded]
    exact Nat.le_trans (slotMessage_member_length branchless (querySlotParts_member original))
      (widths _ (slots.encoded_member branchless original active))

/-- Unit consumers encoded by the valued circuit's physical lookup slots.
The return provider is kept separately in `circuitProviders`. -/
def encodedCircuitQueryPool (emissions : List CircuitEmission) : List (List G) :=
  emissions.flatMap fun emission => encodedQueries emission.branchless emission.queries emission.lookupCount

theorem circuitWitnesses_queries_reflect {program : Toplevel} (witnesses : List CircuitWitness)
    (counted : program.validateRowCounts = true)
    (circuits : ∀ witness ∈ witnesses, witness.circuit ∈ program.circuits)
    (emitted : ∀ witness ∈ witnesses, witness.Emitted program)
    (satisfied : ∀ witness ∈ witnesses, witness.Satisfied)
    (limits : ∀ witness ∈ witnesses, witness.LookupBounds) (width : Nat) :
    (encodedCircuitQueryPool (witnesses.map (·.emission))).map (padMessage width) =
      (circuitQueryPool (witnesses.map (·.emission))).map (padMessage width) := by
  simp only [encodedCircuitQueryPool, circuitQueryPool, List.map_flatMap]
  rw [List.flatMap, List.flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro emission member
  obtain ⟨witness, witnessMember, equal⟩ := List.mem_map.mp member
  subst emission
  exact witness.circuit.emitRow_queries_reflect witness.values program (emitted witness witnessMember)
    (Toplevel.validateRowCounts_circuit counted (circuits witness witnessMember))
    (limits witness witnessMember).1 (limits witness witnessMember).2 (satisfied witness witnessMember) width

theorem circuitWitnesses_decoded_widths {program : Toplevel} (witnesses : List CircuitWitness)
    (counted : program.validateRowCounts = true)
    (circuits : ∀ witness ∈ witnesses, witness.circuit ∈ program.circuits)
    (emitted : ∀ witness ∈ witnesses, witness.Emitted program)
    (satisfied : ∀ witness ∈ witnesses, witness.Satisfied)
    (limits : ∀ witness ∈ witnesses, witness.LookupBounds) (width : Nat)
    (widths : ∀ query ∈ encodedCircuitQueryPool (witnesses.map (·.emission)), query.length ≤ width) :
    ∀ query ∈ circuitQueryPool (witnesses.map (·.emission)), query.length ≤ width := by
  intro query member
  obtain ⟨emission, emissionMember, queryMember⟩ := List.mem_flatMap.mp member
  obtain ⟨witness, witnessMember, equal⟩ := List.mem_map.mp emissionMember
  subst emission
  obtain ⟨bounded, bounds, _, _⟩ := witness.circuit.emitRow_count_bounds witness.values program
    (emitted witness witnessMember) (Toplevel.validateRowCounts_circuit counted (circuits witness witnessMember))
    (satisfied witness witnessMember)
  have slots := witness.circuit.emitRow_querySlots witness.values program (emitted witness witnessMember)
    bounded bounds (limits witness witnessMember).1 (limits witness witnessMember).2 (satisfied witness witnessMember)
  exact slots.decoded_widths witness.emission.branchless width
    (fun message present => widths message (List.mem_flatMap.mpr
      ⟨witness.emission, List.mem_map.mpr ⟨witness, witnessMember, rfl⟩, present⟩)) query queryMember

end Aiur.AIR

namespace Aiur.BoundVerifier
open AIR Bytecode.AIR

theorem Backend.encoded_circuit_execution {selection : Selection} (backend : Backend selection)
    (tables : AuxiliaryTables) (witnesses : List CircuitWitness) (width : Nat)
    (input : Array G) (arity : input.size = selection.inputSize)
    (balanced : PaddedLookupBalance width
      ((buildClaim selection.function input selection.success).toList ::
        encodedCircuitQueryPool (witnesses.map (·.emission)))
      (tables.circuitProviders (witnesses.map (·.emission))))
    (bounded : (encodedCircuitQueryPool (witnesses.map (·.emission))).length + 1 < gSize.toNat)
    (publicWidth : (buildClaim selection.function input selection.success).size + 1 ≤ width)
    (queryWidths : ∀ query ∈ encodedCircuitQueryPool (witnesses.map (·.emission)), query.length ≤ width)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    (circuits : ∀ witness ∈ witnesses, witness.circuit ∈ backend.compiled.bytecode.circuits)
    (emitted : ∀ witness ∈ witnesses, witness.Emitted backend.compiled.bytecode)
    (satisfied : ∀ witness ∈ witnesses, witness.Satisfied)
    (shapes : ∀ witness ∈ witnesses, witness.Shapes backend.compiled.bytecode)
    (limits : ∀ witness ∈ witnesses, witness.LookupBounds) :
    Execution backend.compiled.bytecode (memoryFacts tables.memory)
      ⟨selection.function, input, selection.success, 0⟩ := by
  have messages := circuitWitnesses_queries_reflect witnesses backend.rowCounts circuits emitted satisfied limits width
  have lengths := congrArg List.length messages
  simp only [List.length_map] at lengths
  apply backend.public_circuit_execution tables witnesses width input arity
    (balanced.congr_queries (by simp only [List.map_cons, messages])) (by rwa [← lengths]) publicWidth
    (circuitWitnesses_decoded_widths witnesses backend.rowCounts circuits emitted satisfied limits width queryWidths)
    memoryValid canonical circuits emitted satisfied shapes limits

end Aiur.BoundVerifier
