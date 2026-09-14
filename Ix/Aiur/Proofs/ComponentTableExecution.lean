/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ComponentCircuitExecution
import Ix.Aiur.Proofs.ComponentGlobalExecution
import Ix.Aiur.Proofs.CircuitTableExecution

/-! Construct component function rows from physical circuit providers in
two stages. Neither the provisional providers nor the final function rows
are assumed to be an honest execution trace. -/

namespace Aiur.AIR
open Bytecode

def CircuitWitness.ComponentEmitted (program : Toplevel) (witness : CircuitWitness) : Prop :=
  witness.circuit.emitComponentRow witness.values program = some witness.emission

def CircuitWitness.QueryRanges (witness : CircuitWitness) : Prop :=
  0 < witness.emission.lookupCount ∧
    ∀ part ∈ witness.emission.queries, 0 < part.slot ∧ part.slot < witness.emission.lookupCount

def CircuitWitness.Constrained (witness : CircuitWitness) : Prop :=
  ∀ part ∈ witness.emission.members, part.function.constrained = true

def FunctionRow.ComponentQueriesIn (program : Toplevel) (queries : List (List G)) (row : FunctionRow) : Prop :=
  row.selector = 1 → row.requests.map functionMessage ⊆ queries ∧
    (row.componentByteQueries program).map rangeMessage ⊆ queries

theorem FunctionRow.inactive_componentValid (program : Toplevel) (memory : Bytecode.AIR.Memory) :
    inactive.ComponentValid program memory := by
  have notActive : inactive.selector ≠ 1 := by
    intro equal
    have bad := congrArg G.n equal
    change 0 = 1 at bad
    omega
  refine ⟨Or.inl rfl, ?_, fun active => False.elim (notActive active),
    fun active => False.elim (notActive active), fun active => False.elim (notActive active), ?_⟩
  · change (0 : G) * (1 - 0) = 0
    rw [G.mul_comm, G.mul_zero]
  · intro edge present
    cases present

theorem FunctionRow.inactive_componentQueried (program : Toplevel) (queries : List (List G)) :
    inactive.ComponentQueriesIn program queries := by
  intro active
  have bad := congrArg G.n active
  change 0 = 1 at bad
  omega

theorem CircuitWitness.component_provider_row {program : Toplevel} (witness : CircuitWitness)
    (emitted : witness.ComponentEmitted program) (satisfied : witness.Satisfied)
    (validated : witness.circuit.validateRowCounts program = true) (shape : witness.Shapes program)
    (width : Nat) : ∃ row : FunctionRow, row.Provides width witness.emission := by
  by_cases zero : witness.emission.multiplicity = 0
  · exact ⟨FunctionRow.inactive, FunctionRow.inactive_provides width zero⟩
  · obtain ⟨request, _, message⟩ := witness.circuit.emitComponentRow_provider witness.values program
      emitted validated shape satisfied zero width
    exact ⟨⟨request, [], witness.emission.rankBytes, 0, witness.emission.multiplicity⟩,
      rfl, fun _ => message⟩

theorem CircuitWitness.component_interpreted_row {tables : LookupTables} {width : Nat}
    {queries : List (List G)} {emissions : List CircuitEmission}
    (global : GlobalLookups tables width queries)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    {program : Toplevel} (components : program.validCallComponents = true) (witness : CircuitWitness)
    (emitted : witness.ComponentEmitted program) (satisfied : witness.Satisfied)
    (validated : witness.circuit.validateRowCounts program = true) (shape : witness.Shapes program)
    (constrained : witness.Constrained) (ranges : witness.QueryRanges) (member : witness.emission ∈ emissions)
    (pooled : circuitQueryPool emissions ⊆ queries) :
    ∃ row : FunctionRow, row.ComponentValid program (memoryFacts tables.memory) ∧
      row.Provides width witness.emission ∧ row.ComponentQueriesIn program queries := by
  by_cases zero : witness.emission.multiplicity = 0
  · exact ⟨FunctionRow.inactive, FunctionRow.inactive_componentValid _ _,
      FunctionRow.inactive_provides width zero, FunctionRow.inactive_componentQueried program queries⟩
  · obtain ⟨_, _, row, valid, _, _, _, _, _, multiplicity, _, message, _, called, bytes⟩ :=
      witness.circuit.emitComponentRow_valid_in_pool global memoryValid canonical witness.values program components
        emitted member pooled validated shape constrained ranges.1 ranges.2 satisfied zero
    exact ⟨row, valid, ⟨multiplicity.symm, fun _ => message⟩, fun _ => ⟨called, bytes⟩⟩

theorem componentFunctionQueries_in_pool {program : Toplevel} {queries : List (List G)}
    {roots : List Bytecode.AIR.Call} {rows : List FunctionRow}
    (rootQueries : roots.map functionMessage ⊆ queries)
    (queried : ∀ row ∈ rows, row.ComponentQueriesIn program queries) :
    (functionQueries roots rows).map functionMessage ⊆ queries := by
  intro message present
  obtain ⟨request, requestPresent, equal⟩ := List.mem_map.mp present
  subst message
  rcases List.mem_append.mp requestPresent with root | called
  · exact rootQueries (List.mem_map.mpr ⟨request, root, rfl⟩)
  · obtain ⟨row, rowMember, callMember⟩ := List.mem_flatMap.mp called
    by_cases active : row.selector = 1
    · rw [if_pos active] at callMember
      exact (queried row rowMember active).1 (List.mem_map.mpr ⟨request, callMember, rfl⟩)
    · rw [if_neg active] at callMember
      cases callMember

theorem componentFunctionByteQueries_in_pool {program : Toplevel} {queries : List (List G)}
    {rows : List FunctionRow} (queried : ∀ row ∈ rows, row.ComponentQueriesIn program queries) :
    (componentFunctionByteQueries program rows).map rangeMessage ⊆ queries := by
  intro message present
  obtain ⟨pair, pairMember, equal⟩ := List.mem_map.mp present
  subst message
  obtain ⟨row, rowMember, queryMember⟩ := List.mem_flatMap.mp pairMember
  by_cases active : row.selector = 1
  · rw [if_pos active] at queryMember
    exact (queried row rowMember active).2 (List.mem_map.mpr ⟨pair, queryMember, rfl⟩)
  · rw [if_neg active] at queryMember
    cases queryMember

theorem componentCircuitWitnesses_interpret (tables : AuxiliaryTables) {program : Toplevel}
    (witnesses : List CircuitWitness) {width : Nat} {queries : List (List G)}
    (balanced : PaddedLookupBalance width queries (tables.circuitProviders (witnesses.map (·.emission))))
    (bounded : queries.length < gSize.toNat) (widths : ∀ query ∈ queries, query.length ≤ width)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    (components : program.validCallComponents = true) (counted : program.validateRowCounts = true)
    (circuits : ∀ witness ∈ witnesses, witness.circuit ∈ program.circuits)
    (emitted : ∀ witness ∈ witnesses, witness.ComponentEmitted program)
    (satisfied : ∀ witness ∈ witnesses, witness.Satisfied)
    (shapes : ∀ witness ∈ witnesses, witness.Shapes program)
    (constrained : ∀ witness ∈ witnesses, witness.Constrained)
    (ranges : ∀ witness ∈ witnesses, witness.QueryRanges)
    (pooled : circuitQueryPool (witnesses.map (·.emission)) ⊆ queries) :
    ∃ functions : List FunctionRow,
      List.Forall₂ (FunctionRow.Provides width) (witnesses.map (·.emission)) functions ∧
      GlobalLookups (tables.withFunctions functions) width queries ∧
      (∀ row ∈ functions, row.ComponentValid program (memoryFacts tables.memory)) ∧
      (∀ row ∈ functions, row.ComponentQueriesIn program queries) := by
  have counts := fun witness member => Toplevel.validateRowCounts_circuit counted (circuits witness member)
  obtain ⟨provisional, providers⟩ := forall₂_exists_right witnesses
    (fun witness (row : FunctionRow) => row.Provides width witness.emission)
    (fun witness member => witness.component_provider_row (emitted witness member) (satisfied witness member)
      (counts witness member) (shapes witness member) width)
  have providerRows := forall₂_map_left providers
  have global := tables.global_of_circuit_balance balanced bounded widths providerRows
  obtain ⟨functions, interpreted⟩ := forall₂_exists_right witnesses
    (fun witness (row : FunctionRow) => row.ComponentValid program (memoryFacts tables.memory) ∧
      row.Provides width witness.emission ∧ row.ComponentQueriesIn program queries)
    (fun witness member => witness.component_interpreted_row global memoryValid canonical components
      (emitted witness member) (satisfied witness member) (counts witness member) (shapes witness member)
      (constrained witness member) (ranges witness member) (List.mem_map.mpr ⟨witness, member, rfl⟩) pooled)
  have provided : List.Forall₂ (FunctionRow.Provides width) (witnesses.map (·.emission)) functions := by
    apply forall₂_map_left
    exact forall₂_weaken interpreted (fun _ _ evidence => evidence.2.1)
  refine ⟨functions, provided, tables.global_of_circuit_balance balanced bounded widths provided, ?_, ?_⟩
  · intro row member
    obtain ⟨witness, _, evidence⟩ := forall₂_right_member interpreted member
    exact evidence.1
  · intro row member
    obtain ⟨witness, _, evidence⟩ := forall₂_right_member interpreted member
    exact evidence.2.2

theorem componentCircuitWitnesses_execute (tables : AuxiliaryTables) {program : Toplevel}
    (witnesses : List CircuitWitness) {width : Nat} {queries : List (List G)}
    (balanced : PaddedLookupBalance width queries (tables.circuitProviders (witnesses.map (·.emission))))
    (bounded : queries.length < gSize.toNat) (widths : ∀ query ∈ queries, query.length ≤ width)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    (components : program.validCallComponents = true) (counted : program.validateRowCounts = true)
    (programShapes : program.validateLookupShapes = true)
    (circuits : ∀ witness ∈ witnesses, witness.circuit ∈ program.circuits)
    (emitted : ∀ witness ∈ witnesses, witness.ComponentEmitted program)
    (satisfied : ∀ witness ∈ witnesses, witness.Satisfied)
    (shapes : ∀ witness ∈ witnesses, witness.Shapes program)
    (constrained : ∀ witness ∈ witnesses, witness.Constrained)
    (ranges : ∀ witness ∈ witnesses, witness.QueryRanges)
    (pooled : circuitQueryPool (witnesses.map (·.emission)) ⊆ queries)
    {request : Bytecode.AIR.Call} (shape : request.LookupShape program) (root : functionMessage request ∈ queries) :
    Bytecode.AIR.Execution program (memoryFacts tables.memory) request := by
  obtain ⟨functions, _, global, valid, queried⟩ := componentCircuitWitnesses_interpret tables witnesses
    balanced bounded widths memoryValid canonical components counted circuits emitted satisfied shapes constrained ranges pooled
  apply global.component_roots_execute (roots := [request]) components programShapes valid
    (componentFunctionQueries_in_pool ?_ queried) (componentFunctionByteQueries_in_pool queried) shape List.mem_cons_self
  intro message member
  have equal : message = functionMessage request := List.mem_singleton.mp member
  rwa [equal]

end Aiur.AIR
