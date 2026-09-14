/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CircuitTableData

/-! Construct locally valid function rows from valued circuit witnesses and
physical provider balance, then derive finite call executions. The two-stage
construction avoids assuming the validity of the table being extracted.
Native extraction and the explicit layout/shape conditions remain separate. -/

namespace Aiur.AIR
open Bytecode

theorem forall₂_weaken {α β : Type} {left : List α} {right : List β}
    {first second : α → β → Prop} (related : List.Forall₂ first left right)
    (weaken : ∀ a b, first a b → second a b) : List.Forall₂ second left right := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (weaken _ _ head) ih

def FunctionRow.QueriesIn (queries : List (List G)) (row : FunctionRow) : Prop :=
  row.selector = 1 → row.requests.map functionMessage ⊆ queries ∧ row.byteQueries.map rangeMessage ⊆ queries

theorem FunctionRow.inactive_queried (queries : List (List G)) : inactive.QueriesIn queries := by
  intro active
  have bad := congrArg G.n active
  change 0 = 1 at bad
  omega

theorem CircuitWitness.interpreted_row {tables : LookupTables} {width : Nat}
    {queries : List (List G)} {emissions : List CircuitEmission}
    (global : GlobalLookups tables width queries)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    {program : Toplevel} (witness : CircuitWitness)
    (emitted : witness.Emitted program) (satisfied : witness.Satisfied)
    (validated : witness.circuit.validateRowCounts program = true) (shape : witness.Shapes program)
    (limits : witness.LookupBounds) (member : witness.emission ∈ emissions)
    (pooled : circuitQueryPool emissions ⊆ queries) :
    ∃ row : FunctionRow, row.Valid program (memoryFacts tables.memory) ∧
      row.Provides width witness.emission ∧ row.QueriesIn queries := by
  by_cases zero : witness.emission.multiplicity = 0
  · exact ⟨FunctionRow.inactive, FunctionRow.inactive_valid _ _,
      FunctionRow.inactive_provides width zero, FunctionRow.inactive_queried queries⟩
  · obtain ⟨bounded, bounds, returnBound, single⟩ := witness.circuit.emitRow_count_bounds
      witness.values program emitted validated satisfied
    obtain ⟨_, _, row, valid, _, _, _, _, _, multiplicity, _, message, _, called, bytes⟩ :=
      witness.circuit.emitRow_valid_in_pool global memoryValid canonical witness.values program
        emitted member pooled bounded bounds shape returnBound limits.1 limits.2 single satisfied zero
    exact ⟨row, valid, ⟨multiplicity.symm, fun _ => message⟩, fun _ => ⟨called, bytes⟩⟩

theorem functionQueries_in_pool {queries : List (List G)} {roots : List Bytecode.AIR.Call}
    {rows : List FunctionRow} (rootQueries : roots.map functionMessage ⊆ queries)
    (queried : ∀ row ∈ rows, row.QueriesIn queries) :
    (functionQueries roots rows).map functionMessage ⊆ queries := by
  intro message member
  obtain ⟨request, requestMember, equal⟩ := List.mem_map.mp member
  subst message
  rcases List.mem_append.mp requestMember with root | called
  · exact rootQueries (List.mem_map.mpr ⟨request, root, rfl⟩)
  · obtain ⟨row, rowMember, callMember⟩ := List.mem_flatMap.mp called
    by_cases active : row.selector = 1
    · rw [if_pos active] at callMember
      exact (queried row rowMember active).1 (List.mem_map.mpr ⟨request, callMember, rfl⟩)
    · rw [if_neg active] at callMember
      cases callMember

theorem functionByteQueries_in_pool {queries : List (List G)} {rows : List FunctionRow}
    (queried : ∀ row ∈ rows, row.QueriesIn queries) :
    (functionByteQueries rows).map rangeMessage ⊆ queries := by
  intro message member
  obtain ⟨pair, pairMember, equal⟩ := List.mem_map.mp member
  subst message
  obtain ⟨row, rowMember, queryMember⟩ := List.mem_flatMap.mp pairMember
  by_cases active : row.selector = 1
  · rw [if_pos active] at queryMember
    exact (queried row rowMember active).2 (List.mem_map.mpr ⟨pair, queryMember, rfl⟩)
  · rw [if_neg active] at queryMember
    cases queryMember

/-- Construct locally valid function rows from the complete circuit witness
list. The input balance names only physical circuit providers and auxiliary
tables. Function-row validity is a conclusion, not an input. -/
theorem circuitWitnesses_interpret (tables : AuxiliaryTables) {program : Toplevel}
    (witnesses : List CircuitWitness) {width : Nat} {queries : List (List G)}
    (balanced : PaddedLookupBalance width queries (tables.circuitProviders (witnesses.map (·.emission))))
    (bounded : queries.length < gSize.toNat) (widths : ∀ query ∈ queries, query.length ≤ width)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    (counted : program.validateRowCounts = true)
    (circuits : ∀ witness ∈ witnesses, witness.circuit ∈ program.circuits)
    (emitted : ∀ witness ∈ witnesses, witness.Emitted program)
    (satisfied : ∀ witness ∈ witnesses, witness.Satisfied)
    (shapes : ∀ witness ∈ witnesses, witness.Shapes program)
    (limits : ∀ witness ∈ witnesses, witness.LookupBounds)
    (pooled : circuitQueryPool (witnesses.map (·.emission)) ⊆ queries) :
    ∃ functions : List FunctionRow,
      List.Forall₂ (FunctionRow.Provides width) (witnesses.map (·.emission)) functions ∧
      GlobalLookups (tables.withFunctions functions) width queries ∧
      (∀ row ∈ functions, row.Valid program (memoryFacts tables.memory)) ∧
      (∀ row ∈ functions, row.QueriesIn queries) := by
  have counts := fun witness member => Toplevel.validateRowCounts_circuit counted (circuits witness member)
  obtain ⟨provisional, providers⟩ := forall₂_exists_right witnesses
    (fun witness (row : FunctionRow) => row.Provides width witness.emission)
    (fun witness member => witness.provider_row (emitted witness member) (satisfied witness member)
      (counts witness member) (shapes witness member) width)
  have providerRows := forall₂_map_left providers
  have global := tables.global_of_circuit_balance balanced bounded widths providerRows
  obtain ⟨functions, interpreted⟩ := forall₂_exists_right witnesses
    (fun witness (row : FunctionRow) => row.Valid program (memoryFacts tables.memory) ∧
      row.Provides width witness.emission ∧ row.QueriesIn queries)
    (fun witness member => witness.interpreted_row global memoryValid canonical
      (emitted witness member) (satisfied witness member) (counts witness member) (shapes witness member)
      (limits witness member) (List.mem_map.mpr ⟨witness, member, rfl⟩) pooled)
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

theorem circuitWitnesses_execute (tables : AuxiliaryTables) {program : Toplevel}
    (witnesses : List CircuitWitness) {width : Nat} {queries : List (List G)}
    (balanced : PaddedLookupBalance width queries (tables.circuitProviders (witnesses.map (·.emission))))
    (bounded : queries.length < gSize.toNat) (widths : ∀ query ∈ queries, query.length ≤ width)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    (counted : program.validateRowCounts = true) (programShapes : program.validateLookupShapes = true)
    (circuits : ∀ witness ∈ witnesses, witness.circuit ∈ program.circuits)
    (emitted : ∀ witness ∈ witnesses, witness.Emitted program)
    (satisfied : ∀ witness ∈ witnesses, witness.Satisfied)
    (shapes : ∀ witness ∈ witnesses, witness.Shapes program)
    (limits : ∀ witness ∈ witnesses, witness.LookupBounds)
    (pooled : circuitQueryPool (witnesses.map (·.emission)) ⊆ queries)
    {request : Bytecode.AIR.Call} (shape : request.LookupShape program)
    (root : functionMessage request ∈ queries) :
    Bytecode.AIR.Execution program (memoryFacts tables.memory) request := by
  obtain ⟨functions, _, global, valid, queried⟩ := circuitWitnesses_interpret tables witnesses
    balanced bounded widths memoryValid canonical counted circuits emitted satisfied shapes limits pooled
  apply global.roots_execute (roots := [request]) programShapes valid
    (functionQueries_in_pool ?_ queried) (functionByteQueries_in_pool queried) shape List.mem_cons_self
  intro message member
  have equal : message = functionMessage request := List.mem_singleton.mp member
  rwa [equal]

end Aiur.AIR
