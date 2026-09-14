/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.GraphTraces

/-! Preserve the physical graph's row and slot order through trace extraction.
Slot zero is the function provider; the remaining slots are unit consumers.
This separation also applies when a provider's negative field multiplicity
happens to be one. -/

namespace Aiur.NativeAIR
open AIR Compiler OpEmitter

abbrev LookupRow := List (G × List G)

def Graph.readLookups (graph : Graph) (values : Values G) : Option LookupRow := do
  let buffer ← graph.sweep goldilocksOps values
  graph.lookups.mapM (readLookup buffer)

def Graph.readTraceLookups (graph : Graph) (widths : GraphWidths) {height : Nat}
    (matrix : Fin height → Nat → G) : Option (List LookupRow) :=
  (List.ofFn id).mapM fun index => graph.readLookups (traceRowValues widths matrix index)

def emissionLookupRow (emission : CircuitEmission) : LookupRow :=
  List.ofFn fun slot : Fin emission.lookupCount => emission.lookup slot.val

def graphRowQueries (row : LookupRow) : List (List G) :=
  (List.range row.length).filterMap fun slot =>
    if slot = 0 then none else do
      let lookup ← row[slot]?
      if lookup.1 = 1 then some lookup.2 else none

def graphRowProvider (row : LookupRow) : Option (Provider (List G)) :=
  row[0]?.map fun lookup => (lookup.2, 0 - lookup.1)

def graphFunctionQueries (rows : List LookupRow) : List (List G) := rows.flatMap graphRowQueries

def graphFunctionProviders (rows : List LookupRow) : List (Provider (List G)) := rows.filterMap graphRowProvider

theorem filterMap_eq_of_eq_on {left right : α → Option β} (inputs : List α)
    (equal : ∀ input ∈ inputs, left input = right input) : inputs.filterMap left = inputs.filterMap right := by
  induction inputs with
  | nil => rfl
  | cons input inputs ih =>
    simp only [List.filterMap_cons, equal input List.mem_cons_self,
      ih (fun value member => equal value (List.mem_cons_of_mem _ member))]

theorem encodedQuery_zero {emission : CircuitEmission}
    (ranges : ∀ query ∈ emission.queries, 0 < query.slot) :
    encodedQuery emission.branchless emission.queries 0 = none := by
  have empty : emission.queries.filter (fun query => query.slot == 0) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro query member
    simpa only [beq_iff_eq, Nat.ne_zero_iff_zero_lt] using ranges query member
  simp only [encodedQuery, querySlotMultiplicity, querySlotParts, empty,
    List.map_nil, selectorSum, List.foldl_nil, Ne.symm G.one_ne_zero, if_false]

theorem graphRowQueries_emission (emission : CircuitEmission)
    (ranges : ∀ query ∈ emission.queries, 0 < query.slot) :
    graphRowQueries (emissionLookupRow emission) =
      encodedQueries emission.branchless emission.queries emission.lookupCount := by
  simp only [graphRowQueries, emissionLookupRow, List.length_ofFn, encodedQueries]
  apply filterMap_eq_of_eq_on
  intro slot member
  have inside := List.mem_range.mp member
  by_cases zero : slot = 0
  · subst slot
    simp only [if_true, encodedQuery_zero ranges]
  · simp only [zero, if_false, List.getElem?_ofFn, inside, dif_pos, bind, Option.bind_some,
      CircuitEmission.lookup, encodedQuery]

theorem graphRowProvider_emission (emission : CircuitEmission) (positive : 0 < emission.lookupCount) :
    graphRowProvider (emissionLookupRow emission) = some emission.provider := by
  simp only [graphRowProvider, emissionLookupRow, List.getElem?_ofFn, positive, dif_pos, Option.map_some,
    CircuitEmission.lookup, if_true, CircuitEmission.provider, G.neg_neg]

theorem graphFunctionQueries_emissions (emissions : List CircuitEmission)
    (ranges : ∀ emission ∈ emissions, ∀ query ∈ emission.queries, 0 < query.slot) :
    graphFunctionQueries (emissions.map emissionLookupRow) = encodedCircuitQueryPool emissions := by
  induction emissions with
  | nil => rfl
  | cons emission emissions ih =>
    simp only [List.map_cons, graphFunctionQueries, List.flatMap_cons, encodedCircuitQueryPool,
      graphRowQueries_emission emission (ranges emission List.mem_cons_self)]
    exact congrArg (_ ++ ·) (ih (fun value member => ranges value (List.mem_cons_of_mem _ member)))

theorem graphFunctionProviders_emissions (emissions : List CircuitEmission)
    (positive : ∀ emission ∈ emissions, 0 < emission.lookupCount) :
    graphFunctionProviders (emissions.map emissionLookupRow) = circuitProviders emissions := by
  induction emissions with
  | nil => rfl
  | cons emission emissions ih =>
    simp only [List.map_cons, graphFunctionProviders, List.filterMap_cons,
      graphRowProvider_emission emission (positive emission List.mem_cons_self), circuitProviders]
    exact congrArg (emission.provider :: ·) (ih (fun value member => positive value (List.mem_cons_of_mem _ member)))

theorem CompiledKey.functionCircuit_matrix_extract {logBlowup : Nat} {program : Bytecode.Toplevel}
    {source : Bytecode.Circuit} {artifact : KeyCodec.Circuit}
    (built : CompiledKey.functionCircuit logBlowup program source = some artifact)
    {height : Nat} (matrix : Fin height → Nat → G)
    (satisfied : artifact.graph.TraceSatisfied artifact.widths matrix) :
    ∃ witnesses, (List.ofFn matrix).mapM (emitNativeCircuitWitness program source) = some witnesses ∧
      (∀ witness ∈ witnesses, witness.Satisfied ∧ witness.NativeBounds program) ∧
      artifact.graph.readTraceLookups artifact.widths matrix =
        some (witnesses.map fun witness => emissionLookupRow witness.emission) := by
  have each := fun index => CompiledKey.functionCircuit_trace_witness built matrix index (satisfied index)
  let witnesses := fun index => (each index).choose
  have produced (index : Fin height) : emitNativeCircuitWitness program source (matrix index) = some (witnesses index) :=
    (each index).choose_spec.choose_spec.1
  have valid (index : Fin height) : (witnesses index).Satisfied ∧ (witnesses index).NativeBounds program :=
    ⟨(each index).choose_spec.choose_spec.2.1, (each index).choose_spec.choose_spec.2.2.1⟩
  have read (index : Fin height) : artifact.graph.readLookups (traceRowValues artifact.widths matrix index) =
      some (emissionLookupRow (witnesses index).emission) := by
    dsimp only [witnesses, emissionLookupRow]
    obtain ⟨buffer, _, _, _, swept, lookups⟩ := (each index).choose_spec
    simp only [Graph.readLookups, swept, bind, Option.bind_some, lookups]
  refine ⟨List.ofFn witnesses, list_mapM_ofFn matrix witnesses _ produced, ?_, ?_⟩
  · intro witness member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    exact valid index
  · simpa only [Graph.readTraceLookups, List.map_ofFn, Function.comp_def] using
      list_mapM_ofFn id (fun index => emissionLookupRow (witnesses index).emission)
        (fun index => artifact.graph.readLookups (traceRowValues artifact.widths matrix index)) read

end Aiur.NativeAIR

namespace Aiur.AIR
open Bytecode NativeAIR

def CircuitTraces.graphLookups {circuits : List Circuit} : CircuitTraces circuits → List KeyCodec.Circuit → Option (List LookupRow)
  | .nil, [] => some []
  | .inactive _ rest, _ :: keys => rest.graphLookups keys
  | .active _ _ matrix rest, key :: keys => do
    let first ← key.graph.readTraceLookups key.widths matrix
    let later ← rest.graphLookups keys
    return first ++ later
  | _, _ => none

theorem CircuitTraces.graph_extract {circuits : List Circuit} (traces : CircuitTraces circuits)
    {logBlowup : Nat} {program : Toplevel} {keys : List KeyCodec.Circuit}
    (built : circuits.mapM (CompiledKey.functionCircuit logBlowup program) = some keys)
    (satisfied : traces.GraphSatisfied keys) :
    ∃ witnesses, traces.emitNativeWitnesses program = some witnesses ∧
      (∀ witness ∈ witnesses, witness.Satisfied ∧ witness.NativeBounds program) ∧
      traces.graphLookups keys = some (witnesses.map fun witness => emissionLookupRow witness.emission) := by
  induction traces generalizing keys with
  | nil =>
    have empty : keys = [] := satisfied
    subst keys
    exact ⟨[], rfl, (fun _ member => nomatch member), rfl⟩
  | inactive circuit rest ih =>
    obtain ⟨key, keys, _, tail, equal⟩ := list_mapM_cons_parts built
    subst equal
    exact ih tail satisfied
  | active circuit degree matrix rest ih =>
    obtain ⟨key, keys, head, tail, equal⟩ := list_mapM_cons_parts built
    subst equal
    obtain ⟨later, laterEq, laterValid, laterRead⟩ := ih tail satisfied.2
    obtain ⟨first, firstEq, firstValid, firstRead⟩ := CompiledKey.functionCircuit_matrix_extract head matrix satisfied.1
    refine ⟨first ++ later, ?_, ?_, ?_⟩
    · simp only [emitNativeWitnesses, firstEq, laterEq, bind, Option.bind_some, pure]
    · intro witness member
      exact (List.mem_append.mp member).elim (firstValid witness) (laterValid witness)
    · simp only [graphLookups, firstRead, laterRead, bind, Option.bind_some, pure, List.map_append]

end Aiur.AIR
