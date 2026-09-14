/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.TableGraphTraces

/-! Execution from the selected compiled key's physical base graphs and one
bounded global balance equation. Graph evaluation supplies every emitted
row, layout bound and local equation. PCS authentication, fixed-preprocessing
binding and randomized lookup soundness remain the cryptographic boundary. -/

namespace Aiur.NativeAIR.CompiledKey

theorem circuits_trace_parts {logBlowup : Nat} {program : Bytecode.Toplevel} {keys : List KeyCodec.Circuit}
    (built : circuits logBlowup program = some keys) :
    program.circuits.toList.mapM (functionCircuit logBlowup program) =
        some (keys.take program.circuits.size) ∧
      program.memorySizes.toList.mapM (memoryCircuit logBlowup) =
        some ((keys.drop program.circuits.size).take program.memorySizes.size) := by
  obtain ⟨functions, memories, _, _, functionsBuilt, memoriesBuilt, _, _, equal⟩ := circuits_parts built
  have fl := Bytecode.AIR.list_mapM_some_length _ _ _ functionsBuilt
  have ml := Bytecode.AIR.list_mapM_some_length _ _ _ memoriesBuilt
  simp only [Array.length_toList] at fl ml
  have first : keys.take program.circuits.size = functions := by
    rw [equal, List.append_assoc, ← fl, List.take_left]
  have second : (keys.drop program.circuits.size).take program.memorySizes.size = memories := by
    rw [equal, List.append_assoc, ← fl, List.drop_left, ← ml, List.take_left]
  exact ⟨first ▸ functionsBuilt, second ▸ memoriesBuilt⟩

end Aiur.NativeAIR.CompiledKey

namespace Aiur.AIR
open NativeAIR

structure GraphLookupData where
  functions : List LookupRow
  memories : List LookupRow
  unary : List LookupRow
  binary : List LookupRow

def GraphLookupData.queries (data : GraphLookupData) : List (List G) := graphFunctionQueries data.functions

def GraphLookupData.providers (data : GraphLookupData) : List (Provider (List G)) :=
  graphFunctionProviders data.functions ++
    (graphTableProviders data.memories ++ (graphTableProviders data.unary ++ graphTableProviders data.binary))

def SystemTraces.GraphSatisfied {program : Bytecode.Toplevel} (traces : SystemTraces program)
    (keys : List KeyCodec.Circuit) : Prop :=
  traces.functions.GraphSatisfied (keys.take program.circuits.size) ∧
    traces.memories.GraphSatisfied ((keys.drop program.circuits.size).take program.memorySizes.size)

def SystemTraces.graphLookupData {program : Bytecode.Toplevel} (traces : SystemTraces program)
    (keys : List KeyCodec.Circuit) : Option GraphLookupData := do
  let functions ← traces.functions.graphLookups (keys.take program.circuits.size)
  let memories ← traces.memories.graphLookups ((keys.drop program.circuits.size).take program.memorySizes.size)
  let byte1 ← keys[program.circuits.size + program.memorySizes.size]?
  let byte2 ← keys[program.circuits.size + program.memorySizes.size + 1]?
  let unary ← byte1.graph.readPreprocessedTraceLookups byte1.widths (finiteTraceMatrix traces.bytes.unary)
    (finiteTraceMatrix byte1PreprocessedColumns)
  let binary ← byte2.graph.readPreprocessedTraceLookups byte2.widths (finiteTraceMatrix traces.bytes.binary)
    (finiteTraceMatrix byte2PreprocessedColumns)
  return ⟨functions, memories, unary, binary⟩

theorem SystemTraces.graph_extract {program : Bytecode.Toplevel} (traces : SystemTraces program)
    {logBlowup : Nat} {keys : List KeyCodec.Circuit}
    (built : CompiledKey.circuits logBlowup program = some keys) (satisfied : traces.GraphSatisfied keys) :
    ∃ witnesses data, traces.functions.emitNativeWitnesses program = some witnesses ∧
      (∀ witness ∈ witnesses, witness.Satisfied ∧ witness.NativeBounds program) ∧
      traces.memories.Satisfied ∧ traces.graphLookupData keys = some data ∧
      data.queries = encodedCircuitQueryPool (witnesses.map (·.emission)) ∧
      data.providers = traces.providers (witnesses.map (·.emission)) := by
  have parts := CompiledKey.circuits_trace_parts built
  obtain ⟨witnesses, emitted, valid, functionRead⟩ := traces.functions.graph_extract parts.1 satisfied.1
  obtain ⟨memoryRows, memoryRead, memoryProviders⟩ := traces.memories.graph_providers parts.2
  have memorySatisfied := traces.memories.graph_satisfied parts.2 satisfied.2
  obtain ⟨byte1, byte2, first, second, firstIndex, secondIndex⟩ := CompiledKey.circuits_bytes built
  have unaryRead := CompiledKey.byte1Circuit_matrix_lookups first traces.bytes.unary
  have binaryRead := CompiledKey.byte2Circuit_matrix_lookups second traces.bytes.binary
  let data : GraphLookupData :=
    ⟨witnesses.map (fun witness => emissionLookupRow witness.emission), memoryRows,
      List.ofFn (fun index => Byte1Kind.all.map fun kind => byte1ColumnLookup kind (byte1PreprocessedColumns index) (traces.bytes.unary index)),
      List.ofFn (fun index => Byte2Kind.all.map fun kind => byte2ColumnLookup kind (byte2PreprocessedColumns index) (traces.bytes.binary index))⟩
  refine ⟨witnesses, data, emitted, valid, memorySatisfied, ?_, ?_, ?_⟩
  · simp only [graphLookupData, functionRead, memoryRead, firstIndex, secondIndex,
      unaryRead, binaryRead, bind, Option.bind_some, pure]
    rfl
  · have equality := graphFunctionQueries_emissions (witnesses.map (·.emission)) (by
      intro emission member query queryMember
      obtain ⟨witness, witnessMember, rfl⟩ := List.mem_map.mp member
      exact ((valid witness witnessMember).2.1.2 query queryMember).1)
    simpa only [data, GraphLookupData.queries, List.map_map, Function.comp_def] using equality
  · have equality := graphFunctionProviders_emissions (witnesses.map (·.emission)) (by
      intro emission member
      obtain ⟨witness, witnessMember, rfl⟩ := List.mem_map.mp member
      exact (valid witness witnessMember).2.1.1)
    simp only [List.map_map, Function.comp_def] at equality
    simp only [data, GraphLookupData.providers, equality, memoryProviders,
      graphTableProviders_byte1, graphTableProviders_byte2, SystemTraces.providers, ByteTraces.providers]

end Aiur.AIR

namespace Aiur.BoundVerifier
open AIR Bytecode.AIR

theorem CompiledBackend.graph_trace_execution {selection : Selection} (backend : CompiledBackend selection)
    (traces : SystemTraces backend.compiled.bytecode) (data : GraphLookupData)
    (lookups : traces.graphLookupData backend.keyData.circuits = some data)
    (satisfied : traces.GraphSatisfied backend.keyData.circuits)
    {result : Nat} (budget : traces.queryBound = some result)
    (width : Nat) (input : Array G) (arity : input.size = selection.inputSize)
    (balanced : PaddedLookupBalance width
      ((buildClaim selection.function input selection.success).toList :: data.queries) data.providers)
    (publicWidth : (buildClaim selection.function input selection.success).size + 1 ≤ width)
    (queryWidths : ∀ query ∈ data.queries, query.length ≤ width) :
    Execution backend.compiled.bytecode (memoryFacts traces.memories.rows) ⟨selection.function, input, selection.success, 0⟩ ∧
      ∀ size pointer left right, memoryFacts traces.memories.rows size pointer left →
        memoryFacts traces.memories.rows size pointer right → left = right := by
  obtain ⟨witnesses, actual, emitted, valid, memorySatisfied, read, queries, providers⟩ :=
    traces.graph_extract backend.circuits_bound satisfied
  have equal := Option.some.inj (read.symm.trans lookups)
  subst actual
  rw [queries, providers] at balanced
  rw [queries] at queryWidths
  exact backend.native_column_trace_execution traces emitted budget width input arity balanced publicWidth queryWidths
    (fun witness member => (valid witness member).1) (fun witness member => (valid witness member).2) memorySatisfied

end Aiur.BoundVerifier
