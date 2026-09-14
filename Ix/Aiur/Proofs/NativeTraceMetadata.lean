/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.SystemGraphExecution
import Ix.Aiur.Proofs.ShapedVerifier

/-! The selected key's physical lookup counts and fixed heights agree with
the canonical execution traces. Consequently the already enforced proof
budget supplies the execution bound when PCS supplies the same trace metadata. -/

namespace Aiur.NativeAIR.CompiledKey
open AIR

theorem functionCircuit_trace_metadata {logBlowup : Nat} {program : Bytecode.Toplevel}
    {source : Bytecode.Circuit} {artifact : KeyCodec.Circuit}
    (built : functionCircuit logBlowup program source = some artifact) :
    artifact.graph.lookups.length = source.layout.lookups ∧ artifact.preprocessedHeight = 0 := by
  obtain ⟨result, _, emitted, _, _, lookups, _⟩ := functionCircuit_reflects built
    (traceRowValues_fits artifact.widths (fun _ : Fin 1 => fun _ => 0) 0)
  have count := Bytecode.AIR.list_mapM_some_length _ _ _ lookups
  have extent := source.emitNativeRow_lookupCount _ program emitted
  simp only [List.length_ofFn] at count
  exact ⟨count.symm.trans extent, (functionCircuit_success built).choose_spec.2.2.2.2.1⟩

theorem memoryCircuit_trace_metadata {logBlowup width : Nat} {artifact : KeyCodec.Circuit}
    (built : memoryCircuit logBlowup width = some artifact) :
    artifact.graph.lookups.length = 1 ∧ artifact.preprocessedHeight = 0 := by
  obtain ⟨_, _, _, lookups⟩ := memoryCircuit_reflects built
    (traceRowValues_fits artifact.widths (fun _ : Fin 1 => fun _ => 0) 0)
  have count := Bytecode.AIR.list_mapM_some_length _ _ _ lookups
  exact ⟨count.symm, (memoryCircuit_success built).choose_spec.2.2.2.2.1⟩

theorem byte1Circuit_trace_metadata {logBlowup : Nat} {artifact : KeyCodec.Circuit}
    (built : byte1Circuit logBlowup = some artifact) :
    artifact.graph.lookups.length = 3 ∧ artifact.preprocessedHeight = 256 := by
  obtain ⟨_, _, _, lookups⟩ := byte1Circuit_reflects built
    (traceRowValues_fits artifact.widths (fun _ : Fin 1 => fun _ => 0) 0)
  have count := Bytecode.AIR.list_mapM_some_length _ _ _ lookups
  exact ⟨count.symm, (byte1Circuit_success built).choose_spec.2.2.2.2.1⟩

theorem byte2Circuit_trace_metadata {logBlowup : Nat} {artifact : KeyCodec.Circuit}
    (built : byte2Circuit logBlowup = some artifact) :
    artifact.graph.lookups.length = 10 ∧ artifact.preprocessedHeight = 65536 := by
  obtain ⟨_, _, _, lookups⟩ := byte2Circuit_reflects built
    (traceRowValues_fits artifact.widths (fun _ : Fin 1 => fun _ => 0) 0)
  have count := Bytecode.AIR.list_mapM_some_length _ _ _ lookups
  exact ⟨count.symm, (byte2Circuit_success built).choose_spec.2.2.2.2.1⟩

theorem list_mapM_project {α β γ : Type} {read : α → Option β} {inputs : List α} {outputs : List β}
    (built : inputs.mapM read = some outputs) (input : α → γ) (output : β → γ)
    (each : ∀ a b, read a = some b → output b = input a) : outputs.map output = inputs.map input := by
  have related : List.Forall₂ (fun a b => output b = input a) inputs outputs := by
    apply mapM_forall₂ built
    intro a _ b produced
    exact each a b produced
  clear built each
  induction related with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons, first, ih]

theorem circuits_trace_metadata {logBlowup : Nat} {program : Bytecode.Toplevel} {keys : List KeyCodec.Circuit}
    (built : circuits logBlowup program = some keys) :
    keys.map (·.graph.lookups.length) = systemLookupSlots program ∧
      keys.map (·.preprocessedHeight) = systemFixedHeights program := by
  obtain ⟨functions, memories, byte1, byte2, functionsBuilt, memoriesBuilt, first, second, equal⟩ := circuits_parts built
  have fs := list_mapM_project functionsBuilt (fun circuit => circuit.layout.lookups) (fun key => key.graph.lookups.length)
    (fun _ _ produced => (functionCircuit_trace_metadata produced).1)
  have fh := list_mapM_project functionsBuilt (fun _ => 0) (fun key => key.preprocessedHeight)
    (fun _ _ produced => (functionCircuit_trace_metadata produced).2)
  have ms := list_mapM_project memoriesBuilt (fun _ => 1) (fun key => key.graph.lookups.length)
    (fun _ _ produced => (memoryCircuit_trace_metadata produced).1)
  have mh := list_mapM_project memoriesBuilt (fun _ => 0) (fun key => key.preprocessedHeight)
    (fun _ _ produced => (memoryCircuit_trace_metadata produced).2)
  have unary := byte1Circuit_trace_metadata first
  have binary := byte2Circuit_trace_metadata second
  constructor <;>
    simp only [equal, List.map_append, List.map_cons, List.map_nil, fs, fh, ms, mh,
      unary.1, unary.2, binary.1, binary.2, systemLookupSlots, systemFixedHeights,
      List.map_const', Array.length_toList, List.append_assoc]

end Aiur.NativeAIR.CompiledKey

namespace Aiur.BoundVerifier
open AIR Bytecode.AIR

theorem CompiledBackend.trace_metadata {selection : Selection} (backend : CompiledBackend selection) :
    backend.keyData.circuits.map (·.graph.lookups.length) = systemLookupSlots backend.compiled.bytecode ∧
      backend.keyData.circuits.map (·.preprocessedHeight) = systemFixedHeights backend.compiled.bytecode :=
  NativeAIR.CompiledKey.circuits_trace_metadata backend.circuits_bound

theorem CompiledBackend.checked_trace_budget {selection : Selection} (backend : CompiledBackend selection)
    {bytes : ByteArray} (checked : CheckedProof backend.keyData bytes) (traces : SystemTraces backend.compiled.bytecode)
    (active : traces.bitmap = checked.data.active)
    (degrees : traces.degrees = checked.data.logDegrees.map UInt8.toNat) :
    traces.queryBound = some checked.bound := by
  have budget := checked.budget
  simpa only [NativeAIR.ProofShape.queryBound, backend.trace_metadata.1, SystemTraces.queryBound, active, degrees] using budget

theorem CompiledBackend.checked_graph_trace_execution {selection : Selection} (backend : CompiledBackend selection)
    {bytes : ByteArray} (checked : CheckedProof backend.keyData bytes) (traces : SystemTraces backend.compiled.bytecode)
    (active : traces.bitmap = checked.data.active)
    (degrees : traces.degrees = checked.data.logDegrees.map UInt8.toNat)
    (data : GraphLookupData) (lookups : traces.graphLookupData backend.keyData.circuits = some data)
    (satisfied : traces.GraphSatisfied backend.keyData.circuits)
    (width : Nat) (input : Array G) (arity : input.size = selection.inputSize)
    (balanced : PaddedLookupBalance width
      ((buildClaim selection.function input selection.success).toList :: data.queries) data.providers)
    (publicWidth : (buildClaim selection.function input selection.success).size + 1 ≤ width)
    (queryWidths : ∀ query ∈ data.queries, query.length ≤ width) :
    Execution backend.compiled.bytecode (memoryFacts traces.memories.rows) ⟨selection.function, input, selection.success, 0⟩ ∧
      ∀ size pointer left right, memoryFacts traces.memories.rows size pointer left →
        memoryFacts traces.memories.rows size pointer right → left = right :=
  backend.graph_trace_execution traces data lookups satisfied (backend.checked_trace_budget checked traces active degrees)
    width input arity balanced publicWidth queryWidths

end Aiur.BoundVerifier
