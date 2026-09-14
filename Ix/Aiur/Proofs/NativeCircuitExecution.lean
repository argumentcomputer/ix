/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ComponentEncodedExecution
import Ix.Aiur.Proofs.CompiledKey

/-! One execution endpoint for the rank policy selected by the accepted
compiled key. Circuit membership supplies constrained functions and lookup
shapes; reconstructed graph extents supply the remaining layout bounds. -/

namespace Aiur.Bytecode
open Aiur.AIR

theorem Circuit.emitNativeRow_members (row : Nat → G) (program : Toplevel) (circuit : Circuit)
    {emission : CircuitEmission} (emitted : circuit.emitNativeRow row program = some emission) :
    emission.members.map MemberEmission.functionIndex = circuit.members.toList ∧
      ∀ member ∈ emission.members, program.functions[member.functionIndex]? = some member.function := by
  simp only [Circuit.emitNativeRow] at emitted
  split at emitted
  · obtain ⟨_, indices, source⟩ := circuit.emitRow_spec row program emitted
    exact ⟨indices, fun member present => (source member present).present⟩
  · obtain ⟨_, indices, source⟩ := circuit.emitComponentRow_spec row program emitted
    exact ⟨indices, fun member present => (source member present).present⟩

theorem Circuit.emitNativeRow_lookupCount (row : Nat → G) (program : Toplevel) (circuit : Circuit)
    {emission : CircuitEmission} (emitted : circuit.emitNativeRow row program = some emission) :
    emission.lookupCount = circuit.layout.lookups := by
  simp only [Circuit.emitNativeRow] at emitted
  split at emitted
  · exact congrArg CircuitEmission.lookupCount (circuit.emitRow_spec row program emitted).1
  · exact congrArg CircuitEmission.lookupCount (circuit.emitComponentRow_spec row program emitted).1

end Aiur.Bytecode

namespace Aiur.AIR
open Bytecode

def CircuitWitness.NativeEmitted (program : Toplevel) (witness : CircuitWitness) : Prop :=
  witness.circuit.emitNativeRow witness.values program = some witness.emission

def CircuitWitness.NativeBounds (program : Toplevel) (witness : CircuitWitness) : Prop :=
  witness.QueryRanges ∧ (program.callComponents.isEmpty = true → witness.LookupBounds)

theorem CircuitWitness.native_constrained {program : Toplevel}
    (constrained : CircuitsConstrained program.functions program.circuits)
    (witness : CircuitWitness) (circuit : witness.circuit ∈ program.circuits)
    (emitted : witness.NativeEmitted program) : witness.Constrained := by
  obtain ⟨indices, source⟩ := witness.circuit.emitNativeRow_members witness.values program emitted
  intro part member
  have index : part.functionIndex ∈ witness.circuit.members := by
    apply Array.mem_toList_iff.mp
    rw [← indices]
    exact List.mem_map.mpr ⟨part, member, rfl⟩
  obtain ⟨function, present, isConstrained⟩ := constrained witness.circuit circuit part.functionIndex index
  have equal := Option.some.inj (present.symm.trans (source part member))
  subst function
  exact isConstrained

theorem CircuitWitness.native_shapes {program : Toplevel} (shapes : program.validateLookupShapes = true)
    (constrained : CircuitsConstrained program.functions program.circuits)
    (witness : CircuitWitness) (circuit : witness.circuit ∈ program.circuits)
    (emitted : witness.NativeEmitted program) : witness.Shapes program := by
  have valid := witness.native_constrained constrained circuit emitted
  have source := (witness.circuit.emitNativeRow_members witness.values program emitted).2
  exact fun part member => Toplevel.validateLookupShapes_function shapes (source part member) (valid part member)

end Aiur.AIR

namespace Aiur.NativeAIR.CompiledKey
open AIR Bytecode.AIR Compiler

theorem functionCircuit_witness {logBlowup : Nat} {program : Bytecode.Toplevel}
    {source : Bytecode.Circuit} {artifact : KeyCodec.Circuit}
    (built : functionCircuit logBlowup program source = some artifact)
    {values : Values G} (fits : values.Fits artifact.widths) :
    ∃ witness : CircuitWitness, ∃ buffer,
      witness.circuit = source ∧
      witness.values = (fun column => (values.columns .main .current)[column]?.getD 0) ∧
      witness.NativeEmitted program ∧ witness.NativeBounds program ∧
      artifact.graph.sweep goldilocksOps values = some buffer ∧
      (Vanishes goldilocksOps buffer artifact.graph.zeros ↔ witness.Satisfied) ∧
      artifact.graph.lookups.mapM (readLookup buffer) =
        some (List.ofFn fun slot : Fin witness.emission.lookupCount => witness.emission.lookup slot.val) := by
  obtain ⟨emission, buffer, emitted, swept, zeros, lookups, count, ranges, limits⟩ :=
    functionCircuit_reflects built fits
  let witness : CircuitWitness := ⟨source, (fun column => (values.columns .main .current)[column]?.getD 0), emission⟩
  have lookupCount := source.emitNativeRow_lookupCount witness.values program emitted
  refine ⟨witness, buffer, rfl, rfl, emitted, ⟨⟨count, ranges⟩, ?_⟩, swept, zeros, lookups⟩
  intro generic
  obtain ⟨reserved, bodyLimits⟩ := limits generic
  exact ⟨lookupCount ▸ reserved, fun part member => lookupCount ▸ bodyLimits part member⟩

end Aiur.NativeAIR.CompiledKey

namespace Aiur.BoundVerifier
open AIR Bytecode.AIR NativeAIR NativeAIR.Compiler

theorem CompiledBackend.function_witness {selection : Selection} (backend : CompiledBackend selection)
    {index : Nat} {source : Bytecode.Circuit} {artifact : KeyCodec.Circuit}
    (present : backend.compiled.bytecode.circuits[index]? = some source)
    (selected : backend.keyData.circuits[index]? = some artifact)
    {values : Values G} (fits : values.Fits artifact.widths) :
    ∃ witness : CircuitWitness, ∃ buffer,
      witness.circuit = source ∧
      witness.values = (fun column => (values.columns .main .current)[column]?.getD 0) ∧
      witness.NativeEmitted backend.compiled.bytecode ∧ witness.NativeBounds backend.compiled.bytecode ∧
      artifact.graph.sweep goldilocksOps values = some buffer ∧
      (Vanishes goldilocksOps buffer artifact.graph.zeros ↔ witness.Satisfied) ∧
      artifact.graph.lookups.mapM (readLookup buffer) =
        some (List.ofFn fun slot : Fin witness.emission.lookupCount => witness.emission.lookup slot.val) :=
  CompiledKey.functionCircuit_witness (CompiledKey.circuits_function backend.circuits_bound present selected) fits

theorem CompiledBackend.encoded_native_circuit_execution {selection : Selection} (backend : CompiledBackend selection)
    (tables : AuxiliaryTables) (witnesses : List CircuitWitness) (width : Nat)
    (input : Array G) (arity : input.size = selection.inputSize)
    (balanced : PaddedLookupBalance width
      ((buildClaim selection.function input selection.success).toList :: encodedCircuitQueryPool (witnesses.map (·.emission)))
      (tables.circuitProviders (witnesses.map (·.emission))))
    (bounded : (encodedCircuitQueryPool (witnesses.map (·.emission))).length + 1 < gSize.toNat)
    (publicWidth : (buildClaim selection.function input selection.success).size + 1 ≤ width)
    (queryWidths : ∀ query ∈ encodedCircuitQueryPool (witnesses.map (·.emission)), query.length ≤ width)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    (circuits : ∀ witness ∈ witnesses, witness.circuit ∈ backend.compiled.bytecode.circuits)
    (emitted : ∀ witness ∈ witnesses, witness.NativeEmitted backend.compiled.bytecode)
    (satisfied : ∀ witness ∈ witnesses, witness.Satisfied)
    (bounds : ∀ witness ∈ witnesses, witness.NativeBounds backend.compiled.bytecode) :
    Execution backend.compiled.bytecode (memoryFacts tables.memory) ⟨selection.function, input, selection.success, 0⟩ := by
  have constrained := fun (witness : CircuitWitness) member => witness.native_constrained backend.toBackend.circuits_constrained
    (circuits witness member) (emitted witness member)
  have shapes := fun (witness : CircuitWitness) member => witness.native_shapes backend.lookupShapes backend.toBackend.circuits_constrained
    (circuits witness member) (emitted witness member)
  cases generic : backend.compiled.bytecode.callComponents.isEmpty with
  | true =>
    apply backend.toBackend.encoded_circuit_execution tables witnesses width input arity balanced bounded
      publicWidth queryWidths memoryValid canonical circuits ?_ satisfied shapes (fun witness member => (bounds witness member).2 generic)
    intro witness member
    simpa only [CircuitWitness.NativeEmitted, CircuitWitness.Emitted,
      Bytecode.Circuit.emitNativeRow, generic, if_true] using emitted witness member
  | false =>
    have components := backend.components_checked.resolve_left (by simp only [generic, Bool.false_eq_true, not_false_eq_true])
    apply backend.toBackend.encoded_component_circuit_execution components tables witnesses width input arity balanced bounded
      publicWidth queryWidths memoryValid canonical circuits ?_ satisfied shapes constrained (fun witness member => (bounds witness member).1)
    intro witness member
    simpa only [CircuitWitness.NativeEmitted, CircuitWitness.ComponentEmitted,
      Bytecode.Circuit.emitNativeRow, generic, Bool.false_eq_true, if_false] using emitted witness member

end Aiur.BoundVerifier
