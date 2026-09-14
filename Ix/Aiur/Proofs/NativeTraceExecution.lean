/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.NativeCircuitExecution

/-! Canonical traces use the accepted key's rank policy. The native-style
logical-slot budget bounds all consumers before lookup grouping. Memory and
byte columns supply their existing checked provider interpretations. -/

namespace Aiur.AIR
open Bytecode

def boundedTraceRow (width : Nat) (values : Nat → G) : Nat → G :=
  fun column => (Array.ofFn fun index : Fin width => values index.val)[column]?.getD 0

def emitNativeCircuitWitness (program : Toplevel) (circuit : Circuit) (values : Nat → G) : Option CircuitWitness := do
  let row := boundedTraceRow circuit.layout.width values
  let emission ← circuit.emitNativeRow row program
  return ⟨circuit, row, emission⟩

def CircuitTraces.emitNativeWitnesses {circuits : List Circuit} (program : Toplevel) :
    CircuitTraces circuits → Option (List CircuitWitness)
  | .nil => some []
  | .inactive _ rest => rest.emitNativeWitnesses program
  | .active circuit _ values rest => do
    let first ← (List.ofFn values).mapM (emitNativeCircuitWitness program circuit)
    let later ← rest.emitNativeWitnesses program
    return first ++ later

theorem emitNativeCircuitWitness_spec {program : Toplevel} {circuit : Circuit} {values : Nat → G}
    {witness : CircuitWitness} (emitted : emitNativeCircuitWitness program circuit values = some witness) :
    witness.circuit = circuit ∧ witness.values = boundedTraceRow circuit.layout.width values ∧ witness.NativeEmitted program ∧
      witness.emission.lookupCount = circuit.layout.lookups := by
  simp only [emitNativeCircuitWitness, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  rename_i emission emissionEq
  cases emitted
  exact ⟨rfl, rfl, emissionEq, circuit.emitNativeRow_lookupCount _ program emissionEq⟩

theorem emitNativeCircuitWitnesses_spec {program : Toplevel} {circuit : Circuit}
    {values : List (Nat → G)} {witnesses : List CircuitWitness}
    (emitted : values.mapM (emitNativeCircuitWitness program circuit) = some witnesses) :
    witnesses.length = values.length ∧
      (∀ witness ∈ witnesses, witness.circuit = circuit ∧ witness.NativeEmitted program ∧
        witness.emission.lookupCount = circuit.layout.lookups) := by
  have related : List.Forall₂ (fun _ witness => witness.circuit = circuit ∧ witness.NativeEmitted program ∧
      witness.emission.lookupCount = circuit.layout.lookups) values witnesses := by
    apply mapM_forall₂ emitted
    intro value member witness produced
    obtain ⟨same, _, emitted, count⟩ := emitNativeCircuitWitness_spec produced
    exact ⟨same, emitted, count⟩
  have length : witnesses.length = values.length := by
    clear emitted
    induction related with
    | nil => rfl
    | cons first rest ih => simpa only [List.length_cons] using congrArg (· + 1) ih
  refine ⟨length, ?_⟩
  intro witness member
  obtain ⟨_, _, evidence⟩ := forall₂_right_member related member
  exact evidence

theorem CircuitTraces.emitNativeWitnesses_spec {circuits : List Circuit} (traces : CircuitTraces circuits)
    {program : Toplevel} {witnesses : List CircuitWitness}
    (emitted : traces.emitNativeWitnesses program = some witnesses) :
    (∀ witness ∈ witnesses, witness.circuit ∈ circuits ∧ witness.NativeEmitted program) ∧
      (encodedCircuitQueryPool (witnesses.map (·.emission))).length ≤ traces.capacity := by
  induction traces generalizing witnesses with
  | nil =>
    cases emitted
    exact ⟨by simp only [List.not_mem_nil, false_implies, implies_true], Nat.le_refl 0⟩
  | inactive circuit rest ih =>
    obtain ⟨valid, bounded⟩ := ih emitted
    exact ⟨fun witness member => ⟨List.mem_cons_of_mem _ (valid witness member).1,
      (valid witness member).2⟩, bounded⟩
  | active circuit degree values rest ih =>
    simp only [emitNativeWitnesses, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i first firstEmitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i later laterEmitted
    cases emitted
    obtain ⟨valid, bounded⟩ := ih laterEmitted
    obtain ⟨length, firstValid⟩ := emitNativeCircuitWitnesses_spec firstEmitted
    have firstBound := encodedCircuitQueryPool_uniform_bound first circuit.layout.lookups
      (fun witness member => Nat.le_of_eq (firstValid witness member).2.2)
    simp only [List.length_ofFn] at length
    rw [length] at firstBound
    refine ⟨?_, ?_⟩
    · intro witness member
      rcases List.mem_append.mp member with before | after
      · have evidence := firstValid witness before
        exact ⟨List.mem_cons.mpr (Or.inl evidence.1), evidence.2.1⟩
      · exact ⟨List.mem_cons_of_mem _ (valid witness after).1, (valid witness after).2⟩
    · simp only [encodedCircuitQueryPool, List.map_append, List.flatMap_append, List.length_append, capacity] at *
      omega

end Aiur.AIR

namespace Aiur.BoundVerifier
open AIR Bytecode.AIR

theorem CompiledBackend.native_trace_execution {selection : Selection} (backend : CompiledBackend selection)
    (tables : AuxiliaryTables) (traces : CircuitTraces backend.compiled.bytecode.circuits.toList)
    {witnesses : List CircuitWitness}
    (emitted : traces.emitNativeWitnesses backend.compiled.bytecode = some witnesses)
    {otherSlots : List Nat} {otherActive : List Bool} {otherDegrees : List Nat} {result : Nat}
    (budget : lookupQueryBound
      (backend.compiled.bytecode.circuits.toList.map (·.layout.lookups) ++ otherSlots)
      (traces.bitmap ++ otherActive) (traces.degrees ++ otherDegrees) = some result)
    (width : Nat) (input : Array G) (arity : input.size = selection.inputSize)
    (balanced : PaddedLookupBalance width
      ((buildClaim selection.function input selection.success).toList :: encodedCircuitQueryPool (witnesses.map (·.emission)))
      (tables.circuitProviders (witnesses.map (·.emission))))
    (publicWidth : (buildClaim selection.function input selection.success).size + 1 ≤ width)
    (queryWidths : ∀ query ∈ encodedCircuitQueryPool (witnesses.map (·.emission)), query.length ≤ width)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    (satisfied : ∀ witness ∈ witnesses, witness.Satisfied)
    (bounds : ∀ witness ∈ witnesses, witness.NativeBounds backend.compiled.bytecode) :
    Execution backend.compiled.bytecode (memoryFacts tables.memory) ⟨selection.function, input, selection.success, 0⟩ := by
  obtain ⟨valid, count⟩ := traces.emitNativeWitnesses_spec emitted
  have totalBound := traces.capacity_bounded budget
  exact backend.encoded_native_circuit_execution tables witnesses width input arity balanced (by omega)
    publicWidth queryWidths memoryValid canonical
    (fun witness member => by simpa using (valid witness member).1)
    (fun witness member => (valid witness member).2) satisfied bounds

theorem CompiledBackend.native_column_trace_execution {selection : Selection} (backend : CompiledBackend selection)
    (traces : SystemTraces backend.compiled.bytecode) {witnesses : List CircuitWitness}
    (emitted : traces.functions.emitNativeWitnesses backend.compiled.bytecode = some witnesses)
    {result : Nat} (budget : traces.queryBound = some result)
    (width : Nat) (input : Array G) (arity : input.size = selection.inputSize)
    (balanced : PaddedLookupBalance width
      ((buildClaim selection.function input selection.success).toList :: encodedCircuitQueryPool (witnesses.map (·.emission)))
      (traces.providers (witnesses.map (·.emission))))
    (publicWidth : (buildClaim selection.function input selection.success).size + 1 ≤ width)
    (queryWidths : ∀ query ∈ encodedCircuitQueryPool (witnesses.map (·.emission)), query.length ≤ width)
    (satisfied : ∀ witness ∈ witnesses, witness.Satisfied)
    (bounds : ∀ witness ∈ witnesses, witness.NativeBounds backend.compiled.bytecode)
    (memorySatisfied : traces.memories.Satisfied) :
    Execution backend.compiled.bytecode (memoryFacts traces.memories.rows) ⟨selection.function, input, selection.success, 0⟩ ∧
      ∀ size pointer left right, memoryFacts traces.memories.rows size pointer left →
        memoryFacts traces.memories.rows size pointer right → left = right := by
  unfold SystemTraces.providers at balanced
  have replaced := balanced.perm_providers
    ((traces.bytes.providers_reflect.append_left traces.memories.providers).append_left
      (circuitProviders (witnesses.map CircuitWitness.emission)))
  rw [← List.append_assoc traces.memories.providers] at replaced
  have decoded := replaced.congr_providers
    (traces.memories.circuitProviders_reflect backend.toBackend.memorySizes_distinct memorySatisfied width
      traces.bytes.byte1Weights traces.bytes.byte2Weights _)
  refine ⟨?_, ?_⟩
  · exact backend.native_trace_execution (traces.memories.auxiliary traces.bytes.byte1Weights traces.bytes.byte2Weights)
      traces.functions emitted budget width input arity decoded publicWidth queryWidths
      (traces.memories.rows_valid memorySatisfied) backend.toBackend.memorySizes_canonical satisfied bounds
  · intro size pointer left right loadedLeft loadedRight
    exact traces.memory_functional budget memorySatisfied loadedLeft loadedRight

end Aiur.BoundVerifier
