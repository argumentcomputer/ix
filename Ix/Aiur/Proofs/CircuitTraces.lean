/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.EncodedCircuitExecution
import Ix.Aiur.Proofs.LookupBudget

/-! Canonical circuit traces encode the activation bitmap and active-order
degrees directly. Successful emission supplies every row's circuit and
lookup extent. Unit consumers fit the trace capacity, which the checked
global budget bounds below the field characteristic. Native extraction
from the accepted commitments and proof metadata remains separate. -/

namespace Aiur.AIR
open Bytecode

/-- Trace assignments indexed by the canonical circuit order. An active
circuit has exactly the height specified by its active-position degree. -/
inductive CircuitTraces : List Circuit → Type where
  | nil : CircuitTraces []
  | inactive (circuit : Circuit) {circuits : List Circuit} (rest : CircuitTraces circuits) :
      CircuitTraces (circuit :: circuits)
  | active (circuit : Circuit) (degree : Nat) (values : Fin (2 ^ degree) → Nat → G)
      {circuits : List Circuit} (rest : CircuitTraces circuits) : CircuitTraces (circuit :: circuits)

def CircuitTraces.bitmap {circuits : List Circuit} : CircuitTraces circuits → List Bool
  | .nil => []
  | .inactive _ rest => false :: rest.bitmap
  | .active _ _ _ rest => true :: rest.bitmap

def CircuitTraces.degrees {circuits : List Circuit} : CircuitTraces circuits → List Nat
  | .nil => []
  | .inactive _ rest => rest.degrees
  | .active _ degree _ rest => degree :: rest.degrees

def CircuitTraces.capacity {circuits : List Circuit} : CircuitTraces circuits → Nat
  | .nil => 0
  | .inactive _ rest => rest.capacity
  | .active circuit degree _ rest => 2 ^ degree * circuit.layout.lookups + rest.capacity

def emitCircuitWitness (program : Toplevel) (circuit : Circuit) (values : Nat → G) : Option CircuitWitness := do
  let emission ← circuit.emitRow values program
  return ⟨circuit, values, emission⟩

def CircuitTraces.emitWitnesses {circuits : List Circuit} (program : Toplevel) :
    CircuitTraces circuits → Option (List CircuitWitness)
  | .nil => some []
  | .inactive _ rest => rest.emitWitnesses program
  | .active circuit _ values rest => do
    let first ← (List.ofFn values).mapM (emitCircuitWitness program circuit)
    let later ← rest.emitWitnesses program
    return first ++ later

theorem CircuitTraces.slot_sum_append {circuits : List Circuit} (traces : CircuitTraces circuits)
    (otherSlots : List Nat) (otherActive : List Bool) (otherDegrees : List Nat) :
    lookupSlotSum (circuits.map (·.layout.lookups) ++ otherSlots)
      (traces.bitmap ++ otherActive) (traces.degrees ++ otherDegrees) =
      (lookupSlotSum otherSlots otherActive otherDegrees).map (traces.capacity + ·) := by
  induction traces with
  | nil =>
    simp only [List.map_nil, List.nil_append, bitmap, degrees, capacity, Nat.zero_add]
    cases lookupSlotSum otherSlots otherActive otherDegrees <;> rfl
  | inactive circuit rest ih =>
    simp only [List.map_cons, List.cons_append, bitmap, degrees, capacity, lookupSlotSum]
    exact ih
  | active circuit degree values rest ih =>
    simp only [List.map_cons, List.cons_append, bitmap, degrees, capacity, lookupSlotSum, ih,
      bind, Option.bind]
    cases lookupSlotSum otherSlots otherActive otherDegrees <;>
      simp only [Option.map_none, Option.map_some, pure, Nat.add_assoc]

theorem CircuitTraces.capacity_bounded {circuits : List Circuit} (traces : CircuitTraces circuits)
    {otherSlots : List Nat} {otherActive : List Bool} {otherDegrees : List Nat} {result : Nat}
    (accepted : lookupQueryBound (circuits.map (·.layout.lookups) ++ otherSlots)
      (traces.bitmap ++ otherActive) (traces.degrees ++ otherDegrees) = some result) :
    traces.capacity + 1 < gSize.toNat := by
  obtain ⟨_, total, shape, count, bounded⟩ := lookupQueryBound_sound accepted
  rw [traces.slot_sum_append] at shape
  cases other : lookupSlotSum otherSlots otherActive otherDegrees with
  | none => simp only [other, Option.map_none, reduceCtorEq] at shape
  | some extra =>
    simp only [other, Option.map_some, Option.some.injEq] at shape
    omega

theorem emitCircuitWitness_spec {program : Toplevel} {circuit : Circuit} {values : Nat → G}
    {witness : CircuitWitness} (emitted : emitCircuitWitness program circuit values = some witness) :
    witness.circuit = circuit ∧ witness.values = values ∧ witness.Emitted program ∧
      witness.emission.lookupCount = circuit.layout.lookups := by
  simp only [emitCircuitWitness, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  · rename_i emission emissionEq
    have equal := Option.some.inj emitted
    subst witness
    have description := (circuit.emitRow_spec values program emissionEq).1
    refine ⟨rfl, rfl, emissionEq, ?_⟩
    exact congrArg CircuitEmission.lookupCount description

theorem encodedQueries_length (branchless : Bool) (queries : List QueryPart) (limit : Nat) :
    (encodedQueries branchless queries limit).length ≤ limit := by
  simpa only [encodedQueries, List.length_range] using
    List.length_filterMap_le (encodedQuery branchless queries) (List.range limit)

theorem encodedCircuitQueryPool_uniform_bound (witnesses : List CircuitWitness) (slots : Nat)
    (bounded : ∀ witness ∈ witnesses, witness.emission.lookupCount ≤ slots) :
    (encodedCircuitQueryPool (witnesses.map (·.emission))).length ≤ witnesses.length * slots := by
  induction witnesses with
  | nil => simp only [List.map_nil, encodedCircuitQueryPool, List.flatMap_nil, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons witness rest ih =>
    have first := Nat.le_trans (encodedQueries_length witness.emission.branchless
      witness.emission.queries witness.emission.lookupCount) (bounded witness List.mem_cons_self)
    have later := ih (fun item member => bounded item (List.mem_cons_of_mem _ member))
    simp only [encodedCircuitQueryPool, List.map_cons, List.flatMap_cons,
      List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul] at *
    omega

theorem emitCircuitWitnesses_spec {program : Toplevel} {circuit : Circuit}
    {values : List (Nat → G)} {witnesses : List CircuitWitness}
    (emitted : values.mapM (emitCircuitWitness program circuit) = some witnesses) :
    witnesses.length = values.length ∧
      (∀ witness ∈ witnesses, witness.circuit = circuit ∧ witness.Emitted program ∧
        witness.emission.lookupCount = circuit.layout.lookups) := by
  have related : List.Forall₂ (fun _ witness => witness.circuit = circuit ∧ witness.Emitted program ∧
      witness.emission.lookupCount = circuit.layout.lookups) values witnesses := by
    apply mapM_forall₂ emitted
    intro value member witness produced
    obtain ⟨same, _, emitted, count⟩ := emitCircuitWitness_spec produced
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

theorem CircuitTraces.emitWitnesses_spec {circuits : List Circuit} (traces : CircuitTraces circuits)
    {program : Toplevel} {witnesses : List CircuitWitness}
    (emitted : traces.emitWitnesses program = some witnesses) :
    (∀ witness ∈ witnesses, witness.circuit ∈ circuits ∧ witness.Emitted program) ∧
      (encodedCircuitQueryPool (witnesses.map (·.emission))).length ≤ traces.capacity := by
  induction traces generalizing witnesses with
  | nil =>
    have equal := Option.some.inj emitted
    subst witnesses
    exact ⟨by simp only [List.not_mem_nil, false_implies, implies_true], Nat.le_refl 0⟩
  | inactive circuit rest ih =>
    obtain ⟨valid, bounded⟩ := ih emitted
    exact ⟨fun witness member => ⟨List.mem_cons_of_mem _ (valid witness member).1,
      (valid witness member).2⟩, bounded⟩
  | active circuit degree values rest ih =>
    simp only [emitWitnesses, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i first firstEmitted
      dsimp only at emitted
      split at emitted
      · cases emitted
      · rename_i later laterEmitted
        have equal := Option.some.inj emitted
        subst witnesses
        obtain ⟨valid, bounded⟩ := ih laterEmitted
        obtain ⟨length, firstValid⟩ := emitCircuitWitnesses_spec firstEmitted
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
        · simp only [encodedCircuitQueryPool, List.map_append, List.flatMap_append,
            List.length_append, capacity] at *
          omega

end Aiur.AIR

namespace Aiur.BoundVerifier
open AIR Bytecode.AIR

/-- Trace rows and the checked native-style budget replace the separate
query-count premise. Native commitment/trace extraction remains separate. -/
theorem Backend.trace_circuit_execution {selection : Selection} (backend : Backend selection)
    (tables : AuxiliaryTables) (traces : CircuitTraces backend.compiled.bytecode.circuits.toList)
    {witnesses : List CircuitWitness}
    (emitted : traces.emitWitnesses backend.compiled.bytecode = some witnesses)
    {otherSlots : List Nat} {otherActive : List Bool} {otherDegrees : List Nat} {result : Nat}
    (budget : lookupQueryBound
      (backend.compiled.bytecode.circuits.toList.map (·.layout.lookups) ++ otherSlots)
      (traces.bitmap ++ otherActive) (traces.degrees ++ otherDegrees) = some result)
    (width : Nat) (input : Array G) (arity : input.size = selection.inputSize)
    (balanced : PaddedLookupBalance width
      ((buildClaim selection.function input selection.success).toList ::
        encodedCircuitQueryPool (witnesses.map (·.emission)))
      (tables.circuitProviders (witnesses.map (·.emission))))
    (publicWidth : (buildClaim selection.function input selection.success).size + 1 ≤ width)
    (queryWidths : ∀ query ∈ encodedCircuitQueryPool (witnesses.map (·.emission)), query.length ≤ width)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    (satisfied : ∀ witness ∈ witnesses, witness.Satisfied)
    (shapes : ∀ witness ∈ witnesses, witness.Shapes backend.compiled.bytecode)
    (limits : ∀ witness ∈ witnesses, witness.LookupBounds) :
    Execution backend.compiled.bytecode (memoryFacts tables.memory)
      ⟨selection.function, input, selection.success, 0⟩ := by
  obtain ⟨valid, bound⟩ := traces.emitWitnesses_spec emitted
  have totalBound := traces.capacity_bounded budget
  apply backend.encoded_circuit_execution tables witnesses width input arity balanced (by omega)
    publicWidth queryWidths memoryValid canonical
    (fun witness member => by simpa using (valid witness member).1)
    (fun witness member => (valid witness member).2) satisfied shapes limits

end Aiur.BoundVerifier
