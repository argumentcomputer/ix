/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ProviderEquivalence

/-! Physical circuit providers, auxiliary tables and witness assignments.
Provider-only function rows initialize lookup extraction; their local validity
is not assumed. Zero-weight rows can be represented by a valid inactive row. -/

namespace Aiur.AIR
open Bytecode

/-- Memory and fixed byte tables before any function-row interpretation. -/
structure AuxiliaryTables where
  memoryWidths : List Nat
  memory : Nat → Array MemoryRow
  byte1 : Byte1Kind → Fin 256 → G
  byte2 : Byte2Kind → Fin 65536 → G

def AuxiliaryTables.withFunctions (tables : AuxiliaryTables) (functions : List FunctionRow) : LookupTables :=
  ⟨functions, tables.memoryWidths, tables.memory, tables.byte1, tables.byte2⟩

def AuxiliaryTables.providers (tables : AuxiliaryTables) : List (Provider (List G)) :=
  tables.memoryWidths.flatMap (fun width =>
    mapProviders (fun request => memoryMessage width request.1 request.2)
      (memoryProviders (tables.memory width))) ++
    byte1Providers tables.byte1 ++ byte2Providers tables.byte2

def circuitProviders (emissions : List CircuitEmission) : List (Provider (List G)) :=
  emissions.map CircuitEmission.provider

def AuxiliaryTables.circuitProviders (tables : AuxiliaryTables) (emissions : List CircuitEmission) :
    List (Provider (List G)) := Aiur.AIR.circuitProviders emissions ++ tables.providers

theorem AuxiliaryTables.withFunctions_providers (tables : AuxiliaryTables) (functions : List FunctionRow) :
    (tables.withFunctions functions).providers =
      mapProviders functionMessage (functionProviders functions) ++ tables.providers := by
  simp only [withFunctions, LookupTables.providers, providers, List.append_assoc]

def FunctionRow.Provides (width : Nat) (emission : CircuitEmission) (row : FunctionRow) : Prop :=
  Provider.PaddedEq width emission.provider (functionMessage row.request, row.multiplicity)

theorem AuxiliaryTables.providers_related (tables : AuxiliaryTables) {width : Nat}
    {emissions : List CircuitEmission} {functions : List FunctionRow}
    (related : List.Forall₂ (FunctionRow.Provides width) emissions functions) :
    List.Forall₂ (Provider.PaddedEq width) (tables.circuitProviders emissions)
      (tables.withFunctions functions).providers := by
  rw [tables.withFunctions_providers]
  apply forall₂_append
  · induction related with
    | nil => exact .nil
    | cons first rest ih => exact .cons first ih
  · exact paddedProviders_refl width tables.providers

theorem AuxiliaryTables.global_of_circuit_balance (tables : AuxiliaryTables)
    {width : Nat} {queries : List (List G)} {emissions : List CircuitEmission}
    {functions : List FunctionRow}
    (balanced : PaddedLookupBalance width queries (tables.circuitProviders emissions))
    (bounded : queries.length < gSize.toNat)
    (widths : ∀ query ∈ queries, query.length ≤ width)
    (related : List.Forall₂ (FunctionRow.Provides width) emissions functions) :
    GlobalLookups (tables.withFunctions functions) width queries :=
  ⟨balanced.congr_providers (tables.providers_related related), bounded, widths⟩

def FunctionRow.inactive : FunctionRow :=
  ⟨⟨0, #[], #[], 0⟩, [], fun _ => 0, 0, 0⟩

theorem FunctionRow.inactive_valid (program : Toplevel) (memory : Bytecode.AIR.Memory) :
    inactive.Valid program memory := by
  have notActive : inactive.selector ≠ 1 := by
    intro equal
    have bad := congrArg G.n equal
    change 0 = 1 at bad
    omega
  refine ⟨Or.inl rfl, ?_, fun active => False.elim (notActive active),
    fun active => False.elim (notActive active), ?_⟩
  · change (0 : G) * (1 - 0) = 0
    rw [G.mul_comm, G.mul_zero]
  · intro edge member
    cases member

theorem FunctionRow.inactive_provides (width : Nat) {emission : CircuitEmission}
    (zero : emission.multiplicity = 0) : Provides width emission inactive :=
  ⟨zero, fun nonzero => False.elim (nonzero zero)⟩

theorem forall₂_exists_right {α β : Type} (source : List α) (relation : α → β → Prop)
    (available : ∀ item ∈ source, ∃ value, relation item value) :
    ∃ target, List.Forall₂ relation source target := by
  induction source with
  | nil => exact ⟨[], .nil⟩
  | cons first rest ih =>
    obtain ⟨value, firstRelated⟩ := available first List.mem_cons_self
    obtain ⟨values, restRelated⟩ := ih (fun item member => available item (List.mem_cons_of_mem _ member))
    exact ⟨value :: values, .cons firstRelated restRelated⟩

/-- One valued row, retaining the selected circuit and the assignment used
by its emitter. Membership, successful emission and satisfaction are proved
separately when extracting a trace. -/
structure CircuitWitness where
  circuit : Circuit
  values : Nat → G
  emission : CircuitEmission

def CircuitWitness.Emitted (program : Toplevel) (witness : CircuitWitness) : Prop :=
  witness.circuit.emitRow witness.values program = some witness.emission

def CircuitWitness.Satisfied (witness : CircuitWitness) : Prop :=
  ∀ equation ∈ witness.emission.equations, equation = 0

def CircuitWitness.Shapes (program : Toplevel) (witness : CircuitWitness) : Prop :=
  ∀ part ∈ witness.emission.members, part.function.body.lookupShapes program none = true

def CircuitWitness.LookupBounds (witness : CircuitWitness) : Prop :=
  4 ≤ witness.circuit.layout.lookups ∧
    ∀ part ∈ witness.emission.members, part.body.lookup ≤ witness.circuit.layout.lookups

theorem CircuitWitness.provider_row {program : Toplevel} (witness : CircuitWitness)
    (emitted : witness.Emitted program) (satisfied : witness.Satisfied)
    (validated : witness.circuit.validateRowCounts program = true) (shape : witness.Shapes program)
    (width : Nat) : ∃ row : FunctionRow, row.Provides width witness.emission := by
  by_cases zero : witness.emission.multiplicity = 0
  · exact ⟨FunctionRow.inactive, FunctionRow.inactive_provides width zero⟩
  · obtain ⟨request, _, message⟩ := witness.circuit.emitRow_provider witness.values program
      emitted validated shape satisfied zero width
    exact ⟨⟨request, [], witness.emission.rankBytes, 0, witness.emission.multiplicity⟩,
      rfl, fun _ => message⟩

end Aiur.AIR
