/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.RowCounts

/-! A successful circuit count check discharges all branch and terminal
count premises and the branchless single-return condition in row extraction.
Native expression reflection and the remaining layout obligations are separate. -/

namespace Aiur.Bytecode
open Aiur.AIR

theorem Toplevel.validateRowCounts_circuit {program : Toplevel}
    (validated : program.validateRowCounts = true) {circuit : Circuit}
    (member : circuit ∈ program.circuits) : circuit.validateRowCounts program = true := by
  rw [Toplevel.validateRowCounts, Array.all_eq_true'] at validated
  exact validated circuit member

private theorem mapM_of_members {α β γ : Type} (items : List α) (index : α → β) (value : α → γ)
    (read : β → Option γ) (present : ∀ item ∈ items, read (index item) = some (value item)) :
    (items.map index).mapM read = some (items.map value) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.map_cons, List.mapM_cons, present item List.mem_cons_self,
      ih (fun item member => present item (List.mem_cons_of_mem _ member))]
    rfl

theorem Circuit.validateRowCounts_members (program : Toplevel) (circuit : Circuit)
    (members : List MemberEmission)
    (indices : members.map MemberEmission.functionIndex = circuit.members.toList)
    (source : ∀ member ∈ members, program.functions[member.functionIndex]? = some member.function)
    (validated : circuit.validateRowCounts program = true) :
    circuit.members.size < gSize.toNat ∧
      (∀ part ∈ members, part.function.body.controlCounts.nodes < gSize.toNat) ∧
      (members.map (fun part => part.function.body.controlCounts.leaves)).sum ≤ circuit.layout.selectors := by
  have present := mapM_of_members members (·.functionIndex) (·.function)
    (fun index => program.functions[index]?) source
  rw [indices] at present
  rw [Circuit.validateRowCounts, present] at validated
  simpa only [Bool.and_eq_true, decide_eq_true_eq, List.all_map, List.all_eq_true,
    List.map_map, Function.comp_def] using validated

theorem Circuit.validateRowCounts_spec (row : Nat → G) (program : Toplevel) (circuit : Circuit)
    {emission : CircuitEmission} (emitted : circuit.emitRow row program = some emission)
    (validated : circuit.validateRowCounts program = true) :
    circuit.members.size < gSize.toNat ∧
      (∀ part ∈ emission.members, part.function.body.controlCounts.nodes < gSize.toNat) ∧
      (emission.members.map (fun part => part.function.body.controlCounts.leaves)).sum ≤ circuit.layout.selectors := by
  obtain ⟨_, indices, source⟩ := circuit.emitRow_spec row program emitted
  exact circuit.validateRowCounts_members program emission.members indices
    (fun part member => (source part member).present) validated

theorem flatMap_length_le_sum {α β : Type} (items : List α) (parts : α → List β)
    (bound : α → Nat) (bounded : ∀ item ∈ items, (parts item).length ≤ bound item) :
    (items.flatMap parts).length ≤ (items.map bound).sum := by
  induction items with
  | nil => exact Nat.le_refl _
  | cons first rest ih =>
    have head := bounded first List.mem_cons_self
    have tail := ih (fun item member => bounded item (List.mem_cons_of_mem _ member))
    simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
    omega

theorem Circuit.emitRow_count_bounds (row : Nat → G) (program : Toplevel) (circuit : Circuit)
    {emission : CircuitEmission} (emitted : circuit.emitRow row program = some emission)
    (validated : circuit.validateRowCounts program = true)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0) :
    circuit.members.size < gSize.toNat ∧
      (∀ part ∈ emission.members, part.function.body.rowBounds (part.selector row)) ∧
      (∀ part ∈ emission.members,
        (part.function.body.selectorFlow (part.selector row)).returns.length < gSize.toNat) ∧
      (emission.branchless = true → emission.returns.length ≤ 1) := by
  obtain ⟨bounded, nodes, leaves⟩ := circuit.validateRowCounts_spec row program emitted validated
  refine ⟨bounded, ?_, ?_, ?_⟩
  · intro part member
    exact part.function.body.rowBounds_of_controlCounts (part.selector row) (nodes part member)
  · intro part member
    exact part.function.body.return_bound_of_controlCounts (part.selector row) (nodes part member)
  · intro branchless
    obtain ⟨description, _, source⟩ := circuit.emitRow_spec row program emitted
    have valid : ∀ equation ∈ (circuitEmission row circuit emission.members).equations, equation = 0 := by
      rw [← description]
      exact satisfied
    have each : ∀ part ∈ emission.members, part.body.returns.length ≤ part.function.body.controlCounts.leaves := by
      intro part member
      have gates := congrArg List.length ((source part member).return_gates
        (circuitEmission_member_satisfied valid member))
      simp only [List.length_map] at gates
      rw [gates]
      exact part.function.body.returns_le_selectors (part.selector row)
    have combined := flatMap_length_le_sum emission.members (·.body.returns)
      (fun part => part.function.body.controlCounts.leaves) each
    have returnsEq := congrArg CircuitEmission.returns description
    rw [returnsEq]
    rw [description] at branchless
    change circuitBranchless circuit.layout.selectors (emission.members.map (·.function)) = true at branchless
    unfold circuitBranchless at branchless
    rw [Bool.and_eq_true] at branchless
    have one := beq_iff_eq.mp branchless.1
    change (emission.members.flatMap (·.body.returns)).length ≤ 1
    omega

theorem Circuit.emitRow_valid_checked {tables : LookupTables} {width : Nat} {emissions : List CircuitEmission}
    (global : GlobalLookups tables width (circuitQueryPool emissions))
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    (row : Nat → G) (program : Toplevel) (circuit : Circuit)
    {emission : CircuitEmission} (emitted : circuit.emitRow row program = some emission)
    (member : emission ∈ emissions)
    (validated : circuit.validateRowCounts program = true)
    (shape : ∀ part ∈ emission.members, part.function.body.lookupShapes program none = true)
    (reserved : 4 ≤ circuit.layout.lookups)
    (limits : ∀ part ∈ emission.members, part.body.lookup ≤ circuit.layout.lookups)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0)
    (nonzero : emission.multiplicity ≠ 0) :
    ∃ selected ∈ emission.members, ∃ interpreted : FunctionRow,
      interpreted.Valid program (memoryFacts tables.memory) ∧
      interpreted.request.function = selected.functionIndex ∧
      interpreted.request.inputs = rowValues (rowAdvice row 0 selected.function.layout.inputSize) ∧
      interpreted.request.rank = packRank emission.rankBytes ∧
      interpreted.rankBytes = emission.rankBytes ∧
      interpreted.selector = emission.selector ∧ interpreted.multiplicity = emission.multiplicity ∧
      (1, interpreted.request) ∈ emission.returns ∧
      padMessage width (emission.lookup 0).2 = padMessage width (functionMessage interpreted.request) ∧
      selected.body.CallsAt interpreted.calls ∧
      (interpreted.requests.map functionMessage) ⊆ circuitQueryPool emissions ∧
      (interpreted.byteQueries.map rangeMessage) ⊆ circuitQueryPool emissions := by
  obtain ⟨bounded, bounds, returnBound, single⟩ := circuit.emitRow_count_bounds row program emitted validated satisfied
  exact circuit.emitRow_valid global memoryValid canonical row program emitted member bounded bounds shape
    returnBound reserved limits single satisfied nonzero

end Aiur.Bytecode

namespace Aiur.BoundVerifier

theorem Backend.circuit_row_counts {selection : Selection} (backend : Backend selection)
    {circuit : Bytecode.Circuit} (member : circuit ∈ backend.compiled.bytecode.circuits) :
    circuit.validateRowCounts backend.compiled.bytecode = true :=
  Bytecode.Toplevel.validateRowCounts_circuit backend.rowCounts member

end Aiur.BoundVerifier
