/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ComponentTableExecution
import Ix.Aiur.Proofs.EncodedCircuitExecution

/-! Encoded native slots and decoded component requests have identical
padded messages. The existing branchless guard supplies a single terminal
member, so the ungated optimization also has one writer in each slot. -/

namespace Aiur.AIR
open Bytecode

theorem componentCircuitEmission_single_writer {row : Nat → G} {rank : G} {base : Nat}
    {program : Toplevel} {circuit : Circuit} {members : List MemberEmission}
    (source : ∀ member ∈ members, member.FromComponent row rank base program)
    (enabled : (componentCircuitEmission row program circuit members).branchless = true)
    (slot : Nat) :
    (querySlotParts (componentCircuitEmission row program circuit members).queries slot).length ≤ 1 := by
  obtain ⟨member, membersEq, terminal⟩ := circuitBranchless_member enabled
  subst members
  have body := member.function.emitRow_terminal_writers row (member.selector row) member.functionIndex
    (if (program.componentFor member.functionIndex).ranked then rank else 0)
    (rowAdvice row 0 member.function.layout.inputSize)
    (componentColumn (program.componentFor member.functionIndex).ranked base)
    (componentLookup (program.componentFor member.functionIndex).ranked)
    terminal (source member List.mem_cons_self).emitted
  cases ranked : (program.componentFor member.functionIndex).ranked with
  | false =>
    simpa only [componentCircuitEmission, componentMembers, List.filter_cons, ranked, Bool.false_eq_true,
      if_false, List.filter_nil, List.isEmpty_nil, if_true, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] using body.single slot
  | true =>
    have body' : QueryWriters 4 member.body.lookup member.body.queries := by
      simpa only [componentLookup, ranked, if_true] using body
    have headers := QueryWriters.indexed 1 (selectorSum [member.entry row])
      ((rankByteQueries (circuitRankBytes row circuit.layout)).map rangeMessage)
    have combined := (headers.append body').permuted List.perm_append_comm
    simpa only [componentCircuitEmission, componentMembers, List.filter_cons, ranked, if_true,
      List.filter_nil, List.isEmpty_cons, Bool.false_eq_true, if_false, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil] using combined.single slot

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

theorem Circuit.emitComponentRow_queries_reflect (row : Nat → G) (program : Toplevel) (circuit : Circuit)
    {emission : CircuitEmission} (emitted : circuit.emitComponentRow row program = some emission)
    (validated : circuit.validateRowCounts program = true)
    (reserved : 0 < emission.lookupCount)
    (ranges : ∀ part ∈ emission.queries, 0 < part.slot ∧ part.slot < emission.lookupCount)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0) (width : Nat) :
    (encodedQueries emission.branchless emission.queries emission.lookupCount).map (padMessage width) =
      (decodedQueries emission.queries emission.lookupCount).map (padMessage width) := by
  obtain ⟨bounded, bounds, _, _⟩ := circuit.emitComponentRow_count_bounds row program emitted validated satisfied
  have slots := circuit.emitComponentRow_querySlots row program emitted bounded bounds reserved ranges satisfied
  obtain ⟨description, _, source⟩ := circuit.emitComponentRow_spec row program emitted
  apply slots.queries_reflect
  intro enabled slot
  have writers := componentCircuitEmission_single_writer source (by rw [← description]; exact enabled) slot
  rw [← description] at writers
  exact writers

end Aiur.Bytecode

namespace Aiur.AIR
open Bytecode

theorem componentCircuitWitnesses_queries_reflect {program : Toplevel} (witnesses : List CircuitWitness)
    (counted : program.validateRowCounts = true)
    (circuits : ∀ witness ∈ witnesses, witness.circuit ∈ program.circuits)
    (emitted : ∀ witness ∈ witnesses, witness.ComponentEmitted program)
    (satisfied : ∀ witness ∈ witnesses, witness.Satisfied)
    (ranges : ∀ witness ∈ witnesses, witness.QueryRanges) (width : Nat) :
    (encodedCircuitQueryPool (witnesses.map (·.emission))).map (padMessage width) =
      (circuitQueryPool (witnesses.map (·.emission))).map (padMessage width) := by
  simp only [encodedCircuitQueryPool, circuitQueryPool, List.map_flatMap]
  rw [List.flatMap, List.flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro emission member
  obtain ⟨witness, witnessMember, equal⟩ := List.mem_map.mp member
  subst emission
  exact witness.circuit.emitComponentRow_queries_reflect witness.values program (emitted witness witnessMember)
    (Toplevel.validateRowCounts_circuit counted (circuits witness witnessMember))
    (ranges witness witnessMember).1 (ranges witness witnessMember).2 (satisfied witness witnessMember) width

theorem componentCircuitWitnesses_decoded_widths {program : Toplevel} (witnesses : List CircuitWitness)
    (counted : program.validateRowCounts = true)
    (circuits : ∀ witness ∈ witnesses, witness.circuit ∈ program.circuits)
    (emitted : ∀ witness ∈ witnesses, witness.ComponentEmitted program)
    (satisfied : ∀ witness ∈ witnesses, witness.Satisfied)
    (ranges : ∀ witness ∈ witnesses, witness.QueryRanges) (width : Nat)
    (widths : ∀ query ∈ encodedCircuitQueryPool (witnesses.map (·.emission)), query.length ≤ width) :
    ∀ query ∈ circuitQueryPool (witnesses.map (·.emission)), query.length ≤ width := by
  intro query member
  obtain ⟨emission, emissionMember, queryMember⟩ := List.mem_flatMap.mp member
  obtain ⟨witness, witnessMember, equal⟩ := List.mem_map.mp emissionMember
  subst emission
  obtain ⟨bounded, bounds, _, _⟩ := witness.circuit.emitComponentRow_count_bounds witness.values program
    (emitted witness witnessMember) (Toplevel.validateRowCounts_circuit counted (circuits witness witnessMember))
    (satisfied witness witnessMember)
  have slots := witness.circuit.emitComponentRow_querySlots witness.values program (emitted witness witnessMember)
    bounded bounds (ranges witness witnessMember).1 (ranges witness witnessMember).2 (satisfied witness witnessMember)
  exact slots.decoded_widths witness.emission.branchless width
    (fun message present => widths message (List.mem_flatMap.mpr
      ⟨witness.emission, List.mem_map.mpr ⟨witness, witnessMember, rfl⟩, present⟩)) query queryMember

end Aiur.AIR

namespace Aiur.BoundVerifier
open AIR Bytecode.AIR

theorem Backend.public_component_circuit_execution {selection : Selection} (backend : Backend selection)
    (components : backend.compiled.bytecode.validCallComponents = true)
    (tables : AuxiliaryTables) (witnesses : List CircuitWitness) (width : Nat)
    (input : Array G) (arity : input.size = selection.inputSize)
    (balanced : PaddedLookupBalance width
      ((buildClaim selection.function input selection.success).toList :: circuitQueryPool (witnesses.map (·.emission)))
      (tables.circuitProviders (witnesses.map (·.emission))))
    (bounded : (circuitQueryPool (witnesses.map (·.emission))).length + 1 < gSize.toNat)
    (publicWidth : (buildClaim selection.function input selection.success).size + 1 ≤ width)
    (queryWidths : ∀ query ∈ circuitQueryPool (witnesses.map (·.emission)), query.length ≤ width)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    (circuits : ∀ witness ∈ witnesses, witness.circuit ∈ backend.compiled.bytecode.circuits)
    (emitted : ∀ witness ∈ witnesses, witness.ComponentEmitted backend.compiled.bytecode)
    (satisfied : ∀ witness ∈ witnesses, witness.Satisfied)
    (shapes : ∀ witness ∈ witnesses, witness.Shapes backend.compiled.bytecode)
    (constrained : ∀ witness ∈ witnesses, witness.Constrained)
    (ranges : ∀ witness ∈ witnesses, witness.QueryRanges) :
    Execution backend.compiled.bytecode (memoryFacts tables.memory) ⟨selection.function, input, selection.success, 0⟩ := by
  let request : Call := ⟨selection.function, input, selection.success, 0⟩
  have normalized : PaddedLookupBalance width
      (functionMessage request :: circuitQueryPool (witnesses.map (·.emission)))
      (tables.circuitProviders (witnesses.map (·.emission))) := by
    apply balanced.congr_queries
    change padMessage width (buildClaim selection.function input selection.success).toList :: _ =
      padMessage width (functionMessage request) :: _
    rw [show padMessage width (functionMessage request) =
      padMessage width (buildClaim selection.function input selection.success).toList from claim_padding selection width input]
  apply componentCircuitWitnesses_execute tables witnesses normalized bounded ?_ memoryValid canonical
    components backend.rowCounts backend.lookupShapes circuits emitted satisfied shapes constrained ranges
    (fun _ member => List.mem_cons_of_mem _ member) (backend.root_lookupShape input arity) List.mem_cons_self
  intro query member
  rcases List.mem_cons.mp member with same | rest
  · subst query
    change (functionMessage ⟨selection.function, input, selection.success, 0⟩).length ≤ width
    rw [claim_message, List.length_append, List.length_singleton, Array.length_toList]
    exact publicWidth
  · exact queryWidths query rest

theorem Backend.encoded_component_circuit_execution {selection : Selection} (backend : Backend selection)
    (components : backend.compiled.bytecode.validCallComponents = true)
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
    (emitted : ∀ witness ∈ witnesses, witness.ComponentEmitted backend.compiled.bytecode)
    (satisfied : ∀ witness ∈ witnesses, witness.Satisfied)
    (shapes : ∀ witness ∈ witnesses, witness.Shapes backend.compiled.bytecode)
    (constrained : ∀ witness ∈ witnesses, witness.Constrained)
    (ranges : ∀ witness ∈ witnesses, witness.QueryRanges) :
    Execution backend.compiled.bytecode (memoryFacts tables.memory) ⟨selection.function, input, selection.success, 0⟩ := by
  have messages := componentCircuitWitnesses_queries_reflect witnesses backend.rowCounts circuits emitted satisfied ranges width
  have lengths := congrArg List.length messages
  simp only [List.length_map] at lengths
  exact backend.public_component_circuit_execution components tables witnesses width input arity
    (balanced.congr_queries (by simp only [List.map_cons, messages])) (by rwa [← lengths]) publicWidth
    (componentCircuitWitnesses_decoded_widths witnesses backend.rowCounts circuits emitted satisfied ranges width queryWidths)
    memoryValid canonical circuits emitted satisfied shapes constrained ranges

end Aiur.BoundVerifier
