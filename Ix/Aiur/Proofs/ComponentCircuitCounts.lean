/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ComponentCircuitMembers
import Ix.Aiur.Proofs.CircuitRowCounts

/-! The enforced row-count check controls component members, branches and
returns. A nonzero shared provider supplies the selected component member's
actual return message before interpreting any of its calls. -/

namespace Aiur.AIR
open Bytecode

theorem componentCircuitEmission_return_count {row : Nat → G} {rank : G} {base : Nat}
    {program : Toplevel} {circuit : Circuit} {members : List MemberEmission}
    (source : ∀ member ∈ members, member.FromComponent row rank base program)
    (shape : ∀ member ∈ members, member.function.body.lookupShapes program none = true)
    (bounded : members.length < gSize.toNat)
    (returnBound : ∀ member ∈ members,
      (member.function.body.selectorFlow (member.selector row)).returns.length < gSize.toNat)
    (satisfied : ∀ equation ∈ (componentCircuitEmission row program circuit members).equations, equation = 0)
    (active : (componentCircuitEmission row program circuit members).selector = 1) :
    ((componentCircuitEmission row program circuit members).returns.map Prod.fst).count 1 = 1 := by
  have each := fun member present => MemberEmission.FromProgram.return_count (source member present)
    (shape member present) (returnBound member present) (circuitEmission_member_satisfied satisfied present)
  change ((members.flatMap (·.body.returns)).map Prod.fst).count 1 = 1
  rw [flatMap_return_count members (fun member => member.entry row) (fun member => member.body.returns) each]
  apply selectorSum_active_count
  · intro gate present
    obtain ⟨member, memberPresent, same⟩ := List.mem_map.mp present
    subst gate
    exact componentCircuitEmission_member_boolean source satisfied member memberPresent
  · simpa only [List.length_map] using bounded
  · exact active

theorem componentCircuitEmission_return_message {row : Nat → G} {rank : G} {base : Nat}
    {program : Toplevel} {circuit : Circuit} {members : List MemberEmission}
    (source : ∀ member ∈ members, member.FromComponent row rank base program)
    (shape : ∀ member ∈ members, member.function.body.lookupShapes program none = true)
    (bounded : members.length < gSize.toNat)
    (returnBound : ∀ member ∈ members,
      (member.function.body.selectorFlow (member.selector row)).returns.length < gSize.toNat)
    (satisfied : ∀ equation ∈ (componentCircuitEmission row program circuit members).equations, equation = 0)
    (active : (componentCircuitEmission row program circuit members).selector = 1)
    (width : Nat)
    (single : (componentCircuitEmission row program circuit members).branchless = true →
      (componentCircuitEmission row program circuit members).returns.length ≤ 1)
    {request : Bytecode.AIR.Call} (present : (1, request) ∈ (componentCircuitEmission row program circuit members).returns) :
    padMessage width ((componentCircuitEmission row program circuit members).lookup 0).2 =
      padMessage width (functionMessage request) := by
  have count := componentCircuitEmission_return_count source shape bounded returnBound satisfied active
  apply slotMessage_chosen_count width (componentCircuitEmission row program circuit members).branchless
    (by simpa only [List.length_map] using single)
    (fun part member => ?_)
    (by simpa only [List.map_map, Function.comp_def] using count)
    (List.mem_map.mpr ⟨(1, request), present, rfl⟩) rfl
  obtain ⟨returned, returnMember, same⟩ := List.mem_map.mp member
  subst part
  obtain ⟨body, bodyMember, returnedMember⟩ := List.mem_flatMap.mp returnMember
  exact MemberEmission.FromProgram.return_boolean (source body bodyMember)
    (circuitEmission_member_satisfied satisfied bodyMember) returned returnedMember

theorem componentCircuitEmission_member_rank {row : Nat → G} {program : Toplevel}
    {circuit : Circuit} {members : List MemberEmission} {member : MemberEmission} (present : member ∈ members) :
    (if (program.componentFor member.functionIndex).ranked then
      packRank (componentCircuitEmission row program circuit members).rankBytes else 0) =
    (if (program.componentFor member.functionIndex).ranked then packRank (circuitRankBytes row circuit.layout) else 0) := by
  cases ranked : (program.componentFor member.functionIndex).ranked with
  | false => simp only [Bool.false_eq_true, if_false]
  | true =>
    have inside : member ∈ componentMembers program members := List.mem_filter.mpr ⟨present, ranked⟩
    have nonempty := List.isEmpty_eq_false_iff_exists_mem.mpr ⟨member, inside⟩
    simp only [if_true, componentCircuitEmission, nonempty, Bool.false_eq_true, if_false]

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

theorem Circuit.emitComponentRow_count_bounds (row : Nat → G) (program : Toplevel) (circuit : Circuit)
    {emission : CircuitEmission} (emitted : circuit.emitComponentRow row program = some emission)
    (validated : circuit.validateRowCounts program = true)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0) :
    circuit.members.size < gSize.toNat ∧
      (∀ part ∈ emission.members, part.function.body.rowBounds (part.selector row)) ∧
      (∀ part ∈ emission.members,
        (part.function.body.selectorFlow (part.selector row)).returns.length < gSize.toNat) ∧
      (emission.branchless = true → emission.returns.length ≤ 1) := by
  obtain ⟨description, indices, source⟩ := circuit.emitComponentRow_spec row program emitted
  obtain ⟨bounded, nodes, leaves⟩ := circuit.validateRowCounts_members program emission.members indices
    (fun part member => (source part member).present) validated
  refine ⟨bounded, ?_, ?_, ?_⟩
  · intro part member
    exact part.function.body.rowBounds_of_controlCounts (part.selector row) (nodes part member)
  · intro part member
    exact part.function.body.return_bound_of_controlCounts (part.selector row) (nodes part member)
  · intro branchless
    have valid : ∀ equation ∈ (componentCircuitEmission row program circuit emission.members).equations, equation = 0 := by
      rw [← description]
      exact satisfied
    have each : ∀ part ∈ emission.members, part.body.returns.length ≤ part.function.body.controlCounts.leaves := by
      intro part member
      have gates := congrArg List.length (MemberEmission.FromProgram.return_gates (source part member)
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

theorem Circuit.emitComponentRow_active_member (row : Nat → G) (program : Toplevel) (circuit : Circuit)
    {emission : CircuitEmission} (emitted : circuit.emitComponentRow row program = some emission)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0)
    (bounded : circuit.members.size < gSize.toNat) (nonzero : emission.multiplicity ≠ 0) :
    ∃ member ∈ emission.members, member.entry row = 1 ∧
      member.FromComponent row (packRank emission.rankBytes)
        (circuit.layout.inputSize + circuit.layout.selectors + 1) program := by
  obtain ⟨description, indices, source⟩ := circuit.emitComponentRow_spec row program emitted
  have length := congrArg List.length indices
  simp only [List.length_map, Array.length_toList] at length
  have valid : ∀ equation ∈ (componentCircuitEmission row program circuit emission.members).equations, equation = 0 := by
    rw [← description]
    exact satisfied
  have activity := circuitEmission_activity valid
  have multiplicityEq := congrArg CircuitEmission.multiplicity description
  change emission.multiplicity = (circuitEmission row circuit emission.members).multiplicity at multiplicityEq
  have active := nonzero_multiplicity_selector_one activity (multiplicityEq ▸ nonzero)
  change selectorSum (emission.members.map (fun member : MemberEmission => member.entry row)) = 1 at active
  have count := selectorSum_active_count
    (selectors := emission.members.map (fun member : MemberEmission => member.entry row))
    (fun gate present => by
      obtain ⟨member, memberPresent, same⟩ := List.mem_map.mp present
      subst gate
      exact componentCircuitEmission_member_boolean source valid member memberPresent)
    (by simpa only [List.length_map, length] using bounded) active
  have existsOne : (1 : G) ∈ emission.members.map (·.entry row) := List.count_pos_iff.mp (by omega)
  obtain ⟨member, present, selected⟩ := List.mem_map.mp existsOne
  refine ⟨member, present, selected, ?_⟩
  have rankEq := componentCircuitEmission_member_rank (program := program) (circuit := circuit) (row := row) present
  rw [← description] at rankEq
  unfold MemberEmission.FromComponent
  rw [rankEq]
  exact source member present

theorem Circuit.emitComponentRow_provider (row : Nat → G) (program : Toplevel) (circuit : Circuit)
    {emission : CircuitEmission} (emitted : circuit.emitComponentRow row program = some emission)
    (validated : circuit.validateRowCounts program = true)
    (shape : ∀ part ∈ emission.members, part.function.body.lookupShapes program none = true)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0)
    (nonzero : emission.multiplicity ≠ 0) (width : Nat) :
    ∃ request : AIR.Call, (1, request) ∈ emission.returns ∧
      padMessage width (emission.lookup 0).2 = padMessage width (functionMessage request) := by
  obtain ⟨bounded, _, returnBound, single⟩ := circuit.emitComponentRow_count_bounds row program emitted validated satisfied
  obtain ⟨description, indices, source⟩ := circuit.emitComponentRow_spec row program emitted
  have size := congrArg List.length indices
  simp only [List.length_map, Array.length_toList] at size
  have valid : ∀ equation ∈ (componentCircuitEmission row program circuit emission.members).equations, equation = 0 := by
    rw [← description]
    exact satisfied
  have active : (componentCircuitEmission row program circuit emission.members).selector = 1 :=
    nonzero_multiplicity_selector_one (circuitEmission_activity valid) (by
      change (componentCircuitEmission row program circuit emission.members).multiplicity ≠ 0
      rw [← description]
      exact nonzero)
  have count := componentCircuitEmission_return_count source shape (by omega) returnBound valid active
  rw [← description] at count
  have present : (1 : G) ∈ emission.returns.map Prod.fst := List.count_pos_iff.mp (by rw [count]; decide)
  obtain ⟨⟨gate, request⟩, member, gateEq⟩ := List.mem_map.mp present
  change gate = 1 at gateEq
  subst gate
  refine ⟨request, member, ?_⟩
  have message := componentCircuitEmission_return_message source shape (by omega) returnBound valid active width
    (by rw [← description]; exact single) (by rw [← description]; exact member)
  rw [← description] at message
  exact message

end Aiur.Bytecode
