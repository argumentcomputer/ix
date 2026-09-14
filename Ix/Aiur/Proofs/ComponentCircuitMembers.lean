/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ComponentCircuitRows
import Ix.Aiur.Proofs.CircuitRowReturns

/-! Component member provenance and selector conservation. The circuit
header equations are shared across rank policies; each body retains its
own rank, column cursor, lookup cursor and call-rank table. -/

namespace Aiur.AIR
open Bytecode

def MemberEmission.FromComponent (row : Nat → G) (rank : G) (base : Nat)
    (program : Toplevel) (member : MemberEmission) : Prop :=
  member.FromProgram row (if (program.componentFor member.functionIndex).ranked then rank else 0)
    (componentColumn (program.componentFor member.functionIndex).ranked base)
    (componentLookup (program.componentFor member.functionIndex).ranked)
    program (program.callRanksFor member.functionIndex)

theorem emitComponentMember_spec {row : Nat → G} {rank : G} {base selectorBase : Nat}
    {program : Toplevel} {functionIndex : FunIdx} {member : MemberEmission}
    (emitted : emitComponentMember row rank base selectorBase program functionIndex = some member) :
    member.functionIndex = functionIndex ∧ member.FromComponent row rank base program := by
  obtain ⟨index, present, _, body⟩ := emitComponentMember_present emitted
  refine ⟨index, ?_⟩
  unfold MemberEmission.FromComponent
  rw [index]
  exact ⟨by rw [index]; exact present, by simpa only [index] using body⟩

theorem componentCircuitEmission_member_boolean {row : Nat → G} {rank : G} {base : Nat}
    {program : Toplevel} {circuit : Circuit} {members : List MemberEmission}
    (source : ∀ member ∈ members, member.FromComponent row rank base program)
    (satisfied : ∀ equation ∈ (componentCircuitEmission row program circuit members).equations, equation = 0) :
    ∀ member ∈ members, booleanConstraint (member.entry row) = 0 := by
  intro member present
  exact member.function.body.selectorFlow_boolean (member.selector row)
    (MemberEmission.FromProgram.selector_satisfied (source member present)
      (circuitEmission_member_satisfied satisfied present))

theorem componentCircuitEmission_boolean {row : Nat → G} {rank : G} {base : Nat}
    {program : Toplevel} {circuit : Circuit} {members : List MemberEmission}
    (source : ∀ member ∈ members, member.FromComponent row rank base program)
    (count : members.length = circuit.members.size)
    (satisfied : ∀ equation ∈ (componentCircuitEmission row program circuit members).equations, equation = 0) :
    booleanConstraint (componentCircuitEmission row program circuit members).selector = 0 :=
  circuitEmission_boolean_of_members (componentCircuitEmission_member_boolean source satisfied) count satisfied

theorem componentCircuitEmission_gateCount {row : Nat → G} {rank : G} {base : Nat}
    {program : Toplevel} {circuit : Circuit} {members : List MemberEmission}
    (source : ∀ member ∈ members, member.FromComponent row rank base program)
    (count : members.length = circuit.members.size) (bounded : circuit.members.size < gSize.toNat)
    (satisfied : ∀ equation ∈ (componentCircuitEmission row program circuit members).equations, equation = 0) :
    ((members.map (·.entry row)).map gateCount).sum =
      gateCount (componentCircuitEmission row program circuit members).selector := by
  rw [gateCount_list]
  apply selector_gateCount
  · intro gate present
    obtain ⟨member, memberPresent, same⟩ := List.mem_map.mp present
    subst gate
    exact componentCircuitEmission_member_boolean source satisfied member memberPresent
  · simpa only [List.length_map, count] using bounded
  · exact componentCircuitEmission_boolean source count satisfied

theorem selectorSum_boolean_of_count {gates : List G}
    (individual : ∀ gate ∈ gates, booleanConstraint gate = 0) (count : gates.count 1 ≤ 1) :
    booleanConstraint (selectorSum gates) = 0 := by
  rw [selectorSum_eq_count gates (fun gate present => G.boolean_of_constraint (individual gate present))]
  have alternatives : gates.count 1 = 0 ∨ gates.count 1 = 1 := by omega
  rcases alternatives with zero | one
  · rw [zero]
    rfl
  · rw [one]
    rfl

theorem componentCircuitEmission_rank_boolean {row : Nat → G} {rank : G} {base : Nat}
    {program : Toplevel} {circuit : Circuit} {members : List MemberEmission}
    (source : ∀ member ∈ members, member.FromComponent row rank base program)
    (count : members.length = circuit.members.size) (bounded : circuit.members.size < gSize.toNat)
    (satisfied : ∀ equation ∈ (componentCircuitEmission row program circuit members).equations, equation = 0) :
    booleanConstraint (selectorSum ((componentMembers program members).map (·.entry row))) = 0 := by
  have individual := componentCircuitEmission_member_boolean source satisfied
  apply selectorSum_boolean_of_count
  · intro gate present
    obtain ⟨member, memberPresent, same⟩ := List.mem_map.mp present
    subst gate
    exact individual member (List.mem_filter.mp memberPresent).1
  · have subset := (List.filter_sublist (p := fun member : MemberEmission =>
      (program.componentFor member.functionIndex).ranked) (l := members)).map (fun member => member.entry row)
    have smaller := subset.count_le (1 : G)
    have counts := componentCircuitEmission_gateCount source count bounded satisfied
    rw [gateCount_list] at counts
    exact Nat.le_trans smaller (counts ▸ gateCount_le_one _)

theorem componentCircuitEmission_rank_count {row : Nat → G} {rank : G} {base : Nat}
    {program : Toplevel} {circuit : Circuit} {members : List MemberEmission}
    (source : ∀ member ∈ members, member.FromComponent row rank base program)
    (count : members.length = circuit.members.size) (bounded : circuit.members.size < gSize.toNat)
    (satisfied : ∀ equation ∈ (componentCircuitEmission row program circuit members).equations, equation = 0) :
    (((componentMembers program members).map (·.entry row)).map gateCount).sum =
      gateCount (selectorSum ((componentMembers program members).map (·.entry row))) := by
  rw [gateCount_list]
  apply selector_gateCount
  · intro gate present
    obtain ⟨member, memberPresent, same⟩ := List.mem_map.mp present
    subst gate
    exact componentCircuitEmission_member_boolean source satisfied member (List.mem_filter.mp memberPresent).1
  · simp only [List.length_map]
    exact Nat.lt_of_le_of_lt (List.length_filter_le _ _) (count ▸ bounded)
  · exact componentCircuitEmission_rank_boolean source count bounded satisfied

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

theorem Circuit.emitComponentRow_spec (row : Nat → G) (program : Toplevel) (circuit : Circuit)
    {emission : CircuitEmission} (emitted : circuit.emitComponentRow row program = some emission) :
    emission = componentCircuitEmission row program circuit emission.members ∧
      emission.members.map MemberEmission.functionIndex = circuit.members.toList ∧
      ∀ member ∈ emission.members, member.FromComponent row (packRank (circuitRankBytes row circuit.layout))
        (circuit.layout.inputSize + circuit.layout.selectors + 1) program := by
  simp only [Circuit.emitComponentRow, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  rename_i members membersEmitted
  cases emitted
  obtain ⟨indices, source⟩ := emitComponentMembers_present membersEmitted
  exact ⟨rfl, indices, fun member present => (emitComponentMember_spec (source member present)).2⟩

theorem Circuit.emitComponentRow_boolean (row : Nat → G) (program : Toplevel) (circuit : Circuit)
    {emission : CircuitEmission} (emitted : circuit.emitComponentRow row program = some emission)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0) :
    booleanConstraint emission.selector = 0 := by
  obtain ⟨description, indices, source⟩ := circuit.emitComponentRow_spec row program emitted
  have count := congrArg List.length indices
  simp only [List.length_map, Array.length_toList] at count
  have valid : ∀ equation ∈ (componentCircuitEmission row program circuit emission.members).equations, equation = 0 := by
    rw [← description]
    exact satisfied
  have boolean := componentCircuitEmission_boolean source count valid
  rw [← description] at boolean
  exact boolean

end Aiur.Bytecode
