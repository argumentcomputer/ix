/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CircuitRows

/-!
Successful circuit emission retains the actual program functions and
member selector offsets. Satisfying header and body equations make the
circuit selector boolean. Nonzero provider multiplicity selects an active
member under the explicit member-count bound.
-/

namespace Aiur.AIR
open Bytecode

structure MemberEmission.FromProgram (row : Nat → G) (rank : G) (column lookup : Nat)
    (program : Toplevel) (member : MemberEmission) (callRanks : Array CallRank := #[]) : Prop where
  present : program.functions[member.functionIndex]? = some member.function
  emitted : member.function.emitRow row (member.selector row) member.functionIndex rank
    (rowAdvice row 0 member.function.layout.inputSize) column lookup callRanks = some member.body

theorem emitMember_spec (row : Nat → G) (rank : G) (column lookup selectorBase : Nat)
    (program : Toplevel) (functionIndex : FunIdx) {member : MemberEmission} {callRanks : Array CallRank}
    (emitted : emitMember row rank column lookup selectorBase program functionIndex callRanks = some member) :
    member.functionIndex = functionIndex ∧ member.selectorBase = selectorBase ∧
      member.FromProgram row rank column lookup program callRanks := by
  simp only [emitMember, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  · rename_i function present
    dsimp only at emitted
    split at emitted
    · cases emitted
    · rename_i body bodyEmitted
      have equal := Option.some.inj emitted
      subst member
      exact ⟨rfl, rfl, present, bodyEmitted⟩

theorem emitMembers_spec (row : Nat → G) (rank : G) (column lookup selectorBase : Nat)
    (program : Toplevel) (indices : List FunIdx) {members : List MemberEmission}
    (emitted : emitMembers row rank column lookup selectorBase program indices = some members) :
    members.map MemberEmission.functionIndex = indices ∧
      ∀ member ∈ members, member.FromProgram row rank column lookup program := by
  induction indices generalizing selectorBase members with
  | nil =>
    have equal := Option.some.inj emitted
    subst members
    exact ⟨rfl, by simp⟩
  | cons index indices ih =>
    simp only [emitMembers, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i member memberEmitted
      dsimp only at emitted
      split at emitted
      · cases emitted
      · rename_i rest restEmitted
        have equal := Option.some.inj emitted
        subst members
        obtain ⟨indexEq, _, first⟩ := emitMember_spec row rank column lookup selectorBase program index memberEmitted
        obtain ⟨indicesEq, remaining⟩ := ih _ restEmitted
        refine ⟨by rw [List.map_cons, indexEq, indicesEq], ?_⟩
        intro item present
        rcases List.mem_cons.mp present with equal | tail
        · subst item
          exact first
        · exact remaining item tail

theorem MemberEmission.FromProgram.selector_satisfied {row : Nat → G} {rank : G} {column lookup : Nat}
    {program : Toplevel} {member : MemberEmission} {callRanks : Array CallRank}
    (source : member.FromProgram row rank column lookup program callRanks)
    (satisfied : ∀ equation ∈ member.body.equations, equation = 0) :
    (member.function.body.selectorFlow (member.selector row)).Satisfied := by
  have emitted := source.emitted
  rw [Bytecode.Function.emitRow] at emitted
  exact member.function.body.emitRow_selectors row (member.selector row) _ _ _ _ _ emitted satisfied

theorem circuitEmission_member_satisfied {row : Nat → G} {circuit : Circuit} {members : List MemberEmission}
    (satisfied : ∀ equation ∈ (circuitEmission row circuit members).equations, equation = 0)
    {member : MemberEmission} (present : member ∈ members) :
    ∀ equation ∈ member.body.equations, equation = 0 := by
  intro equation member
  apply satisfied equation
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨_, present, member⟩)))

theorem circuitEmission_activity {row : Nat → G} {circuit : Circuit} {members : List MemberEmission}
    (satisfied : ∀ equation ∈ (circuitEmission row circuit members).equations, equation = 0) :
    activityConstraint (circuitEmission row circuit members).multiplicity
      (circuitEmission row circuit members).selector = 0 :=
  satisfied _ (List.mem_append_right _ List.mem_cons_self)

theorem circuitEmission_member_boolean {row : Nat → G} {rank : G} {column lookup : Nat}
    {program : Toplevel} {circuit : Circuit} {members : List MemberEmission}
    (source : ∀ member ∈ members, member.FromProgram row rank column lookup program)
    (satisfied : ∀ equation ∈ (circuitEmission row circuit members).equations, equation = 0) :
    ∀ member ∈ members, booleanConstraint (member.entry row) = 0 := by
  intro member present
  exact member.function.body.selectorFlow_boolean (member.selector row)
    ((source member present).selector_satisfied (circuitEmission_member_satisfied satisfied present))

theorem circuitEmission_boolean_of_members {row : Nat → G} {circuit : Circuit} {members : List MemberEmission}
    (individual : ∀ member ∈ members, booleanConstraint (member.entry row) = 0)
    (count : members.length = circuit.members.size)
    (satisfied : ∀ equation ∈ (circuitEmission row circuit members).equations, equation = 0) :
    booleanConstraint (circuitEmission row circuit members).selector = 0 := by
  by_cases grouped : 1 < circuit.members.size
  · have constraint : oneSubBooleanConstraint (circuitEmission row circuit members).selector = 0 := by
      apply satisfied _
      apply List.mem_append_left
      apply List.mem_append_right
      simp only [if_pos grouped]
      exact List.mem_cons_self
    rcases G.boolean_of_one_sub_constraint constraint with inactive | active
    · rw [inactive]; rfl
    · rw [active]; rfl
  · have bounded : members.length ≤ 1 := by omega
    cases members with
    | nil =>
      change booleanConstraint 0 = 0
      rw [booleanConstraint, G.mul_comm, G.mul_zero]
    | cons member rest =>
      have empty : rest = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at bounded; omega)
      subst rest
      have boolean := individual member List.mem_cons_self
      change booleanConstraint (selectorSum [member.entry row]) = 0
      rw [selectorSum_cons]
      change booleanConstraint (member.entry row + 0) = 0
      rw [G.add_zero]
      exact boolean

theorem circuitEmission_boolean {row : Nat → G} {rank : G} {column lookup : Nat}
    {program : Toplevel} {circuit : Circuit} {members : List MemberEmission}
    (source : ∀ member ∈ members, member.FromProgram row rank column lookup program)
    (count : members.length = circuit.members.size)
    (satisfied : ∀ equation ∈ (circuitEmission row circuit members).equations, equation = 0) :
    booleanConstraint (circuitEmission row circuit members).selector = 0 :=
  circuitEmission_boolean_of_members (circuitEmission_member_boolean source satisfied) count satisfied

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

theorem Circuit.emitRow_spec (row : Nat → G) (program : Toplevel) (circuit : Circuit)
    {emission : CircuitEmission} (emitted : circuit.emitRow row program = some emission) :
    emission = circuitEmission row circuit emission.members ∧
      emission.members.map MemberEmission.functionIndex = circuit.members.toList ∧
      ∀ member ∈ emission.members,
        member.FromProgram row (packRank (circuitRankBytes row circuit.layout))
          (circuit.layout.inputSize + circuit.layout.selectors + 1 + 6) 4 program := by
  simp only [Circuit.emitRow, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  · rename_i members membersEmitted
    have equal := Option.some.inj emitted
    subst emission
    obtain ⟨indices, source⟩ := emitMembers_spec row _ _ _ _ program _ membersEmitted
    exact ⟨rfl, indices, source⟩

theorem Circuit.emitRow_boolean (row : Nat → G) (program : Toplevel) (circuit : Circuit)
    {emission : CircuitEmission} (emitted : circuit.emitRow row program = some emission)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0) :
    booleanConstraint emission.selector = 0 := by
  obtain ⟨description, indices, source⟩ := circuit.emitRow_spec row program emitted
  have count := congrArg List.length indices
  simp only [List.length_map, Array.length_toList] at count
  have valid : ∀ equation ∈ (circuitEmission row circuit emission.members).equations, equation = 0 := by
    rw [← description]
    exact satisfied
  have boolean := circuitEmission_boolean source count valid
  rw [← description] at boolean
  exact boolean

theorem Circuit.emitRow_active_member (row : Nat → G) (program : Toplevel) (circuit : Circuit)
    {emission : CircuitEmission} (emitted : circuit.emitRow row program = some emission)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0)
    (bounded : circuit.members.size < gSize.toNat) (nonzero : emission.multiplicity ≠ 0) :
    ∃ member ∈ emission.members, member.entry row = 1 ∧
      member.FromProgram row (packRank emission.rankBytes)
        (circuit.layout.inputSize + circuit.layout.selectors + 1 + 6) 4 program := by
  obtain ⟨description, indices, source⟩ := circuit.emitRow_spec row program emitted
  have length := congrArg List.length indices
  simp only [List.length_map, Array.length_toList] at length
  have valid : ∀ equation ∈ (circuitEmission row circuit emission.members).equations, equation = 0 := by
    rw [← description]
    exact satisfied
  have activity := circuitEmission_activity valid
  rw [← description] at activity
  have active := nonzero_multiplicity_selector_one activity nonzero
  have individual := circuitEmission_member_boolean source valid
  have selectorEq := congrArg CircuitEmission.selector description
  have count := selectorSum_active_count
    (selectors := emission.members.map (fun member : MemberEmission => member.entry row))
    (fun gate member => by
      obtain ⟨part, partMember, equal⟩ := List.mem_map.mp member
      subst gate
      exact individual part partMember)
    (by simpa only [List.length_map, length] using bounded)
    (show selectorSum (emission.members.map (fun member => member.entry row)) = 1 from selectorEq.symm.trans active)
  have existsOne : (1 : G) ∈ emission.members.map (·.entry row) :=
    List.count_pos_iff.mp (Nat.lt_of_lt_of_eq (by decide : 0 < 1) count.symm)
  obtain ⟨member, present, selected⟩ := List.mem_map.mp existsOne
  refine ⟨member, present, selected, ?_⟩
  have rankEq := congrArg CircuitEmission.rankBytes description
  rw [rankEq]
  exact source member present

end Aiur.Bytecode
