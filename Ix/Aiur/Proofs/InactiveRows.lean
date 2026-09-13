/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CircuitRows

/-! Zero selectors satisfy every successfully emitted block, for arbitrary
logical values and advice. The all-zero circuit row therefore witnesses that
symbolic circuit constraints contain no contradictory constant equation. -/

namespace Aiur.AIR
open Bytecode

theorem selectorSum_zero (values : List G) (zero : ∀ value ∈ values, value = 0) :
    selectorSum values = 0 := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    rw [selectorSum_cons, zero value List.mem_cons_self,
      ih (fun value member => zero value (List.mem_cons_of_mem _ member)), G.zero_add]

theorem emitOp_inactive {row : Nat → G} {rank : G} (op : Op) {values : Array RowValue}
    {emission : OpEmission} (emitted : emitOp row 0 rank op values = some emission) :
    ∀ equation ∈ emission.equations, equation = 0 := by
  cases op <;> simp only [emitOp, emitAdvice, emitByte1, emitByte2, emitU32LessThan,
    emitU32Add, bind, Option.bind] at emitted
  all_goals repeat' first | split at emitted | (dsimp only at emitted; split at emitted)
  all_goals cases emitted
  all_goals simp [G.mul_comm (0 : G), G.mul_zero]

theorem emitOps_inactive {row : Nat → G} {rank : G} (ops : List Op) {values : Array RowValue}
    {column : Nat} {emission : OpsEmission} (emitted : emitOps row 0 rank ops values column = some emission) :
    ∀ equation ∈ emission.equations, equation = 0 := by
  induction ops generalizing values column emission with
  | nil => cases emitted; simp
  | cons op ops ih =>
    simp only [emitOps, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i first firstEmitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i rest restEmitted
    cases emitted
    intro equation member
    rcases List.mem_append.mp member with firstMember | restMember
    · exact emitOp_inactive op firstEmitted equation firstMember
    · exact ih restEmitted equation restMember

def BlockEmission.Inactive (emission : BlockEmission) : Prop :=
  (∀ equation ∈ emission.equations, equation = 0) ∧ ∀ part ∈ emission.yields, part.1 = 0

theorem BlockEmission.Inactive.prefix {emission : BlockEmission} (inactive : emission.Inactive)
    (equations : List G) (zero : ∀ equation ∈ equations, equation = 0) :
    (emission.prefix equations).Inactive := by
  refine ⟨?_, inactive.2⟩
  intro equation member
  rcases List.mem_append.mp member with first | last
  · exact zero equation first
  · exact inactive.1 equation last

theorem BlockEmission.Inactive.afterOps {emission : BlockEmission} (inactive : emission.Inactive)
    (incoming : G) (lookup : Nat) (ops : OpsEmission) (zero : ∀ equation ∈ ops.equations, equation = 0) :
    (emission.afterOps incoming lookup ops).Inactive := inactive.prefix _ zero

theorem joinBlockEmissions_inactive (values : Array RowValue) (column lookup : Nat)
    (emissions : List BlockEmission) (inactive : ∀ emission ∈ emissions, emission.Inactive) :
    (joinBlockEmissions values column lookup emissions).Inactive := by
  constructor
  · intro equation member
    obtain ⟨emission, member, present⟩ := List.mem_flatMap.mp member
    exact (inactive emission member).1 equation present
  · intro part member
    obtain ⟨emission, member, present⟩ := List.mem_flatMap.mp member
    exact (inactive emission member).2 part present

theorem BlockEmission.Inactive.continued {branches continuation : BlockEmission}
    (first : branches.Inactive) (last : continuation.Inactive)
    (equations : List G) (zero : ∀ equation ∈ equations, equation = 0) :
    (branches.continued equations continuation).Inactive := by
  refine ⟨?_, last.2⟩
  intro equation member
  rcases List.mem_append.mp member with before | after
  · rcases List.mem_append.mp before with branch | link
    · exact first.1 equation branch
    · exact zero equation link
  · exact last.1 equation after

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

private theorem inactive_case_smaller {branches : Array (G × Block)} {pair : G × Block}
    (member : pair ∈ branches.toList) : sizeOf pair.2 < sizeOf branches := by
  have bound := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp member)
  cases pair
  simp at bound ⊢
  omega

private theorem inactive_default_smaller {fallback : Option Block} {block : Block}
    (present : fallback = some block) : sizeOf block < sizeOf fallback := by
  rw [present]
  simp

theorem branchSelectorFlows_entry_zero (branches : Array (G × Block)) (fallback : Option Block)
    (caseZero : ∀ pair ∈ branches.toList, (pair.2.selectorFlow (fun _ => 0)).entry = 0)
    (defaultZero : ∀ block, fallback = some block → (block.selectorFlow (fun _ => 0)).entry = 0) :
    (SelectorFlow.join (branchSelectorFlows (fun _ => 0) branches fallback)).entry = 0 := by
  apply selectorSum_zero
  intro value member
  obtain ⟨flow, flowMember, equal⟩ := List.mem_map.mp member
  subst value
  rcases List.mem_append.mp flowMember with first | last
  · obtain ⟨pair, pairMember, equal⟩ := List.mem_map.mp first
    subst flow
    exact caseZero pair pairMember
  · obtain ⟨block, blockMember, equal⟩ := List.mem_map.mp last
    subst flow
    exact defaultZero block (by simpa only [Option.mem_toList] using blockMember)

mutual

theorem Ctrl.selectorFlow_entry_zero (ctrl : Ctrl) : (ctrl.selectorFlow (fun _ => 0)).entry = 0 := by
  cases ctrl with
  | «return» index values | yield index values => rw [Ctrl.selectorFlow.eq_def]; rfl
  | «match» index branches fallback =>
    rw [Ctrl.selectorFlow_match]
    exact branchSelectorFlows_entry_zero branches fallback
      (fun pair member => Block.selectorFlow_entry_zero pair.2)
      (fun block present => Block.selectorFlow_entry_zero block)
  | matchContinue index branches fallback size aux slots continuation =>
    rw [Ctrl.selectorFlow_matchContinue]
    exact branchSelectorFlows_entry_zero branches fallback
      (fun pair member => Block.selectorFlow_entry_zero pair.2)
      (fun block present => Block.selectorFlow_entry_zero block)
termination_by sizeOf ctrl
decreasing_by
  all_goals subst ctrl
  all_goals first
    | (have bound := inactive_case_smaller ‹_ ∈ _›; simp; omega)
    | (have bound := inactive_default_smaller ‹_ = some _›; simp; omega)

theorem Block.selectorFlow_entry_zero (block : Block) : (block.selectorFlow (fun _ => 0)).entry = 0 := by
  rw [Block.selectorFlow]
  exact Ctrl.selectorFlow_entry_zero block.ctrl
termination_by sizeOf block
decreasing_by cases block; simp; omega

end

theorem branchRows_inactive (row : Nat → G) (context : RowContext) (matched : G)
    (values : Array RowValue) (column lookup : Nat) (branches : Array (G × Block)) (fallback : Option Block)
    {emission : BlockEmission}
    (caseSound : ∀ pair ∈ branches.toList, ∀ result,
      pair.2.emitRow row (fun _ => 0) context 0 values column lookup = some result → result.Inactive)
    (defaultSound : ∀ block, fallback = some block → ∀ result,
      block.emitRow row (fun _ => 0) context 0 values (column + branches.size) lookup = some result → result.Inactive)
    (emitted : branchRows row (fun _ => 0) context matched values column lookup branches fallback = some emission) :
    emission.Inactive := by
  simp only [branchRows, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  rename_i cases casesEmitted
  dsimp only at emitted
  split at emitted
  · cases emitted
  rename_i defaults defaultsEmitted
  cases emitted
  have casesValid : ∀ result ∈ cases, result.Inactive := by
    have related : List.Forall₂ (fun _ result => result.Inactive) branches.toList cases := by
      apply mapM_forall₂ casesEmitted
      intro pair member result resultEmitted
      simp only [caseRow, Block.selectorFlow_entry_zero, bind, Option.bind] at resultEmitted
      split at resultEmitted
      · cases resultEmitted
      rename_i body bodyEmitted
      cases resultEmitted
      exact (caseSound pair member body bodyEmitted).prefix _ (by simp [G.mul_comm (0 : G), G.mul_zero])
    intro result member
    obtain ⟨_, _, valid⟩ := forall₂_right_member related member
    exact valid
  have defaultsValid : ∀ result ∈ defaults, result.Inactive := by
    cases present : fallback with
    | none =>
      simp only [defaultRow, present, Option.some.injEq] at defaultsEmitted
      subst defaults
      simp
    | some block =>
      simp only [defaultRow, present, Block.selectorFlow_entry_zero, bind, Option.bind] at defaultsEmitted
      split at defaultsEmitted
      · cases defaultsEmitted
      rename_i body bodyEmitted
      cases defaultsEmitted
      intro result member
      have equal := List.mem_singleton.mp member
      subst result
      apply (defaultSound block present body bodyEmitted).prefix
      simp [G.mul_comm (0 : G), G.mul_zero]
  apply joinBlockEmissions_inactive
  intro result member
  rcases List.mem_append.mp member with first | last
  · exact casesValid result first
  · exact defaultsValid result last

mutual

theorem Ctrl.emitRow_inactive (row : Nat → G) (context : RowContext) (ctrl : Ctrl)
    (values : Array RowValue) (column lookup : Nat) {emission : BlockEmission}
    (emitted : ctrl.emitRow row (fun _ => 0) context 0 values column lookup = some emission) :
    emission.Inactive := by
  cases ctrl with
  | «return» index indices | yield index indices =>
    rw [Ctrl.emitRow.eq_def] at emitted
    simp only [bind, Option.bind] at emitted
    repeat' first | split at emitted | (dsimp only at emitted; split at emitted)
    all_goals cases emitted
    all_goals simp [BlockEmission.Inactive]
  | «match» index branches fallback =>
    rw [Ctrl.emitRow_match] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    dsimp only at emitted
    exact branchRows_inactive row context _ values column lookup branches fallback
      (fun pair member result emitted => Block.emitRow_inactive row context pair.2 values column lookup emitted)
      (fun block present result emitted => Block.emitRow_inactive row context block values _ lookup emitted) emitted
  | matchContinue index branches fallback size aux slots continuation =>
    rw [Ctrl.emitRow_matchContinue] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i joined joinedEmitted
    have joinedValid := branchRows_inactive row context _ values column lookup branches fallback
      (fun pair member result emitted => Block.emitRow_inactive row context pair.2 values column lookup emitted)
      (fun block present result emitted => Block.emitRow_inactive row context block values _ lookup emitted) joinedEmitted
    have gate : selectorSum (joined.yields.map Prod.fst) = 0 := by
      apply selectorSum_zero
      intro value member
      obtain ⟨part, partMember, equal⟩ := List.mem_map.mp member
      subst value
      exact joinedValid.2 part partMember
    simp only [continueRow, gate, Block.selectorFlow_entry_zero] at emitted
    split at emitted
    · simp only [bind, Option.bind] at emitted
      split at emitted
      · cases emitted
      rename_i continued continuedEmitted
      cases emitted
      apply joinedValid.continued (Block.emitRow_inactive row context continuation _ _ _ continuedEmitted)
      intro equation member
      rcases List.mem_append.mp member with merged | linked
      · obtain ⟨index, _, equal⟩ := List.mem_map.mp merged
        rw [← equal]
        exact (G.mul_comm 0 _).trans (G.mul_zero _)
      · have equal := List.mem_singleton.mp linked
        exact equal.trans (show (0 : G) - 0 = 0 from rfl)
    · cases emitted
termination_by sizeOf ctrl
decreasing_by
  all_goals subst ctrl
  all_goals first
    | (have bound := inactive_case_smaller ‹_ ∈ _›; simp; omega)
    | (have bound := inactive_default_smaller ‹_ = some _›; simp; omega)
    | decreasing_tactic

theorem Block.emitRow_inactive (row : Nat → G) (context : RowContext) (block : Block)
    (values : Array RowValue) (column lookup : Nat) {emission : BlockEmission}
    (emitted : block.emitRow row (fun _ => 0) context 0 values column lookup = some emission) :
    emission.Inactive := by
  rw [Block.emitRow] at emitted
  simp only [bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  rename_i operations opsEmitted
  dsimp only at emitted
  split at emitted
  · cases emitted
  rename_i control ctrlEmitted
  cases emitted
  have controlValid := Ctrl.emitRow_inactive row context block.ctrl _ _ _ ctrlEmitted
  apply (controlValid.afterOps _ _ _ (emitOps_inactive block.ops.toList opsEmitted)).prefix
  simp [Block.selectorFlow_entry_zero, oneSubBooleanConstraint, G.mul_comm (0 : G), G.mul_zero]
termination_by sizeOf block
decreasing_by cases block; simp; omega

end

end Aiur.Bytecode

namespace Aiur.AIR
open Bytecode

theorem MemberEmission.entry_zero (member : MemberEmission) : member.entry (fun _ => 0) = 0 :=
  Block.selectorFlow_entry_zero member.function.body

theorem emitMember_zero {rank : G} {column lookup selectorBase : Nat} {program : Toplevel}
    {functionIndex : FunIdx} {member : MemberEmission}
    (emitted : emitMember (fun _ => 0) rank column lookup selectorBase program functionIndex = some member) :
    member.body.Inactive := by
  simp only [emitMember, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  rename_i function functionRead
  dsimp only at emitted
  split at emitted
  · cases emitted
  rename_i body bodyEmitted
  cases emitted
  simp only [Function.emitRow, Block.selectorFlow_entry_zero] at bodyEmitted
  exact Block.emitRow_inactive _ _ _ _ _ _ bodyEmitted

theorem emitMembers_zero {rank : G} (column lookup selectorBase : Nat) (program : Toplevel)
    (indices : List FunIdx) {members : List MemberEmission}
    (emitted : emitMembers (fun _ => 0) rank column lookup selectorBase program indices = some members) :
    ∀ member ∈ members, member.body.Inactive := by
  induction indices generalizing selectorBase members with
  | nil => cases emitted; simp
  | cons index indices ih =>
    simp only [emitMembers, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i member memberEmitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i rest restEmitted
    cases emitted
    intro chosen memberOf
    rcases List.mem_cons.mp memberOf with equal | later
    · subst chosen; exact emitMember_zero memberEmitted
    · exact ih _ restEmitted chosen later

theorem circuitEmission_zero (circuit : Circuit) (members : List MemberEmission)
    (inactive : ∀ member ∈ members, member.body.Inactive) :
    ∀ equation ∈ (circuitEmission (fun _ => 0) circuit members).equations, equation = 0 := by
  have selected : selectorSum (members.map (·.entry (fun _ => 0))) = 0 := by
    apply selectorSum_zero
    intro value member
    obtain ⟨part, _, equal⟩ := List.mem_map.mp member
    subst value
    exact part.entry_zero
  intro equation member
  dsimp only [circuitEmission] at member
  rw [selected] at member
  rcases List.mem_append.mp member with prior | activity
  · rcases List.mem_append.mp prior with prior | group
    · rcases List.mem_append.mp prior with body | boolean
      · obtain ⟨part, partMember, present⟩ := List.mem_flatMap.mp body
        exact (inactive part partMember).1 equation present
      · obtain ⟨_, _, equal⟩ := List.mem_map.mp boolean
        exact equal.symm.trans (show booleanConstraint 0 = 0 from rfl)
    · split at group
      · exact (List.mem_singleton.mp group).trans (show oneSubBooleanConstraint 0 = 0 from rfl)
      · cases group
  · exact (List.mem_singleton.mp activity).trans (show activityConstraint 0 0 = 0 from rfl)

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

theorem Circuit.emitRow_zero (program : Toplevel) (circuit : Circuit) {emission : CircuitEmission}
    (emitted : circuit.emitRow (fun _ => 0) program = some emission) :
    ∀ equation ∈ emission.equations, equation = 0 := by
  simp only [Circuit.emitRow, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  rename_i members membersEmitted
  cases emitted
  exact circuitEmission_zero circuit members (emitMembers_zero _ _ _ program circuit.members.toList membersEmitted)

end Aiur.Bytecode
