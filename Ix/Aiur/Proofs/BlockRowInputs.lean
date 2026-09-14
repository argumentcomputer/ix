/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.BlockRowCalls

/-!
Input-prefix preservation through the valued block emitter. Operation
outputs and continuation merges append logical values, while branch joins
restore their incoming scope. Every emitted return therefore identifies
the original function, inputs and rank, including on inactive branches.
-/

namespace Aiur.AIR
open Bytecode

theorem option_array_eq_of_toList {α : Type} {result : Option (Array α)} {expected : Array α}
    (equal : (Array.toList <$> result) = some expected.toList) : result = some expected := by
  cases result with
  | none => cases equal
  | some array => exact congrArg some (Array.toList_inj.mp (Option.some.inj equal))

theorem forall₂_imp {α β : Type} {source : List α} {target : List β}
    {first last : α → β → Prop} (related : List.Forall₂ first source target)
    (implies : ∀ left right, first left right → last left right) :
    List.Forall₂ last source target := by
  induction related with
  | nil => exact .nil
  | cons head _ ih => exact .cons (implies _ _ head) ih

theorem forall₂_of_get {α β : Type} {source : List α} {target : List β} {relation : α → β → Prop}
    (sizes : source.length = target.length)
    (related : ∀ index (leftBound : index < source.length) (rightBound : index < target.length),
      relation source[index] target[index]) : List.Forall₂ relation source target := by
  induction source generalizing target with
  | nil =>
    have empty : target = [] := List.eq_nil_of_length_eq_zero sizes.symm
    subst target
    exact .nil
  | cons head tail ih =>
    cases target with
    | nil => simp at sizes
    | cons first rest =>
      refine .cons (related 0 (by simp) (by simp)) ?_
      apply ih (Nat.succ.inj sizes)
      intro index leftBound rightBound
      exact related (index + 1) (by simpa using leftBound) (by simpa using rightBound)

theorem readValues_append {values extra : Array G} {indices : Array ValIdx} {outputs : Array G}
    (read : Bytecode.AIR.readValues values indices = some outputs) :
    Bytecode.AIR.readValues (values ++ extra) indices = some outputs := by
  have listRead := congrArg (Functor.map Array.toList) read
  rw [Bytecode.AIR.readValues, Array.toList_mapM] at listRead
  have related := mapM_forall₂ listRead (fun _ _ _ equal => equal)
  have lifted := forall₂_imp related (last := fun index value => (values ++ extra)[index]? = some value)
    (fun index value present => by
      have bound := (Array.getElem?_eq_some_iff.mp present).choose
      rw [Array.getElem?_append_left bound]
      exact present)
  apply option_array_eq_of_toList
  rw [Bytecode.AIR.readValues, Array.toList_mapM]
  exact mapM_of_forall₂ lifted

theorem readValues_range (values : Array G) :
    Bytecode.AIR.readValues values (Array.range values.size) = some values := by
  apply option_array_eq_of_toList
  rw [Bytecode.AIR.readValues, Array.toList_mapM]
  apply mapM_of_forall₂
  apply forall₂_of_get (by simp)
  intro index leftBound rightBound
  have bound : index < values.size := by simpa only [Array.length_toList] using rightBound
  simpa only [Array.getElem_toList, Array.getElem_range] using Array.getElem?_eq_getElem bound

def RowInputs (size : Nat) (inputs : Array G) (values : Array RowValue) : Prop :=
  Bytecode.AIR.readValues (rowValues values) (Array.range size) = some inputs

theorem RowInputs.append {size : Nat} {inputs : Array G} {values extra : Array RowValue}
    (preserved : RowInputs size inputs values) : RowInputs size inputs (values ++ extra) := by
  unfold RowInputs at *
  rw [rowValues_append]
  exact readValues_append preserved

theorem RowInputs.full (values : Array RowValue) : RowInputs values.size (rowValues values) values := by
  have read := readValues_range (rowValues values)
  simpa only [RowInputs, rowValues, Array.size_map] using read

theorem emitOps_inputs {row : Nat → G} {selector rank : G} {ops : List Op}
    {values : Array RowValue} {column : Nat} {emission : OpsEmission} {callRanks : Array CallRank}
    (emitted : emitOps row selector rank ops values column callRanks = some emission)
    {size : Nat} {inputs : Array G} (preserved : RowInputs size inputs values) :
    RowInputs size inputs emission.values := by
  induction ops generalizing values column emission with
  | nil =>
    simp only [emitOps, Option.some.injEq] at emitted
    subst emission
    exact preserved
  | cons op ops ih =>
    simp only [emitOps, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i first firstEmitted
      dsimp only at emitted
      split at emitted
      · cases emitted
      · rename_i rest restEmitted
        have equal := Option.some.inj emitted
        subst emission
        change RowInputs size inputs rest.values
        exact ih restEmitted preserved.append

structure InputPreservation (context : RowContext) (inputs : Array G) (emission : BlockEmission) : Prop where
  values : RowInputs context.inputSize inputs emission.values
  returned : ∀ part ∈ emission.returns,
    part.2.function = context.function ∧ part.2.inputs = inputs ∧ part.2.rank = context.rank

theorem InputPreservation.prefix {context : RowContext} {inputs : Array G} {emission : BlockEmission}
    (preserved : InputPreservation context inputs emission) (equations : List G) :
    InputPreservation context inputs (emission.prefix equations) :=
  ⟨preserved.values, preserved.returned⟩

theorem InputPreservation.afterOps {context : RowContext} {inputs : Array G} {control : BlockEmission}
    (preserved : InputPreservation context inputs control) (incoming : G) (lookup : Nat)
    (operations : OpsEmission) : InputPreservation context inputs (control.afterOps incoming lookup operations) :=
  ⟨preserved.values, preserved.returned⟩

theorem InputPreservation.join {context : RowContext} {inputs : Array G} {values : Array RowValue}
    (initial : RowInputs context.inputSize inputs values) (column lookup : Nat) (emissions : List BlockEmission)
    (preserved : ∀ emission ∈ emissions, InputPreservation context inputs emission) :
    InputPreservation context inputs (joinBlockEmissions values column lookup emissions) := by
  refine ⟨initial, ?_⟩
  intro part member
  obtain ⟨emission, emissionMember, partMember⟩ := List.mem_flatMap.mp member
  exact (preserved emission emissionMember).returned part partMember

theorem InputPreservation.continued {context : RowContext} {inputs : Array G}
    {branches continuation : BlockEmission}
    (first : InputPreservation context inputs branches) (last : InputPreservation context inputs continuation)
    (equations : List G) : InputPreservation context inputs (branches.continued equations continuation) := by
  refine ⟨last.values, ?_⟩
  intro part member
  rcases List.mem_append.mp member with left | right
  · exact first.returned part left
  · exact last.returned part right

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

theorem branchRows_inputs (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (matched : G) (values : Array RowValue) (column lookup : Nat)
    (branches : Array (G × Block)) (fallback : Option Block) {emission : BlockEmission}
    {inputs : Array G} (initial : RowInputs context.inputSize inputs values)
    (emitted : branchRows row selector context matched values column lookup branches fallback = some emission)
    (caseSound : ∀ pair ∈ branches.toList, ∀ emission,
      pair.2.emitRow row selector context (pair.2.selectorFlow selector).entry values column lookup = some emission →
      InputPreservation context inputs emission)
    (defaultSound : ∀ block, fallback = some block → ∀ emission,
      block.emitRow row selector context (block.selectorFlow selector).entry values
        (column + branches.size) lookup = some emission → InputPreservation context inputs emission) :
    InputPreservation context inputs emission := by
  simp only [branchRows, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  · rename_i cases casesEmitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    · rename_i default defaultEmitted
      have equal := Option.some.inj emitted
      subst emission
      have casesPreserved : ∀ emission ∈ cases, InputPreservation context inputs emission := by
        apply forall₂_right_property
        apply mapM_forall₂ casesEmitted
        intro pair member result resultEmitted
        simp only [caseRow, bind, Option.bind] at resultEmitted
        split at resultEmitted
        · cases resultEmitted
        · rename_i body bodyEmitted
          have equal := Option.some.inj resultEmitted
          subst result
          exact (caseSound pair member body bodyEmitted).prefix _
      have defaultPreserved : ∀ emission ∈ default, InputPreservation context inputs emission := by
        cases fallback with
        | none =>
          simp only [defaultRow, Option.some.injEq] at defaultEmitted
          subst default
          simp
        | some block =>
          simp only [defaultRow, bind, Option.bind] at defaultEmitted
          split at defaultEmitted
          · cases defaultEmitted
          · rename_i body bodyEmitted
            have equal := Option.some.inj defaultEmitted
            subst default
            intro emission member
            have equal := List.mem_singleton.mp member
            subst emission
            exact (defaultSound block rfl body bodyEmitted).prefix _
      apply InputPreservation.join initial
      intro emission member
      rcases List.mem_append.mp member with left | right
      · exact casesPreserved emission left
      · exact defaultPreserved emission right

private theorem block_input_smaller (block : Block) : sizeOf block.ctrl < sizeOf block := by
  cases block
  simp
  omega

mutual

theorem Ctrl.emitRow_inputs (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (incoming : G) (values : Array RowValue) (column lookup : Nat) (ctrl : Ctrl)
    {emission : BlockEmission} {inputs : Array G} (initial : RowInputs context.inputSize inputs values)
    (emitted : ctrl.emitRow row selector context incoming values column lookup = some emission) :
    InputPreservation context inputs emission := by
  cases ctrl with
  | «return» index indices =>
    rw [Ctrl.emitRow.eq_def] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i provided readInputs
      dsimp only at emitted
      split at emitted
      · cases emitted
      · have equal := Option.some.inj emitted
        subst emission
        refine ⟨initial, ?_⟩
        intro part member
        have equal := List.mem_singleton.mp member
        subst part
        exact ⟨rfl, Option.some.inj (readInputs.symm.trans initial), rfl⟩
  | yield index indices =>
    rw [Ctrl.emitRow.eq_def] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · have equal := Option.some.inj emitted
      subst emission
      exact ⟨initial, by simp⟩
  | «match» index branches fallback =>
    rw [Ctrl.emitRow_match] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i matched read
      apply branchRows_inputs row selector context matched.value values column lookup branches fallback initial emitted
      · intro pair member body bodyEmitted
        exact Block.emitRow_inputs row selector context _ values column lookup pair.2 initial bodyEmitted
      · intro block present body bodyEmitted
        exact Block.emitRow_inputs row selector context _ values _ lookup block initial bodyEmitted
  | matchContinue index branches fallback size aux slots continuation =>
    rw [Ctrl.emitRow_matchContinue] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i matched read
      dsimp only at emitted
      split at emitted
      · cases emitted
      · rename_i joined branchesEmitted
        have branchesPreserved := branchRows_inputs row selector context matched.value values column lookup
          branches fallback initial branchesEmitted
          (fun pair member body bodyEmitted =>
            Block.emitRow_inputs row selector context _ values column lookup pair.2 initial bodyEmitted)
          (fun block present body bodyEmitted =>
            Block.emitRow_inputs row selector context _ values _ lookup block initial bodyEmitted)
        simp only [continueRow] at emitted
        split at emitted
        · simp only [bind, Option.bind] at emitted
          split at emitted
          · cases emitted
          · rename_i continued contEmitted
            have contPreserved := Block.emitRow_inputs row selector context _ _ _ _ continuation initial.append contEmitted
            have equal := Option.some.inj emitted
            subst emission
            exact branchesPreserved.continued contPreserved _
        · cases emitted
termination_by sizeOf ctrl
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem (Array.mem_def.mpr ‹_ ∈ _›); grind)

theorem Block.emitRow_inputs (row : Nat → G) (selector : SelIdx → G) (context : RowContext)
    (incoming : G) (values : Array RowValue) (column lookup : Nat) (block : Block)
    {emission : BlockEmission} {inputs : Array G} (initial : RowInputs context.inputSize inputs values)
    (emitted : block.emitRow row selector context incoming values column lookup = some emission) :
    InputPreservation context inputs emission := by
  rw [Block.emitRow] at emitted
  simp only [bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  · rename_i operations opsEmitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    · rename_i control ctrlEmitted
      have preserved := Ctrl.emitRow_inputs row selector context incoming _ _ _ block.ctrl
        (emitOps_inputs opsEmitted initial) ctrlEmitted
      have equal := Option.some.inj emitted
      subst emission
      exact (preserved.afterOps incoming lookup operations).prefix _
termination_by sizeOf block
decreasing_by exact block_input_smaller block

end

end Aiur.Bytecode
