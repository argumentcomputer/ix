/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.EmissionControls

/-! Every checked block emits, with yields scoped to their own continuation. -/

namespace Aiur.NativeAIR.BlockEmitter
open OpEmitter Bytecode

def Emission.YieldShape (size : Option Nat) (emission : Emission) : Prop :=
  ∀ part ∈ emission.yields, size = some part.values.size

theorem Emission.YieldShape.prefix {emission : Emission} {size : Option Nat}
    (valid : emission.YieldShape size) (equations : List Expr) :
    (emission.prefix equations).YieldShape size := valid

theorem join_yieldShape (rows : Array RowExpr) (column lookup : Nat) (emissions : List Emission)
    {size : Option Nat} (valid : ∀ emission ∈ emissions, emission.YieldShape size) :
    (join rows column lookup emissions).YieldShape size := by
  intro part member
  obtain ⟨emission, present, yielded⟩ := List.mem_flatMap.mp member
  exact valid emission present part yielded

private theorem list_mapM_defined_property {read : α → Option β} (inputs : List α) (property : β → Prop)
    (defined : ∀ input ∈ inputs, ∃ output, read input = some output ∧ property output) :
    ∃ outputs, inputs.mapM read = some outputs ∧ ∀ output ∈ outputs, property output := by
  induction inputs with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons input inputs ih =>
    obtain ⟨output, head, valid⟩ := defined input List.mem_cons_self
    obtain ⟨outputs, tail, rest⟩ := ih (fun value member => defined value (List.mem_cons_of_mem _ member))
    exact ⟨output :: outputs,
      by simp only [List.mapM_cons, head, tail, bind, Option.bind_some, pure],
      by simpa only [List.forall_mem_cons] using And.intro valid rest⟩

theorem branchRows_defined (selectors : Array Expr) (context : Context) (matched : RowExpr)
    (rows : Array RowExpr) (column lookup : Nat) (branches : Array (G × Block))
    (fallback : Option Block) (size : Option Nat)
    (casesDefined : ∀ pair ∈ branches.toList, ∃ entry emission,
      blockSelector selectors pair.2 = some entry ∧
        emitBlock selectors context entry rows column lookup pair.2 = some emission ∧ emission.YieldShape size)
    (defaultDefined : ∀ block, fallback = some block → ∃ entry emission,
      blockSelector selectors block = some entry ∧
        emitBlock selectors context entry rows (column + branches.size) lookup block = some emission ∧
          emission.YieldShape size) :
    ∃ emission, branchRows selectors context matched rows column lookup branches fallback = some emission ∧
      emission.YieldShape size := by
  obtain ⟨cases, casesEmitted, casesValid⟩ := list_mapM_defined_property branches.toList
    (fun emission : Emission => emission.YieldShape size) (read := caseRow selectors context matched rows column lookup) (by
      intro pair member
      obtain ⟨entry, emission, selected, emitted, valid⟩ := casesDefined pair member
      exact ⟨emission.prefix [caseEquation entry matched pair.1],
        by simp only [caseRow, selected, emitted, bind, Option.bind_some, pure], valid.prefix _⟩)
  have defaults : ∃ defaults,
      defaultRow selectors context matched rows column lookup branches fallback = some defaults ∧
        ∀ emission ∈ defaults, emission.YieldShape size := by
    cases fallback with
    | none => exact ⟨[], rfl, by simp⟩
    | some block =>
      obtain ⟨entry, emission, selected, emitted, valid⟩ := defaultDefined block rfl
      exact ⟨[emission.prefix (defaultEquations entry matched column branches)],
        by simp only [defaultRow, selected, emitted, bind, Option.bind_some, pure],
        by simpa only [List.forall_mem_singleton] using valid.prefix (defaultEquations entry matched column branches)⟩
  obtain ⟨defaults, defaultsEmitted, defaultsValid⟩ := defaults
  refine ⟨join rows column lookup (cases ++ defaults), ?_, ?_⟩
  · simp only [branchRows, casesEmitted, defaultsEmitted, bind, Option.bind_some, pure]
  · exact join_yieldShape rows column lookup _ (by simpa only [List.forall_mem_append] using And.intro casesValid defaultsValid)

mutual

theorem emitCtrl_defined (selectors : Array Expr) (context : Context) (incoming : Expr)
    (rows : Array RowExpr) (column lookup : Nat) (ctrl : Ctrl) {size : Option Nat}
    (valid : DegreeValid rows) (inputs : context.inputSize ≤ rows.size)
    (checked : ctrl.emissionChecks rows.size selectors.size size = true) :
    ∃ emission, emitCtrl selectors context incoming rows column lookup ctrl = some emission ∧ emission.YieldShape size := by
  cases ctrl with
  | «return» index outputs =>
    obtain ⟨_, outputChecks⟩ : index < selectors.size ∧ indicesInScope rows.size outputs = true := by
      simpa only [Ctrl.emissionChecks, Bool.and_eq_true, decide_eq_true_eq] using checked
    have inputChecks : indicesInScope rows.size (Array.range context.inputSize) = true := by
      rw [indicesInScope_spec]
      intro index member
      exact Nat.lt_of_lt_of_le (by simpa using member) inputs
    obtain ⟨inputValues, inputsRead⟩ := select_defined inputChecks
    obtain ⟨outputValues, outputsRead⟩ := select_defined outputChecks
    refine ⟨returned context incoming rows inputValues outputValues column lookup, ?_, ?_⟩
    · rw [emitCtrl.eq_def]
      simp only [inputsRead, outputsRead, bind, Option.bind_some, pure]
    · simp [Emission.YieldShape, returned]
  | yield index outputs =>
    obtain ⟨bound, outputChecks, width⟩ : index < selectors.size ∧
        indicesInScope rows.size outputs = true ∧ size = some outputs.size := by
      simpa only [Ctrl.emissionChecks, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using checked
    obtain ⟨outputValues, outputsRead⟩ := select_defined outputChecks
    refine ⟨yielded selectors[index] rows outputValues column lookup, ?_, ?_⟩
    · rw [emitCtrl.eq_def]
      simp only [getElem?_pos selectors index bound, outputsRead, bind, Option.bind_some, pure]
    · simpa only [Emission.YieldShape, yielded, List.forall_mem_singleton, array_mapM_size outputsRead] using width
  | «match» index branches fallback =>
    obtain ⟨bound, casesValid, defaultValid⟩ := (emissionChecks_match _ _ _ _ _ _).mp checked
    obtain ⟨emission, emitted, shape⟩ := branchRows_defined selectors context rows[index] rows column lookup branches fallback size
      (by
        intro pair member
        obtain ⟨entry, selected⟩ := blockSelector_defined selectors pair.2 (casesValid pair member)
        obtain ⟨emission, emitted, shape⟩ := emitBlock_defined selectors context entry rows column lookup pair.2
          valid inputs (casesValid pair member)
        exact ⟨entry, emission, selected, emitted, shape⟩)
      (by
        intro block present
        obtain ⟨entry, selected⟩ := blockSelector_defined selectors block (defaultValid block present)
        obtain ⟨emission, emitted, shape⟩ := emitBlock_defined selectors context entry rows (column + branches.size) lookup block
          valid inputs (defaultValid block present)
        exact ⟨entry, emission, selected, emitted, shape⟩)
    exact ⟨emission, by rw [emitCtrl_match, getElem?_pos rows index bound]; exact emitted, shape⟩
  | matchContinue index branches fallback outputs aux lookups continuation =>
    obtain ⟨bound, casesValid, defaultValid, next, added, continuationValid⟩ :=
      (emissionChecks_matchContinue _ _ _ _ _ _ _ _ _ _).mp checked
    obtain ⟨joined, joinedEmitted, shape⟩ := branchRows_defined selectors context rows[index] rows column lookup branches fallback (some outputs)
      (by
        intro pair member
        obtain ⟨entry, selected⟩ := blockSelector_defined selectors pair.2 (casesValid pair member)
        obtain ⟨emission, emitted, shape⟩ := emitBlock_defined selectors context entry rows column lookup pair.2
          valid inputs (casesValid pair member)
        exact ⟨entry, emission, selected, emitted, shape⟩)
      (by
        intro block present
        obtain ⟨entry, selected⟩ := blockSelector_defined selectors block (defaultValid block present)
        obtain ⟨emission, emitted, shape⟩ := emitBlock_defined selectors context entry rows (column + branches.size) lookup block
          valid inputs (defaultValid block present)
        exact ⟨entry, emission, selected, emitted, shape⟩)
    have yieldsValid : joined.yields.all (fun part => part.values.size == outputs) = true := by
      rw [List.all_eq_true]
      intro part member
      exact beq_iff_eq.mpr (Option.some.inj (shape part member)).symm
    have nextSize : (rows ++ advice joined.column outputs).size = next := by
      simp only [Array.size_append, advice, Array.size_ofFn, (addScope_eq added).1]
    have continuationChecks : continuation.emissionChecks (rows ++ advice joined.column outputs).size selectors.size size = true :=
      nextSize ▸ continuationValid
    obtain ⟨entry, selected⟩ := blockSelector_defined selectors continuation continuationChecks
    obtain ⟨continued, continuedEmitted, continuedShape⟩ := emitBlock_defined selectors context (yieldGate joined.yields)
      (rows ++ advice joined.column outputs) (joined.column + outputs) joined.lookup continuation
      (valid.append (advice_degreeValid _ _)) (by simp only [Array.size_append]; omega) continuationChecks
    refine ⟨joined.continued (mergeEquations incoming joined.column outputs joined.yields ++ [entry.frontSub (yieldGate joined.yields)]) continued, ?_, continuedShape⟩
    rw [emitCtrl_matchContinue, getElem?_pos rows index bound]
    simp only [joinedEmitted, continueRow, yieldsValid, if_true, selected, continuedEmitted,
      bind, Option.bind_some, pure]
termination_by sizeOf ctrl
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem (show pair ∈ branches from by simpa using member); grind)

theorem emitBlock_defined (selectors : Array Expr) (context : Context) (incoming : Expr)
    (rows : Array RowExpr) (column lookup : Nat) (block : Block) {size : Option Nat}
    (valid : DegreeValid rows) (inputs : context.inputSize ≤ rows.size)
    (checked : block.emissionChecks rows.size selectors.size size = true) :
    ∃ emission, emitBlock selectors context incoming rows column lookup block = some emission ∧ emission.YieldShape size := by
  obtain ⟨next, checkedOps, checkedCtrl⟩ := Block.emissionChecks_parts checked
  obtain ⟨entry, selected⟩ := blockSelector_defined selectors block checked
  obtain ⟨operations, operationsEmitted, valuesSize⟩ := emitOps_defined incoming context.rank block.ops.toList rows column valid checkedOps
  obtain ⟨control, controlEmitted, shape⟩ := emitCtrl_defined selectors context incoming operations.values operations.column
    (lookup + operations.queries.length) block.ctrl (emitOps_degreeValid valid operationsEmitted)
    (by have mono := checkEmissionOps_le checkedOps; omega) (valuesSize ▸ checkedCtrl)
  refine ⟨(control.afterOps incoming lookup operations).prefix [entry.frontMul ((Expr.konst 1).frontSub entry)], ?_, shape⟩
  rw [emitBlock.eq_def]
  simp only [selected, operationsEmitted, controlEmitted, bind, Option.bind_some, pure]
termination_by sizeOf block
decreasing_by cases block; simp; omega

end

end Aiur.NativeAIR.BlockEmitter
