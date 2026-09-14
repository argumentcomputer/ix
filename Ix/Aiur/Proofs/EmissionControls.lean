/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.EmissionInputs
import Ix.Aiur.Proofs.BlockDegrees

/-! Checked control scopes provide every selector used by circuit emission. -/

namespace Aiur.Bytecode

theorem emissionChecks_match (available selectors : Nat) (yieldSize : Option Nat)
    (index : ValIdx) (branches : Array (G × Block)) (fallback : Option Block) :
    (Ctrl.match index branches fallback).emissionChecks available selectors yieldSize = true ↔
      index < available ∧
        (∀ pair ∈ branches.toList, pair.2.emissionChecks available selectors yieldSize = true) ∧
          (∀ block, fallback = some block → block.emissionChecks available selectors yieldSize = true) := by
  rw [Ctrl.emissionChecks.eq_def]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true',
    Array.mem_attach, forall_const, Subtype.forall]
  cases fallback <;> simp

theorem emissionChecks_matchContinue (available selectors : Nat) (yieldSize : Option Nat)
    (index : ValIdx) (branches : Array (G × Block)) (fallback : Option Block)
    (size aux lookups : Nat) (continuation : Block) :
    (Ctrl.matchContinue index branches fallback size aux lookups continuation).emissionChecks
      available selectors yieldSize = true ↔
      index < available ∧
        (∀ pair ∈ branches.toList, pair.2.emissionChecks available selectors (some size) = true) ∧
          (∀ block, fallback = some block → block.emissionChecks available selectors (some size) = true) ∧
            ∃ next, addScope available size = some next ∧ continuation.emissionChecks next selectors yieldSize = true := by
  rw [Ctrl.emissionChecks.eq_def]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true',
    Array.mem_attach, forall_const, Subtype.forall]
  cases fallback <;> cases added : addScope available size <;> simp

theorem Block.emissionChecks_parts {block : Block} {available selectors : Nat} {yieldSize : Option Nat}
    (checked : block.emissionChecks available selectors yieldSize = true) :
    ∃ next, checkEmissionOps block.ops.toList available = some next ∧
      block.ctrl.emissionChecks next selectors yieldSize = true := by
  unfold Block.emissionChecks at checked
  split at checked
  · cases checked
  next next checkedOps => exact ⟨next, checkedOps, checked⟩

theorem Toplevel.validateEmission_function {program : Toplevel} (checked : program.validateEmission = true)
    {function : Function} (member : function ∈ program.functions) (constrained : function.constrained = true) :
    function.emissionChecks = true := by
  rw [Toplevel.validateEmission, Array.all_eq_true'] at checked
  simpa only [constrained, Bool.not_true, Bool.false_or] using checked function member

end Aiur.Bytecode

namespace Aiur.NativeAIR.BlockEmitter
open OpEmitter Bytecode

private theorem branchSelectors_defined (selectors : Array Expr) (branches : Array (G × Block))
    (fallback : Option Block)
    (casesDefined : ∀ pair ∈ branches.toList, ∃ entry, blockSelector selectors pair.2 = some entry)
    (defaultDefined : ∀ block, fallback = some block → ∃ entry, blockSelector selectors block = some entry) :
    ∃ entries last,
      (branches.attach.toList.mapM fun pair => blockSelector selectors pair.val.2) = some entries ∧
      (match fallback with
      | none => some []
      | some block => (blockSelector selectors block).map (fun entry => [entry])) = some last := by
  obtain ⟨entries, casesRead⟩ := list_mapM_defined branches.attach.toList (fun pair _ =>
    casesDefined pair.val (by simpa using pair.property))
  cases fallback with
  | none => exact ⟨entries, [], casesRead, rfl⟩
  | some block =>
    obtain ⟨entry, defaultRead⟩ := defaultDefined block rfl
    exact ⟨entries, [entry], casesRead, by simp only [defaultRead, Option.map_some]⟩

mutual

theorem ctrlSelector_defined (selectors : Array Expr) (ctrl : Ctrl) {available : Nat} {yieldSize : Option Nat}
    (checked : ctrl.emissionChecks available selectors.size yieldSize = true) :
    ∃ entry, ctrlSelector selectors ctrl = some entry := by
  cases ctrl with
  | «return» index outputs | yield index outputs =>
    have bound : index < selectors.size := by
      simp only [Ctrl.emissionChecks, Bool.and_eq_true, decide_eq_true_eq] at checked
      exact checked.1
    exact ⟨selectors[index], by simpa only [ctrlSelector] using getElem?_pos selectors index bound⟩
  | «match» index branches fallback =>
    obtain ⟨_, casesValid, defaultValid⟩ := (emissionChecks_match _ _ _ _ _ _).mp checked
    obtain ⟨entries, last, casesRead, defaultRead⟩ := branchSelectors_defined selectors branches fallback
      (fun pair member => blockSelector_defined selectors pair.2 (casesValid pair member))
      (fun block present => blockSelector_defined selectors block (defaultValid block present))
    refine ⟨sum (entries ++ last), ?_⟩
    rw [ctrlSelector.eq_def]
    cases fallback with
    | none => cases defaultRead; simp only [casesRead, bind, Option.bind_some, pure]
    | some block =>
      simp only at defaultRead
      simp only [casesRead, bind, Option.bind_some, pure]
      rw [defaultRead]
      rfl
  | matchContinue index branches fallback size aux lookups continuation =>
    obtain ⟨_, casesValid, defaultValid, _⟩ := (emissionChecks_matchContinue _ _ _ _ _ _ _ _ _ _).mp checked
    obtain ⟨entries, last, casesRead, defaultRead⟩ := branchSelectors_defined selectors branches fallback
      (fun pair member => blockSelector_defined selectors pair.2 (casesValid pair member))
      (fun block present => blockSelector_defined selectors block (defaultValid block present))
    refine ⟨sum (entries ++ last), ?_⟩
    rw [ctrlSelector.eq_def]
    cases fallback with
    | none => cases defaultRead; simp only [casesRead, bind, Option.bind_some, pure]
    | some block =>
      simp only at defaultRead
      simp only [casesRead, bind, Option.bind_some, pure]
      rw [defaultRead]
      rfl
termination_by sizeOf ctrl
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem (show pair ∈ branches from by simpa using member); grind)

theorem blockSelector_defined (selectors : Array Expr) (block : Block) {available : Nat} {yieldSize : Option Nat}
    (checked : block.emissionChecks available selectors.size yieldSize = true) :
    ∃ entry, blockSelector selectors block = some entry := by
  obtain ⟨_, _, control⟩ := Block.emissionChecks_parts checked
  simpa only [blockSelector] using ctrlSelector_defined selectors block.ctrl control
termination_by sizeOf block
decreasing_by cases block; simp; omega

end

end Aiur.NativeAIR.BlockEmitter
