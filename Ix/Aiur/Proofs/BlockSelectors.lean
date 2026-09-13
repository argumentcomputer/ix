/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.LookupExpressions

/-!
The native block selector is a left-associated sum of its immediate branch
selectors. A continuation's selector is excluded. Selector reads use a finite
table so successful reflection requires no readings of unallocated columns.
-/

namespace Aiur.NativeAIR.BlockEmitter
open OpEmitter

theorem evaluated_read {values : Values G} {expressions : Array Expr} {results : Array G}
    (evaluated : expressions.mapM (evalExpr values) = some results)
    {index : Nat} {expr : Expr} (present : expressions[index]? = some expr) :
    evalExpr values expr = some (results[index]?.getD 0) := by
  have size := array_mapM_size evaluated
  have inputBound := (Array.getElem?_eq_some_iff.mp present).choose
  have bound : index < results.size := by omega
  have read := array_mapM_read evaluated index
  simpa only [present, bind, Option.bind_some, getElem?_pos results index bound,
    Option.getD_some] using read

theorem list_mapM_evaluate {α β γ : Type} {first : α → Option β} {evaluate : β → Option γ}
    {inputs : List α} {outputs : List β} (selected : inputs.mapM first = some outputs)
    (value : α → γ)
    (related : ∀ input output, first input = some output → evaluate output = some (value input)) :
    outputs.mapM evaluate = some (inputs.map value) := by
  obtain ⟨results, selected, evaluated⟩ := list_mapM_refine selected
    (second := fun input => some (value input))
    (fun input output read => ⟨value input, rfl, related input output read⟩)
  have equal : inputs.mapM (fun input => some (value input)) = some (inputs.map value) := by
    simpa only [List.map_id] using list_mapM_of_map inputs id value
      (fun input => some (value input)) (fun _ _ => rfl)
  rw [equal] at selected
  cases selected
  exact evaluated

def sum (expressions : List Expr) : Expr := expressions.foldl Expr.frontAdd (.konst 0)

theorem sum_fold_eval {values : Values G} {expressions : List Expr} {results : List G}
    (evaluated : expressions.mapM (evalExpr values) = some results)
    {initial : Expr} {start : G} (initialEval : evalExpr values initial = some start) :
    evalExpr values (expressions.foldl Expr.frontAdd initial) = some (results.foldl (· + ·) start) := by
  induction expressions generalizing results initial start with
  | nil =>
    cases evaluated
    exact initialEval
  | cons expr rest ih =>
    simp only [List.mapM_cons, bind, Option.bind] at evaluated
    split at evaluated
    · cases evaluated
    rename_i value valueEval
    dsimp only at evaluated
    split at evaluated
    · cases evaluated
    rename_i tail tailEval
    cases evaluated
    exact ih tailEval (Expr.frontAdd_eval goldilocksLaws values initialEval valueEval)

theorem sum_eval {values : Values G} {expressions : List Expr} {results : List G}
    (evaluated : expressions.mapM (evalExpr values) = some results) :
    evalExpr values (sum expressions) = some (AIR.selectorSum results) := sum_fold_eval evaluated rfl

def SelectorReads (values : Values G) (selectors : Array Expr) (selector : Nat → G) : Prop :=
  ∀ {index : Nat} {expr : Expr}, selectors[index]? = some expr → evalExpr values expr = some (selector index)

theorem selectors_array_eval {values : Values G} {selectors : Array Expr} {results : Array G}
    (evaluated : selectors.mapM (evalExpr values) = some results) :
    SelectorReads values selectors (fun index => results[index]?.getD 0) :=
  fun read => evaluated_read evaluated read

private theorem block_smaller (block : Bytecode.Block) : sizeOf block.ctrl < sizeOf block := by
  cases block
  simp
  omega

mutual

def ctrlSelector (selectors : Array Expr) : Bytecode.Ctrl → Option Expr
  | .return index _ | .yield index _ => selectors[index]?
  | .match _ branches fallback | .matchContinue _ branches fallback .. => do
    let entries ← branches.attach.toList.mapM fun ⟨pair, _⟩ => blockSelector selectors pair.2
    let last : List Expr ← match fallback with
      | none => some []
      | some block => (blockSelector selectors block).map (fun expr => [expr])
    return sum (entries ++ last)
termination_by ctrl => sizeOf ctrl
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

def blockSelector (selectors : Array Expr) (block : Bytecode.Block) : Option Expr :=
  ctrlSelector selectors block.ctrl
termination_by sizeOf block
decreasing_by exact block_smaller block

end

mutual

theorem ctrlSelector_reads {values : Values G} {selectors : Array Expr} {selector : Nat → G}
    (evaluated : SelectorReads values selectors selector)
    (ctrl : Bytecode.Ctrl) {expr : Expr} (selected : ctrlSelector selectors ctrl = some expr) :
    evalExpr values expr = some (ctrl.selectorFlow selector).entry := by
  cases ctrl with
  | «return» index indices | yield index indices =>
    simp only [ctrlSelector] at selected
    simpa only [Bytecode.Ctrl.selectorFlow, AIR.SelectorFlow.guard] using evaluated selected
  | «match» index branches fallback | matchContinue index branches fallback size aux lookups continuation =>
    simp only [ctrlSelector, bind, Option.bind] at selected
    split at selected
    · cases selected
    rename_i entries entriesSelected
    dsimp only at selected
    have entriesEval := list_mapM_evaluate entriesSelected
      (fun pair => (pair.val.2.selectorFlow selector).entry)
      (fun ⟨pair, _⟩ output read => blockSelector_reads evaluated pair.2 read)
    cases fallback with
    | none =>
      cases selected
      have summed := sum_eval entriesEval
      simpa only [Bytecode.Ctrl.selectorFlow, AIR.SelectorFlow.guard,
        AIR.SelectorFlow.join, AIR.SelectorFlow.continue,
        List.append_nil, List.map_map, Function.comp_def] using summed
    | some block =>
      cases entrySelected : blockSelector selectors block with
      | none => simp only [entrySelected, Option.map_none] at selected; cases selected
      | some entry =>
        simp only [entrySelected, Option.map_some] at selected
        cases selected
        have entryEval := blockSelector_reads evaluated block entrySelected
        have singleton : [entry].mapM (evalExpr values) =
            some [(block.selectorFlow selector).entry] := by
          simp only [List.mapM_cons, List.mapM_nil, entryEval, bind, Option.bind_some, pure]
        have combined : (entries ++ [entry]).mapM (evalExpr values) =
            some ((branches.attach.toList.map fun pair =>
              (pair.val.2.selectorFlow selector).entry) ++
                [(block.selectorFlow selector).entry]) := by
          simp only [List.mapM_append, entriesEval, singleton, bind, Option.bind_some, pure]
        have summed := sum_eval combined
        simpa only [Bytecode.Ctrl.selectorFlow, AIR.SelectorFlow.guard,
          AIR.SelectorFlow.join, AIR.SelectorFlow.continue, List.map_append,
          List.map_cons, List.map_nil, List.map_map, Function.comp_def] using summed
termination_by sizeOf ctrl
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

theorem blockSelector_reads {values : Values G} {selectors : Array Expr} {selector : Nat → G}
    (evaluated : SelectorReads values selectors selector)
    (block : Bytecode.Block) {expr : Expr} (selected : blockSelector selectors block = some expr) :
    evalExpr values expr = some (block.selectorFlow selector).entry := by
  simp only [blockSelector] at selected
  simpa only [Bytecode.Block.selectorFlow] using ctrlSelector_reads evaluated block.ctrl selected
termination_by sizeOf block
decreasing_by exact block_smaller block

end


theorem ctrlSelector_eval {values : Values G} {selectors : Array Expr} {results : Array G}
    (evaluated : selectors.mapM (evalExpr values) = some results)
    (ctrl : Bytecode.Ctrl) {expr : Expr} (selected : ctrlSelector selectors ctrl = some expr) :
    evalExpr values expr = some (ctrl.selectorFlow (fun index => results[index]?.getD 0)).entry :=
  ctrlSelector_reads (selectors_array_eval evaluated) ctrl selected

theorem blockSelector_eval {values : Values G} {selectors : Array Expr} {results : Array G}
    (evaluated : selectors.mapM (evalExpr values) = some results)
    (block : Bytecode.Block) {expr : Expr} (selected : blockSelector selectors block = some expr) :
    evalExpr values expr = some (block.selectorFlow (fun index => results[index]?.getD 0)).entry :=
  blockSelector_reads (selectors_array_eval evaluated) block selected

end Aiur.NativeAIR.BlockEmitter
