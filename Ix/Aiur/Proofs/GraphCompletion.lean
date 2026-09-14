/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.GraphCompilation

/-! Defined reads make expression and lookup compilation total. A satisfying
assignment also excludes the compiler's rejection of a nonzero constant
constraint. The latter requires an injective interpretation of constants. -/

namespace Aiur.NativeAIR.Compiler

theorem compileExpr_defined {ops : EvalOps W} {values : Values W} {widths : GraphWidths}
    (fits : values.Fits widths) (allowStage2 : Bool) (stage : widths.stage2 = 0 ∨ allowStage2 = true)
    (expr : Expr) (nodes : List Node) {value : W} (evaluated : expr.eval ops values = some value) :
    ∃ result, compileExpr widths allowStage2 expr nodes = some result := by
  induction expr generalizing nodes value with
  | konst constant => exact ⟨_, rfl⟩
  | var column =>
    have bound := (Array.getElem?_eq_some_iff.mp evaluated).choose
    rw [fits.1] at bound
    have enabled : (column.source != .stage2 || allowStage2) = true := by
      rcases stage with empty | allowed
      · cases source : column.source
        · rfl
        · rfl
        · rw [source, GraphWidths.width, empty] at bound
          omega
      · simp only [allowed, Bool.or_true]
    simp only [compileExpr, enabled, decide_eq_true bound, Bool.and_self, ite_true]
    exact ⟨_, rfl⟩
  | publicInput index =>
    have bound := (Array.getElem?_eq_some_iff.mp evaluated).choose
    rw [fits.2] at bound
    simp only [compileExpr, bound, if_true]
    exact ⟨_, rfl⟩
  | isFirstRow | isLastRow | isTransition => exact ⟨_, rfl⟩
  | add left right leftIH rightIH | sub left right leftIH rightIH | mul left right leftIH rightIH =>
    simp only [Expr.eval, bind, Option.bind] at evaluated
    split at evaluated
    · cases evaluated
    rename_i leftValue leftRead
    dsimp only at evaluated
    split at evaluated
    · cases evaluated
    rename_i rightValue rightRead
    obtain ⟨middle, first⟩ := leftIH nodes leftRead
    obtain ⟨result, last⟩ := rightIH middle.1 rightRead
    simp only [compileExpr, first, last, bind, Option.bind_some, pure]
    exact ⟨_, rfl⟩
  | neg child ih =>
    simp only [Expr.eval, bind, Option.bind] at evaluated
    split at evaluated
    · cases evaluated
    rename_i childValue childRead
    obtain ⟨result, compiled⟩ := ih nodes childRead
    simp only [compileExpr, compiled, bind, Option.bind_some, pure]
    exact ⟨_, rfl⟩

theorem compileExprs_defined {ops : EvalOps W} {values : Values W} {widths : GraphWidths}
    (fits : values.Fits widths) (allowStage2 : Bool) (stage : widths.stage2 = 0 ∨ allowStage2 = true)
    (exprs : List Expr) (nodes : List Node) {results : List W}
    (evaluated : evalExprs ops values exprs = some results) :
    ∃ result, compileExprs widths allowStage2 exprs nodes = some result := by
  induction exprs generalizing nodes results with
  | nil => exact ⟨_, rfl⟩
  | cons expr exprs ih =>
    simp only [evalExprs, List.mapM_cons, bind, Option.bind] at evaluated
    split at evaluated
    · cases evaluated
    rename_i value valueRead
    dsimp only at evaluated
    split at evaluated
    · cases evaluated
    rename_i rest restRead
    obtain ⟨middle, first⟩ := compileExpr_defined fits allowStage2 stage expr nodes valueRead
    obtain ⟨result, last⟩ := ih middle.1 restRead
    simp only [compileExprs, first, last, bind, Option.bind_some, pure]
    exact ⟨_, rfl⟩

theorem compileLookup_defined {ops : EvalOps W} {values : Values W} {widths : GraphWidths}
    (fits : values.Fits widths) (stage : widths.stage2 = 0) (lookup : ExprLookup) (nodes : List Node)
    {value : W × List W} (evaluated : lookup.eval ops values = some value) :
    ∃ result, compileLookup widths lookup nodes = some result := by
  simp only [ExprLookup.eval, bind, Option.bind] at evaluated
  split at evaluated
  · cases evaluated
  rename_i multiplicity weightRead
  dsimp only at evaluated
  split at evaluated
  · cases evaluated
  rename_i args argsRead
  obtain ⟨middle, first⟩ := compileExpr_defined fits false (.inl stage) lookup.multiplicity nodes weightRead
  obtain ⟨result, last⟩ := compileExprs_defined fits false (.inl stage) lookup.args middle.1 argsRead
  simp only [compileLookup, ExprLookup.exprs, compileExprs, first, last, bind, Option.bind_some, pure]
  exact ⟨_, rfl⟩

theorem compileLookups_defined {ops : EvalOps W} {values : Values W} {widths : GraphWidths}
    (fits : values.Fits widths) (stage : widths.stage2 = 0) (lookups : List ExprLookup) (nodes : List Node)
    {valuesRead : List (W × List W)} (evaluated : lookups.mapM (ExprLookup.eval ops values) = some valuesRead) :
    ∃ result, compileLookups widths lookups nodes = some result := by
  induction lookups generalizing nodes valuesRead with
  | nil => exact ⟨_, rfl⟩
  | cons lookup lookups ih =>
    simp only [List.mapM_cons, bind, Option.bind] at evaluated
    split at evaluated
    · cases evaluated
    rename_i value valueRead
    dsimp only at evaluated
    split at evaluated
    · cases evaluated
    rename_i rest restRead
    obtain ⟨middle, first⟩ := compileLookup_defined fits stage lookup nodes valueRead
    obtain ⟨result, last⟩ := ih middle.1 restRead
    simp only [compileLookups, first, last, bind, Option.bind_some, pure]
    exact ⟨_, rfl⟩

theorem recordZero_defined {ops : EvalOps W} {values : Values W} {nodes : List Node} {buffer : Array W}
    (injective : Function.Injective ops.konst) (valid : Evaluation ops values nodes buffer) {root : Nat}
    (read : buffer[root]? = some (ops.konst 0)) : ∃ roots, recordZero nodes root = some roots := by
  unfold recordZero
  cases found : asConst nodes root with
  | none => exact ⟨_, rfl⟩
  | some constant =>
    have zero : constant = 0 := (injective (asConst_value valid found read)).symm
    simp only [zero, beq_self_eq_true, if_true]
    exact ⟨_, rfl⟩

theorem compileZeros_defined {ops : EvalOps W} (laws : GraphEvalLaws ops)
    (injective : Function.Injective ops.konst) {values : Values W} {widths : GraphWidths}
    (fits : values.Fits widths) (stage : widths.stage2 = 0) (exprs : List Expr)
    {nodes : List Node} {buffer : Array W} (valid : Evaluation ops values nodes buffer)
    (satisfied : ExprsVanish ops values exprs) :
    ∃ result, compileZeros widths exprs nodes = some result := by
  induction exprs generalizing nodes buffer with
  | nil => exact ⟨_, rfl⟩
  | cons expr exprs ih =>
    have valueRead := satisfied expr List.mem_cons_self
    obtain ⟨middle, compiled⟩ := compileExpr_defined fits false (.inl stage) expr nodes valueRead
    obtain ⟨value, evaluated, after, afterValid, _, read⟩ :=
      compileExpr_reflects laws fits false expr valid compiled
    have equal := Option.some.inj (evaluated.symm.trans valueRead)
    rw [equal] at read
    obtain ⟨roots, recorded⟩ := recordZero_defined injective afterValid read
    obtain ⟨result, rest⟩ := ih afterValid (fun expr member => satisfied expr (List.mem_cons_of_mem _ member))
    simp only [compileZeros, compiled, recorded, rest, bind, Option.bind_some, pure]
    exact ⟨_, rfl⟩

theorem compileBase_defined {ops : EvalOps W} (laws : GraphEvalLaws ops)
    (injective : Function.Injective ops.konst) {values : Values W} {widths : GraphWidths}
    (fits : values.Fits widths) (stage : widths.stage2 = 0) (lookups : List ExprLookup) (constraints : List Expr)
    {valuesRead : List (W × List W)} (lookupsRead : lookups.mapM (ExprLookup.eval ops values) = some valuesRead)
    (satisfied : ExprsVanish ops values constraints) :
    ∃ result, compileBase widths lookups constraints = some result := by
  obtain ⟨middle, compiled⟩ := compileLookups_defined fits stage lookups [] lookupsRead
  obtain ⟨buffer, valid, _, _⟩ := compileLookups_reflects laws fits lookups (Evaluation.empty ops values) compiled
  obtain ⟨result, zeros⟩ := compileZeros_defined laws injective fits stage constraints valid satisfied
  simp only [compileBase, compiled, zeros, bind, Option.bind_some, pure]
  exact ⟨_, rfl⟩

end Aiur.NativeAIR.Compiler
