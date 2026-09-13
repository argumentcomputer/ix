/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.OperationReflection

/-!
Symbolic operation sequences preserve the logical value map and fresh-column
cursor. Their reflection derives the entire valued emission from successful
symbolic emission and defined reads of exactly the consumed column interval.
-/

namespace Aiur.NativeAIR.OpEmitter

theorem evalRows_append {values : Values G} {left right : Array RowExpr}
    {a b : Array AIR.RowValue} (leftEval : evalRows values left = some a)
    (rightEval : evalRows values right = some b) :
    evalRows values (left ++ right) = some (a ++ b) := by
  have leftList := congrArg (Functor.map Array.toList) leftEval
  have rightList := congrArg (Functor.map Array.toList) rightEval
  change (Functor.map Array.toList) (left.mapM (RowExpr.eval values)) = _ at leftList
  change (Functor.map Array.toList) (right.mapM (RowExpr.eval values)) = _ at rightList
  rw [Array.toList_mapM] at leftList rightList
  simp only [Functor.map, Option.map_some] at leftList rightList
  simp only [evalRows, Array.mapM_eq_mapM_toList, Array.toList_append,
    List.mapM_append, leftList, rightList, bind, Option.bind_some, pure,
    Functor.map, Option.map_some]
  congr 1
  apply Array.toList_inj.mp
  simp only [Array.toList_append]

theorem Normal.append {left right : Array RowExpr} (a : Normal left) (b : Normal right) :
    Normal (left ++ right) := by
  intro row member
  rcases Array.mem_append.mp member with member | member
  · exact a row member
  · exact b row member

theorem Emission.eval_components {values : Values G} {emission : Emission} {result : AIR.OpEmission}
    (evaluated : emission.eval values = some result) :
    evalRows values emission.outputs = some result.outputs ∧ emission.used = result.used ∧
    emission.equations.mapM (evalExpr values) = some result.equations ∧
    emission.queries.mapM (List.mapM (evalExpr values)) = some result.queries ∧
    emission.calls.mapM (CallExpr.eval values) = some result.calls := by
  simp only [Emission.eval, bind, Option.bind] at evaluated
  split at evaluated
  · cases evaluated
  rename_i outputs outputsEval
  dsimp only at evaluated
  split at evaluated
  · cases evaluated
  rename_i equations equationsEval
  dsimp only at evaluated
  split at evaluated
  · cases evaluated
  rename_i queries queriesEval
  dsimp only at evaluated
  split at evaluated
  · cases evaluated
  rename_i calls callsEval
  cases evaluated
  exact ⟨outputsEval, rfl, equationsEval, queriesEval, callsEval⟩

structure OpsEmission where
  values : Array RowExpr
  column : Nat
  equations : List Expr := []
  queries : List (List Expr) := []
  calls : List CallExpr := []

def OpsEmission.eval (values : Values G) (emission : OpsEmission) : Option AIR.OpsEmission := do
  let outputs ← evalRows values emission.values
  let equations ← emission.equations.mapM (evalExpr values)
  let queries ← emission.queries.mapM (List.mapM (evalExpr values))
  let calls ← emission.calls.mapM (CallExpr.eval values)
  return ⟨outputs, emission.column, equations, queries, calls⟩

theorem OpsEmission.eval_of {values : Values G} {emission : OpsEmission} {result : AIR.OpsEmission}
    (outputs : evalRows values emission.values = some result.values)
    (column : emission.column = result.column)
    (equations : emission.equations.mapM (evalExpr values) = some result.equations)
    (queries : emission.queries.mapM (List.mapM (evalExpr values)) = some result.queries)
    (calls : emission.calls.mapM (CallExpr.eval values) = some result.calls) :
    emission.eval values = some result := by
  simp only [OpsEmission.eval, outputs, equations, queries, calls, column, bind, Option.bind_some, pure]

theorem OpsEmission.eval_components {values : Values G} {emission : OpsEmission} {result : AIR.OpsEmission}
    (evaluated : emission.eval values = some result) :
    evalRows values emission.values = some result.values ∧ emission.column = result.column ∧
    emission.equations.mapM (evalExpr values) = some result.equations ∧
    emission.queries.mapM (List.mapM (evalExpr values)) = some result.queries ∧
    emission.calls.mapM (CallExpr.eval values) = some result.calls := by
  simp only [OpsEmission.eval, bind, Option.bind] at evaluated
  split at evaluated
  · cases evaluated
  rename_i outputs outputsEval
  dsimp only at evaluated
  split at evaluated
  · cases evaluated
  rename_i equations equationsEval
  dsimp only at evaluated
  split at evaluated
  · cases evaluated
  rename_i queries queriesEval
  dsimp only at evaluated
  split at evaluated
  · cases evaluated
  rename_i calls callsEval
  cases evaluated
  exact ⟨outputsEval, rfl, equationsEval, queriesEval, callsEval⟩

def emitOps (selector rank : Expr) : List Bytecode.Op → Array RowExpr → Nat → Option OpsEmission
  | [], rows, column => some { values := rows, column }
  | op :: ops, rows, column => do
    let first ← emitOp selector rank column op rows
    let rest ← emitOps selector rank ops (rows ++ first.outputs) (column + first.used)
    return { rest with
      equations := first.equations ++ rest.equations
      queries := first.queries ++ rest.queries
      calls := first.calls ++ rest.calls }

theorem emitOps_column {selector rank : Expr} {ops : List Bytecode.Op} {rows : Array RowExpr}
    {column : Nat} {emission : OpsEmission}
    (emitted : emitOps selector rank ops rows column = some emission) : column ≤ emission.column := by
  induction ops generalizing rows column emission with
  | nil =>
    cases emitted
    exact Nat.le_refl _
  | cons op ops ih =>
    simp only [emitOps, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i rest restEmitted
    cases emitted
    exact Nat.le_trans (Nat.le_add_right _ _) (ih (emission := rest) restEmitted)

theorem emitOps_normal {selector rank : Expr} {ops : List Bytecode.Op} {rows : Array RowExpr}
    {column : Nat} {emission : OpsEmission} (normal : Normal rows)
    (emitted : emitOps selector rank ops rows column = some emission) : Normal emission.values := by
  induction ops generalizing rows column emission with
  | nil =>
    cases emitted
    exact normal
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
    exact ih (emission := rest) (normal.append (emitOp_normal normal firstEmitted)) restEmitted

theorem emitOps_reflects (values : Values G) (row : Nat → G)
    {selector rank : Expr} {s r : G} {ops : List Bytecode.Op} {rows : Array RowExpr}
    {inputs : Array AIR.RowValue} {column : Nat} {emission : OpsEmission}
    (selectorEval : evalExpr values selector = some s) (rankEval : evalExpr values rank = some r)
    (inputEval : evalRows values rows = some inputs) (normal : Normal rows)
    (emitted : emitOps selector rank ops rows column = some emission)
    (reads : ∀ index, column ≤ index → index < emission.column →
      (values.columns .main .current)[index]? = some (row index)) :
    ∃ result, AIR.emitOps row s r ops inputs column = some result ∧ emission.eval values = some result := by
  induction ops generalizing rows inputs column emission with
  | nil =>
    cases emitted
    exact ⟨_, rfl, OpsEmission.eval_of inputEval rfl rfl rfl rfl⟩
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
    have bound := emitOps_column restEmitted
    obtain ⟨firstValue, firstValueEmitted, firstEval⟩ := emitOp_reflects values
      (fun index => row (column + index)) selectorEval rankEval inputEval normal firstEmitted
      (fun index indexBound => reads (column + index) (by omega) (by dsimp only; omega))
    obtain ⟨firstOutputs, used, firstEquations, firstQueries, firstCalls⟩ :=
      Emission.eval_components firstEval
    obtain ⟨restValue, restValueEmitted, restEval⟩ := ih (evalRows_append inputEval firstOutputs)
      (normal.append (emitOp_normal normal firstEmitted)) restEmitted
      (fun index lower upper => reads index (by omega) upper)
    obtain ⟨restOutputs, finish, restEquations, restQueries, restCalls⟩ :=
      OpsEmission.eval_components restEval
    refine ⟨{ restValue with
      equations := firstValue.equations ++ restValue.equations
      queries := firstValue.queries ++ restValue.queries
      calls := firstValue.calls ++ restValue.calls }, ?_, ?_⟩
    · simp only [AIR.emitOps, firstValueEmitted, bind, Option.bind_some, ← used,
        restValueEmitted, pure]
    · apply OpsEmission.eval_of
      · exact restOutputs
      · exact finish
      all_goals
        simp only [List.mapM_append, firstEquations, restEquations, firstQueries,
          restQueries, firstCalls, restCalls, bind, Option.bind_some, pure]

end Aiur.NativeAIR.OpEmitter
