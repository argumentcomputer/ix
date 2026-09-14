/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.OperationDegrees
import Ix.Aiur.Proofs.BlockExpressions

/-! The degree-zero constant invariant survives branches and continuations. -/

namespace Aiur.NativeAIR.BlockEmitter
open OpEmitter

theorem branchRows_values {selectors : Array Expr} {context : Context} {matched : RowExpr}
    {rows : Array RowExpr} {column lookup : Nat} {branches : Array (G × Bytecode.Block)}
    {fallback : Option Bytecode.Block} {emission : Emission}
    (emitted : branchRows selectors context matched rows column lookup branches fallback = some emission) :
    emission.values = rows := by
  simp only [branchRows, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  dsimp only at emitted
  split at emitted
  · cases emitted
  cases emitted
  rfl

mutual

theorem emitCtrl_degreeValid {selectors : Array Expr} {context : Context} {incoming : Expr}
    {rows : Array RowExpr} {column lookup : Nat} (ctrl : Bytecode.Ctrl) {emission : Emission}
    (valid : DegreeValid rows)
    (emitted : emitCtrl selectors context incoming rows column lookup ctrl = some emission) :
    DegreeValid emission.values := by
  cases ctrl with
  | «return» index indices | yield index indices =>
    simp only [emitCtrl, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    cases emitted
    exact valid
  | «match» index branches fallback =>
    rw [emitCtrl_match] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    dsimp only at emitted
    rw [branchRows_values emitted]
    exact valid
  | matchContinue index branches fallback size aux lookups continuation =>
    rw [emitCtrl_matchContinue] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    simp only [continueRow] at emitted
    split at emitted
    · simp only [bind, Option.bind] at emitted
      split at emitted
      · cases emitted
      dsimp only at emitted
      split at emitted
      · cases emitted
      rename_i continued continuedEmitted
      cases emitted
      change DegreeValid continued.values
      exact emitBlock_degreeValid continuation (valid.append (advice_degreeValid _ _)) continuedEmitted
    · cases emitted
termination_by sizeOf ctrl
decreasing_by all_goals decreasing_tactic

theorem emitBlock_degreeValid {selectors : Array Expr} {context : Context} {incoming : Expr}
    {rows : Array RowExpr} {column lookup : Nat} (block : Bytecode.Block) {emission : Emission}
    (valid : DegreeValid rows)
    (emitted : emitBlock selectors context incoming rows column lookup block = some emission) :
    DegreeValid emission.values := by
  simp only [emitBlock, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  dsimp only at emitted
  split at emitted
  · cases emitted
  rename_i operations operationsEmitted
  dsimp only at emitted
  split at emitted
  · cases emitted
  rename_i control controlEmitted
  cases emitted
  change DegreeValid control.values
  exact emitCtrl_degreeValid block.ctrl (emitOps_degreeValid valid operationsEmitted) controlEmitted
termination_by sizeOf block
decreasing_by cases block; simp; omega

end

end Aiur.NativeAIR.BlockEmitter
