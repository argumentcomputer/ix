/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CheckedCircuit

/-! Additional columns do not change successful graph compilation. Widths
only guard variable reads; interning, folding and root order are preserved.
This lets physical function circuits use the complete native key widths. -/

namespace Aiur.NativeAIR

def GraphWidths.Le (small large : GraphWidths) : Prop :=
  (∀ source, small.width source ≤ large.width source) ∧ small.publics ≤ large.publics

namespace Compiler

theorem compileExpr_widen {small large : GraphWidths} (widths : small.Le large)
    (allowStage2 : Bool) (expr : Expr) {nodes : List Node} {result : List Node × Nat}
    (compiled : compileExpr small allowStage2 expr nodes = some result) :
    compileExpr large allowStage2 expr nodes = some result := by
  induction expr generalizing nodes result with
  | konst | isFirstRow | isLastRow | isTransition => exact compiled
  | var column =>
    simp only [compileExpr] at compiled ⊢
    split at compiled
    · rename_i valid
      simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
      have bound := Nat.lt_of_lt_of_le valid.2 (widths.1 column.source)
      simpa only [valid.1, bound, decide_true, Bool.true_and, if_true] using compiled
    · cases compiled
  | publicInput index =>
    simp only [compileExpr] at compiled ⊢
    split at compiled
    · rename_i bound
      simpa only [Nat.lt_of_lt_of_le bound widths.2, if_true] using compiled
    · cases compiled
  | add left right ihLeft ihRight | sub left right ihLeft ihRight | mul left right ihLeft ihRight =>
    cases leftBuilt : compileExpr small allowStage2 left nodes with
    | none => simp only [compileExpr, leftBuilt, bind, Option.bind_none, reduceCtorEq] at compiled
    | some leftResult =>
      cases rightBuilt : compileExpr small allowStage2 right leftResult.1 with
      | none => simp only [compileExpr, leftBuilt, rightBuilt, bind, Option.bind_some, Option.bind_none, reduceCtorEq] at compiled
      | some rightResult =>
        simp only [compileExpr, leftBuilt, rightBuilt, bind, Option.bind_some] at compiled
        simpa only [compileExpr, ihLeft leftBuilt, ihRight rightBuilt, bind, Option.bind_some] using compiled
  | neg child ih =>
    cases childBuilt : compileExpr small allowStage2 child nodes with
    | none => simp only [compileExpr, childBuilt, bind, Option.bind_none, reduceCtorEq] at compiled
    | some childResult =>
      simp only [compileExpr, childBuilt, bind, Option.bind_some] at compiled
      simpa only [compileExpr, ih childBuilt, bind, Option.bind_some] using compiled

theorem compileExprs_widen {small large : GraphWidths} (widths : small.Le large)
    (allowStage2 : Bool) (exprs : List Expr) {nodes : List Node} {result : List Node × List Nat}
    (compiled : compileExprs small allowStage2 exprs nodes = some result) :
    compileExprs large allowStage2 exprs nodes = some result := by
  induction exprs generalizing nodes result with
  | nil => exact compiled
  | cons expr exprs ih =>
    cases headBuilt : compileExpr small allowStage2 expr nodes with
    | none => simp only [compileExprs, headBuilt, bind, Option.bind_none, reduceCtorEq] at compiled
    | some headResult =>
      cases tailBuilt : compileExprs small allowStage2 exprs headResult.1 with
      | none => simp only [compileExprs, headBuilt, tailBuilt, bind, Option.bind_some, Option.bind_none, reduceCtorEq] at compiled
      | some tailResult =>
        have headWide := compileExpr_widen widths allowStage2 expr headBuilt
        have tailWide := ih tailBuilt
        simp only [compileExprs, headBuilt, tailBuilt, bind, Option.bind_some] at compiled
        simpa only [compileExprs, headWide, tailWide, bind, Option.bind_some] using compiled

theorem compileLookup_widen {small large : GraphWidths} (widths : small.Le large)
    (lookup : ExprLookup) {nodes : List Node} {result : List Node × Lookup}
    (compiled : compileLookup small lookup nodes = some result) :
    compileLookup large lookup nodes = some result := by
  cases built : compileExprs small false lookup.exprs nodes with
  | none => simp only [compileLookup, built, bind, Option.bind_none, reduceCtorEq] at compiled
  | some exprs =>
    have wide := compileExprs_widen widths false lookup.exprs built
    simp only [compileLookup, built, bind, Option.bind_some] at compiled
    simpa only [compileLookup, wide, bind, Option.bind_some] using compiled

theorem compileLookups_widen {small large : GraphWidths} (widths : small.Le large)
    (lookups : List ExprLookup) {nodes : List Node} {result : List Node × List Lookup}
    (compiled : compileLookups small lookups nodes = some result) :
    compileLookups large lookups nodes = some result := by
  induction lookups generalizing nodes result with
  | nil => exact compiled
  | cons lookup lookups ih =>
    cases headBuilt : compileLookup small lookup nodes with
    | none => simp only [compileLookups, headBuilt, bind, Option.bind_none, reduceCtorEq] at compiled
    | some headResult =>
      cases tailBuilt : compileLookups small lookups headResult.1 with
      | none => simp only [compileLookups, headBuilt, tailBuilt, bind, Option.bind_some, Option.bind_none, reduceCtorEq] at compiled
      | some tailResult =>
        have headWide := compileLookup_widen widths lookup headBuilt
        have tailWide := ih tailBuilt
        simp only [compileLookups, headBuilt, tailBuilt, bind, Option.bind_some] at compiled
        simpa only [compileLookups, headWide, tailWide, bind, Option.bind_some] using compiled

theorem compileZeros_widen {small large : GraphWidths} (widths : small.Le large)
    (exprs : List Expr) {nodes : List Node} {result : List Node × List Nat}
    (compiled : compileZeros small exprs nodes = some result) :
    compileZeros large exprs nodes = some result := by
  induction exprs generalizing nodes result with
  | nil => exact compiled
  | cons expr exprs ih =>
    cases headBuilt : compileExpr small false expr nodes with
    | none => simp only [compileZeros, headBuilt, bind, Option.bind_none, reduceCtorEq] at compiled
    | some headResult =>
      cases recorded : recordZero headResult.1 headResult.2 with
      | none => simp only [compileZeros, headBuilt, recorded, bind, Option.bind_some, Option.bind_none, reduceCtorEq] at compiled
      | some roots =>
        cases tailBuilt : compileZeros small exprs headResult.1 with
        | none => simp only [compileZeros, headBuilt, recorded, tailBuilt, bind, Option.bind_some, Option.bind_none, reduceCtorEq] at compiled
        | some tailResult =>
          have headWide := compileExpr_widen widths false expr headBuilt
          have tailWide := ih tailBuilt
          simp only [compileZeros, headBuilt, recorded, tailBuilt, bind, Option.bind_some] at compiled
          simpa only [compileZeros, headWide, recorded, tailWide, bind, Option.bind_some] using compiled

theorem compileBase_widen {small large : GraphWidths} (widths : small.Le large)
    (lookups : List ExprLookup) (constraints : List Expr) {result : BaseCompilation}
    (compiled : compileBase small lookups constraints = some result) :
    compileBase large lookups constraints = some result := by
  cases lookupsBuilt : compileLookups small lookups [] with
  | none => simp only [compileBase, lookupsBuilt, bind, Option.bind_none, reduceCtorEq] at compiled
  | some lookupResult =>
    cases zerosBuilt : compileZeros small constraints lookupResult.1 with
    | none => simp only [compileBase, lookupsBuilt, zerosBuilt, bind, Option.bind_some, Option.bind_none, reduceCtorEq] at compiled
    | some zeroResult =>
      have lookupsWide := compileLookups_widen widths lookups lookupsBuilt
      have zerosWide := compileZeros_widen widths constraints zerosBuilt
      simp only [compileBase, lookupsBuilt, zerosBuilt, bind, Option.bind_some] at compiled
      simpa only [compileBase, lookupsWide, zerosWide, bind, Option.bind_some] using compiled

end Compiler

namespace CircuitEmitter

theorem compileCircuit_widen {small large : GraphWidths} (widths : small.Le large)
    (program : Bytecode.Toplevel) (circuit : Bytecode.Circuit) {compiled : Compiled}
    (built : compileCircuit small program circuit = some compiled) :
    compileCircuit large program circuit = some compiled := by
  cases emitted : emitCircuit program circuit with
  | none => simp only [compileCircuit, emitted, bind, Option.bind_none, reduceCtorEq] at built
  | some emission =>
    cases baseBuilt : Compiler.compileBase small emission.lookups emission.equations with
    | none => simp only [compileCircuit, emitted, baseBuilt, bind, Option.bind_some, Option.bind_none, reduceCtorEq] at built
    | some base =>
      have baseWide := Compiler.compileBase_widen widths emission.lookups emission.equations baseBuilt
      simp only [compileCircuit, emitted, baseBuilt, bind, Option.bind_some] at built
      simpa only [compileCircuit, emitted, baseWide, bind, Option.bind_some] using built

theorem circuitWidths_le {circuit : Bytecode.Circuit} {widths : GraphWidths}
    (main : circuit.layout.width ≤ widths.main) : (circuitWidths circuit).Le widths := by
  refine ⟨?_, Nat.zero_le _⟩
  intro source
  cases source <;> simp only [circuitWidths, GraphWidths.width, Nat.zero_le, main]

end CircuitEmitter
end Aiur.NativeAIR
