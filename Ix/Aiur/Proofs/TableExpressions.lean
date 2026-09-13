/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.CompiledKey

/-! The memory and byte expression builders evaluate to their physical
column models. Every read follows from the matrix dimensions. -/

namespace Aiur.NativeAIR.CompiledKey
open Compiler OpEmitter

def columns (values : Values G) (source : Source) (offset : RowOffset) (width : Nat) : Fin width → G :=
  fun index => (values.columns source offset)[index.val]?.getD 0

theorem column_eval {values : Values G} {widths : GraphWidths} (fits : values.Fits widths)
    (source : Source) (offset : RowOffset) {width : Nat} (bound : width ≤ widths.width source)
    (index : Fin width) :
    (Expr.var ⟨source, offset, index.val⟩).eval goldilocksOps values =
      some (columns values source offset width index) := by
  have inside : index.val < (values.columns source offset).size := by
    rw [fits.1]
    exact Nat.lt_of_lt_of_le index.isLt bound
  simp only [Expr.eval, columns, Array.getElem?_eq_getElem inside, Option.getD_some]

theorem memoryEquations_eval {values : Values G} {widths : GraphWidths} (fits : values.Fits widths)
    (width : Nat) (bound : 3 + width ≤ widths.main) :
    memoryEquations.mapM (Expr.eval goldilocksOps values) = some
      (AIR.memoryColumnEquations width (columns values .main .current (3 + width))
        (columns values .main .next (3 + width)) values.isTransition) := by
  have cur := column_eval fits .main .current bound
  have nxt := column_eval fits .main .next bound
  have one : (Expr.konst 1).eval goldilocksOps values = some 1 := rfl
  have selector := cur ⟨1, by omega⟩
  have multiplicity := cur ⟨0, by omega⟩
  have transition := Expr.frontMul_eval goldilocksLaws values (nxt ⟨1, by omega⟩)
    (show Expr.isTransition.eval goldilocksOps values = some values.isTransition from rfl)
  have minusOne := Expr.frontSub_eval goldilocksLaws values selector one
  have first := Expr.frontMul_eval goldilocksLaws values selector minusOne
  have second := Expr.frontMul_eval goldilocksLaws values multiplicity
    (Expr.frontSub_eval goldilocksLaws values one selector)
  have third := Expr.frontMul_eval goldilocksLaws values transition minusOne
  have fourth := Expr.frontMul_eval goldilocksLaws values transition
    (Expr.frontSub_eval goldilocksLaws values
      (Expr.frontAdd_eval goldilocksLaws values (cur ⟨2, by omega⟩) one) (nxt ⟨2, by omega⟩))
  simp only [memoryEquations, main, next, AIR.memoryColumnEquations, List.mapM_cons, List.mapM_nil,
    first, second, third, fourth, bind, Option.bind_some, pure]
  rfl

theorem memoryLookup_eval {values : Values G} {widths : GraphWidths} (fits : values.Fits widths)
    (width : Nat) (bound : 3 + width ≤ widths.main) :
    (memoryLookup width).eval goldilocksOps values =
      some (AIR.memoryColumnLookup width (columns values .main .current (3 + width))) := by
  let row := columns values .main .current (3 + width)
  have cur := column_eval fits .main .current bound
  have selector := cur ⟨1, by omega⟩
  have multiplicity := Expr.frontNeg_eval goldilocksLaws values (cur ⟨0, by omega⟩)
  have channel := Expr.frontMul_eval goldilocksLaws values selector
    (show (Expr.konst 1).eval goldilocksOps values = some 1 from rfl)
  have size := Expr.frontMul_eval goldilocksLaws values selector
    (show (Expr.konst (G.ofNat width)).eval goldilocksOps values = some (G.ofNat width) from rfl)
  have pointer := Expr.frontMul_eval goldilocksLaws values selector (cur ⟨2, by omega⟩)
  have contents := list_mapM_ofFn
    (fun i : Fin width => (main 1).frontMul (main (3 + i.val)))
    (fun i : Fin width => row ⟨1, by omega⟩ * row ⟨3 + i.val, by omega⟩)
    (Expr.eval goldilocksOps values)
    (fun i => Expr.frontMul_eval goldilocksLaws values selector (cur ⟨3 + i.val, by omega⟩))
  simp only [main] at contents
  simp only [memoryLookup, ExprLookup.eval, evalExprs, main, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mapM_cons,
    multiplicity, channel, size, pointer, contents, bind, Option.bind_some, pure,
    AIR.memoryColumnLookup, AIR.memoryMessage, AIR.decodeMemoryRow, Array.toList_ofFn,
    List.map_ofFn, Function.comp_def]
  rfl

theorem byte1Lookup_eval {values : Values G} {widths : GraphWidths} (fits : values.Fits widths)
    (mainBound : 3 ≤ widths.main) (preprocessedBound : 11 ≤ widths.preprocessed) (kind : AIR.Byte1Kind) :
    (byte1Lookup kind).eval goldilocksOps values = some
      (AIR.byte1ColumnLookup kind (columns values .preprocessed .current 11) (columns values .main .current 3)) := by
  have cur := column_eval fits .main .current mainBound
  have pre (index : Nat) (bound : index < 11) :
      (values.columns .preprocessed .current)[index]? =
        some (columns values .preprocessed .current 11 ⟨index, bound⟩) :=
    column_eval fits .preprocessed .current preprocessedBound ⟨index, bound⟩
  have multiplicity := Expr.frontNeg_eval goldilocksLaws values (cur kind.column)
  have bits := list_mapM_ofFn (fun i : Fin 8 => preprocessed (1 + i.val))
    (fun i : Fin 8 => columns values .preprocessed .current 11 ⟨1 + i.val, by omega⟩)
    (Expr.eval goldilocksOps values) (fun i => pre (1 + i.val) (by omega))
  simp only [preprocessed] at bits
  cases kind <;>
    simp only [byte1Lookup, ExprLookup.eval, evalExprs, List.cons_append, List.nil_append,
      List.mapM_cons, List.mapM_nil, main, multiplicity, preprocessed, Expr.eval, bits,
      pre 0 (by decide), pre 9 (by decide), pre 10 (by decide),
      bind, Option.bind_some, pure, AIR.byte1ColumnLookup] <;> rfl

theorem byte2Lookup_eval {values : Values G} {widths : GraphWidths} (fits : values.Fits widths)
    (mainBound : 10 ≤ widths.main) (preprocessedBound : 14 ≤ widths.preprocessed) (kind : AIR.Byte2Kind) :
    (byte2Lookup kind).eval goldilocksOps values = some
      (AIR.byte2ColumnLookup kind (columns values .preprocessed .current 14) (columns values .main .current 10)) := by
  have cur := column_eval fits .main .current mainBound
  have pre (index : Nat) (bound : index < 14) :
      (values.columns .preprocessed .current)[index]? =
        some (columns values .preprocessed .current 14 ⟨index, bound⟩) :=
    column_eval fits .preprocessed .current preprocessedBound ⟨index, bound⟩
  have multiplicity := Expr.frontNeg_eval goldilocksLaws values (cur kind.column)
  cases kind <;>
    simp only [byte2Lookup, ExprLookup.eval, evalExprs, List.cons_append, List.nil_append,
      List.mapM_cons, List.mapM_nil, main, multiplicity, preprocessed, Expr.eval,
      pre 0 (by decide), pre 1 (by decide), pre 2 (by decide), pre 3 (by decide), pre 4 (by decide),
      pre 5 (by decide), pre 6 (by decide), pre 7 (by decide), pre 8 (by decide), pre 9 (by decide),
      pre 10 (by decide), pre 11 (by decide), pre 12 (by decide), pre 13 (by decide),
      bind, Option.bind_some, pure, AIR.byte2ColumnLookup] <;> rfl

end Aiur.NativeAIR.CompiledKey
