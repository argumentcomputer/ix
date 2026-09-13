/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.OperationDegrees
import Ix.Aiur.Proofs.CompilerAllocation

/-! Symbolic emission agrees with the compiler's logical degrees and physical
auxiliary allocation. Degree-zero constant folding is justified by the invariant
preserved from the initial advice map. -/

namespace Aiur.NativeAIR.OpEmitter
open Aiur.Bytecode

def rowDegrees (rows : Array RowExpr) : Array Nat := rows.map RowExpr.degree

theorem rowDegrees_empty : rowDegrees #[] = #[] := Array.map_empty

theorem rowDegrees_append (left right : Array RowExpr) :
    rowDegrees (left ++ right) = rowDegrees left ++ rowDegrees right := Array.map_append

theorem rowDegrees_push (rows : Array RowExpr) (row : RowExpr) :
    rowDegrees (rows.push row) = (rowDegrees rows).push row.degree := Array.map_push

theorem rowDegrees_singleton (row : RowExpr) : rowDegrees #[row] = #[row.degree] :=
  Array.map_singleton

theorem rowDegrees_getD (rows : Array RowExpr) (index : Nat) :
    (rowDegrees rows)[index]?.getD 0 = (rows[index]?.getD (.konst 0)).degree := by
  simp only [rowDegrees, Array.getElem?_map]
  cases rows[index]? <;> rfl

theorem rowDegrees_read {rows : Array RowExpr} {index : Nat} {row : RowExpr}
    (read : rows[index]? = some row) : (rowDegrees rows)[index]?.getD 0 = row.degree := by
  rw [rowDegrees_getD, read]
  rfl

theorem select_degrees {rows : Array RowExpr} {indices : Array Nat} {selected : Array RowExpr}
    (read : select rows indices = some selected) :
    indices.map (fun index => (rowDegrees rows)[index]?.getD 0) = rowDegrees selected := by
  have selectedMap := congrArg rowDegrees (array_map_getD_of_mapM (.konst 0) read)
  simpa only [rowDegrees, Array.map_map, Function.comp_def, ← rowDegrees_getD] using selectedMap

theorem advice_degrees (first count : Nat) :
    rowDegrees (advice first count) = Array.replicate count 1 := by
  apply Array.ext (by simp only [rowDegrees, Array.size_map, advice, Array.size_ofFn, Array.size_replicate])
  intro index _ _
  simp only [rowDegrees, advice, Array.getElem_map, Array.getElem_ofFn,
    Array.getElem_replicate, mainCurrent, RowExpr.variable]

theorem packFour_degree (bytes : Fin 4 → RowExpr) :
    (packFour bytes).degree = (rowDegrees (Array.ofFn bytes)).foldl Nat.max 0 := by
  simp only [rowDegrees, Array.map_ofFn, ← Array.foldl_toList, Array.toList_ofFn,
    list_ofFn_four, List.foldl_cons, List.foldl_nil, Function.comp_def,
    packFour, RowExpr.add, RowExpr.mul, RowExpr.konst, Nat.add_zero]

theorem readWord_degree {rows : Array RowExpr} {indices : Array Nat} {word : RowExpr}
    (read : readWord rows indices = some word) :
    word.degree = selectedDegree (rowDegrees rows) indices 0 := by
  simp only [readWord, bind, Option.bind] at read
  split at read
  · cases read
  next size =>
    cases selected : select rows indices <;> simp only [selected] at read
    · cases read
    next bytes =>
      cases read
      have width : indices.size = 4 := by omega
      rw [packFour_degree, array_ofFn_getD bytes (.konst 0) ((array_mapM_size selected).trans width)]
      simp only [selectedDegree, select_degrees selected]

def Emission.allocation (emission : Emission) : OpAllocation :=
  ⟨rowDegrees emission.outputs, emission.used⟩

theorem emitAdvice_allocation (first count : Nat) :
    (emitAdvice first count).allocation = .advice count := by
  simp only [Emission.allocation, emitAdvice, advice_degrees, OpAllocation.advice]

theorem emitWordSum_allocation (first : Nat) (sum : RowExpr) :
    (emitWordSum first sum).allocation = ⟨(Array.replicate 4 1).push (max sum.degree 1), 4⟩ := by
  simp only [Emission.allocation, emitWordSum, rowDegrees_push, advice_degrees,
    RowExpr.mul, RowExpr.sub, RowExpr.konst, packedAdvice, packFour, RowExpr.add,
    mainCurrent, RowExpr.variable, Nat.add_zero]
  rfl

theorem emitByte1_dispatch_allocation (selector rank : Expr) (first : Nat) (kind : AIR.Byte1Kind)
    (index : Nat) {rows : Array RowExpr} {emission : Emission}
    (emitted : emitOp selector rank first (kind.op index) rows = some emission) :
    emission.allocation = (kind.op index).allocation (rowDegrees rows) := by
  rw [emitOp_byte1] at emitted
  simp only [bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  cases emitted
  cases kind <;> simp only [Emission.allocation, emitByte1, advice_degrees,
    AIR.Byte1Kind.op, AIR.Byte1Kind.outputSize, Op.allocation, OpAllocation.advice]

theorem emitByte2_dispatch_allocation (selector rank : Expr) (first : Nat) (kind : AIR.Byte2Kind)
    (a b : Nat) {rows : Array RowExpr} {emission : Emission}
    (emitted : emitOp selector rank first (kind.op a b) rows = some emission) :
    emission.allocation = (kind.op a b).allocation (rowDegrees rows) := by
  rw [emitOp_byte2] at emitted
  simp only [bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  rename_i left readA
  dsimp only at emitted
  split at emitted
  · cases emitted
  rename_i right readB
  cases emitted
  have degreeA := rowDegrees_read readA
  have degreeB := rowDegrees_read readB
  cases kind <;> simp only [Emission.allocation, emitByte2, advice_degrees, rowDegrees_push,
    AIR.Byte2Kind.op, AIR.Byte2Kind.outputSize, Op.allocation, OpAllocation.advice,
    byteCarry, degreeA, degreeB] <;> rfl

theorem emitOp_allocation {selector rank : Expr} {first : Nat} {op : Op}
    {rows : Array RowExpr} {emission : Emission} (valid : DegreeValid rows)
    (emitted : emitOp selector rank first op rows = some emission) :
    emission.allocation = op.allocation (rowDegrees rows) := by
  cases op with
  | const value =>
    cases emitted
    simp only [Emission.allocation, fromScalar, rowDegrees_singleton, RowExpr.konst, Op.allocation]
  | add a b | sub a b | mul a b =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i left readA
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i right readB
    cases emitted
    have degreeA := rowDegrees_read readA
    have degreeB := rowDegrees_read readB
    simp only [Emission.allocation, fromScalar, rowDegrees_singleton, Op.allocation, degreeA, degreeB]
    first
    | rfl
    | (simp only [emitMul, RowExpr.mul]; split <;>
        simp_all only [if_pos, mulRegular, mainCurrent, RowExpr.variable, OpAllocation.advice] <;> rfl)
  | eqZero index =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i input read
    cases emitted
    have allocated := emitEqZero_allocation selector first (valid.read read)
    simp only [Emission.allocation, fromScalar, rowDegrees_singleton, Op.allocation, rowDegrees_read read]
    split at allocated <;>
      simp_all only [Prod.mk.injEq, if_true, if_false]
  | call function indices size unconstrained =>
    cases unconstrained with
    | true =>
      cases emitted
      simp only [emitAdvice_allocation, Op.allocation, if_true, Nat.add_zero, OpAllocation.advice]
    | false =>
      simp only [emitOp, Bool.false_eq_true, if_false, bind, Option.bind] at emitted
      split at emitted
      · cases emitted
      cases emitted
      simp only [Emission.allocation, emitCall, advice_degrees, Op.allocation,
        Bool.false_eq_true, if_false]
  | store indices | load size index =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    cases emitted
    simp only [Emission.allocation, emitStore, emitLoad, advice_degrees, Op.allocation, OpAllocation.advice]
  | assertEq xs ys message =>
    simp only [emitOp] at emitted
    split at emitted
    · cases emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    cases emitted
    simp only [Emission.allocation, emitAssert, rowDegrees_empty, Op.allocation]
  | ioGetInfo | ioRead | unconstrainedBigUintDivMod | unconstrainedGToBytes | unconstrainedGInverse =>
    cases emitted
    exact emitAdvice_allocation _ _
  | ioSetInfo | ioWrite | debug =>
    cases emitted
    simp only [Emission.allocation, rowDegrees_empty, Op.allocation]
  | u8BitDecomposition index => exact emitByte1_dispatch_allocation selector rank first .bits index emitted
  | u8ShiftLeft index => exact emitByte1_dispatch_allocation selector rank first .shiftLeft index emitted
  | u8ShiftRight index => exact emitByte1_dispatch_allocation selector rank first .shiftRight index emitted
  | u8Xor a b => exact emitByte2_dispatch_allocation selector rank first .xor a b emitted
  | u8Add a b => exact emitByte2_dispatch_allocation selector rank first .add a b emitted
  | u8Sub a b => exact emitByte2_dispatch_allocation selector rank first .sub a b emitted
  | u8And a b => exact emitByte2_dispatch_allocation selector rank first .and a b emitted
  | u8Or a b => exact emitByte2_dispatch_allocation selector rank first .or a b emitted
  | u8LessThan a b => exact emitByte2_dispatch_allocation selector rank first .lessThan a b emitted
  | u8RangeCheck a b => exact emitByte2_dispatch_allocation selector rank first .range a b emitted
  | u8Mul a b => exact emitByte2_dispatch_allocation selector rank first .mul a b emitted
  | u8XorSplit7 a b => exact emitByte2_dispatch_allocation selector rank first .split7 a b emitted
  | u8XorSplit4 a b => exact emitByte2_dispatch_allocation selector rank first .split4 a b emitted
  | u32LessThan a b =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    cases emitted
    simp only [Emission.allocation, emitU32LessThan, rowDegrees_singleton, Op.allocation]
  | unconstrainedU32Add a b =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i left readA
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i right readB
    cases emitted
    simp only [emitWordSum_allocation, Op.allocation, RowExpr.add,
      readWord_degree readA, readWord_degree readB, selectedDegree_append,
      selectedDegree_initial (rowDegrees rows) a 1]
    simp only [Nat.max_assoc, Nat.max_comm]
  | unconstrainedU32Add3 a b c =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i left readA
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i right readB
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i third readC
    cases emitted
    simp only [emitWordSum_allocation, Op.allocation, RowExpr.add,
      readWord_degree readA, readWord_degree readB, readWord_degree readC,
      selectedDegree_append, selectedDegree_initial (rowDegrees rows) a 1]
    simp only [Nat.max_assoc, Nat.max_comm]
  | u32ToField indices =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i word read
    cases emitted
    simp only [Emission.allocation, fromScalar, rowDegrees_singleton, Op.allocation, readWord_degree read]

theorem emitOp_layout {selector rank : Expr} {first : Nat} {op : Op}
    {rows : Array RowExpr} {emission : Emission} (initial : Concrete.Bytecode.LayoutMState)
    (valid : DegreeValid rows) (aligned : rowDegrees rows = initial.degrees)
    (emitted : emitOp selector rank first op rows = some emission) :
    ((Concrete.Bytecode.opLayout op).run initial).2.degrees = rowDegrees (rows ++ emission.outputs) ∧
    ((Concrete.Bytecode.opLayout op).run initial).2.functionLayout.auxiliaries =
      initial.functionLayout.auxiliaries + emission.used := by
  have allocated := emitOp_allocation valid emitted
  rw [aligned] at allocated
  have degrees := congrArg OpAllocation.degrees allocated
  have auxiliaries := congrArg OpAllocation.auxiliaries allocated
  obtain ⟨layoutDegrees, layoutAux⟩ := Concrete.Bytecode.opLayout_allocation op initial
  simp only [Emission.allocation] at degrees auxiliaries
  rw [← degrees] at layoutDegrees
  rw [← auxiliaries] at layoutAux
  exact ⟨by simpa only [rowDegrees_append, aligned] using layoutDegrees, layoutAux⟩

theorem emitOps_fold_layout {selector rank : Expr} {ops : List Op} {rows : Array RowExpr}
    {column : Nat} {emission : OpsEmission} (initial : Concrete.Bytecode.LayoutMState) (base : Nat)
    (valid : DegreeValid rows) (aligned : rowDegrees rows = initial.degrees)
    (cursor : column = base + initial.functionLayout.auxiliaries)
    (emitted : emitOps selector rank ops rows column = some emission) :
    ((ops.foldlM (fun _ op => Concrete.Bytecode.opLayout op) ()).run initial).2.degrees =
      rowDegrees emission.values ∧
    emission.column = base +
      ((ops.foldlM (fun _ op => Concrete.Bytecode.opLayout op) ()).run initial).2.functionLayout.auxiliaries := by
  induction ops generalizing rows column emission initial with
  | nil =>
    cases emitted
    exact ⟨aligned.symm, cursor⟩
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
    obtain ⟨nextDegrees, nextAux⟩ := emitOp_layout initial valid aligned firstEmitted
    have reflected := ih ((Concrete.Bytecode.opLayout op).run initial).2
      (valid.append (emitOp_degreeValid valid firstEmitted)) nextDegrees.symm
      (by rw [cursor, nextAux, Nat.add_assoc]) restEmitted
    rw [List.foldlM_cons]
    exact reflected

theorem emitOps_layout {selector rank : Expr} {ops : Array Op} {rows : Array RowExpr}
    {column : Nat} {emission : OpsEmission} (initial : Concrete.Bytecode.LayoutMState) (base : Nat)
    (valid : DegreeValid rows) (aligned : rowDegrees rows = initial.degrees)
    (cursor : column = base + initial.functionLayout.auxiliaries)
    (emitted : emitOps selector rank ops.toList rows column = some emission) :
    ((ops.forM Concrete.Bytecode.opLayout).run initial).2.degrees = rowDegrees emission.values ∧
    emission.column = base + ((ops.forM Concrete.Bytecode.opLayout).run initial).2.functionLayout.auxiliaries := by
  unfold Array.forM
  rw [← Array.foldlM_toList]
  exact emitOps_fold_layout initial base valid aligned cursor emitted

end Aiur.NativeAIR.OpEmitter
