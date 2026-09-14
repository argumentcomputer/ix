/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.EmissionChecks
import Ix.Aiur.Proofs.EmissionAllocation

/-! Checked operand scopes supply operation emission and its exact output size. -/

namespace Aiur.Bytecode

theorem indicesInScope_spec (available : Nat) (indices : Array ValIdx) :
    indicesInScope available indices = true ↔ ∀ index ∈ indices, index < available := by
  simp only [indicesInScope, Array.all_eq_true', decide_eq_true_eq]

theorem wordInScope_spec (available : Nat) (indices : Array ValIdx) :
    wordInScope available indices = true ↔ indices.size = 4 ∧ indicesInScope available indices = true := by
  simp only [wordInScope, Bool.and_eq_true, beq_iff_eq]

theorem addScope_eq {available count next : Nat} (checked : addScope available count = some next) :
    next = available + count ∧ next < 2^64 := by
  unfold addScope at checked
  dsimp only at checked
  split at checked
  · cases checked
    exact ⟨rfl, ‹_›⟩
  · cases checked

theorem checkEmissionOps_cons {op : Op} {ops : List Op} {available next : Nat}
    (checked : checkEmissionOps (op :: ops) available = some next) :
    op.emissionInputs available = true ∧
      ∃ after, addScope available op.outputSize = some after ∧ checkEmissionOps ops after = some next := by
  simp only [checkEmissionOps] at checked
  split at checked
  · cases checked
  next valid =>
    refine ⟨by simpa using valid, ?_⟩
    simp only [bind, Option.bind] at checked
    split at checked
    · cases checked
    next after added => exact ⟨after, added, checked⟩

theorem checkEmissionOps_le {ops : List Op} {available next : Nat}
    (checked : checkEmissionOps ops available = some next) : available ≤ next := by
  induction ops generalizing available with
  | nil => cases checked; exact Nat.le_refl _
  | cons op ops ih =>
    obtain ⟨_, after, added, rest⟩ := checkEmissionOps_cons checked
    have size := (addScope_eq added).1
    have mono := ih rest
    omega

theorem Op.allocation_outputSize (op : Op) (degrees : Array Nat) :
    (op.allocation degrees).degrees.size = op.outputSize := by
  cases op <;> simp only [Op.allocation, Op.outputSize, OpAllocation.advice]
  all_goals first
    | rfl
    | simp only [Array.size_replicate]
    | (split <;> rfl)

theorem Op.allocationFor_outputSize (op : Op) (callRanks : Array CallRank) (degrees : Array Nat) :
    (op.allocationFor callRanks degrees).degrees.size = op.outputSize := by
  cases op <;> simp only [Op.allocationFor, Op.allocation_outputSize]
  simp only [Op.outputSize, Array.size_replicate]

end Aiur.Bytecode

namespace Aiur.NativeAIR.OpEmitter
open Bytecode

variable {callRanks : Array CallRank}

theorem list_mapM_defined {read : α → Option β} (inputs : List α)
    (defined : ∀ input ∈ inputs, ∃ output, read input = some output) :
    ∃ outputs, inputs.mapM read = some outputs := by
  induction inputs with
  | nil => exact ⟨[], rfl⟩
  | cons input inputs ih =>
    obtain ⟨output, head⟩ := defined input List.mem_cons_self
    obtain ⟨outputs, tail⟩ := ih (fun value member => defined value (List.mem_cons_of_mem _ member))
    exact ⟨output :: outputs, by simp only [List.mapM_cons, head, tail, bind, Option.bind_some, pure]⟩

theorem array_mapM_defined {read : α → Option β} (inputs : Array α)
    (defined : ∀ input ∈ inputs, ∃ output, read input = some output) :
    ∃ outputs, inputs.mapM read = some outputs := by
  obtain ⟨outputs, evaluated⟩ := list_mapM_defined inputs.toList (by simpa using defined)
  exact ⟨outputs.toArray, by simp only [Array.mapM_eq_mapM_toList, evaluated, Functor.map, Option.map_some]⟩

theorem select_defined {rows : Array RowExpr} {indices : Array Nat}
    (checked : indicesInScope rows.size indices = true) : ∃ outputs, select rows indices = some outputs := by
  apply array_mapM_defined
  intro index member
  have bound := (indicesInScope_spec _ _).mp checked index member
  exact ⟨rows[index], getElem?_pos rows index bound⟩

theorem readWord_defined {rows : Array RowExpr} {indices : Array Nat}
    (checked : wordInScope rows.size indices = true) : ∃ output, readWord rows indices = some output := by
  obtain ⟨size, valid⟩ := (wordInScope_spec _ _).mp checked
  obtain ⟨outputs, selected⟩ := select_defined valid
  exact ⟨_, by simp only [readWord, size, ne_eq, not_true_eq_false, if_false, selected,
    bind, Option.bind_some, pure]; rfl⟩

theorem emitOp_defined (selector rank : Expr) (first : Nat) (op : Op) (rows : Array RowExpr)
    (checked : op.emissionInputs rows.size = true) : ∃ emission, emitOp selector rank first op rows callRanks = some emission := by
  cases op with
  | const | ioGetInfo | ioRead | ioSetInfo | ioWrite | debug | unconstrainedBigUintDivMod
  | unconstrainedGToBytes | unconstrainedGInverse => exact ⟨_, rfl⟩
  | add a b | sub a b | mul a b | u8Xor a b | u8Add a b | u8Mul a b | u8Sub a b
  | u8And a b | u8Or a b | u8LessThan a b | u32LessThan a b | u8XorSplit7 a b
  | u8XorSplit4 a b | u8RangeCheck a b =>
    obtain ⟨left, right⟩ : a < rows.size ∧ b < rows.size := by
      simpa only [Op.emissionInputs, Bool.and_eq_true, decide_eq_true_eq] using checked
    exact ⟨_, by simp only [emitOp, getElem?_pos rows a left, getElem?_pos rows b right,
      bind, Option.bind_some, pure]; rfl⟩
  | eqZero index | load size index | u8BitDecomposition index | u8ShiftLeft index | u8ShiftRight index =>
    have bound : index < rows.size := by simpa only [Op.emissionInputs, decide_eq_true_eq] using checked
    exact ⟨_, by simp only [emitOp, getElem?_pos rows index bound, bind, Option.bind_some, pure]; rfl⟩
  | call function indices size unconstrained =>
    cases unconstrained with
    | true => exact ⟨_, rfl⟩
    | false =>
      obtain ⟨outputs, selected⟩ := select_defined checked
      exact ⟨_, by simp only [emitOp, Bool.false_eq_true, if_false, selected, bind, Option.bind_some, pure]; rfl⟩
  | store indices =>
    obtain ⟨outputs, selected⟩ := select_defined checked
    exact ⟨_, by simp only [emitOp, selected, bind, Option.bind_some, pure]; rfl⟩
  | assertEq left right message =>
    obtain ⟨size, leftValid, rightValid⟩ : left.size = right.size ∧
        indicesInScope rows.size left = true ∧ indicesInScope rows.size right = true := by
      simpa only [Op.emissionInputs, Bool.and_eq_true, beq_iff_eq] using checked
    obtain ⟨xs, leftRead⟩ := select_defined leftValid
    obtain ⟨ys, rightRead⟩ := select_defined rightValid
    exact ⟨_, by simp only [emitOp, size, ne_eq, not_true_eq_false, if_false, leftRead, rightRead,
      bind, Option.bind_some, pure]; rfl⟩
  | unconstrainedU32Add left right =>
    obtain ⟨leftValid, rightValid⟩ : wordInScope rows.size left = true ∧ wordInScope rows.size right = true := by
      simpa only [Op.emissionInputs, Bool.and_eq_true] using checked
    obtain ⟨a, leftRead⟩ := readWord_defined leftValid
    obtain ⟨b, rightRead⟩ := readWord_defined rightValid
    exact ⟨_, by simp only [emitOp, leftRead, rightRead, bind, Option.bind_some, pure]; rfl⟩
  | unconstrainedU32Add3 left middle right =>
    obtain ⟨leftValid, middleValid, rightValid⟩ : wordInScope rows.size left = true ∧
        wordInScope rows.size middle = true ∧ wordInScope rows.size right = true := by
      simpa only [Op.emissionInputs, Bool.and_eq_true] using checked
    obtain ⟨a, leftRead⟩ := readWord_defined leftValid
    obtain ⟨b, middleRead⟩ := readWord_defined middleValid
    obtain ⟨c, rightRead⟩ := readWord_defined rightValid
    exact ⟨_, by simp only [emitOp, leftRead, middleRead, rightRead, bind, Option.bind_some, pure]; rfl⟩
  | u32ToField indices =>
    obtain ⟨output, selected⟩ := readWord_defined checked
    exact ⟨_, by simp only [emitOp, selected, bind, Option.bind_some, pure]; rfl⟩

theorem emitOp_outputSize {selector rank : Expr} {first : Nat} {op : Op}
    {rows : Array RowExpr} {emission : Emission} (valid : DegreeValid rows)
    (emitted : emitOp selector rank first op rows callRanks = some emission) :
    emission.outputs.size = op.outputSize := by
  have allocated := congrArg (fun allocation => allocation.degrees.size) (emitOp_allocationFor valid emitted)
  simpa only [Emission.allocation, rowDegrees, Array.size_map, Op.allocationFor_outputSize] using allocated

theorem emitOps_defined (selector rank : Expr) (ops : List Op) (rows : Array RowExpr) (column : Nat)
    {next : Nat} (valid : DegreeValid rows) (checked : checkEmissionOps ops rows.size = some next) :
    ∃ emission, emitOps selector rank ops rows column callRanks = some emission ∧ emission.values.size = next := by
  induction ops generalizing rows column with
  | nil => cases checked; exact ⟨_, rfl, rfl⟩
  | cons op ops ih =>
    obtain ⟨inputs, after, added, rest⟩ := checkEmissionOps_cons checked
    obtain ⟨first, firstEmitted⟩ := emitOp_defined (callRanks := callRanks) selector rank column op rows inputs
    have size := emitOp_outputSize valid firstEmitted
    have nextSize : (rows ++ first.outputs).size = after := by
      simp only [Array.size_append, size, (addScope_eq added).1]
    obtain ⟨last, lastEmitted, lastSize⟩ := ih (rows ++ first.outputs) (column + first.used)
      (valid.append (emitOp_degreeValid valid firstEmitted)) (nextSize ▸ rest)
    refine ⟨{ last with
      equations := first.equations ++ last.equations,
      queries := first.queries ++ last.queries, calls := first.calls ++ last.calls }, ?_, lastSize⟩
    simp only [emitOps, firstEmitted, lastEmitted, bind, Option.bind_some, pure]

end Aiur.NativeAIR.OpEmitter
