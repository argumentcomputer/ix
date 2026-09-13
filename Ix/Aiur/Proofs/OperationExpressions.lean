/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.FrontendExpressions

/-!
Symbolic operation emission and its evaluation in the valued AIR model.
The symbolic outputs retain the frontend expression trees and independently
tracked degrees. Queries are the ungated contributions later assembled into
physical lookup slots. The call records retain the same expressions as those
queries and the six allocated rank-gap bytes.
-/

namespace Aiur.NativeAIR
namespace OpEmitter

theorem list_mapM_read {read : α → Option β} {inputs : List α} {outputs : List β}
    (evaluated : inputs.mapM read = some outputs) (index : Nat) :
    (inputs[index]? >>= read) = outputs[index]? := by
  induction inputs generalizing outputs index with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at evaluated
    subst outputs
    rfl
  | cons input rest ih =>
    simp only [List.mapM_cons, bind, Option.bind, pure] at evaluated
    cases head : read input <;> simp only [head] at evaluated
    · cases evaluated
    cases tail : rest.mapM read <;> simp only [tail] at evaluated
    · cases evaluated
    cases evaluated
    cases index with
    | zero => exact head
    | succ index => exact ih tail index

theorem array_mapM_read {read : α → Option β} {inputs : Array α} {outputs : Array β}
    (evaluated : inputs.mapM read = some outputs) (index : Nat) :
    (inputs[index]? >>= read) = outputs[index]? := by
  have lists := congrArg (Functor.map Array.toList) evaluated
  rw [Array.toList_mapM] at lists
  simpa only [Array.getElem?_toList] using list_mapM_read lists index

theorem array_mapM_size {read : α → Option β} {inputs : Array α} {outputs : Array β}
    (evaluated : inputs.mapM read = some outputs) : outputs.size = inputs.size := by
  have lists := congrArg (Functor.map Array.toList) evaluated
  rw [Array.toList_mapM] at lists
  exact Bytecode.AIR.list_mapM_some_length read inputs.toList outputs.toList lists

theorem array_mapM_push (read : α → Option β) (inputs : Array α) (input : α) :
    (inputs.push input).mapM read = (do
      let outputs ← inputs.mapM read
      let output ← read input
      return outputs.push output) := by
  simp only [Array.mapM_eq_mapM_toList, Array.toList_push, List.mapM_append,
    List.mapM_cons, List.mapM_nil]
  cases inputs.toList.mapM read <;> cases read input <;>
    simp only [bind, Option.bind, pure, Functor.map, Option.map]
  congr 1
  apply Array.toList_inj.mp
  simp only [Array.toList_push]

theorem list_mapM_of_map (items : List α) (input : α → β) (output : α → γ)
    (read : β → Option γ) (evaluated : ∀ item ∈ items, read (input item) = some (output item)) :
    (items.map input).mapM read = some (items.map output) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.map_cons, List.mapM_cons, evaluated item List.mem_cons_self,
      ih (fun value member => evaluated value (List.mem_cons_of_mem _ member))]
    rfl

theorem array_mapM_ofFn {n : Nat} (input : Fin n → α) (output : Fin n → β)
    (read : α → Option β) (evaluated : ∀ index, read (input index) = some (output index)) :
    (Array.ofFn input).mapM read = some (Array.ofFn output) := by
  rw [Array.mapM_eq_mapM_toList, Array.toList_ofFn]
  have listEval : (List.ofFn input).mapM read = some (List.ofFn output) := by
    simpa only [List.map_ofFn, Function.comp_id] using
      list_mapM_of_map (List.ofFn id) input output read (fun index _ => evaluated index)
  rw [listEval]
  simp only [Functor.map, Option.map_some, List.toArray_ofFn]

theorem list_mapM_ofFn {n : Nat} (input : Fin n → α) (output : Fin n → β)
    (read : α → Option β) (evaluated : ∀ index, read (input index) = some (output index)) :
    (List.ofFn input).mapM read = some (List.ofFn output) := by
  simpa only [List.map_ofFn, Function.comp_id] using
    list_mapM_of_map (List.ofFn id) input output read (fun index _ => evaluated index)

theorem list_mapM_transform {read : α → Option β} {inputs : List α} {outputs : List β}
    (evaluated : inputs.mapM read = some outputs) (input : α → γ) (output : β → δ)
    (next : γ → Option δ)
    (related : ∀ a b, read a = some b → next (input a) = some (output b)) :
    (inputs.map input).mapM next = some (outputs.map output) := by
  induction inputs generalizing outputs with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at evaluated
    subst outputs
    rfl
  | cons a rest ih =>
    simp only [List.mapM_cons, bind, Option.bind, pure] at evaluated
    cases head : read a <;> simp only [head] at evaluated
    · cases evaluated
    cases tail : rest.mapM read <;> simp only [tail] at evaluated
    · cases evaluated
    cases evaluated
    simp only [List.map_cons, List.mapM_cons, related _ _ head, ih tail]
    rfl

theorem array_mapM_transform {read : α → Option β} {inputs : Array α} {outputs : Array β}
    (evaluated : inputs.mapM read = some outputs) (input : α → γ) (output : β → δ)
    (next : γ → Option δ)
    (related : ∀ a b, read a = some b → next (input a) = some (output b)) :
    (inputs.map input).mapM next = some (outputs.map output) := by
  have lists := congrArg (Functor.map Array.toList) evaluated
  rw [Array.toList_mapM] at lists
  rw [Array.mapM_eq_mapM_toList, Array.toList_map,
    list_mapM_transform lists input output next related]
  simp only [Functor.map, Option.map_some, ← Array.toList_map, Array.toArray_toList]

theorem list_mapM_refine {first : α → Option β} {second : α → Option γ} {evaluate : β → Option γ}
    {inputs : List α} {outputs : List β} (selected : inputs.mapM first = some outputs)
    (related : ∀ input output, first input = some output →
      ∃ value, second input = some value ∧ evaluate output = some value) :
    ∃ values, inputs.mapM second = some values ∧ outputs.mapM evaluate = some values := by
  induction inputs generalizing outputs with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at selected
    subst outputs
    exact ⟨[], rfl, rfl⟩
  | cons input rest ih =>
    simp only [List.mapM_cons, bind, Option.bind, pure] at selected
    cases head : first input <;> simp only [head] at selected
    · cases selected
    cases tail : rest.mapM first <;> simp only [tail] at selected
    · cases selected
    cases selected
    obtain ⟨value, read, evaluated⟩ := related _ _ head
    obtain ⟨values, reads, evaluations⟩ := ih tail
    refine ⟨value :: values, ?_, ?_⟩ <;>
      simp only [List.mapM_cons, read, evaluated, reads, evaluations, bind, Option.bind_some, pure]

theorem array_mapM_refine {first : α → Option β} {second : α → Option γ} {evaluate : β → Option γ}
    {inputs : Array α} {outputs : Array β} (selected : inputs.mapM first = some outputs)
    (related : ∀ input output, first input = some output →
      ∃ value, second input = some value ∧ evaluate output = some value) :
    ∃ values, inputs.mapM second = some values ∧ outputs.mapM evaluate = some values := by
  have lists := congrArg (Functor.map Array.toList) selected
  rw [Array.toList_mapM] at lists
  obtain ⟨values, reads, evaluations⟩ := list_mapM_refine lists related
  refine ⟨values.toArray, ?_, ?_⟩ <;>
    simp only [Array.mapM_eq_mapM_toList, reads, evaluations, Functor.map, Option.map_some]

abbrev evalExpr (values : Values G) := Expr.eval goldilocksOps values

def evalRows (values : Values G) (rows : Array RowExpr) : Option (Array AIR.RowValue) :=
  rows.mapM (RowExpr.eval values)

theorem evalRows_empty (values : Values G) : evalRows values #[] = some #[] :=
  Array.mapM_empty _

theorem evalRows_singleton {values : Values G} {expr : RowExpr} {value : AIR.RowValue}
    (reflected : expr.Reflects values value) : evalRows values #[expr] = some #[value] := by
  change ((#[] : Array RowExpr).push expr).mapM (RowExpr.eval values) = some #[value]
  rw [array_mapM_push, Array.mapM_empty, (RowExpr.reflects_iff_eval _ _ _).mp reflected]
  rfl

def rowExprs (rows : Array RowExpr) : Array Expr := rows.map RowExpr.expr

def Normal (rows : Array RowExpr) : Prop :=
  ∀ row ∈ rows, row.expr.noConstantNegs = true

theorem evalRows_values {values : Values G} {rows : Array RowExpr} {outputs : Array AIR.RowValue}
    (evaluated : evalRows values rows = some outputs) :
    (rowExprs rows).mapM (evalExpr values) = some (AIR.rowValues outputs) := by
  apply array_mapM_transform evaluated RowExpr.expr AIR.RowValue.value
  intro expr value result
  exact ((RowExpr.reflects_iff_eval _ _ _).mpr result).1

theorem evalRows_read {values : Values G} {rows : Array RowExpr} {outputs : Array AIR.RowValue}
    (evaluated : evalRows values rows = some outputs) {index : Nat} {row : RowExpr}
    (present : rows[index]? = some row) :
    ∃ output, outputs[index]? = some output ∧ row.Reflects values output := by
  have read := array_mapM_read evaluated index
  rw [present] at read
  dsimp only [bind, Option.bind_some] at read
  cases result : row.eval values with
  | none =>
    have sizes := array_mapM_size evaluated
    obtain ⟨bound, _⟩ := Array.getElem?_eq_some_iff.mp present
    have absent := Array.getElem?_eq_none_iff.mp (read.symm.trans result)
    omega
  | some output =>
    exact ⟨output, read.symm.trans result, (RowExpr.reflects_iff_eval _ _ _).mpr result⟩

def select (rows : Array RowExpr) (indices : Array Nat) : Option (Array RowExpr) :=
  indices.mapM fun index => rows[index]?

theorem select_reflects {values : Values G} {rows : Array RowExpr} {outputs : Array AIR.RowValue}
    (evaluated : evalRows values rows = some outputs) {indices : Array Nat} {selected : Array RowExpr}
    (read : select rows indices = some selected) :
    ∃ results, indices.mapM (fun index => outputs[index]?) = some results ∧
      evalRows values selected = some results := by
  apply array_mapM_refine read
  intro index expr present
  obtain ⟨value, present, reflected⟩ := evalRows_read evaluated present
  exact ⟨value, present, (RowExpr.reflects_iff_eval _ _ _).mp reflected⟩

theorem select_values {rows : Array AIR.RowValue} {indices : Array Nat} {outputs : Array AIR.RowValue}
    (read : indices.mapM (fun index => rows[index]?) = some outputs) :
    Bytecode.AIR.readValues (AIR.rowValues rows) indices = some (AIR.rowValues outputs) := by
  have result := array_mapM_transform read id AIR.RowValue.value
    (fun index => (AIR.rowValues rows)[index]?) (fun _ _ present => AIR.rowValues_read present)
  simpa only [Array.map_id, Bytecode.AIR.readValues, AIR.rowValues] using result

theorem select_normal {rows : Array RowExpr} (normal : Normal rows)
    {indices : Array Nat} {selected : Array RowExpr} (read : select rows indices = some selected) :
    Normal selected := by
  intro expr member
  obtain ⟨index, bound, equal⟩ := Array.mem_iff_getElem.mp member
  have selectedRead : selected[index]? = some expr := Array.getElem?_eq_some_iff.mpr ⟨bound, equal⟩
  have input := array_mapM_read read index
  rw [selectedRead] at input
  cases indexRead : indices[index]? with
  | none => simp only [indexRead, bind, Option.bind_none, reduceCtorEq] at input
  | some inputIndex =>
    simp only [indexRead, bind, Option.bind_some] at input
    exact normal expr (Array.mem_of_getElem? input)

theorem array_ofFn_getD (items : Array α) (fallback : α) {count : Nat} (size : items.size = count) :
    Array.ofFn (fun index : Fin count => items[index.val]?.getD fallback) = items := by
  apply Array.ext (by simp only [Array.size_ofFn, size])
  intro index _ bound
  simp only [Array.getElem_ofFn, getElem?_pos items index bound, Option.getD_some]

theorem array_map_getD_of_mapM {α : Type} {items : Array α} {indices : Array Nat} {selected : Array α}
    (fallback : α) (read : indices.mapM (fun index => items[index]?) = some selected) :
    indices.map (fun index => items[index]?.getD fallback) = selected := by
  have size := array_mapM_size read
  apply Array.ext (by simp only [Array.size_map, size])
  intro index inputBound outputBound
  have bound : index < indices.size := by simpa only [Array.size_map] using inputBound
  have result := array_mapM_read read index
  simp only [getElem?_pos indices index bound, getElem?_pos selected index outputBound,
    bind, Option.bind_some] at result
  simp only [Array.getElem_map, result, Option.getD_some]

theorem evalRows_getD {values : Values G} {rows : Array RowExpr} {outputs : Array AIR.RowValue}
    (evaluated : evalRows values rows = some outputs) {index : Nat} (bound : index < rows.size) :
    (rows[index]?.getD (.konst 0)).Reflects values (outputs[index]?.getD (.konst 0)) := by
  have present : rows[index]? = some rows[index] := getElem?_pos rows index bound
  obtain ⟨value, output, reflected⟩ := evalRows_read evaluated present
  simpa only [present, output, Option.getD_some] using reflected

def advice (first count : Nat) : Array RowExpr :=
  Array.ofFn fun index : Fin count => mainCurrent (first + index.val)

theorem advice_eval (values : Values G) (row : Nat → G) (first count : Nat)
    (reads : ∀ index < count,
      (values.columns .main .current)[first + index]? = some (row index)) :
    evalRows values (advice first count) = some (AIR.rowAdvice row 0 count) := by
  apply array_mapM_ofFn
  intro index
  exact (RowExpr.reflects_iff_eval _ _ _).mp
    (RowExpr.variable_reflects values (by simpa only [Nat.zero_add] using reads index.val index.isLt))

theorem advice_normal (first count : Nat) : Normal (advice first count) := by
  intro expr member
  obtain ⟨index, rfl⟩ := Array.mem_ofFn.mp member
  rfl

structure CallExpr where
  function : Nat
  inputs : Array Expr
  outputs : Array Expr
  rank : Expr
  gap : Fin 6 → Expr

def CallExpr.eval (values : Values G) (call : CallExpr) :
    Option (Bytecode.AIR.Call × (Fin 6 → G)) := do
  let inputs ← call.inputs.mapM (evalExpr values)
  let outputs ← call.outputs.mapM (evalExpr values)
  let rank ← call.rank.eval goldilocksOps values
  let gap ← (Array.ofFn call.gap).mapM (evalExpr values)
  return (⟨call.function, inputs, outputs, rank⟩, fun index => gap[index.val]?.getD 0)

theorem CallExpr.eval_of {values : Values G} {call : CallExpr} {inputs outputs : Array G}
    {rank : G} {gap : Fin 6 → G}
    (inputEval : call.inputs.mapM (evalExpr values) = some inputs)
    (outputEval : call.outputs.mapM (evalExpr values) = some outputs)
    (rankEval : evalExpr values call.rank = some rank)
    (gapEval : ∀ index, evalExpr values (call.gap index) = some (gap index)) :
    call.eval values = some (⟨call.function, inputs, outputs, rank⟩, gap) := by
  have bytes := array_mapM_ofFn call.gap gap (evalExpr values) gapEval
  simp only [CallExpr.eval, inputEval, outputEval, rankEval, bytes, bind, Option.bind_some, pure]
  congr 2
  funext index
  simp only [Array.getElem?_ofFn, index.isLt, dif_pos, Option.getD_some]

structure Emission where
  outputs : Array RowExpr := #[]
  used : Nat := 0
  equations : List Expr := []
  queries : List (List Expr) := []
  calls : List CallExpr := []

def Emission.eval (values : Values G) (emission : Emission) : Option AIR.OpEmission := do
  let outputs ← evalRows values emission.outputs
  let equations ← emission.equations.mapM (evalExpr values)
  let queries ← emission.queries.mapM (List.mapM (evalExpr values))
  let calls ← emission.calls.mapM (CallExpr.eval values)
  return ⟨outputs, emission.used, equations, queries, calls⟩

def fromScalar (emission : ScalarEmission) : Emission :=
  { outputs := #[emission.output], used := emission.used, equations := emission.equations }

def emitAdvice (first count : Nat) : Emission :=
  { outputs := advice first count, used := count }

theorem emitAdvice_reflects (values : Values G) (row : Nat → G) (first count : Nat)
    (reads : ∀ index < count,
      (values.columns .main .current)[first + index]? = some (row index)) :
    (emitAdvice first count).eval values = some (AIR.emitAdvice row count) := by
  simp only [Emission.eval, emitAdvice, advice_eval values row first count reads,
    List.mapM_nil, bind, Option.bind_some, pure, AIR.emitAdvice]

theorem Emission.eval_of {values : Values G} {emission : Emission} {result : AIR.OpEmission}
    (outputs : evalRows values emission.outputs = some result.outputs)
    (used : emission.used = result.used)
    (equations : emission.equations.mapM (evalExpr values) = some result.equations)
    (queries : emission.queries.mapM (List.mapM (evalExpr values)) = some result.queries)
    (calls : emission.calls.mapM (CallExpr.eval values) = some result.calls) :
    emission.eval values = some result := by
  simp only [Emission.eval, outputs, equations, queries, calls, used, bind, Option.bind_some, pure]

def emitByte1 (first : Nat) (kind : AIR.Byte1Kind) (input : RowExpr) : Emission :=
  let outputs := advice first kind.outputSize
  { outputs, used := kind.outputSize,
    queries := [[.konst kind.channel, input.expr] ++ (rowExprs outputs).toList] }

theorem emitByte1_reflects (values : Values G) (row : Nat → G) (first : Nat) (kind : AIR.Byte1Kind)
    {input : RowExpr} {value : AIR.RowValue} (inputRef : input.Reflects values value)
    (reads : ∀ index < kind.outputSize,
      (values.columns .main .current)[first + index]? = some (row index)) :
    (emitByte1 first kind input).eval values =
      some { outputs := AIR.rowAdvice row 0 kind.outputSize, used := kind.outputSize,
             queries := [AIR.byte1Request kind value.value
               (AIR.rowValues (AIR.rowAdvice row 0 kind.outputSize))] } := by
  have outputs := advice_eval values row first kind.outputSize reads
  have raw := congrArg (Functor.map Array.toList) (evalRows_values outputs)
  rw [Array.toList_mapM] at raw
  simp only [Functor.map, Option.map_some] at raw
  apply Emission.eval_of outputs rfl rfl ?_ rfl
  simp only [emitByte1, List.mapM_cons, List.mapM_nil, List.cons_append, List.nil_append,
    inputRef.1, show evalExpr values (.konst kind.channel) = some kind.channel from rfl,
    raw, bind, Option.bind_some, pure, AIR.byte1Request]

def byteCarry (first : Nat) (subtract : Bool) (left right : RowExpr) : RowExpr :=
  let low := (mainCurrent first).expr
  let numerator := if subtract then (low.frontAdd right.expr).frontSub left.expr
    else (left.expr.frontAdd right.expr).frontSub low
  ⟨numerator.frontMul (.konst AIR.inverse256), max (max left.degree right.degree) 1⟩

theorem scale_isConstant (expr : Expr) {coefficient : G} (nonzero : coefficient ≠ 0) :
    (expr.frontMul (.konst coefficient)).isConstant = expr.isConstant := by
  have known := expr.isConstant_eq
  have notZero : (coefficient == 0) = false := by simpa only [beq_eq_false_iff_ne] using nonzero
  cases constant : expr.constantValue with
  | none =>
    simp only [constant, Option.isSome_none] at known
    simp only [Expr.frontMul, constant,
      show (Expr.konst coefficient).constantValue = some coefficient from rfl,
      notZero, Bool.false_eq_true, if_false]
    split
    · rfl
    · exact known.symm
  | some value =>
    simp only [constant, Option.isSome_some] at known
    simp only [Expr.frontMul, constant,
      show (Expr.konst coefficient).constantValue = some coefficient from rfl]
    exact known.symm

theorem byteCarry_reflects (values : Values G) (row : Nat → G) (first : Nat) (subtract : Bool)
    {left right : RowExpr} {a b : AIR.RowValue}
    (leftRef : left.Reflects values a) (rightRef : right.Reflects values b)
    (leftNormal : left.expr.noConstantNegs = true)
    (read : (values.columns .main .current)[first]? = some (row 0)) :
    (byteCarry first subtract left right).Reflects values
      ⟨(if subtract then row 0 + b.value - a.value else a.value + b.value - row 0) * AIR.inverse256,
        max (max a.degree b.degree) 1, false⟩ := by
  have low : evalExpr values (mainCurrent first).expr = some (row 0) := read
  have coeff : evalExpr values (.konst AIR.inverse256) = some AIR.inverse256 := rfl
  have invNonzero : AIR.inverse256 ≠ 0 := by decide +kernel
  unfold RowExpr.Reflects
  cases subtract <;> simp only [byteCarry, Bool.false_eq_true, if_false, if_true]
  all_goals refine ⟨?_, ?_, ?_⟩
  · exact Expr.frontMul_eval goldilocksLaws values
      (Expr.frontSub_eval goldilocksLaws values
        (Expr.frontAdd_eval goldilocksLaws values leftRef.1 rightRef.1) low) coeff
  · rw [leftRef.2.1, rightRef.2.1]
  · rw [scale_isConstant _ invNonzero, Expr.frontSub_isConstant _ _ (by rfl)]
    exact Bool.and_false _
  · exact Expr.frontMul_eval goldilocksLaws values
      (Expr.frontSub_eval goldilocksLaws values
        (Expr.frontAdd_eval goldilocksLaws values low rightRef.1) leftRef.1) coeff
  · rw [leftRef.2.1, rightRef.2.1]
  · rw [scale_isConstant _ invNonzero, Expr.frontSub_isConstant _ _ leftNormal,
      Expr.frontAdd_isConstant]
    rfl

theorem byteCarry_normal (first : Nat) (subtract : Bool) {left right : RowExpr}
    (leftNormal : left.expr.noConstantNegs = true)
    (rightNormal : right.expr.noConstantNegs = true) :
    (byteCarry first subtract left right).expr.noConstantNegs = true := by
  cases subtract
  · exact Expr.frontMul_noConstantNegs
      (Expr.frontSub_noConstantNegs (Expr.frontAdd_noConstantNegs leftNormal rightNormal) rfl) rfl
  · exact Expr.frontMul_noConstantNegs
      (Expr.frontSub_noConstantNegs (Expr.frontAdd_noConstantNegs rfl rightNormal) leftNormal) rfl

def emitByte2 (first : Nat) (kind : AIR.Byte2Kind) (left right : RowExpr) : Emission :=
  let allocated := advice first kind.outputSize
  let outputs := match kind with
    | .add => allocated.push (byteCarry first false left right)
    | .sub => allocated.push (byteCarry first true left right)
    | _ => allocated
  { outputs, used := kind.outputSize,
    queries := [[.konst kind.channel, left.expr, right.expr] ++ (rowExprs allocated).toList] }

theorem emitByte2_reflects (values : Values G) (row : Nat → G) (first : Nat) (kind : AIR.Byte2Kind)
    {left right : RowExpr} {a b : AIR.RowValue}
    (leftRef : left.Reflects values a) (rightRef : right.Reflects values b)
    (leftNormal : left.expr.noConstantNegs = true)
    (reads : ∀ index < kind.outputSize,
      (values.columns .main .current)[first + index]? = some (row index)) :
    (emitByte2 first kind left right).eval values =
      some { outputs := kind.extendRowOutputs a b (AIR.rowAdvice row 0 kind.outputSize),
             used := kind.outputSize,
             queries := [AIR.byte2Request kind a.value b.value
               (AIR.rowValues (AIR.rowAdvice row 0 kind.outputSize))] } := by
  have allocated := advice_eval values row first kind.outputSize reads
  have raw := congrArg (Functor.map Array.toList) (evalRows_values allocated)
  rw [Array.toList_mapM] at raw
  simp only [Functor.map, Option.map_some] at raw
  apply Emission.eval_of ?_ rfl rfl ?_ rfl
  · cases kind <;> try exact allocated
    all_goals
      have firstRead : (values.columns .main .current)[first]? = some (row 0) := by
        simpa only [Nat.add_zero] using reads 0 (by decide)
      have carry (subtract : Bool) := (RowExpr.reflects_iff_eval _ _ _).mp
        (byteCarry_reflects values row first subtract leftRef rightRef leftNormal firstRead)
      simp only [emitByte2, AIR.Byte2Kind.extendRowOutputs, AIR.Byte2Kind.outputSize, evalRows, array_mapM_push,
        show (advice first 1).mapM (RowExpr.eval values) = some (AIR.rowAdvice row 0 1) from allocated,
        carry, bind, Option.bind_some, pure, AIR.rowValues, AIR.rowAdvice,
        Array.map_ofFn, Array.getElem?_ofFn, Nat.zero_lt_succ, dif_pos, Option.getD_some,
        AIR.RowValue.variable, Nat.zero_add, Function.comp_def, Bool.false_eq_true, if_false, if_true]
  · simp only [emitByte2, List.mapM_cons, List.mapM_nil, List.cons_append, List.nil_append,
      leftRef.1, rightRef.1, show evalExpr values (.konst kind.channel) = some kind.channel from rfl,
      raw, bind, Option.bind_some, pure, AIR.byte2Request]

theorem emitByte2_normal (first : Nat) (kind : AIR.Byte2Kind) {left right : RowExpr}
    (leftNormal : left.expr.noConstantNegs = true)
    (rightNormal : right.expr.noConstantNegs = true) :
    Normal (emitByte2 first kind left right).outputs := by
  cases kind <;> try exact advice_normal _ _
  all_goals
    intro expr member
    rcases Array.mem_push.mp member with member | rfl
    · exact advice_normal _ _ expr member
    · exact byteCarry_normal _ _ leftNormal rightNormal

/-- The native four-term, little-endian left fold, including its initial
zero and unit coefficient. Metadata follows the same maximum fold. -/
def packFour (bytes : Fin 4 → RowExpr) : RowExpr :=
  ((((RowExpr.konst 0).add ((bytes 0).mul (.konst (G.ofNat (256^0))))).add
    ((bytes 1).mul (.konst (G.ofNat (256^1))))).add
    ((bytes 2).mul (.konst (G.ofNat (256^2))))).add
      ((bytes 3).mul (.konst (G.ofNat (256^3))))

theorem scale_reflects (values : Values G) {expr : RowExpr} {value : AIR.RowValue}
    (reflected : expr.Reflects values value) (coefficient : G) (nonzero : coefficient ≠ 0) :
    (expr.mul (.konst coefficient)).Reflects values
      ⟨value.value * coefficient, value.degree, value.constant⟩ := by
  refine ⟨Expr.frontMul_eval goldilocksLaws values reflected.1 rfl, ?_, ?_⟩
  · exact reflected.2.1
  · exact (scale_isConstant expr.expr nonzero).trans reflected.2.2

private def packFourValue (results : Fin 4 → AIR.RowValue) : AIR.RowValue :=
  ((((AIR.RowValue.konst 0).add
    ⟨(results 0).value * G.ofNat (256^0), (results 0).degree, (results 0).constant⟩).add
    ⟨(results 1).value * G.ofNat (256^1), (results 1).degree, (results 1).constant⟩).add
    ⟨(results 2).value * G.ofNat (256^2), (results 2).degree, (results 2).constant⟩).add
    ⟨(results 3).value * G.ofNat (256^3), (results 3).degree, (results 3).constant⟩

theorem list_ofFn_four (values : Fin 4 → α) :
    List.ofFn values = [values 0, values 1, values 2, values 3] := by
  simp only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one,
    show (1 : Fin 2).succ = (2 : Fin 3) from rfl,
    show (1 : Fin 3).succ = (2 : Fin 4) from rfl,
    show (2 : Fin 3).succ = (3 : Fin 4) from rfl]

theorem list_foldl_zip_four (values : Fin 4 → α) (step : β → α × Nat → β) (initial : β) :
    (List.ofFn values).zipIdx.foldl step initial =
      step (step (step (step initial (values 0, 0)) (values 1, 1)) (values 2, 2)) (values 3, 3) := by
  rw [list_ofFn_four]
  rfl

private theorem rowValue_ext {left right : AIR.RowValue}
    (value : left.value = right.value) (degree : left.degree = right.degree)
    (constant : left.constant = right.constant) : left = right := by
  cases left
  cases right
  cases value
  cases degree
  cases constant
  rfl

private theorem packFourValue_eq (results : Fin 4 → AIR.RowValue) :
    packFourValue results = AIR.RowValue.pack (Array.ofFn results) := by
  apply rowValue_ext
  · change (0 + (results 0).value * G.ofNat (256^0) + (results 1).value * G.ofNat (256^1) +
      (results 2).value * G.ofNat (256^2) + (results 3).value * G.ofNat (256^3)) =
        ((Array.ofFn results).map AIR.RowValue.value).toList.zipIdx.foldl
          (fun value (byte, index) => value + byte * G.ofNat (256^index)) 0
    rw [Array.map_ofFn, Array.toList_ofFn]
    exact (list_foldl_zip_four (fun index => (results index).value)
      (fun value (byte, index) => value + byte * G.ofNat (256^index)) 0).symm
  · change max (max (max (max 0 (results 0).degree) (results 1).degree) (results 2).degree)
      (results 3).degree = (Array.ofFn results).toList.foldl (fun d v => max d v.degree) 0
    simp only [Array.toList_ofFn, list_ofFn_four, List.foldl_cons, List.foldl_nil]
  · change ((((true && (results 0).constant) && (results 1).constant) && (results 2).constant) &&
      (results 3).constant) = (Array.ofFn results).all AIR.RowValue.constant
    simp only [← Array.all_toList, Array.toList_ofFn, list_ofFn_four, List.all_cons,
      List.all_nil, Bool.true_and, Bool.and_true, Bool.and_assoc]

theorem packFour_reflects (values : Values G) (bytes : Fin 4 → RowExpr)
    (results : Fin 4 → AIR.RowValue)
    (reflected : ∀ index, (bytes index).Reflects values (results index)) :
    (packFour bytes).Reflects values (AIR.RowValue.pack (Array.ofFn results)) := by
  have r0 := scale_reflects values (reflected 0) (G.ofNat (256^0)) (by decide +kernel)
  have r1 := scale_reflects values (reflected 1) (G.ofNat (256^1)) (by decide +kernel)
  have r2 := scale_reflects values (reflected 2) (G.ofNat (256^2)) (by decide +kernel)
  have r3 := scale_reflects values (reflected 3) (G.ofNat (256^3)) (by decide +kernel)
  have result := RowExpr.add_reflects values
    (RowExpr.add_reflects values
      (RowExpr.add_reflects values
        (RowExpr.add_reflects values (RowExpr.konst_reflects values 0) r0) r1) r2) r3
  change (packFour bytes).Reflects values (packFourValue results) at result
  rw [packFourValue_eq] at result
  exact result

theorem packFour_normal (bytes : Fin 4 → RowExpr)
    (normal : ∀ index, (bytes index).expr.noConstantNegs = true) :
    (packFour bytes).expr.noConstantNegs = true := by
  exact Expr.frontAdd_noConstantNegs
    (Expr.frontAdd_noConstantNegs
      (Expr.frontAdd_noConstantNegs
        (Expr.frontAdd_noConstantNegs rfl
          (Expr.frontMul_noConstantNegs (normal 0) rfl))
        (Expr.frontMul_noConstantNegs (normal 1) rfl))
      (Expr.frontMul_noConstantNegs (normal 2) rfl))
    (Expr.frontMul_noConstantNegs (normal 3) rfl)

def readWord (rows : Array RowExpr) (indices : Array Nat) : Option RowExpr := do
  if indices.size ≠ 4 then none else do
    let bytes ← select rows indices
    return packFour fun index => bytes[index.val]?.getD (.konst 0)

theorem readWord_reflects {values : Values G} {rows : Array RowExpr} {outputs : Array AIR.RowValue}
    (evaluated : evalRows values rows = some outputs) {indices : Array Nat} {word : RowExpr}
    (read : readWord rows indices = some word) :
    ∃ value, AIR.readRowWord outputs indices = some value ∧ word.Reflects values value := by
  simp only [readWord, bind, Option.bind] at read
  split at read
  · cases read
  next size =>
    have width : indices.size = 4 := by omega
    cases selected : select rows indices <;> simp only [selected] at read
    · cases read
    next bytes =>
      cases read
      have byteSize := (array_mapM_size selected).trans width
      obtain ⟨results, resultRead, resultEval⟩ := select_reflects evaluated selected
      have resultSize := (array_mapM_size resultRead).trans width
      have reflected := packFour_reflects values
        (fun index => bytes[index.val]?.getD (.konst 0))
        (fun index => results[index.val]?.getD (.konst 0))
        (fun index => evalRows_getD resultEval (by omega))
      rw [array_ofFn_getD results (.konst 0) resultSize] at reflected
      refine ⟨AIR.RowValue.pack results, ?_, reflected⟩
      simp only [AIR.readRowWord, Bytecode.AIR.readWord, if_neg size,
        select_values resultRead, bind, Option.bind_some]
      rw [array_map_getD_of_mapM (.konst 0) resultRead]
      rfl

theorem readWord_normal {rows : Array RowExpr} (normal : Normal rows)
    {indices : Array Nat} {word : RowExpr} (read : readWord rows indices = some word) :
    word.expr.noConstantNegs = true := by
  simp only [readWord, bind, Option.bind] at read
  split at read
  · cases read
  next size =>
    cases selected : select rows indices <;> simp only [selected] at read
    · cases read
    next bytes =>
      cases read
      apply packFour_normal
      intro index
      have byteSize := array_mapM_size selected
      have bound : index.val < bytes.size := by omega
      simp only [getElem?_pos bytes index.val bound, Option.getD_some]
      exact select_normal normal selected _ (Array.getElem_mem ..)

def packedAdvice (first : Nat) : RowExpr :=
  packFour fun index => mainCurrent (first + index.val)

theorem packedAdvice_reflects (values : Values G) (row : Nat → G) (first : Nat)
    (reads : ∀ index < 4,
      (values.columns .main .current)[first + index]? = some (row index)) :
    (packedAdvice first).Reflects values (AIR.RowValue.pack (AIR.rowAdvice row 0 4)) := by
  apply packFour_reflects
  intro index
  apply RowExpr.variable_reflects values
  simpa only [Nat.zero_add] using reads index.val index.isLt

theorem packedAdvice_normal (first : Nat) : (packedAdvice first).expr.noConstantNegs = true :=
  packFour_normal _ (fun _ => rfl)

theorem packed_advice_not_constant (row : Nat → G) :
    (AIR.RowValue.pack (AIR.rowAdvice row 0 4)).constant = false := by
  change (Array.ofFn (fun index : Fin 4 => AIR.RowValue.variable (row (0 + index.val)))).all
    AIR.RowValue.constant = false
  simp only [← Array.all_toList, Array.toList_ofFn, list_ofFn_four,
    List.all_cons, List.all_nil, AIR.RowValue.variable, Bool.false_and]

def emitWordSum (first : Nat) (sum : RowExpr) : Emission :=
  let packed := packedAdvice first
  { outputs := (advice first 4).push ((sum.sub packed).mul (.konst 0xfffffffe00000002)), used := 4 }

theorem emitWordSum_reflects (values : Values G) (row : Nat → G) (first : Nat)
    {sum : RowExpr} {value : AIR.RowValue} (sumRef : sum.Reflects values value)
    (reads : ∀ index < 4,
      (values.columns .main .current)[first + index]? = some (row index)) :
    (emitWordSum first sum).eval values =
      some { outputs := (AIR.rowAdvice row 0 4).push
               ⟨(value.value - (AIR.RowValue.pack (AIR.rowAdvice row 0 4)).value) * 0xfffffffe00000002,
                 max value.degree (AIR.RowValue.pack (AIR.rowAdvice row 0 4)).degree, false⟩,
             used := 4 } := by
  have allocated := advice_eval values row first 4 reads
  have packed := packedAdvice_reflects values row first reads
  have difference := RowExpr.sub_reflects values sumRef packed (packedAdvice_normal first)
  have carry := scale_reflects values difference 0xfffffffe00000002 (by decide +kernel)
  have absent := packed_advice_not_constant row
  have carryEval := (RowExpr.reflects_iff_eval _ _ _).mp carry
  have constant : (value.sub (AIR.RowValue.pack (AIR.rowAdvice row 0 4))).constant = false := by
    change (value.constant && (AIR.RowValue.pack (AIR.rowAdvice row 0 4)).constant) = false
    rw [absent, Bool.and_false]
  rw [constant] at carryEval
  apply Emission.eval_of ?_ rfl rfl rfl rfl
  simp only [emitWordSum, evalRows, array_mapM_push,
    show (advice first 4).mapM (RowExpr.eval values) = some (AIR.rowAdvice row 0 4) from allocated,
    carryEval, bind, Option.bind_some, pure]
  rfl

theorem emitWordSum_normal (first : Nat) {sum : RowExpr}
    (normal : sum.expr.noConstantNegs = true) : Normal (emitWordSum first sum).outputs := by
  intro expr member
  rcases Array.mem_push.mp member with member | rfl
  · exact advice_normal _ _ expr member
  · exact Expr.frontMul_noConstantNegs
      (Expr.frontSub_noConstantNegs normal (packedAdvice_normal first)) rfl

theorem packed_advice_value (row : Nat → G) :
    (AIR.RowValue.pack (AIR.rowAdvice row 0 4)).value = AIR.pack4 (fun index => row index.val) := by
  change ((Array.ofFn (fun index : Fin 4 => AIR.RowValue.variable (row (0 + index.val)))).map
    AIR.RowValue.value).toList.zipIdx.foldl (fun acc (byte, index) => acc + byte * G.ofNat (256^index)) 0 = _
  rw [Array.map_ofFn, Array.toList_ofFn, list_foldl_zip_four]
  change 0 + row 0 * G.ofNat (256^0) + row 1 * G.ofNat (256^1) + row 2 * G.ofNat (256^2) +
    row 3 * G.ofNat (256^3) = AIR.pack4 (fun index => row index.val)
  rw [show G.ofNat (256^0) = (1 : G) from by decide +kernel,
    show G.ofNat (256^1) = (256 : G) from by decide +kernel,
    show G.ofNat (256^2) = (65536 : G) from by decide +kernel,
    show G.ofNat (256^3) = (16777216 : G) from by decide +kernel,
    G.mul_one, G.zero_add, G.mul_comm (row 1) 256, G.mul_comm (row 2) 65536,
    G.mul_comm (row 3) 16777216]
  rfl

def carryStep (x y z previous : Expr) : Expr :=
  (((x.frontAdd y).frontAdd previous).frontSub z).frontMul (.konst AIR.inverse256)

theorem carryStep_eval {values : Values G} {x y z previous : Expr} {a b c d : G}
    (xe : evalExpr values x = some a) (ye : evalExpr values y = some b)
    (ze : evalExpr values z = some c) (pe : evalExpr values previous = some d) :
    evalExpr values (carryStep x y z previous) = some (AIR.carryStep a b c d) :=
  Expr.frontMul_eval goldilocksLaws values
    (Expr.frontSub_eval goldilocksLaws values
      (Expr.frontAdd_eval goldilocksLaws values
        (Expr.frontAdd_eval goldilocksLaws values xe ye) pe) ze) rfl

theorem carryStep_normal {x y z previous : Expr}
    (xn : x.noConstantNegs = true) (yn : y.noConstantNegs = true)
    (zn : z.noConstantNegs = true) (pn : previous.noConstantNegs = true) :
    (carryStep x y z previous).noConstantNegs = true :=
  Expr.frontMul_noConstantNegs
    (Expr.frontSub_noConstantNegs
      (Expr.frontAdd_noConstantNegs (Expr.frontAdd_noConstantNegs xn yn) pn) zn) rfl

theorem carryStep_not_constant {x y z previous : Expr}
    (zn : z.noConstantNegs = true) (zc : z.isConstant = false) :
    (carryStep x y z previous).isConstant = false := by
  rw [carryStep, scale_isConstant _ (show AIR.inverse256 ≠ 0 from by decide +kernel),
    Expr.frontSub_isConstant _ _ zn, zc, Bool.and_false]

def carries (x y z : Fin 4 → Expr) : Fin 5 → Expr :=
  let c1 := carryStep (x 0) (y 0) (z 0) (.konst 1)
  let c2 := carryStep (x 1) (y 1) (z 1) c1
  let c3 := carryStep (x 2) (y 2) (z 2) c2
  let c4 := carryStep (x 3) (y 3) (z 3) c3
  fun index => match index with
    | 0 => .konst 1
    | 1 => c1
    | 2 => c2
    | 3 => c3
    | 4 => c4

theorem carries_eval {values : Values G} {x y z : Fin 4 → Expr} {a b c : Fin 4 → G}
    (xe : ∀ index, evalExpr values (x index) = some (a index))
    (ye : ∀ index, evalExpr values (y index) = some (b index))
    (ze : ∀ index, evalExpr values (z index) = some (c index)) :
    ∀ index, evalExpr values (carries x y z index) = some (AIR.u32Carries a b c index) := by
  have c1 := carryStep_eval (xe 0) (ye 0) (ze 0)
    (show evalExpr values (.konst 1) = some 1 from rfl)
  have c2 := carryStep_eval (xe 1) (ye 1) (ze 1) c1
  have c3 := carryStep_eval (xe 2) (ye 2) (ze 2) c2
  have c4 := carryStep_eval (xe 3) (ye 3) (ze 3) c3
  intro ⟨index, bound⟩
  have options : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by omega
  rcases options with rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact c1
  · exact c2
  · exact c3
  · exact c4

theorem carries_normal {x y z : Fin 4 → Expr}
    (xn : ∀ index, (x index).noConstantNegs = true)
    (yn : ∀ index, (y index).noConstantNegs = true)
    (zn : ∀ index, (z index).noConstantNegs = true) :
    ∀ index, (carries x y z index).noConstantNegs = true := by
  have first := carryStep_normal (xn 0) (yn 0) (zn 0) (show (Expr.konst 1).noConstantNegs = true from rfl)
  have second := carryStep_normal (xn 1) (yn 1) (zn 1) first
  have third := carryStep_normal (xn 2) (yn 2) (zn 2) second
  have fourth := carryStep_normal (xn 3) (yn 3) (zn 3) third
  intro ⟨index, bound⟩
  have options : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by omega
  rcases options with rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact first
  · exact second
  · exact third
  · exact fourth

def packSix (bytes : Fin 6 → Expr) : Expr :=
  ((((((Expr.konst 0).frontAdd ((bytes 0).frontMul (.konst 1))).frontAdd
    ((bytes 1).frontMul (.konst 256))).frontAdd ((bytes 2).frontMul (.konst 65536))).frontAdd
    ((bytes 3).frontMul (.konst 16777216))).frontAdd
    ((bytes 4).frontMul (.konst 4294967296))).frontAdd
    ((bytes 5).frontMul (.konst 1099511627776))

private def packSixValue (bytes : Fin 6 → G) : G :=
  0 + bytes 0 * 1 + bytes 1 * 256 + bytes 2 * 65536 + bytes 3 * 16777216 +
    bytes 4 * 4294967296 + bytes 5 * 1099511627776

private theorem packSixValue_eq (bytes : Fin 6 → G) : packSixValue bytes = AIR.packRank bytes := by
  unfold packSixValue AIR.packRank
  rw [G.mul_one, G.zero_add, G.mul_comm (bytes 1) 256, G.mul_comm (bytes 2) 65536,
    G.mul_comm (bytes 3) 16777216, G.mul_comm (bytes 4) 4294967296,
    G.mul_comm (bytes 5) 1099511627776]

theorem packSix_eval (values : Values G) (bytes : Fin 6 → Expr) (results : Fin 6 → G)
    (evaluated : ∀ index, evalExpr values (bytes index) = some (results index)) :
    evalExpr values (packSix bytes) = some (AIR.packRank results) := by
  have term (index : Fin 6) (coefficient : G) := Expr.frontMul_eval goldilocksLaws values
    (evaluated index) (show evalExpr values (.konst coefficient) = some coefficient from rfl)
  have packed := Expr.frontAdd_eval goldilocksLaws values
    (Expr.frontAdd_eval goldilocksLaws values
      (Expr.frontAdd_eval goldilocksLaws values
        (Expr.frontAdd_eval goldilocksLaws values
          (Expr.frontAdd_eval goldilocksLaws values
            (Expr.frontAdd_eval goldilocksLaws values
              (show evalExpr values (.konst 0) = some 0 from rfl) (term 0 1))
            (term 1 256)) (term 2 65536)) (term 3 16777216)) (term 4 4294967296))
      (term 5 1099511627776)
  change evalExpr values (packSix bytes) = some (packSixValue results) at packed
  rw [packSixValue_eq] at packed
  exact packed

def rangePair (left right : Expr) : List Expr := [.konst 11, left, right]

def rangeSix (bytes : Fin 6 → Expr) : List (List Expr) :=
  [rangePair (bytes 0) (bytes 1), rangePair (bytes 2) (bytes 3), rangePair (bytes 4) (bytes 5)]

theorem rangePair_eval {values : Values G} {left right : Expr} {a b : G}
    (leftEval : evalExpr values left = some a) (rightEval : evalExpr values right = some b) :
    (rangePair left right).mapM (evalExpr values) = some (AIR.rangeMessage (a, b)) := by
  simp only [rangePair, List.mapM_cons, List.mapM_nil, leftEval, rightEval,
    show evalExpr values (.konst 11) = some 11 from rfl, bind, Option.bind_some, pure]
  rfl

theorem rangeSix_eval {values : Values G} (bytes : Fin 6 → Expr) (results : Fin 6 → G)
    (evaluated : ∀ index, evalExpr values (bytes index) = some (results index)) :
    (rangeSix bytes).mapM (List.mapM (evalExpr values)) =
      some ((AIR.rankByteQueries results).map AIR.rangeMessage) := by
  simp only [rangeSix, List.mapM_cons, List.mapM_nil,
    rangePair_eval (evaluated 0) (evaluated 1), rangePair_eval (evaluated 2) (evaluated 3),
    rangePair_eval (evaluated 4) (evaluated 5), bind, Option.bind_some, pure]
  rfl

def emitCall (selector rank : Expr) (first function : Nat) (inputs : Array RowExpr)
    (size : Nat) : Emission :=
  let outputs := advice first size
  let child := (mainCurrent (first + size)).expr
  let gap : Fin 6 → Expr := fun index => (mainCurrent (first + size + 1 + index.val)).expr
  { outputs, used := size + 7,
    equations := [selector.frontMul
      (((child.frontSub rank).frontSub (.konst 1)).frontSub (packSix gap))],
    queries := ([.konst 0, .konst (G.ofNat function)] ++
      (rowExprs inputs).toList ++ (rowExprs outputs).toList ++ [child]) :: rangeSix gap,
    calls := [⟨function, rowExprs inputs, rowExprs outputs, child, gap⟩] }

theorem emitCall_reflects (values : Values G) (row : Nat → G) (first function size : Nat)
    {selector rank : Expr} {s r : G} {inputs : Array RowExpr} {arguments : Array AIR.RowValue}
    (selectorEval : evalExpr values selector = some s) (rankEval : evalExpr values rank = some r)
    (inputEval : evalRows values inputs = some arguments)
    (reads : ∀ index < size + 7,
      (values.columns .main .current)[first + index]? = some (row index)) :
    (emitCall selector rank first function inputs size).eval values =
      some { outputs := AIR.rowAdvice row 0 size, used := size + 7,
             equations := [s * AIR.callOrderConstraint r (row size)
               (AIR.packRank (fun index => row (size + 1 + index.val)))],
             queries := AIR.functionMessage
               ⟨function, AIR.rowValues arguments, AIR.rowValues (AIR.rowAdvice row 0 size), row size⟩ ::
               (AIR.rankByteQueries (fun index => row (size + 1 + index.val))).map AIR.rangeMessage,
             calls := [(⟨function, AIR.rowValues arguments, AIR.rowValues (AIR.rowAdvice row 0 size), row size⟩,
               fun index => row (size + 1 + index.val))] } := by
  have outputs := advice_eval values row first size (fun index bound => reads index (by omega))
  have child : evalExpr values (mainCurrent (first + size)).expr = some (row size) :=
    reads size (by omega)
  have gap (index : Fin 6) :
      evalExpr values (mainCurrent (first + size + 1 + index.val)).expr =
        some (row (size + 1 + index.val)) := by
    change (values.columns .main .current)[first + size + 1 + index.val]? = _
    simpa only [Nat.add_assoc] using reads (size + 1 + index.val) (by omega)
  have order := Expr.frontMul_eval goldilocksLaws values selectorEval
    (Expr.frontSub_eval goldilocksLaws values
      (Expr.frontSub_eval goldilocksLaws values
        (Expr.frontSub_eval goldilocksLaws values child rankEval)
        (show evalExpr values (.konst 1) = some 1 from rfl))
      (packSix_eval values _ _ gap))
  have args := congrArg (Functor.map Array.toList) (evalRows_values inputEval)
  have outs := congrArg (Functor.map Array.toList) (evalRows_values outputs)
  rw [Array.toList_mapM] at args outs
  simp only [Functor.map, Option.map_some] at args outs
  apply Emission.eval_of outputs rfl ?_ ?_ ?_
  · simp only [emitCall, List.mapM_cons, List.mapM_nil, order, bind, Option.bind_some, pure]
    rfl
  · simp only [emitCall, List.mapM_cons, List.mapM_append, List.mapM_nil,
      show evalExpr values (.konst 0) = some 0 from rfl,
      show evalExpr values (.konst (G.ofNat function)) = some (G.ofNat function) from rfl,
      args, outs, child, rangeSix_eval _ _ gap, bind, Option.bind_some, pure]
    rfl
  · have call := CallExpr.eval_of
      (call := ⟨function, rowExprs inputs, rowExprs (advice first size),
        (mainCurrent (first + size)).expr,
        fun index => (mainCurrent (first + size + 1 + index.val)).expr⟩)
      (evalRows_values inputEval) (evalRows_values outputs) child gap
    simp only [emitCall, List.mapM_cons, List.mapM_nil, call, bind, Option.bind_some, pure]

def emitStore (first : Nat) (contents : Array RowExpr) : Emission :=
  { outputs := advice first 1, used := 1,
    queries := [[.konst 1, .konst (G.ofNat contents.size), (mainCurrent first).expr] ++
      (rowExprs contents).toList] }

theorem emitStore_reflects (values : Values G) (row : Nat → G) (first : Nat)
    {contents : Array RowExpr} {stored : Array AIR.RowValue}
    (contentsEval : evalRows values contents = some stored)
    (read : (values.columns .main .current)[first]? = some (row 0)) :
    (emitStore first contents).eval values =
      some { outputs := AIR.rowAdvice row 0 1, used := 1,
             queries := [AIR.memoryMessage contents.size (row 0) (AIR.rowValues stored)] } := by
  have outputs := advice_eval values row first 1 (by
    intro index bound
    have equal : index = 0 := by omega
    subst index
    simpa only [Nat.add_zero] using read)
  have storedEval := congrArg (Functor.map Array.toList) (evalRows_values contentsEval)
  rw [Array.toList_mapM] at storedEval
  simp only [Functor.map, Option.map_some] at storedEval
  apply Emission.eval_of outputs rfl rfl ?_ rfl
  simp only [emitStore, List.cons_append, List.nil_append, List.mapM_cons, List.mapM_nil,
    show evalExpr values (.konst 1) = some 1 from rfl,
    show evalExpr values (.konst (G.ofNat contents.size)) = some (G.ofNat contents.size) from rfl,
    show evalExpr values (mainCurrent first).expr = some (row 0) from read,
    storedEval, bind, Option.bind_some, pure, AIR.memoryMessage]

def emitLoad (first size : Nat) (pointer : RowExpr) : Emission :=
  let outputs := advice first size
  { outputs, used := size,
    queries := [[.konst 1, .konst (G.ofNat size), pointer.expr] ++ (rowExprs outputs).toList] }

theorem emitLoad_reflects (values : Values G) (row : Nat → G) (first size : Nat)
    {pointer : RowExpr} {address : AIR.RowValue} (pointerRef : pointer.Reflects values address)
    (reads : ∀ index < size,
      (values.columns .main .current)[first + index]? = some (row index)) :
    (emitLoad first size pointer).eval values =
      some { outputs := AIR.rowAdvice row 0 size, used := size,
             queries := [AIR.memoryMessage size address.value (AIR.rowValues (AIR.rowAdvice row 0 size))] } := by
  have outputs := advice_eval values row first size reads
  have raw := congrArg (Functor.map Array.toList) (evalRows_values outputs)
  rw [Array.toList_mapM] at raw
  simp only [Functor.map, Option.map_some] at raw
  apply Emission.eval_of outputs rfl rfl ?_ rfl
  simp only [emitLoad, List.cons_append, List.nil_append, List.mapM_cons, List.mapM_nil,
    show evalExpr values (.konst 1) = some 1 from rfl,
    show evalExpr values (.konst (G.ofNat size)) = some (G.ofNat size) from rfl,
    pointerRef.1, raw, bind, Option.bind_some, pure, AIR.memoryMessage]

def rangeFour (bytes : Fin 4 → Expr) : List (List Expr) :=
  [rangePair (bytes 0) (bytes 1), rangePair (bytes 2) (bytes 3)]

theorem rangeFour_eval {values : Values G} (bytes : Fin 4 → Expr) (results : Fin 4 → G)
    (evaluated : ∀ index, evalExpr values (bytes index) = some (results index)) :
    (rangeFour bytes).mapM (List.mapM (evalExpr values)) = some (AIR.range4Queries results) := by
  simp only [rangeFour, List.mapM_cons, List.mapM_nil,
    rangePair_eval (evaluated 0) (evaluated 1), rangePair_eval (evaluated 2) (evaluated 3),
    bind, Option.bind_some, pure]
  rfl

def booleanExpr (expr : Expr) : Expr := expr.frontMul (expr.frontSub (.konst 1))

theorem booleanExpr_eval {values : Values G} {expr : Expr} {value : G}
    (evaluated : evalExpr values expr = some value) :
    evalExpr values (booleanExpr expr) = some (AIR.booleanConstraint value) :=
  Expr.frontMul_eval goldilocksLaws values evaluated
    (Expr.frontSub_eval goldilocksLaws values evaluated rfl)

def emitU32LessThan (selector : Expr) (first : Nat) (left right : RowExpr) : Emission :=
  let x : Fin 4 → Expr := fun index => (mainCurrent (first + index.val)).expr
  let y : Fin 4 → Expr := fun index => (mainCurrent (first + 4 + index.val)).expr
  let z : Fin 4 → Expr := fun index => (mainCurrent (first + 8 + index.val)).expr
  let chain := carries x y z
  { outputs := #[⟨(Expr.konst 1).frontSub (chain 4), 1⟩], used := 12,
    equations := selector.frontMul (left.expr.frontSub (packedAdvice first).expr) ::
      selector.frontMul (right.expr.frontSub (packedAdvice (first + 8)).expr) ::
      List.ofFn (fun index : Fin 4 => selector.frontMul (booleanExpr (chain index.succ))),
    queries := rangeFour x ++ rangeFour y ++ rangeFour z }

theorem emitU32LessThan_reflects (values : Values G) (row : Nat → G) (first : Nat)
    {selector : Expr} {s : G} {left right : RowExpr} {a b : AIR.RowValue}
    (selectorEval : evalExpr values selector = some s)
    (leftRef : left.Reflects values a) (rightRef : right.Reflects values b)
    (reads : ∀ index < 12,
      (values.columns .main .current)[first + index]? = some (row index)) :
    (emitU32LessThan selector first left right).eval values =
      some { outputs := #[⟨1 - AIR.u32Carries (fun i => row i.val)
               (fun i => row (4 + i.val)) (fun i => row (8 + i.val)) 4, 1, false⟩],
             used := 12,
             equations := s * (a.value - AIR.pack4 (fun i => row i.val)) ::
               s * (b.value - AIR.pack4 (fun i => row (8 + i.val))) ::
               List.ofFn (fun i : Fin 4 => s * AIR.booleanConstraint
                 (AIR.u32Carries (fun i => row i.val) (fun i => row (4 + i.val))
                   (fun i => row (8 + i.val)) i.succ)),
             queries := AIR.range4Queries (fun i => row i.val) ++
               AIR.range4Queries (fun i => row (4 + i.val)) ++ AIR.range4Queries (fun i => row (8 + i.val)) } := by
  let x : Fin 4 → Expr := fun index => (mainCurrent (first + index.val)).expr
  let y : Fin 4 → Expr := fun index => (mainCurrent (first + 4 + index.val)).expr
  let z : Fin 4 → Expr := fun index => (mainCurrent (first + 8 + index.val)).expr
  have xe (index : Fin 4) : evalExpr values (x index) = some (row index.val) :=
    reads index.val (by omega)
  have ye (index : Fin 4) : evalExpr values (y index) = some (row (4 + index.val)) := by
    change (values.columns .main .current)[first + 4 + index.val]? = _
    simpa only [Nat.add_assoc] using reads (4 + index.val) (by omega)
  have ze (index : Fin 4) : evalExpr values (z index) = some (row (8 + index.val)) := by
    change (values.columns .main .current)[first + 8 + index.val]? = _
    simpa only [Nat.add_assoc] using reads (8 + index.val) (by omega)
  have chain := carries_eval xe ye ze
  have px := (packedAdvice_reflects values row first (fun index bound => reads index (by omega))).1
  have pz := (packedAdvice_reflects values (fun index => row (8 + index)) (first + 8) (by
    intro index bound
    simpa only [Nat.add_assoc] using reads (8 + index) (by omega))).1
  rw [packed_advice_value] at px pz
  have firstEq := Expr.frontMul_eval goldilocksLaws values selectorEval
    (Expr.frontSub_eval goldilocksLaws values leftRef.1 px)
  have secondEq := Expr.frontMul_eval goldilocksLaws values selectorEval
    (Expr.frontSub_eval goldilocksLaws values rightRef.1 pz)
  have restEq (index : Fin 4) := Expr.frontMul_eval goldilocksLaws values selectorEval
    (booleanExpr_eval (chain index.succ))
  have chainNormal : (carries x y z 4).noConstantNegs = true :=
    carries_normal (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) 4
  have chainNonconstant : (carries x y z 4).isConstant = false := carryStep_not_constant rfl rfl
  have output : (⟨(Expr.konst 1).frontSub (carries x y z 4), 1⟩ : RowExpr).Reflects values
      ⟨1 - AIR.u32Carries (fun i => row i.val) (fun i => row (4 + i.val))
        (fun i => row (8 + i.val)) 4, 1, false⟩ := by
    refine ⟨Expr.frontSub_eval goldilocksLaws values
      (show evalExpr values (.konst 1) = some 1 from rfl) (chain 4), rfl, ?_⟩
    change ((Expr.konst 1).frontSub (carries x y z 4)).isConstant = false
    rw [Expr.frontSub_isConstant _ _ chainNormal, chainNonconstant, Bool.and_false]
  apply Emission.eval_of (evalRows_singleton output) rfl ?_ ?_ rfl
  · have remaining := list_mapM_ofFn _ _ (evalExpr values) restEq
    dsimp only [x, y, z] at remaining
    simp only [emitU32LessThan, List.mapM_cons, firstEq, secondEq, remaining,
      bind, Option.bind_some, pure, goldilocks_mul, goldilocks_sub]
  · have rx := rangeFour_eval x _ xe
    have ry := rangeFour_eval y _ ye
    have rz := rangeFour_eval z _ ze
    dsimp only [x, y, z] at rx ry rz
    simp only [emitU32LessThan, List.mapM_append, rx, ry, rz, bind, Option.bind_some, pure]

theorem emitU32LessThan_normal (selector : Expr) (first : Nat) (left right : RowExpr) :
    Normal (emitU32LessThan selector first left right).outputs := by
  intro expr member
  have equal := Array.mem_singleton.mp member
  subst expr
  let x : Fin 4 → Expr := fun index => (mainCurrent (first + index.val)).expr
  let y : Fin 4 → Expr := fun index => (mainCurrent (first + 4 + index.val)).expr
  let z : Fin 4 → Expr := fun index => (mainCurrent (first + 8 + index.val)).expr
  have normal : (carries x y z 4).noConstantNegs = true :=
    carries_normal (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) 4
  exact Expr.frontSub_noConstantNegs (left := Expr.konst 1) (right := carries x y z 4) rfl normal

def emitAssert (selector : Expr) (left right : Array RowExpr) : Emission :=
  { equations := List.ofFn fun index : Fin left.size => selector.frontMul
      ((left[index.val]?.getD (.konst 0)).expr.frontSub (right[index.val]?.getD (.konst 0)).expr) }

theorem rowValues_getD (rows : Array AIR.RowValue) (index : Nat) :
    (AIR.rowValues rows)[index]?.getD 0 = (rows[index]?.getD (.konst 0)).value := by
  simp only [AIR.rowValues, Array.getElem?_map]
  cases rows[index]? <;> rfl

theorem emitAssert_reflects {values : Values G} {selector : Expr} {s : G}
    {left right : Array RowExpr} {a b : Array AIR.RowValue}
    (selectorEval : evalExpr values selector = some s)
    (leftEval : evalRows values left = some a) (rightEval : evalRows values right = some b)
    (size : left.size = right.size) :
    (emitAssert selector left right).eval values =
      some { equations := List.ofFn fun index : Fin left.size =>
        s * ((AIR.rowValues a)[index.val]?.getD 0 - (AIR.rowValues b)[index.val]?.getD 0) } := by
  apply Emission.eval_of (evalRows_empty values) rfl ?_ rfl rfl
  apply list_mapM_ofFn
  intro index
  have leftRef := evalRows_getD leftEval index.isLt
  have rightRef := evalRows_getD rightEval (index := index.val) (by omega)
  rw [rowValues_getD, rowValues_getD]
  exact Expr.frontMul_eval goldilocksLaws values selectorEval
    (Expr.frontSub_eval goldilocksLaws values leftRef.1 rightRef.1)

/-- The operation dispatcher mirrors the native emitter's fresh-column order.
Operand reads here are checked in the incoming logical scope. The native store
reads after pushing its pointer, so that correspondence also uses the checked
program's incoming-scope index validity. -/
def emitOp (selector rank : Expr) (first : Nat) (op : Bytecode.Op)
    (rows : Array RowExpr) : Option Emission :=
  match op with
  | .const value => some (fromScalar ⟨.konst value, 0, []⟩)
  | .add a b => do return fromScalar ⟨(← rows[a]?).add (← rows[b]?), 0, []⟩
  | .sub a b => do return fromScalar ⟨(← rows[a]?).sub (← rows[b]?), 0, []⟩
  | .mul a b => do return fromScalar (NativeAIR.emitMul selector first (← rows[a]?) (← rows[b]?))
  | .eqZero a => do return fromScalar (NativeAIR.emitEqZero selector first (← rows[a]?))
  | .call function indices size unconstrained =>
    if unconstrained then some (emitAdvice first size)
    else do return emitCall selector rank first function (← select rows indices) size
  | .store indices => do return emitStore first (← select rows indices)
  | .load size index => do return emitLoad first size (← rows[index]?)
  | .assertEq xs ys _ =>
    if xs.size ≠ ys.size then none
    else do return emitAssert selector (← select rows xs) (← select rows ys)
  | .ioGetInfo .. => some (emitAdvice first 2)
  | .ioRead _ _ size => some (emitAdvice first size)
  | .ioSetInfo .. | .ioWrite .. | .debug .. => some {}
  | .u8BitDecomposition index => do return emitByte1 first .bits (← rows[index]?)
  | .u8ShiftLeft index => do return emitByte1 first .shiftLeft (← rows[index]?)
  | .u8ShiftRight index => do return emitByte1 first .shiftRight (← rows[index]?)
  | .u8Xor a b => do return emitByte2 first .xor (← rows[a]?) (← rows[b]?)
  | .u8Add a b => do return emitByte2 first .add (← rows[a]?) (← rows[b]?)
  | .u8Sub a b => do return emitByte2 first .sub (← rows[a]?) (← rows[b]?)
  | .u8And a b => do return emitByte2 first .and (← rows[a]?) (← rows[b]?)
  | .u8Or a b => do return emitByte2 first .or (← rows[a]?) (← rows[b]?)
  | .u8LessThan a b => do return emitByte2 first .lessThan (← rows[a]?) (← rows[b]?)
  | .u8RangeCheck a b => do return emitByte2 first .range (← rows[a]?) (← rows[b]?)
  | .u8Mul a b => do return emitByte2 first .mul (← rows[a]?) (← rows[b]?)
  | .u8XorSplit7 a b => do return emitByte2 first .split7 (← rows[a]?) (← rows[b]?)
  | .u8XorSplit4 a b => do return emitByte2 first .split4 (← rows[a]?) (← rows[b]?)
  | .u32LessThan a b => do return emitU32LessThan selector first (← rows[a]?) (← rows[b]?)
  | .unconstrainedBigUintDivMod .. => some (emitAdvice first 2)
  | .unconstrainedGToBytes .. => some (emitAdvice first 8)
  | .unconstrainedGInverse .. => some (emitAdvice first 1)
  | .unconstrainedU32Add a b => do
    return emitWordSum first ((← readWord rows a).add (← readWord rows b))
  | .unconstrainedU32Add3 a b c => do
    return emitWordSum first (((← readWord rows a).add (← readWord rows b)).add (← readWord rows c))
  | .u32ToField indices => do return fromScalar ⟨← readWord rows indices, 0, []⟩

end OpEmitter
end Aiur.NativeAIR
