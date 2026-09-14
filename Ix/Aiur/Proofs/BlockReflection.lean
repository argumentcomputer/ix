/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.BlockExpressions

/-!
Reflection of symbolic block and control emission into the valued model.
Branch callbacks below are discharged by structural recursion over bytecode;
fresh reads are restricted to the columns consumed by the complete emission.
-/

namespace Aiur.NativeAIR.BlockEmitter
open OpEmitter LookupEmitter

def selectorAt (selectors : Array G) (index : Nat) : G := selectors[index]?.getD 0

def Context.valued (context : Context) (rank : G) : AIR.RowContext :=
  ⟨context.function, context.inputSize, rank, context.callRanks⟩

def BlockReflects (values : Values G) (row : Nat → G) (selectors : Array Expr) (selected : Nat → G)
    (context : Context) (rank : G) (block : Bytecode.Block) : Prop :=
  ∀ {incoming : Expr} {s : G} {rows : Array RowExpr} {inputs : Array AIR.RowValue}
    {column lookup : Nat} {emission : Emission},
    evalExpr values incoming = some s → evalRows values rows = some inputs → Normal rows →
    emitBlock selectors context incoming rows column lookup block = some emission →
    (∀ index, column ≤ index → index < emission.column →
      (values.columns .main .current)[index]? = some (row index)) →
    ∃ result, block.emitRow row selected (context.valued rank) s inputs column lookup = some result ∧
      emission.eval values = some result

def CtrlReflects (values : Values G) (row : Nat → G) (selectors : Array Expr) (selected : Nat → G)
    (context : Context) (rank : G) (ctrl : Bytecode.Ctrl) : Prop :=
  ∀ {incoming : Expr} {s : G} {rows : Array RowExpr} {inputs : Array AIR.RowValue}
    {column lookup : Nat} {emission : Emission},
    evalExpr values incoming = some s → evalRows values rows = some inputs → Normal rows →
    emitCtrl selectors context incoming rows column lookup ctrl = some emission →
    (∀ index, column ≤ index → index < emission.column →
      (values.columns .main .current)[index]? = some (row index)) →
    ∃ result, ctrl.emitRow row selected (context.valued rank) s inputs column lookup = some result ∧
      emission.eval values = some result

theorem list_mapM_refine_mem {α β γ : Type} {first : α → Option β} {second : α → Option γ}
    {evaluate : β → Option γ} {inputs : List α} {outputs : List β}
    (selected : inputs.mapM first = some outputs)
    (related : ∀ input ∈ inputs, ∀ output ∈ outputs, first input = some output →
      ∃ value, second input = some value ∧ evaluate output = some value) :
    ∃ values, inputs.mapM second = some values ∧ outputs.mapM evaluate = some values := by
  induction inputs generalizing outputs with
  | nil =>
    cases selected
    exact ⟨[], rfl, rfl⟩
  | cons input rest ih =>
    simp only [List.mapM_cons, bind, Option.bind] at selected
    split at selected
    · cases selected
    rename_i output outputSelected
    dsimp only at selected
    split at selected
    · cases selected
    rename_i tail tailSelected
    cases selected
    obtain ⟨value, read, evaluated⟩ := related input List.mem_cons_self output List.mem_cons_self outputSelected
    obtain ⟨values, reads, evaluations⟩ := ih tailSelected (fun input member output present selected =>
      related input (List.mem_cons_of_mem _ member) output (List.mem_cons_of_mem _ present) selected)
    refine ⟨value :: values, ?_, ?_⟩ <;>
      simp only [List.mapM_cons, read, evaluated, reads, evaluations, bind, Option.bind_some, pure]

theorem caseRows_reflects {values : Values G} (row : Nat → G)
    {selectors : Array Expr} {selected : Nat → G} {context : Context} (rank : G)
    {matched : RowExpr} {value : AIR.RowValue} {rows : Array RowExpr} {inputs : Array AIR.RowValue}
    (column lookup limit : Nat) {branches : Array (G × Bytecode.Block)} {emissions : List Emission}
    (selectorEval : SelectorReads values selectors selected)
    (matchedRef : matched.Reflects values value)
    (inputEval : evalRows values rows = some inputs) (normal : Normal rows)
    (emitted : branches.toList.mapM (caseRow selectors context matched rows column lookup) = some emissions)
    (bounds : ∀ emission ∈ emissions, emission.column ≤ limit)
    (reads : ∀ index, column ≤ index → index < limit →
      (values.columns .main .current)[index]? = some (row index))
    (reflection : ∀ pair ∈ branches.toList, BlockReflects values row selectors selected context rank pair.2) :
    ∃ results, branches.toList.mapM (Bytecode.caseRow row selected (context.valued rank)
      value.value inputs column lookup) = some results ∧ emissions.mapM (Emission.eval values) = some results := by
  apply list_mapM_refine_mem emitted
  intro pair member emission present emitted
  simp only [caseRow, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  rename_i entry entrySelected
  dsimp only at emitted
  split at emitted
  · cases emitted
  rename_i child childEmitted
  cases emitted
  have upper := bounds _ present
  have entryEval : evalExpr values entry = some (pair.2.selectorFlow selected).entry :=
    blockSelector_reads selectorEval pair.2 entrySelected
  obtain ⟨result, resultEmitted, resultEval⟩ := reflection pair member entryEval inputEval normal childEmitted
    (fun index lower bound => reads index lower (Nat.lt_of_lt_of_le bound upper))
  have equation : [caseEquation entry matched pair.1].mapM (evalExpr values) =
      some [(pair.2.selectorFlow selected).entry * (value.value - pair.1)] := by
    simp only [List.mapM_cons, List.mapM_nil, caseEquation_eval entryEval matchedRef,
      bind, Option.bind_some, pure]
  refine ⟨_, ?_, Emission.prefix_eval resultEval equation⟩
  simp only [Bytecode.caseRow, resultEmitted, bind, Option.bind_some, pure]

theorem defaultRow_reflects {values : Values G} (row : Nat → G)
    {selectors : Array Expr} {selected : Nat → G} {context : Context} (rank : G)
    {matched : RowExpr} {value : AIR.RowValue} {rows : Array RowExpr} {inputs : Array AIR.RowValue}
    (column lookup limit : Nat) (branches : Array (G × Bytecode.Block)) {fallback : Option Bytecode.Block}
    {emissions : List Emission} (selectorEval : SelectorReads values selectors selected)
    (matchedRef : matched.Reflects values value)
    (inputEval : evalRows values rows = some inputs) (normal : Normal rows)
    (emitted : defaultRow selectors context matched rows column lookup branches fallback = some emissions)
    (bounds : ∀ emission ∈ emissions, emission.column ≤ limit)
    (reads : ∀ index, column ≤ index → index < limit →
      (values.columns .main .current)[index]? = some (row index))
    (reflection : ∀ block ∈ fallback.toList, BlockReflects values row selectors selected context rank block) :
    ∃ results, Bytecode.defaultRow row selected (context.valued rank) value.value
      inputs column lookup branches fallback = some results ∧ emissions.mapM (Emission.eval values) = some results := by
  cases fallback with
  | none =>
    cases emitted
    exact ⟨[], rfl, rfl⟩
  | some block =>
    simp only [defaultRow, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i entry entrySelected
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i child childEmitted
    cases emitted
    have upper := bounds _ List.mem_cons_self
    have allocated := (emitBlock_invariants block normal childEmitted).2
    have entryEval : evalExpr values entry = some (block.selectorFlow selected).entry :=
      blockSelector_reads selectorEval block entrySelected
    obtain ⟨result, resultEmitted, resultEval⟩ := reflection block List.mem_cons_self entryEval inputEval normal childEmitted
      (fun index lower upperBound => reads index (by omega) (Nat.lt_of_lt_of_le upperBound upper))
    have equations := defaultEquations_eval row column branches entryEval matchedRef
      (fun index bound => reads (column + index) (by omega) (by dsimp only [Emission.prefix] at upper; omega))
    have prefixed := Emission.prefix_eval resultEval equations
    refine ⟨[result.prefix (branches.toList.mapIdx fun index pair =>
      (block.selectorFlow selected).entry * ((value.value - pair.1) * row (column + index) - 1))], ?_, ?_⟩
    · simp only [Bytecode.defaultRow, resultEmitted, bind, Option.bind_some, pure]
    · simp only [List.mapM_cons, List.mapM_nil, prefixed, bind, Option.bind_some, pure]

theorem branchRows_reflects {values : Values G} (row : Nat → G)
    {selectors : Array Expr} {selected : Nat → G} {context : Context} (rank : G)
    {matched : RowExpr} {value : AIR.RowValue} {rows : Array RowExpr} {inputs : Array AIR.RowValue}
    {column lookup : Nat} {branches : Array (G × Bytecode.Block)} {fallback : Option Bytecode.Block}
    {emission : Emission} (selectorEval : SelectorReads values selectors selected)
    (matchedRef : matched.Reflects values value)
    (inputEval : evalRows values rows = some inputs) (normal : Normal rows)
    (emitted : branchRows selectors context matched rows column lookup branches fallback = some emission)
    (reads : ∀ index, column ≤ index → index < emission.column →
      (values.columns .main .current)[index]? = some (row index))
    (casesReflect : ∀ pair ∈ branches.toList, BlockReflects values row selectors selected context rank pair.2)
    (defaultReflect : ∀ block ∈ fallback.toList, BlockReflects values row selectors selected context rank block) :
    ∃ result, Bytecode.branchRows row selected (context.valued rank) value.value
      inputs column lookup branches fallback = some result ∧ emission.eval values = some result := by
  simp only [branchRows, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  rename_i cases casesEmitted
  dsimp only at emitted
  split at emitted
  · cases emitted
  rename_i default defaultEmitted
  cases emitted
  obtain ⟨caseValues, casesRead, casesEval⟩ := caseRows_reflects row rank column lookup
    (join rows column lookup (cases ++ default)).column selectorEval matchedRef inputEval normal casesEmitted
    (fun emission member => fold_max_member Emission.column (List.mem_append_left default member) column) reads casesReflect
  obtain ⟨defaultValues, defaultRead, defaultEval⟩ := defaultRow_reflects row rank column lookup
    (join rows column lookup (cases ++ default)).column branches selectorEval matchedRef inputEval normal defaultEmitted
    (fun emission member => fold_max_member Emission.column (List.mem_append_right cases member) column) reads defaultReflect
  have combined : (cases ++ default).mapM (Emission.eval values) = some (caseValues ++ defaultValues) := by
    simp only [List.mapM_append, casesEval, defaultEval, bind, Option.bind_some, pure]
  refine ⟨_, ?_, join_eval inputEval column lookup combined⟩
  simp only [Bytecode.branchRows, casesRead, defaultRead, bind, Option.bind_some, pure]

theorem continueRow_column {selectors : Array Expr} {context : Context} {incoming : Expr}
    {rows : Array RowExpr} {size : Nat} {continuation : Bytecode.Block} {joined emission : Emission}
    (normal : Normal rows)
    (emitted : continueRow selectors context incoming rows size continuation joined = some emission) :
    joined.column ≤ emission.column := by
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
    exact Nat.le_trans (Nat.le_add_right _ _)
      (emitBlock_invariants continuation (normal.append (advice_normal _ _)) continuedEmitted).2
  · cases emitted

theorem advice_absolute_eval {values : Values G} (row : Nat → G) (column size : Nat)
    (reads : ∀ index < size, (values.columns .main .current)[column + index]? = some (row (column + index))) :
    evalRows values (advice column size) = some (AIR.rowAdvice row column size) := by
  simpa only [AIR.rowAdvice, Nat.zero_add] using advice_eval values (fun index => row (column + index)) column size reads

theorem continueRow_reflects {values : Values G} (row : Nat → G)
    {selectors : Array Expr} {selected : Nat → G} {context : Context} (rank : G)
    {incoming : Expr} {s : G} {rows : Array RowExpr} {inputs : Array AIR.RowValue}
    (size : Nat) (continuation : Bytecode.Block) {joined emission : Emission} {branches : AIR.BlockEmission}
    (selectorEval : SelectorReads values selectors selected)
    (incomingEval : evalExpr values incoming = some s)
    (inputEval : evalRows values rows = some inputs) (normal : Normal rows)
    (joinedEval : joined.eval values = some branches)
    (emitted : continueRow selectors context incoming rows size continuation joined = some emission)
    (reads : ∀ index, joined.column ≤ index → index < emission.column →
      (values.columns .main .current)[index]? = some (row index))
    (reflection : BlockReflects values row selectors selected context rank continuation) :
    ∃ result, Bytecode.continueRow row selected (context.valued rank) s inputs size continuation branches =
      some result ∧ emission.eval values = some result := by
  simp only [continueRow] at emitted
  split at emitted
  · rename_i widths
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i entry entrySelected
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i continued continuedEmitted
    cases emitted
    have allocated := (emitBlock_invariants continuation (normal.append (advice_normal _ _)) continuedEmitted).2
    obtain ⟨_, column, lookup, _, _, _, yieldsEval, _⟩ := Emission.eval_components joinedEval
    have validWidths : branches.yields.all (fun part => part.2.size == size) = true :=
      (yields_size yieldsEval size).symm.trans widths
    have fresh : ∀ index < size,
        (values.columns .main .current)[joined.column + index]? = some (row (joined.column + index)) :=
      fun index bound => reads (joined.column + index) (by omega)
        (by change joined.column + index < continued.column; omega)
    have outputs := advice_absolute_eval row joined.column size fresh
    have gateEval := yieldGate_eval yieldsEval
    have entryEval : evalExpr values entry = some (continuation.selectorFlow selected).entry :=
      blockSelector_reads selectorEval continuation entrySelected
    obtain ⟨result, resultEmitted, resultEval⟩ := reflection gateEval (evalRows_append inputEval outputs)
      (normal.append (advice_normal _ _)) continuedEmitted (fun index lower upper => reads index (by omega) upper)
    have mergeEval := mergeEquations_eval row joined.column size incomingEval yieldsEval fresh
    have linkEval := Expr.frontSub_eval goldilocksLaws values entryEval gateEval
    have equations : (mergeEquations incoming joined.column size joined.yields ++ [entry.frontSub (yieldGate joined.yields)]).mapM
        (evalExpr values) = some (AIR.mergeEquations row s joined.column size branches.yields ++
          [(continuation.selectorFlow selected).entry - AIR.selectorSum (branches.yields.map Prod.fst)]) := by
      simp only [List.mapM_append, List.mapM_cons, List.mapM_nil, mergeEval, linkEval,
        bind, Option.bind_some, pure, goldilocks_sub]
    refine ⟨_, ?_, Emission.continued_eval joinedEval resultEval equations⟩
    simp only [Bytecode.continueRow, validWidths, if_true, ← column, ← lookup,
      resultEmitted, bind, Option.bind_some, pure]
  · cases emitted

private theorem case_block_smaller {branches : Array (G × Bytecode.Block)} {pair : G × Bytecode.Block}
    (member : pair ∈ branches.toList) : sizeOf pair.2 < sizeOf branches := by
  have present : pair ∈ branches := Array.mem_toList_iff.mp member
  have bound := Array.sizeOf_lt_of_mem present
  cases pair
  simp at bound ⊢
  omega

private theorem fallback_block_smaller {fallback : Option Bytecode.Block} {block : Bytecode.Block}
    (member : block ∈ fallback.toList) : sizeOf block < sizeOf fallback := by
  cases fallback with
  | none => cases member
  | some value =>
    have equal := List.mem_singleton.mp member
    subst block
    simp

private theorem block_smaller (block : Bytecode.Block) : sizeOf block.ctrl < sizeOf block := by
  cases block
  simp
  omega

mutual

theorem ctrl_reflects (values : Values G) (row : Nat → G)
    {selectors : Array Expr} {selected : Nat → G} {context : Context} {rank : G}
    (selectorEval : SelectorReads values selectors selected)
    (rankEval : evalExpr values context.rank = some rank) (ctrl : Bytecode.Ctrl) :
    CtrlReflects values row selectors selected context rank ctrl := by
  intro incoming s rows inputs column lookup emission incomingEval inputEval normal emitted reads
  cases ctrl with
  | «return» index indices =>
    simp only [emitCtrl, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i arguments argsSelected
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i outputs outputsSelected
    cases emitted
    obtain ⟨args, argsRead, argsEval⟩ := select_reflects inputEval argsSelected
    obtain ⟨out, outRead, outEval⟩ := select_reflects inputEval outputsSelected
    refine ⟨_, ?_, returned_eval column lookup incomingEval rankEval inputEval argsEval outEval⟩
    simp only [Bytecode.Ctrl.emitRow, Context.valued, select_values argsRead, select_values outRead,
      bind, Option.bind_some, pure]
  | yield index indices =>
    simp only [emitCtrl, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i selector selectorRead
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i outputs outputsSelected
    cases emitted
    obtain ⟨out, outRead, outEval⟩ := select_reflects inputEval outputsSelected
    have selectedEval : evalExpr values selector = some (selected index) := selectorEval selectorRead
    have selectedList := congrArg (Functor.map Array.toList) outRead
    rw [Array.toList_mapM] at selectedList
    simp only [Functor.map, Option.map_some] at selectedList
    refine ⟨_, ?_, yielded_eval column lookup selectedEval inputEval outEval⟩
    simp only [Bytecode.Ctrl.emitRow, selectedList, bind, Option.bind_some, pure, Array.toArray_toList]
  | «match» index branches fallback =>
    rw [emitCtrl_match] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i matched matchedRead
    dsimp only at emitted
    obtain ⟨value, valueRead, valueRef⟩ := evalRows_read inputEval matchedRead
    obtain ⟨result, resultEmitted, resultEval⟩ := branchRows_reflects row rank selectorEval valueRef inputEval normal emitted reads
      (fun pair member => block_reflects values row selectorEval rankEval pair.2)
      (fun block member => block_reflects values row selectorEval rankEval block)
    refine ⟨result, ?_, resultEval⟩
    simp only [Bytecode.Ctrl.emitRow_match, valueRead, resultEmitted, bind, Option.bind_some]
  | matchContinue index branches fallback size aux slots continuation =>
    rw [emitCtrl_matchContinue] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i matched matchedRead
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i joined joinedEmitted
    dsimp only at emitted
    have finish := continueRow_column normal emitted
    have start := (branchRows_invariants normal joinedEmitted).2
    obtain ⟨value, valueRead, valueRef⟩ := evalRows_read inputEval matchedRead
    obtain ⟨branchValue, branchEmitted, branchEval⟩ := branchRows_reflects row rank selectorEval valueRef inputEval normal
      joinedEmitted (fun index lower upper => reads index lower (Nat.lt_of_lt_of_le upper finish))
      (fun pair member => block_reflects values row selectorEval rankEval pair.2)
      (fun block member => block_reflects values row selectorEval rankEval block)
    obtain ⟨result, resultEmitted, resultEval⟩ := continueRow_reflects row rank size continuation
      selectorEval incomingEval inputEval normal branchEval emitted
      (fun index lower upper => reads index (Nat.le_trans start lower) upper)
      (block_reflects values row selectorEval rankEval continuation)
    refine ⟨result, ?_, resultEval⟩
    simp only [Bytecode.Ctrl.emitRow_matchContinue, valueRead, branchEmitted, resultEmitted, bind, Option.bind_some]
termination_by sizeOf ctrl
decreasing_by
  all_goals subst ctrl
  all_goals first
    | (have bound := case_block_smaller ‹_ ∈ _›; simp; omega)
    | (have bound := fallback_block_smaller ‹_ ∈ _›; simp; omega)
    | decreasing_tactic

theorem block_reflects (values : Values G) (row : Nat → G)
    {selectors : Array Expr} {selected : Nat → G} {context : Context} {rank : G}
    (selectorEval : SelectorReads values selectors selected)
    (rankEval : evalExpr values context.rank = some rank) (block : Bytecode.Block) :
    BlockReflects values row selectors selected context rank block := by
  intro incoming s rows inputs column lookup emission incomingEval inputEval normal emitted reads
  simp only [emitBlock, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  rename_i entry entrySelected
  dsimp only at emitted
  split at emitted
  · cases emitted
  rename_i operations operationsEmitted
  dsimp only at emitted
  split at emitted
  · cases emitted
  rename_i control controlEmitted
  cases emitted
  have operationsNormal := emitOps_normal normal operationsEmitted
  have endBound := (emitCtrl_invariants block.ctrl operationsNormal controlEmitted).2
  have startBound := emitOps_column operationsEmitted
  obtain ⟨opValue, opEmitted, opEval⟩ := emitOps_reflects values row incomingEval rankEval inputEval normal operationsEmitted
    (fun index lower upper => reads index lower (by change index < control.column; omega))
  obtain ⟨opValues, columnEq, _, queriesEval, _⟩ := OpsEmission.eval_components opEval
  have queryCount := Bytecode.AIR.list_mapM_some_length _ _ _ queriesEval
  obtain ⟨result, resultEmitted, resultEval⟩ := ctrl_reflects values row selectorEval rankEval block.ctrl
    incomingEval opValues operationsNormal controlEmitted
    (fun index lower upper => reads index (Nat.le_trans startBound lower) upper)
  have entryEval : evalExpr values entry = some (block.selectorFlow selected).entry :=
    blockSelector_reads selectorEval block entrySelected
  have guard := Expr.frontMul_eval goldilocksLaws values entryEval
    (Expr.frontSub_eval goldilocksLaws values (show evalExpr values (.konst 1) = some 1 from rfl) entryEval)
  have guarded : [entry.frontMul ((Expr.konst 1).frontSub entry)].mapM (evalExpr values) =
      some [AIR.oneSubBooleanConstraint (block.selectorFlow selected).entry] := by
    simp only [List.mapM_cons, List.mapM_nil, guard, bind, Option.bind_some, pure, goldilocks_mul, goldilocks_sub]
    rfl
  refine ⟨_, ?_, Emission.prefix_eval (Emission.afterOps_eval lookup incomingEval opEval resultEval) guarded⟩
  simp only [Bytecode.Block.emitRow, show (context.valued rank).rank = rank from rfl,
    show (context.valued rank).callRanks = context.callRanks from rfl, opEmitted,
    bind, Option.bind_some, ← columnEq, queryCount, resultEmitted, pure]
termination_by sizeOf block
decreasing_by exact block_smaller block

end

end Aiur.NativeAIR.BlockEmitter
