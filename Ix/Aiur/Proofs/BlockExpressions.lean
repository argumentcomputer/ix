/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.BlockSelectors

/-!
Symbolic block emission retains returns, escaping yields, and gated call
records alongside the native expressions. Branch joins restore the incoming
logical map; continuations consume their local yields and append merge columns.
-/

namespace Aiur.NativeAIR.BlockEmitter
open OpEmitter LookupEmitter

theorem list_mapM_flatMap {α β γ δ : Type} {read : α → Option β}
    {inputs : List α} {outputs : List β} (evaluated : inputs.mapM read = some outputs)
    (first : α → List γ) (second : β → List δ) (evaluate : γ → Option δ)
    (related : ∀ input output, read input = some output →
      (first input).mapM evaluate = some (second output)) :
    (inputs.flatMap first).mapM evaluate = some (outputs.flatMap second) := by
  induction inputs generalizing outputs with
  | nil =>
    cases evaluated
    rfl
  | cons input rest ih =>
    simp only [List.mapM_cons, bind, Option.bind] at evaluated
    split at evaluated
    · cases evaluated
    rename_i output outputEval
    dsimp only at evaluated
    split at evaluated
    · cases evaluated
    rename_i tail tailEval
    cases evaluated
    simp only [List.flatMap_cons, List.mapM_append, related input output outputEval,
      ih tailEval, bind, Option.bind_some, pure]

theorem list_mapM_foldl {α β γ : Type} {read : α → Option β}
    {inputs : List α} {outputs : List β} (evaluated : inputs.mapM read = some outputs)
    (first : γ → α → γ) (second : γ → β → γ)
    (related : ∀ input output, read input = some output → ∀ start, first start input = second start output)
    (start : γ) : inputs.foldl first start = outputs.foldl second start := by
  induction inputs generalizing outputs start with
  | nil =>
    cases evaluated
    rfl
  | cons input rest ih =>
    simp only [List.mapM_cons, bind, Option.bind] at evaluated
    split at evaluated
    · cases evaluated
    rename_i output outputEval
    dsimp only at evaluated
    split at evaluated
    · cases evaluated
    rename_i tail tailEval
    cases evaluated
    simp only [List.foldl_cons, related input output outputEval, ih tailEval]

structure Context where
  function : Nat
  inputSize : Nat
  rank : Expr

structure ReturnExpr where
  selector : Expr
  function : Nat
  inputs : Array Expr
  outputs : Array Expr
  rank : Expr

def ReturnExpr.eval (values : Values G) (returned : ReturnExpr) : Option (G × Bytecode.AIR.Call) := do
  let selector ← evalExpr values returned.selector
  let inputs ← returned.inputs.mapM (evalExpr values)
  let outputs ← returned.outputs.mapM (evalExpr values)
  let rank ← evalExpr values returned.rank
  return (selector, ⟨returned.function, inputs, outputs, rank⟩)

def ReturnExpr.message (returned : ReturnExpr) : List Expr :=
  [.konst 0, .konst (G.ofNat returned.function)] ++ returned.inputs.toList ++
    returned.outputs.toList ++ [returned.rank]

structure YieldExpr where
  selector : Expr
  values : Array RowExpr

def YieldExpr.eval (values : Values G) (yielded : YieldExpr) : Option (G × Array AIR.RowValue) := do
  let selector ← evalExpr values yielded.selector
  let outputs ← evalRows values yielded.values
  return (selector, outputs)

def evalGatedCall (values : Values G) (called : Expr × CallExpr) :
    Option (G × (Bytecode.AIR.Call × (Fin 6 → G))) := do
  let selector ← evalExpr values called.1
  let call ← called.2.eval values
  return (selector, call)

structure Emission where
  values : Array RowExpr
  column : Nat
  lookup : Nat
  equations : List Expr := []
  queries : List QueryExpr := []
  returns : List ReturnExpr := []
  yields : List YieldExpr := []
  calls : List (Expr × CallExpr) := []

def Emission.eval (values : Values G) (emission : Emission) : Option AIR.BlockEmission := do
  let outputs ← evalRows values emission.values
  let equations ← emission.equations.mapM (evalExpr values)
  let queries ← emission.queries.mapM (QueryExpr.eval values)
  let returns ← emission.returns.mapM (ReturnExpr.eval values)
  let yields ← emission.yields.mapM (YieldExpr.eval values)
  let calls ← emission.calls.mapM (evalGatedCall values)
  return ⟨outputs, emission.column, emission.lookup, equations, queries, returns, yields, calls⟩

theorem Emission.eval_of {values : Values G} {emission : Emission} {result : AIR.BlockEmission}
    (outputs : evalRows values emission.values = some result.values)
    (column : emission.column = result.column) (lookup : emission.lookup = result.lookup)
    (equations : emission.equations.mapM (evalExpr values) = some result.equations)
    (queries : emission.queries.mapM (QueryExpr.eval values) = some result.queries)
    (returns : emission.returns.mapM (ReturnExpr.eval values) = some result.returns)
    (yields : emission.yields.mapM (YieldExpr.eval values) = some result.yields)
    (calls : emission.calls.mapM (evalGatedCall values) = some result.calls) :
    emission.eval values = some result := by
  simp only [Emission.eval, outputs, equations, queries, returns, yields, calls,
    column, lookup, bind, Option.bind_some, pure]

theorem Emission.eval_components {values : Values G} {emission : Emission} {result : AIR.BlockEmission}
    (evaluated : emission.eval values = some result) :
    evalRows values emission.values = some result.values ∧
    emission.column = result.column ∧ emission.lookup = result.lookup ∧
    emission.equations.mapM (evalExpr values) = some result.equations ∧
    emission.queries.mapM (QueryExpr.eval values) = some result.queries ∧
    emission.returns.mapM (ReturnExpr.eval values) = some result.returns ∧
    emission.yields.mapM (YieldExpr.eval values) = some result.yields ∧
    emission.calls.mapM (evalGatedCall values) = some result.calls := by
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
  rename_i returns returnsEval
  dsimp only at evaluated
  split at evaluated
  · cases evaluated
  rename_i yields yieldsEval
  dsimp only at evaluated
  split at evaluated
  · cases evaluated
  rename_i calls callsEval
  cases evaluated
  exact ⟨outputsEval, rfl, rfl, equationsEval, queriesEval, returnsEval, yieldsEval, callsEval⟩

def Emission.prefix (equations : List Expr) (emission : Emission) : Emission :=
  { emission with equations := equations ++ emission.equations }

theorem Emission.prefix_eval {values : Values G} {emission : Emission} {result : AIR.BlockEmission}
    {equations : List Expr} {results : List G} (evaluated : emission.eval values = some result)
    (equationsEval : equations.mapM (evalExpr values) = some results) :
    (emission.prefix equations).eval values = some (result.prefix results) := by
  obtain ⟨outputs, column, lookup, oldEquations, queries, returns, yields, calls⟩ :=
    Emission.eval_components evaluated
  apply Emission.eval_of
  · exact outputs
  · exact column
  · exact lookup
  · simp only [Emission.prefix, List.mapM_append, equationsEval, oldEquations,
      bind, Option.bind_some, pure, AIR.BlockEmission.prefix]
  · exact queries
  · exact returns
  · exact yields
  · exact calls

def Emission.afterOps (incoming : Expr) (lookup : Nat) (ops : OpsEmission) (control : Emission) : Emission :=
  { control with
    equations := ops.equations ++ control.equations
    queries := LookupEmitter.queryParts lookup incoming ops.queries ++ control.queries
    calls := ops.calls.map (incoming, ·) ++ control.calls }

theorem Emission.afterOps_eval {values : Values G} {incoming : Expr} {s : G} (lookup : Nat)
    {ops : OpsEmission} {operations : AIR.OpsEmission} {control : Emission} {result : AIR.BlockEmission}
    (incomingEval : evalExpr values incoming = some s)
    (opsEval : ops.eval values = some operations) (controlEval : control.eval values = some result) :
    (control.afterOps incoming lookup ops).eval values = some (result.afterOps s lookup operations) := by
  obtain ⟨_, _, opEquations, opQueries, opCalls⟩ := OpsEmission.eval_components opsEval
  obtain ⟨outputs, column, lookupEq, equations, queries, returns, yields, calls⟩ :=
    Emission.eval_components controlEval
  have gatedCalls : (ops.calls.map (incoming, ·)).mapM (evalGatedCall values) =
      some (operations.calls.map (s, ·)) := by
    apply list_mapM_transform opCalls (incoming, ·) (s, ·) (evalGatedCall values)
    intro call result reflected
    simp only [evalGatedCall, incomingEval, reflected, bind, Option.bind_some, pure]
  apply Emission.eval_of
  · exact outputs
  · exact column
  · exact lookupEq
  · simp only [Emission.afterOps, List.mapM_append, opEquations, equations,
      bind, Option.bind_some, pure, AIR.BlockEmission.afterOps]
  · simp only [Emission.afterOps, List.mapM_append, LookupEmitter.queryParts_eval incomingEval opQueries,
      queries, bind, Option.bind_some, pure, AIR.BlockEmission.afterOps]
  · exact returns
  · exact yields
  · simp only [Emission.afterOps, List.mapM_append, gatedCalls, calls,
      bind, Option.bind_some, pure, AIR.BlockEmission.afterOps]

def join (values : Array RowExpr) (column lookup : Nat) (emissions : List Emission) : Emission :=
  { values
    column := emissions.foldl (fun column emission => max column emission.column) column
    lookup := emissions.foldl (fun lookup emission => max lookup emission.lookup) lookup
    equations := emissions.flatMap (·.equations)
    queries := emissions.flatMap (·.queries)
    returns := emissions.flatMap (·.returns)
    yields := emissions.flatMap (·.yields)
    calls := emissions.flatMap (·.calls) }

theorem join_eval {values : Values G} {rows : Array RowExpr} {inputs : Array AIR.RowValue}
    (inputEval : evalRows values rows = some inputs) (column lookup : Nat)
    {emissions : List Emission} {results : List AIR.BlockEmission}
    (evaluated : emissions.mapM (Emission.eval values) = some results) :
    (join rows column lookup emissions).eval values = some (AIR.joinBlockEmissions inputs column lookup results) := by
  apply Emission.eval_of
  · exact inputEval
  · apply list_mapM_foldl evaluated
    intro emission result reflected start
    rw [(Emission.eval_components reflected).2.1]
  · apply list_mapM_foldl evaluated
    intro emission result reflected start
    rw [(Emission.eval_components reflected).2.2.1]
  · exact list_mapM_flatMap evaluated Emission.equations AIR.BlockEmission.equations
      (evalExpr values) (fun _ _ reflected => (Emission.eval_components reflected).2.2.2.1)
  · exact list_mapM_flatMap evaluated Emission.queries AIR.BlockEmission.queries
      (QueryExpr.eval values) (fun _ _ reflected => (Emission.eval_components reflected).2.2.2.2.1)
  · exact list_mapM_flatMap evaluated Emission.returns AIR.BlockEmission.returns
      (ReturnExpr.eval values) (fun _ _ reflected => (Emission.eval_components reflected).2.2.2.2.2.1)
  · exact list_mapM_flatMap evaluated Emission.yields AIR.BlockEmission.yields
      (YieldExpr.eval values) (fun _ _ reflected => (Emission.eval_components reflected).2.2.2.2.2.2.1)
  · exact list_mapM_flatMap evaluated Emission.calls AIR.BlockEmission.calls
      (evalGatedCall values) (fun _ _ reflected => (Emission.eval_components reflected).2.2.2.2.2.2.2)

def Emission.continued (branches : Emission) (equations : List Expr) (continuation : Emission) : Emission :=
  { continuation with
    equations := branches.equations ++ equations ++ continuation.equations
    queries := branches.queries ++ continuation.queries
    returns := branches.returns ++ continuation.returns
    calls := branches.calls ++ continuation.calls }

theorem Emission.continued_eval {values : Values G}
    {branches continuation : Emission} {first last : AIR.BlockEmission}
    {equations : List Expr} {results : List G}
    (branchesEval : branches.eval values = some first)
    (continuationEval : continuation.eval values = some last)
    (equationsEval : equations.mapM (evalExpr values) = some results) :
    (branches.continued equations continuation).eval values = some (first.continued results last) := by
  obtain ⟨_, _, _, firstEquations, firstQueries, firstReturns, _, firstCalls⟩ :=
    Emission.eval_components branchesEval
  obtain ⟨outputs, column, lookup, lastEquations, lastQueries, lastReturns, yields, lastCalls⟩ :=
    Emission.eval_components continuationEval
  apply Emission.eval_of
  · exact outputs
  · exact column
  · exact lookup
  · simp only [Emission.continued, AIR.BlockEmission.continued, List.mapM_append,
      firstEquations, equationsEval, lastEquations, bind, Option.bind_some, pure]
  · simp only [Emission.continued, AIR.BlockEmission.continued, List.mapM_append,
      firstQueries, lastQueries, bind, Option.bind_some, pure]
  · simp only [Emission.continued, AIR.BlockEmission.continued, List.mapM_append,
      firstReturns, lastReturns, bind, Option.bind_some, pure]
  · exact yields
  · simp only [Emission.continued, AIR.BlockEmission.continued, List.mapM_append,
      firstCalls, lastCalls, bind, Option.bind_some, pure]

theorem YieldExpr.eval_of {values : Values G} {yielded : YieldExpr} {s : G} {outputs : Array AIR.RowValue}
    (selectorEval : evalExpr values yielded.selector = some s)
    (outputsEval : evalRows values yielded.values = some outputs) :
    yielded.eval values = some (s, outputs) := by
  simp only [YieldExpr.eval, selectorEval, outputsEval, bind, Option.bind_some, pure]

theorem YieldExpr.eval_components {values : Values G} {yielded : YieldExpr} {result : G × Array AIR.RowValue}
    (evaluated : yielded.eval values = some result) :
    evalExpr values yielded.selector = some result.1 ∧ evalRows values yielded.values = some result.2 := by
  simp only [YieldExpr.eval, bind, Option.bind] at evaluated
  split at evaluated
  · cases evaluated
  rename_i selector selectorEval
  dsimp only at evaluated
  split at evaluated
  · cases evaluated
  rename_i outputs outputsEval
  cases evaluated
  exact ⟨selectorEval, outputsEval⟩

theorem ReturnExpr.eval_of {values : Values G} {returned : ReturnExpr} {s r : G}
    {inputs outputs : Array G} (selectorEval : evalExpr values returned.selector = some s)
    (inputsEval : returned.inputs.mapM (evalExpr values) = some inputs)
    (outputsEval : returned.outputs.mapM (evalExpr values) = some outputs)
    (rankEval : evalExpr values returned.rank = some r) :
    returned.eval values = some (s, ⟨returned.function, inputs, outputs, r⟩) := by
  simp only [ReturnExpr.eval, selectorEval, inputsEval, outputsEval, rankEval, bind, Option.bind_some, pure]

theorem ReturnExpr.eval_components {values : Values G} {returned : ReturnExpr} {result : G × Bytecode.AIR.Call}
    (evaluated : returned.eval values = some result) :
    returned.function = result.2.function ∧ evalExpr values returned.selector = some result.1 ∧
    returned.inputs.mapM (evalExpr values) = some result.2.inputs ∧
    returned.outputs.mapM (evalExpr values) = some result.2.outputs ∧
    evalExpr values returned.rank = some result.2.rank := by
  simp only [ReturnExpr.eval, bind, Option.bind] at evaluated
  split at evaluated
  · cases evaluated
  rename_i selector selectorEval
  dsimp only at evaluated
  split at evaluated
  · cases evaluated
  rename_i inputs inputsEval
  dsimp only at evaluated
  split at evaluated
  · cases evaluated
  rename_i outputs outputsEval
  dsimp only at evaluated
  split at evaluated
  · cases evaluated
  rename_i rank rankEval
  cases evaluated
  exact ⟨rfl, selectorEval, inputsEval, outputsEval, rankEval⟩

theorem ReturnExpr.message_eval {values : Values G} {returned : ReturnExpr} {result : G × Bytecode.AIR.Call}
    (evaluated : returned.eval values = some result) :
    returned.message.mapM (evalExpr values) = some (AIR.functionMessage result.2) := by
  obtain ⟨function, _, inputsEval, outputsEval, rankEval⟩ := ReturnExpr.eval_components evaluated
  have inputs := congrArg (Functor.map Array.toList) inputsEval
  have outputs := congrArg (Functor.map Array.toList) outputsEval
  rw [Array.toList_mapM] at inputs outputs
  simp only [Functor.map, Option.map_some] at inputs outputs
  simp only [ReturnExpr.message, List.mapM_append, List.mapM_cons, List.mapM_nil,
    inputs, outputs, rankEval,
    show evalExpr values (.konst 0) = some 0 from rfl,
    show evalExpr values (.konst (G.ofNat result.2.function)) = some (G.ofNat result.2.function) from rfl,
    bind, Option.bind_some, pure, AIR.functionMessage, function,
    List.cons_append, List.nil_append, List.append_assoc]

def returned (context : Context) (incoming : Expr) (rows inputs outputs : Array RowExpr)
    (column lookup : Nat) : Emission :=
  { values := rows, column, lookup,
    returns := [⟨incoming, context.function, rowExprs inputs, rowExprs outputs, context.rank⟩] }

theorem returned_eval {values : Values G} {context : Context} {incoming : Expr} {s r : G}
    {rows inputs outputs : Array RowExpr} {a b c : Array AIR.RowValue} (column lookup : Nat)
    (incomingEval : evalExpr values incoming = some s) (rankEval : evalExpr values context.rank = some r)
    (rowsEval : evalRows values rows = some a) (inputsEval : evalRows values inputs = some b)
    (outputsEval : evalRows values outputs = some c) :
    (returned context incoming rows inputs outputs column lookup).eval values =
      some { values := a, column, lookup,
             returns := [(s, ⟨context.function, AIR.rowValues b, AIR.rowValues c, r⟩)] } := by
  have result := ReturnExpr.eval_of (returned :=
    ⟨incoming, context.function, rowExprs inputs, rowExprs outputs, context.rank⟩)
    incomingEval (evalRows_values inputsEval) (evalRows_values outputsEval) rankEval
  apply Emission.eval_of rowsEval rfl rfl rfl rfl ?_ rfl rfl
  simp only [returned, List.mapM_cons, List.mapM_nil, result, bind, Option.bind_some, pure]

def yielded (selector : Expr) (rows outputs : Array RowExpr) (column lookup : Nat) : Emission :=
  { values := rows, column, lookup, yields := [⟨selector, outputs⟩] }

theorem yielded_eval {values : Values G} {selector : Expr} {s : G}
    {rows outputs : Array RowExpr} {a b : Array AIR.RowValue} (column lookup : Nat)
    (selectorEval : evalExpr values selector = some s)
    (rowsEval : evalRows values rows = some a) (outputsEval : evalRows values outputs = some b) :
    (yielded selector rows outputs column lookup).eval values =
      some { values := a, column, lookup, yields := [(s, b)] } := by
  have result := YieldExpr.eval_of (yielded := ⟨selector, outputs⟩) selectorEval outputsEval
  apply Emission.eval_of rowsEval rfl rfl rfl rfl rfl ?_ rfl
  simp only [yielded, List.mapM_cons, List.mapM_nil, result, bind, Option.bind_some, pure]

theorem evalRows_getD_any {values : Values G} {rows : Array RowExpr} {results : Array AIR.RowValue}
    (evaluated : evalRows values rows = some results) (index : Nat) :
    (rows[index]?.getD (.konst 0)).Reflects values (results[index]?.getD (.konst 0)) := by
  by_cases bound : index < rows.size
  · exact evalRows_getD evaluated bound
  · have size := array_mapM_size evaluated
    have absent : rows[index]? = none := Array.getElem?_eq_none_iff.mpr (by omega)
    have resultAbsent : results[index]? = none := Array.getElem?_eq_none_iff.mpr (by omega)
    simp only [absent, resultAbsent, Option.getD_none]
    exact RowExpr.konst_reflects _ _

def yieldValue (yielded : YieldExpr) (index : Nat) : Expr :=
  yielded.selector.frontMul (yielded.values[index]?.getD (.konst 0)).expr

theorem yieldValue_eval {values : Values G} {yielded : YieldExpr} {result : G × Array AIR.RowValue}
    (evaluated : yielded.eval values = some result) (index : Nat) :
    evalExpr values (yieldValue yielded index) =
      some (result.1 * (AIR.rowValues result.2)[index]?.getD 0) := by
  obtain ⟨selectorEval, outputsEval⟩ := YieldExpr.eval_components evaluated
  rw [rowValues_getD]
  exact Expr.frontMul_eval goldilocksLaws values selectorEval (evalRows_getD_any outputsEval index).1

def yieldGate (yields : List YieldExpr) : Expr := sum (yields.map (·.selector))

theorem yieldGate_eval {values : Values G} {yields : List YieldExpr} {results : List (G × Array AIR.RowValue)}
    (evaluated : yields.mapM (YieldExpr.eval values) = some results) :
    evalExpr values (yieldGate yields) = some (AIR.selectorSum (results.map Prod.fst)) := by
  apply sum_eval
  exact list_mapM_transform evaluated YieldExpr.selector Prod.fst (evalExpr values)
    (fun _ _ reflected => (YieldExpr.eval_components reflected).1)

def mergeEquations (incoming : Expr) (column size : Nat) (yields : List YieldExpr) : List Expr :=
  (List.range size).map fun index => incoming.frontMul
    ((mainCurrent (column + index)).expr.frontSub (sum (yields.map (yieldValue · index))))

theorem mergeEquations_eval {values : Values G} (row : Nat → G) {incoming : Expr} {s : G}
    (column size : Nat) {yields : List YieldExpr} {results : List (G × Array AIR.RowValue)}
    (incomingEval : evalExpr values incoming = some s)
    (evaluated : yields.mapM (YieldExpr.eval values) = some results)
    (reads : ∀ index < size, (values.columns .main .current)[column + index]? = some (row (column + index))) :
    (mergeEquations incoming column size yields).mapM (evalExpr values) =
      some (AIR.mergeEquations row s column size results) := by
  apply list_mapM_of_map
  intro index member
  have sumValues := list_mapM_transform evaluated (yieldValue · index)
    (fun result => result.1 * (AIR.rowValues result.2)[index]?.getD 0) (evalExpr values)
    (fun _ _ reflected => yieldValue_eval reflected index)
  have merged : evalExpr values (mainCurrent (column + index)).expr = some (row (column + index)) :=
    reads index (List.mem_range.mp member)
  exact Expr.frontMul_eval goldilocksLaws values incomingEval
    (Expr.frontSub_eval goldilocksLaws values merged (sum_eval sumValues))

theorem yields_size {values : Values G} {yields : List YieldExpr} {results : List (G × Array AIR.RowValue)}
    (evaluated : yields.mapM (YieldExpr.eval values) = some results) (size : Nat) :
    yields.all (fun part => part.values.size == size) = results.all (fun part => part.2.size == size) := by
  have related := AIR.mapM_forall₂ evaluated (fun _ _ _ reflected =>
    (array_mapM_size (YieldExpr.eval_components reflected).2).symm)
  clear evaluated
  induction related with
  | nil => rfl
  | cons head _ ih => simp only [List.all_cons, head, ih]

def caseEquation (entry : Expr) (matched : RowExpr) (value : G) : Expr :=
  entry.frontMul (matched.expr.frontSub (.konst value))

theorem caseEquation_eval {values : Values G} {entry : Expr} {s : G} {matched : RowExpr} {value : AIR.RowValue}
    (entryEval : evalExpr values entry = some s) (matchedRef : matched.Reflects values value) (branch : G) :
    evalExpr values (caseEquation entry matched branch) = some (s * (value.value - branch)) :=
  Expr.frontMul_eval goldilocksLaws values entryEval
    (Expr.frontSub_eval goldilocksLaws values matchedRef.1 rfl)

def defaultEquations (entry : Expr) (matched : RowExpr) (column : Nat)
    (branches : Array (G × Bytecode.Block)) : List Expr :=
  branches.toList.mapIdx fun index pair => entry.frontMul
    (((matched.expr.frontSub (.konst pair.1)).frontMul (mainCurrent (column + index)).expr).frontSub (.konst 1))

theorem defaultEquations_eval {values : Values G} (row : Nat → G)
    {entry : Expr} {s : G} {matched : RowExpr} {value : AIR.RowValue}
    (column : Nat) (branches : Array (G × Bytecode.Block))
    (entryEval : evalExpr values entry = some s) (matchedRef : matched.Reflects values value)
    (reads : ∀ index < branches.size,
      (values.columns .main .current)[column + index]? = some (row (column + index))) :
    (defaultEquations entry matched column branches).mapM (evalExpr values) =
      some (branches.toList.mapIdx fun index pair => s * ((value.value - pair.1) * row (column + index) - 1)) := by
  simp only [defaultEquations, List.mapIdx_eq_zipIdx_map]
  apply list_mapM_of_map
  intro pair member
  have present := List.mk_mem_zipIdx_iff_getElem?.mp member
  have bound : pair.2 < branches.size := by
    have original := (List.getElem?_eq_some_iff.mp present).choose
    simpa only [Array.length_toList] using original
  have inverse : evalExpr values (mainCurrent (column + pair.2)).expr = some (row (column + pair.2)) :=
    reads pair.2 bound
  exact Expr.frontMul_eval goldilocksLaws values entryEval
    (Expr.frontSub_eval goldilocksLaws values
      (Expr.frontMul_eval goldilocksLaws values
        (Expr.frontSub_eval goldilocksLaws values matchedRef.1 rfl) inverse) rfl)

private theorem block_smaller (block : Bytecode.Block) : sizeOf block.ctrl < sizeOf block := by
  cases block
  simp
  omega

mutual

def emitCtrl (selectors : Array Expr) (context : Context) (incoming : Expr)
    (rows : Array RowExpr) (column lookup : Nat) : Bytecode.Ctrl → Option Emission
  | .return _ indices => do
    let inputs ← select rows (Array.range context.inputSize)
    let outputs ← select rows indices
    return returned context incoming rows inputs outputs column lookup
  | .yield index indices => do
    let selector ← selectors[index]?
    let outputs ← select rows indices
    return yielded selector rows outputs column lookup
  | .match index branches fallback => do
    let matched ← rows[index]?
    let cases ← branches.attach.toList.mapM fun ⟨pair, _⟩ => do
      let entry ← blockSelector selectors pair.2
      let emission ← emitBlock selectors context entry rows column lookup pair.2
      return emission.prefix [caseEquation entry matched pair.1]
    let default : List Emission ← match fallback with
      | none => some []
      | some block => do
        let entry ← blockSelector selectors block
        let emission ← emitBlock selectors context entry rows (column + branches.size) lookup block
        pure [emission.prefix (defaultEquations entry matched column branches)]
    return join rows column lookup (cases ++ default)
  | .matchContinue index branches fallback size _ _ continuation => do
    let matched ← rows[index]?
    let cases ← branches.attach.toList.mapM fun ⟨pair, _⟩ => do
      let entry ← blockSelector selectors pair.2
      let emission ← emitBlock selectors context entry rows column lookup pair.2
      return emission.prefix [caseEquation entry matched pair.1]
    let default : List Emission ← match fallback with
      | none => some []
      | some block => do
        let entry ← blockSelector selectors block
        let emission ← emitBlock selectors context entry rows (column + branches.size) lookup block
        pure [emission.prefix (defaultEquations entry matched column branches)]
    let joined := join rows column lookup (cases ++ default)
    if joined.yields.all (fun part => part.values.size == size) then do
      let gate := yieldGate joined.yields
      let entry ← blockSelector selectors continuation
      let equations := mergeEquations incoming joined.column size joined.yields ++ [entry.frontSub gate]
      let continued ← emitBlock selectors context gate (rows ++ advice joined.column size)
        (joined.column + size) joined.lookup continuation
      return joined.continued equations continued
    else none
termination_by ctrl => sizeOf ctrl
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

def emitBlock (selectors : Array Expr) (context : Context) (incoming : Expr)
    (rows : Array RowExpr) (column lookup : Nat) (block : Bytecode.Block) : Option Emission := do
  let entry ← blockSelector selectors block
  let operations ← OpEmitter.emitOps incoming context.rank block.ops.toList rows column
  let control ← emitCtrl selectors context incoming operations.values operations.column
    (lookup + operations.queries.length) block.ctrl
  return (control.afterOps incoming lookup operations).prefix
    [entry.frontMul ((Expr.konst 1).frontSub entry)]
termination_by sizeOf block
decreasing_by exact block_smaller block

end

theorem fold_max_start (measure : α → Nat) (items : List α) (start : Nat) :
    start ≤ items.foldl (fun current item => max current (measure item)) start := by
  induction items generalizing start with
  | nil => exact Nat.le_refl _
  | cons item items ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem fold_max_member (measure : α → Nat) {items : List α} {item : α}
    (member : item ∈ items) (start : Nat) :
    measure item ≤ items.foldl (fun current item => max current (measure item)) start := by
  induction items generalizing start with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with equal | tail
    · subst item
      exact Nat.le_trans (Nat.le_max_right _ _) (fold_max_start measure rest _)
    · exact ih tail _

def caseRow (selectors : Array Expr) (context : Context) (matched : RowExpr)
    (rows : Array RowExpr) (column lookup : Nat) (pair : G × Bytecode.Block) : Option Emission := do
  let entry ← blockSelector selectors pair.2
  let emission ← emitBlock selectors context entry rows column lookup pair.2
  return emission.prefix [caseEquation entry matched pair.1]

def defaultRow (selectors : Array Expr) (context : Context) (matched : RowExpr)
    (rows : Array RowExpr) (column lookup : Nat) (branches : Array (G × Bytecode.Block))
    (fallback : Option Bytecode.Block) : Option (List Emission) :=
  match fallback with
  | none => some []
  | some block => do
    let entry ← blockSelector selectors block
    let emission ← emitBlock selectors context entry rows (column + branches.size) lookup block
    return [emission.prefix (defaultEquations entry matched column branches)]

def branchRows (selectors : Array Expr) (context : Context) (matched : RowExpr)
    (rows : Array RowExpr) (column lookup : Nat) (branches : Array (G × Bytecode.Block))
    (fallback : Option Bytecode.Block) : Option Emission := do
  let cases ← branches.toList.mapM (caseRow selectors context matched rows column lookup)
  let default ← defaultRow selectors context matched rows column lookup branches fallback
  return join rows column lookup (cases ++ default)

def continueRow (selectors : Array Expr) (context : Context) (incoming : Expr)
    (rows : Array RowExpr) (size : Nat) (continuation : Bytecode.Block) (joined : Emission) : Option Emission :=
  if joined.yields.all (fun part => part.values.size == size) then do
    let gate := yieldGate joined.yields
    let entry ← blockSelector selectors continuation
    let equations := mergeEquations incoming joined.column size joined.yields ++ [entry.frontSub gate]
    let continued ← emitBlock selectors context gate (rows ++ advice joined.column size)
      (joined.column + size) joined.lookup continuation
    return joined.continued equations continued
  else none

theorem emitCtrl_match (selectors : Array Expr) (context : Context) (incoming : Expr)
    (rows : Array RowExpr) (column lookup index : Nat) (branches : Array (G × Bytecode.Block))
    (fallback : Option Bytecode.Block) :
    emitCtrl selectors context incoming rows column lookup (.match index branches fallback) = (do
      let matched ← rows[index]?
      branchRows selectors context matched rows column lookup branches fallback) := by
  rw [emitCtrl.eq_def]
  simp only [branchRows, Array.toList_attach]
  cases rows[index]? with
  | none => simp only [bind, Option.bind_none]
  | some matched =>
    simp only [bind, Option.bind_some]
    rw [AIR.attachWith_mapM_val _ _ _ (fun pair : G × Bytecode.Block =>
      (blockSelector selectors pair.2).bind fun entry =>
        (emitBlock selectors context entry rows column lookup pair.2).bind fun emission =>
          pure (emission.prefix [caseEquation entry matched pair.1]))]
    change (branches.toList.mapM (caseRow selectors context matched rows column lookup)).bind _ = _
    congr 1
    funext cases
    cases fallback <;> simp only [defaultRow, bind, Option.bind_assoc, Option.bind_some]

theorem emitCtrl_matchContinue (selectors : Array Expr) (context : Context) (incoming : Expr)
    (rows : Array RowExpr) (column lookup index : Nat) (branches : Array (G × Bytecode.Block))
    (fallback : Option Bytecode.Block) (size aux slots : Nat) (continuation : Bytecode.Block) :
    emitCtrl selectors context incoming rows column lookup (.matchContinue index branches fallback size aux slots continuation) = (do
      let matched ← rows[index]?
      let joined ← branchRows selectors context matched rows column lookup branches fallback
      continueRow selectors context incoming rows size continuation joined) := by
  rw [emitCtrl.eq_def]
  simp only [branchRows, Array.toList_attach]
  cases rows[index]? with
  | none => simp only [bind, Option.bind_none]
  | some matched =>
    simp only [bind, Option.bind_some]
    rw [AIR.attachWith_mapM_val _ _ _ (fun pair : G × Bytecode.Block =>
      (blockSelector selectors pair.2).bind fun entry =>
        (emitBlock selectors context entry rows column lookup pair.2).bind fun emission =>
          pure (emission.prefix [caseEquation entry matched pair.1]))]
    simp only [Option.bind_assoc]
    change (branches.toList.mapM (caseRow selectors context matched rows column lookup)).bind _ = _
    congr 1
    funext cases
    cases fallback <;> simp only [defaultRow, continueRow, bind, pure, Option.bind_assoc, Option.bind_some]

theorem branchRows_invariants {selectors : Array Expr} {context : Context} {matched : RowExpr}
    {rows : Array RowExpr} {column lookup : Nat} {branches : Array (G × Bytecode.Block)}
    {fallback : Option Bytecode.Block} {emission : Emission} (normal : Normal rows)
    (emitted : branchRows selectors context matched rows column lookup branches fallback = some emission) :
    Normal emission.values ∧ column ≤ emission.column := by
  simp only [branchRows, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  dsimp only at emitted
  split at emitted
  · cases emitted
  cases emitted
  exact ⟨normal, fold_max_start Emission.column _ column⟩

mutual

theorem emitCtrl_invariants {selectors : Array Expr} {context : Context} {incoming : Expr}
    {rows : Array RowExpr} {column lookup : Nat} (ctrl : Bytecode.Ctrl) {emission : Emission}
    (normal : Normal rows) (emitted : emitCtrl selectors context incoming rows column lookup ctrl = some emission) :
    Normal emission.values ∧ column ≤ emission.column := by
  cases ctrl with
  | «return» index indices | yield index indices =>
    simp only [emitCtrl, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    cases emitted
    exact ⟨normal, Nat.le_refl _⟩
  | «match» index branches fallback =>
    rw [emitCtrl_match] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    dsimp only at emitted
    exact branchRows_invariants normal emitted
  | matchContinue index branches fallback size aux lookups continuation =>
    rw [emitCtrl_matchContinue] at emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i joined joinedEmitted
    have joinedBounds := branchRows_invariants normal joinedEmitted
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
      have result := emitBlock_invariants continuation
        (normal.append (advice_normal _ _)) continuedEmitted
      exact ⟨result.1, Nat.le_trans joinedBounds.2 (Nat.le_trans (Nat.le_add_right _ _) result.2)⟩
    · cases emitted
termination_by sizeOf ctrl
decreasing_by all_goals decreasing_tactic

theorem emitBlock_invariants {selectors : Array Expr} {context : Context} {incoming : Expr}
    {rows : Array RowExpr} {column lookup : Nat} (block : Bytecode.Block) {emission : Emission}
    (normal : Normal rows) (emitted : emitBlock selectors context incoming rows column lookup block = some emission) :
    Normal emission.values ∧ column ≤ emission.column := by
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
  have result := emitCtrl_invariants block.ctrl (emitOps_normal normal operationsEmitted) controlEmitted
  exact ⟨result.1, Nat.le_trans (emitOps_column operationsEmitted) result.2⟩
termination_by sizeOf block
decreasing_by exact block_smaller block

end

end Aiur.NativeAIR.BlockEmitter
