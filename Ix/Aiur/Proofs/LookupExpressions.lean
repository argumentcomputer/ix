/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.OperationSequences
import Ix.Aiur.Proofs.GraphCompilation
import Ix.Aiur.Proofs.QuerySlotMessages

/-!
Native lookup argument gating and accumulation, retaining exact frontend
expression trees. A slot's evaluation is the existing valued multiplicity
and combined message, including unequal message widths and repeated writers.
The resulting expression lookups feed the checked base-graph compiler.
-/

namespace Aiur.NativeAIR
namespace LookupEmitter
open OpEmitter Compiler

def addArgs : List Expr → List Expr → List Expr
  | [], right => right
  | left, [] => left
  | x :: left, y :: right => x.frontAdd y :: addArgs left right

def gateArgs (branchless : Bool) (selector : Expr) (args : List Expr) : List Expr :=
  if branchless then args else args.map selector.frontMul

theorem addArgs_eval {values : Values G} {left right : List Expr} {a b : List G}
    (leftEval : left.mapM (evalExpr values) = some a)
    (rightEval : right.mapM (evalExpr values) = some b) :
    (addArgs left right).mapM (evalExpr values) = some (AIR.addMessages a b) := by
  induction left generalizing right a b with
  | nil =>
    cases leftEval
    exact rightEval
  | cons x left ih =>
    cases right with
    | nil =>
      cases rightEval
      have empty : AIR.addMessages a [] = a := by cases a <;> rfl
      simpa only [addArgs, List.reverse_nil, empty] using leftEval
    | cons y right =>
      simp only [List.mapM_cons, bind, Option.bind] at leftEval rightEval
      split at leftEval
      · cases leftEval
      rename_i xValue xEval
      dsimp only at leftEval
      split at leftEval
      · cases leftEval
      rename_i leftValues leftValuesEval
      cases leftEval
      split at rightEval
      · cases rightEval
      rename_i yValue yEval
      dsimp only at rightEval
      split at rightEval
      · cases rightEval
      rename_i rightValues rightValuesEval
      cases rightEval
      simp only [addArgs, AIR.addMessages, List.mapM_cons,
        Expr.frontAdd_eval goldilocksLaws values xEval yEval,
        ih leftValuesEval rightValuesEval, bind, Option.bind_some, pure, goldilocks_add]

theorem gateArgs_eval (branchless : Bool) {values : Values G} {selector : Expr} {s : G}
    {args : List Expr} {results : List G} (selectorEval : evalExpr values selector = some s)
    (argsEval : args.mapM (evalExpr values) = some results) :
    (gateArgs branchless selector args).mapM (evalExpr values) =
      some (AIR.gateMessage branchless s results) := by
  cases branchless with
  | true => exact argsEval
  | false =>
    exact list_mapM_transform argsEval selector.frontMul (s * ·) (evalExpr values)
      (fun _ _ evaluated => Expr.frontMul_eval goldilocksLaws values selectorEval evaluated)

structure QueryExpr where
  slot : Nat
  selector : Expr
  message : List Expr

def QueryExpr.eval (values : Values G) (query : QueryExpr) : Option AIR.QueryPart := do
  let selector ← evalExpr values query.selector
  let message ← query.message.mapM (evalExpr values)
  return ⟨query.slot, selector, message⟩

theorem QueryExpr.eval_components {values : Values G} {query : QueryExpr} {result : AIR.QueryPart}
    (evaluated : query.eval values = some result) :
    query.slot = result.slot ∧ evalExpr values query.selector = some result.selector ∧
      query.message.mapM (evalExpr values) = some result.message := by
  simp only [QueryExpr.eval, bind, Option.bind] at evaluated
  split at evaluated
  · cases evaluated
  rename_i selector selectorEval
  dsimp only at evaluated
  split at evaluated
  · cases evaluated
  rename_i message messageEval
  cases evaluated
  exact ⟨rfl, selectorEval, messageEval⟩

def queryParts (slot : Nat) (selector : Expr) (queries : List (List Expr)) : List QueryExpr :=
  queries.mapIdx fun index message => ⟨slot + index, selector, message⟩

theorem queryParts_cons (slot : Nat) (selector : Expr) (message : List Expr) (queries : List (List Expr)) :
    queryParts slot selector (message :: queries) =
      ⟨slot, selector, message⟩ :: queryParts (slot + 1) selector queries := by
  simp [queryParts, List.mapIdx_cons, Nat.add_comm, Nat.add_left_comm]

theorem queryParts_eval {values : Values G} {selector : Expr} {s : G}
    {queries : List (List Expr)} {messages : List (List G)}
    (selectorEval : evalExpr values selector = some s)
    (evaluated : queries.mapM (List.mapM (evalExpr values)) = some messages) (slot : Nat) :
    (queryParts slot selector queries).mapM (QueryExpr.eval values) =
      some (AIR.queryParts slot s messages) := by
  induction queries generalizing messages slot with
  | nil =>
    cases evaluated
    rfl
  | cons query queries ih =>
    simp only [List.mapM_cons, bind, Option.bind] at evaluated
    split at evaluated
    · cases evaluated
    rename_i message messageEval
    dsimp only at evaluated
    split at evaluated
    · cases evaluated
    rename_i rest restEval
    cases evaluated
    rw [queryParts_cons, AIR.queryParts_cons]
    have head : (QueryExpr.mk slot selector query).eval values = some ⟨slot, s, message⟩ := by
      simp only [QueryExpr.eval, selectorEval, messageEval, bind, Option.bind_some, pure]
    simp only [List.mapM_cons, head, ih restEval, bind, Option.bind_some, pure]

def accumulate (branchless : Bool) (lookup : ExprLookup) (query : QueryExpr) : ExprLookup :=
  ⟨lookup.multiplicity.frontAdd query.selector,
    addArgs lookup.args (gateArgs branchless query.selector query.message)⟩

theorem accumulate_eval (branchless : Bool) {values : Values G}
    {lookup : ExprLookup} {query : QueryExpr} {initial : G × List G} {part : AIR.QueryPart}
    (initialEval : lookup.eval goldilocksOps values = some initial)
    (queryEval : query.eval values = some part) :
    (accumulate branchless lookup query).eval goldilocksOps values =
      some (initial.1 + part.selector,
        AIR.addMessages initial.2 (AIR.gateMessage branchless part.selector part.message)) := by
  obtain ⟨_, selectorEval, messageEval⟩ := QueryExpr.eval_components queryEval
  simp only [ExprLookup.eval, bind, Option.bind] at initialEval
  split at initialEval
  · cases initialEval
  rename_i multiplicity multiplicityEval
  dsimp only at initialEval
  split at initialEval
  · cases initialEval
  rename_i args argsEval
  cases initialEval
  have weight := Expr.frontAdd_eval goldilocksLaws values multiplicityEval selectorEval
  have message := addArgs_eval argsEval (gateArgs_eval branchless selectorEval messageEval)
  simp only [accumulate, ExprLookup.eval, weight, show evalExprs goldilocksOps values
    (addArgs lookup.args (gateArgs branchless query.selector query.message)) =
      some (AIR.addMessages args (AIR.gateMessage branchless part.selector part.message)) from message,
    bind, Option.bind_some, pure, goldilocks_add]

def valuedAccumulate (branchless : Bool) (lookup : G × List G) (query : AIR.QueryPart) : G × List G :=
  (lookup.1 + query.selector, AIR.addMessages lookup.2 (AIR.gateMessage branchless query.selector query.message))

theorem fold_eval (branchless : Bool) {values : Values G}
    {queries : List QueryExpr} {parts : List AIR.QueryPart}
    (evaluated : queries.mapM (QueryExpr.eval values) = some parts)
    {initial : ExprLookup} {start : G × List G} (initialEval : initial.eval goldilocksOps values = some start) :
    (queries.foldl (accumulate branchless) initial).eval goldilocksOps values =
      some (parts.foldl (valuedAccumulate branchless) start) := by
  induction queries generalizing parts initial start with
  | nil =>
    cases evaluated
    exact initialEval
  | cons query queries ih =>
    simp only [List.mapM_cons, bind, Option.bind] at evaluated
    split at evaluated
    · cases evaluated
    rename_i part partEval
    dsimp only at evaluated
    split at evaluated
    · cases evaluated
    rename_i rest restEval
    cases evaluated
    exact ih restEval (accumulate_eval branchless initialEval partEval)

theorem filter_eval {values : Values G} {queries : List QueryExpr} {parts : List AIR.QueryPart}
    (evaluated : queries.mapM (QueryExpr.eval values) = some parts) (slot : Nat) :
    (queries.filter (fun query => query.slot == slot)).mapM (QueryExpr.eval values) =
      some (parts.filter fun query => query.slot == slot) := by
  induction queries generalizing parts with
  | nil =>
    cases evaluated
    rfl
  | cons query queries ih =>
    simp only [List.mapM_cons, bind, Option.bind] at evaluated
    split at evaluated
    · cases evaluated
    rename_i part partEval
    dsimp only at evaluated
    split at evaluated
    · cases evaluated
    rename_i rest restEval
    cases evaluated
    have same := (QueryExpr.eval_components partEval).1
    simp only [List.filter_cons, same]
    split
    · simp only [List.mapM_cons, partEval, ih restEval, bind, Option.bind_some, pure]
    · exact ih restEval

theorem valuedFold_eq (branchless : Bool) (parts : List AIR.QueryPart) (start : G × List G) :
    parts.foldl (valuedAccumulate branchless) start =
      ((parts.map AIR.QueryPart.selector).foldl (· + ·) start.1,
        (parts.map fun part => (part.selector, part.message)).foldl
          (fun args part => AIR.addMessages args (AIR.gateMessage branchless part.1 part.2)) start.2) := by
  induction parts generalizing start with
  | nil => rfl
  | cons part parts ih => exact ih _

def slot (branchless : Bool) (queries : List QueryExpr) (index : Nat) : ExprLookup :=
  (queries.filter fun query => query.slot == index).foldl (accumulate branchless) ⟨.konst 0, []⟩

theorem slot_eval (branchless : Bool) {values : Values G}
    {queries : List QueryExpr} {parts : List AIR.QueryPart}
    (evaluated : queries.mapM (QueryExpr.eval values) = some parts) (index : Nat) :
    (slot branchless queries index).eval goldilocksOps values =
      some (AIR.querySlotMultiplicity parts index,
        AIR.slotMessage branchless (AIR.querySlotParts parts index)) := by
  have result := fold_eval branchless (filter_eval evaluated index)
    (show (ExprLookup.mk (.konst 0) []).eval goldilocksOps values = some (0, []) from rfl)
  rw [valuedFold_eq] at result
  simpa only [slot, AIR.querySlotMultiplicity, AIR.querySlotParts, AIR.selectorSum,
    AIR.slotMessage, List.map_map, Function.comp_def] using result

def slots (branchless : Bool) (queries : List QueryExpr) (count : Nat) : List ExprLookup :=
  List.ofFn fun index : Fin count => slot branchless queries index.val

theorem slots_eval (branchless : Bool) {values : Values G}
    {queries : List QueryExpr} {parts : List AIR.QueryPart}
    (evaluated : queries.mapM (QueryExpr.eval values) = some parts) (count : Nat) :
    (slots branchless queries count).mapM (ExprLookup.eval goldilocksOps values) =
      some (List.ofFn fun index : Fin count =>
        (AIR.querySlotMultiplicity parts index.val,
          AIR.slotMessage branchless (AIR.querySlotParts parts index.val))) := by
  exact list_mapM_ofFn _ _ _ (fun index => slot_eval branchless evaluated index.val)

end LookupEmitter
end Aiur.NativeAIR
