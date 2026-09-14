/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.BlockReflection

/-! Returns contribute arguments to the provider slot without adding weight.
Consumer slots retain both multiplicities and gated argument accumulation. -/

namespace Aiur.NativeAIR.BlockEmitter
open OpEmitter LookupEmitter Compiler

def returnArgs (branchless : Bool) (returns : List ReturnExpr) : List Expr :=
  returns.foldl (fun args returned => addArgs args (gateArgs branchless returned.selector returned.message)) []

theorem returnArgs_fold_eval (branchless : Bool) {values : Values G}
    {returns : List ReturnExpr} {results : List (G × Bytecode.AIR.Call)}
    (evaluated : returns.mapM (ReturnExpr.eval values) = some results)
    {initial : List Expr} {start : List G}
    (initialEval : initial.mapM (evalExpr values) = some start) :
    (returns.foldl (fun args returned => addArgs args (gateArgs branchless returned.selector returned.message)) initial).mapM
      (evalExpr values) = some (results.foldl (fun args part =>
        AIR.addMessages args (AIR.gateMessage branchless part.1 (AIR.functionMessage part.2))) start) := by
  induction returns generalizing results initial start with
  | nil =>
    cases evaluated
    exact initialEval
  | cons returned rest ih =>
    simp only [List.mapM_cons, bind, Option.bind] at evaluated
    split at evaluated
    · cases evaluated
    rename_i result resultEval
    dsimp only at evaluated
    split at evaluated
    · cases evaluated
    rename_i tail tailEval
    cases evaluated
    exact ih tailEval (addArgs_eval initialEval (gateArgs_eval branchless
      (ReturnExpr.eval_components resultEval).2.1 (ReturnExpr.message_eval resultEval)))

theorem returnArgs_eval (branchless : Bool) {values : Values G}
    {returns : List ReturnExpr} {results : List (G × Bytecode.AIR.Call)}
    (evaluated : returns.mapM (ReturnExpr.eval values) = some results) :
    (returnArgs branchless returns).mapM (evalExpr values) = some
      (AIR.slotMessage branchless (results.map fun part => (part.1, AIR.functionMessage part.2))) := by
  simpa only [returnArgs, AIR.slotMessage, List.foldl_map] using
    returnArgs_fold_eval branchless evaluated (show [].mapM (evalExpr values) = some [] from rfl)

def lookup (branchless : Bool) (emission : Emission) (slot : Nat) : ExprLookup :=
  if slot = 0 then ⟨.konst 0, returnArgs branchless emission.returns⟩
  else LookupEmitter.slot branchless emission.queries slot

theorem lookup_eval (branchless : Bool) {values : Values G} {emission : Emission} {result : AIR.BlockEmission}
    (evaluated : emission.eval values = some result) (slot : Nat) :
    (lookup branchless emission slot).eval goldilocksOps values = some
      (if slot = 0 then (0, AIR.slotMessage branchless (result.returns.map fun part => (part.1, AIR.functionMessage part.2)))
       else (AIR.querySlotMultiplicity result.queries slot,
         AIR.slotMessage branchless (AIR.querySlotParts result.queries slot))) := by
  obtain ⟨_, _, _, _, queries, returns, _, _⟩ := Emission.eval_components evaluated
  by_cases zero : slot = 0
  · simp only [lookup, zero, if_true]
    change ((returnArgs branchless emission.returns).mapM (evalExpr values)).bind
      (fun args => some (0, args)) = _
    rw [returnArgs_eval branchless returns]
    rfl
  · simpa only [lookup, zero, if_false] using LookupEmitter.slot_eval branchless queries slot

end Aiur.NativeAIR.BlockEmitter
