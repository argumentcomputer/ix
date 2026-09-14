/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.LocalStateEffects
import Lean.LabelAttribute

/-!
# Proof search for structural local-state effects

The tactic composes proved frame rules, unfolds finite monadic control flow,
and applies named helper lemmas or local induction premises. It only introduces
explicit quantifiers; it never unfolds a frame into an unconstrained outcome.
All generated proof terms are checked by Lean. Recursive source workers still
need induction, and recursive method calls need the smaller table's frame.
-/

namespace Ix.Kernel.Consistency

register_label_attr local_state_frame

private def frameHead : Lean.Expr → Option Lean.Name
  | .forallE _ _ body _ => frameHead body
  | .mdata _ body => frameHead body
  | type => do
      if !type.getAppFn.isConstOf ``FramesLocalState then none else do
        let action ← type.getAppArgs.back?
        let action ← if action.getAppFn.isConstOf ``ReaderT.run then
          action.getAppArgs[action.getAppArgs.size - 2]?
        else some action
        match action.getAppFn with
        | .const name _ => some name
        | .fvar id => some id.name
        | _ => none

open Lean Elab Tactic in
elab "local_frame_goal" : tactic => do
  unless (← Lean.instantiateMVars (← getMainTarget)).consumeMData.getAppFn.isConstOf ``FramesLocalState do
    throwError "expected a local-state computation frame"

open Lean Elab Tactic in
elab "local_relation_goal" : tactic => do
  unless (← Lean.instantiateMVars (← getMainTarget)).consumeMData.getAppFn.isConstOf ``LocalStateFrame do
    throwError "expected a relation between checker states"

open Lean Elab Tactic in
elab "local_frame_head " head:ident : tactic => do
  unless frameHead (← Lean.instantiateMVars (← getMainTarget)) == some head.getId.eraseMacroScopes do
    throwError "different computation head"

open Lean Elab Tactic in
elab "local_frame_intro" : tactic => do
  unless (← Lean.instantiateMVars (← getMainTarget)).consumeMData.isForall do
    throwError "expected an explicit universal quantifier"
  evalTactic (← `(tactic| intro))

open Lean Elab Tactic Meta in
elab "local_frame_assumption" : tactic => withMainContext do
  let goal ← getMainGoal
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      let saved ← saveState
      try
        if (← withReducible (goal.apply decl.toExpr)).isEmpty then
          replaceMainGoal []
          return
      catch _ => pure ()
      saved.restore
  throwError "no local premise closes this frame"

open Lean Elab Tactic Meta in
elab "local_frame_lemma" : tactic => withMainContext do
  let goal ← getMainGoal
  let some head := frameHead (← Lean.instantiateMVars (← goal.getType)) |
    throwError "expected a named computation"
  for name in (← labelled `local_state_frame).reverse do
    if frameHead (← getConstInfo name).type != some head then continue
    let saved ← saveState
    try
      let goals ← withReducible (goal.apply (← mkConstWithFreshMVarLevels name))
      for subgoal in goals do
        subgoal.withContext subgoal.assumption
      replaceMainGoal []
      return
    catch _ => saved.restore
  throwError "no registered lemma closes this frame"

macro "local_state" : tactic => `(tactic|
  with_reducible repeat' first
    | assumption
    | local_frame_assumption
    | (local_relation_goal; exact ⟨Nat.le_refl _, .refl _, rfl⟩)
    | local_frame_intro
    | (local_frame_goal; first
    | local_frame_lemma
    | apply FramesLocalState.bindRead
    | exact FramesLocalState.pureRec _
    | exact FramesLocalState.throwRec _
    | exact FramesLocalState.throwExceptRec _
    | exact FramesLocalState.getRec
    | (local_frame_head MonadLiftT.monadLift; apply FramesLocalState.liftRec)
    | (local_frame_head MonadLiftT.monadLift; apply FramesLocalState.liftSelf)
    | (with_reducible apply FramesLocalState.bindRec)
    | (with_reducible apply FramesLocalState.bind)
    | (local_frame_head Pure.pure; exact FramesLocalState.pure _)
    | (local_frame_head MonadExceptOf.throw; exact FramesLocalState.throw _)
    | exact FramesLocalState.intern _
    | exact FramesLocalState.runIntern _
    | exact FramesLocalState.get
    | exact FramesLocalState.instantiateUnivParams _ _
    | exact FramesLocalState.prims _
    | exact FramesLocalState.tryGetConst _
    | exact FramesLocalState.getConst _
    | exact FramesLocalState.tryGetBlock _
    | exact FramesLocalState.inferKey _
    | exact FramesLocalState.whnfKey _
    | exact FramesLocalState.tick
    | exact FramesLocalState.isLetVar _
    | exact FramesLocalState.lookupLetVal _
    | exact FramesLocalState.stepTrace _ _
    | exact FramesLocalState.whnfRec (by assumption) _
    | exact FramesLocalState.whnfModeRec (by assumption) _ _
    | exact FramesLocalState.whnfCoreFlagsRec (by assumption) _ _
    | exact FramesLocalState.inferOnlyRec (by assumption) _
    | exact MethodsLocalState.infer (by assumption) _
    | apply FramesLocalState.modifyRec
    | apply FramesLocalState.modify
    | apply FramesLocalState.bumpStats
    | apply FramesLocalState.bindRec
    | apply FramesLocalState.bind
    | apply FramesLocalState.map
    | apply FramesLocalState.mapRec
    | apply FramesLocalState.forInList
    | apply FramesLocalState.forInRange
    | apply FramesLocalState.forInArray
    | apply FramesLocalState.forInListTcM
    | apply FramesLocalState.tryFinallyRec
    | apply FramesLocalState.tryCatchRec
    | apply FramesLocalState.tryCatchExceptRec
    | apply FramesLocalState.tryFinally
    | apply FramesLocalState.tryCatch
    | apply FramesLocalState.runBounded
    | apply FramesLocalState.withCheapRecursionDepth
    | apply FramesLocalState.withInferOnly
    | apply FramesLocalState.tryOptional
    | apply FramesLocalState.tryProbe
    | split
    | dsimp only
    | dsimp only [ReaderT.run_bind, ReaderT.run_monadLift]))

end Ix.Kernel.Consistency
