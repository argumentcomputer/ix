/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.LocalSubstitution
import Ix.Kernel.Verify.Consistency.InferenceCache
import Ix.Kernel.Knot

/-!
# The production let-inference path

Successful execution produces the complete trace in either validation mode,
including reduction-dependent sort exposure and conversion. Opening and
closing preserve the source and inferred-type readings before the final
cheap-beta pass. The value and body typing premises are the recursive
inference obligations; this module does not supply general reduction or
cache soundness.
-/

namespace Ix.Kernel.Consistency

/-- Successful validation before the local scope is opened. Infer-only skips
both checks. Full mode follows the actual sort-exposure and conversion calls,
including their reduction-dependent paths and state changes. -/
inductive LetValidationTrace
    (inferRec : KExpr .anon → RecM .anon (KExpr .anon))
    (methods : Methods .anon) (type value : KExpr .anon) :
    Bool → TcState .anon → TcState .anon → Prop
  | skipped (before : TcState .anon) : LetValidationTrace inferRec methods type value true before before
  | full {before typeState sorted valueState checked : TcState .anon}
      {typeType valueType : KExpr .anon} {level : KUniv .anon}
      (typeRun : inferRec type methods before = .ok typeType typeState)
      (sortRun : RecM.ensureSortDirect typeType methods typeState = .ok level sorted)
      (valueRun : inferRec value methods sorted = .ok valueType valueState)
      (conversion : RecM.isDefEqCall valueType type methods valueState = .ok true checked) :
      LetValidationTrace inferRec methods type value false before checked

/-- Actual successful let inference, with the deterministic closing sequence
and final local-scope cleanup. This trace is extracted from execution. -/
structure LetInferenceTrace
    (inferRec : KExpr .anon → RecM .anon (KExpr .anon))
    (methods : Methods .anon) (inferOnly : Bool)
    (name : Mode.anon.F Name) (type value body : KExpr .anon)
    (before : TcState .anon) (result : KExpr .anon) (after : TcState .anon) where
  validated : TcState .anon
  validation : LetValidationTrace inferRec methods type value inferOnly before validated
  opened : KExpr .anon
  fresh : FVarId
  openedState : TcState .anon
  bodyType : KExpr .anon
  bodyState : TcState .anon
  openRun : TcM.openLet name type value body validated = .ok (opened, fresh) openedState
  bodyRun : inferRec opened methods openedState = .ok bodyType bodyState
  resultEq :
    let abstracted := abstractFVars bodyType #[fresh] bodyState.env.intern
    let substituted := subst abstracted.1 value 0 abstracted.2
    result = (cheapBetaReduce substituted.1 substituted.2).1
  stateEq :
    let abstracted := abstractFVars bodyType #[fresh] bodyState.env.intern
    let substituted := subst abstracted.1 value 0 abstracted.2
    let reduced := cheapBetaReduce substituted.1 substituted.2
    after = {bodyState with
      env := {bodyState.env with intern := reduced.2}
      lctx := bodyState.lctx.truncate validated.lctx.size}

private theorem bind_success {α γ : Type _} {action : TcM .anon α}
    {next : α → TcM .anon γ} {before after : TcState .anon} {result : γ}
    (run : (action >>= next) before = .ok result after) :
    ∃ value state, action before = .ok value state ∧ next value state = .ok result after := by
  cases first : action before with
  | error error state => simp [bind, EStateM.bind, first] at run
  | ok value state =>
      refine ⟨value, state, rfl, ?_⟩
      simpa [bind, EStateM.bind, first] using run

private theorem withLctxScope_success {action : RecM .anon α}
    {methods : Methods .anon} {before after : TcState .anon} {result : α}
    (run : (RecM.withLctxScope action).run methods before = .ok result after) :
    ∃ state, action.run methods before = .ok result state ∧
      after = {state with lctx := state.lctx.truncate before.lctx.size} := by
  rw [withLctxScope_eq] at run
  cases bodyRun : action.run methods before with
  | error error state => rw [bodyRun] at run; contradiction
  | ok value state =>
      rw [bodyRun] at run
      cases run
      exact ⟨state, rfl, rfl⟩

private theorem let_scope_success
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)} {methods : Methods .anon}
    {inferOnly : Bool} {name : Mode.anon.F Name} {type value body result : KExpr .anon}
    {before validated after : TcState .anon}
    (validation : LetValidationTrace inferRec methods type value inferOnly before validated)
    (run : ((RecM.withLctxScope (m := .anon) do
      let (opened, fresh) ← TcM.openLet name type value body
      let bodyType ← inferRec opened
      let abstracted ← TcM.runIntern (abstractFVars bodyType #[fresh])
      let substituted ← TcM.runIntern (subst abstracted value 0)
      TcM.runIntern (cheapBetaReduce substituted)).run methods) validated = .ok result after) :
    Nonempty (LetInferenceTrace inferRec methods inferOnly name type value body before result after) := by
  obtain ⟨finished, run, cleanup⟩ := withLctxScope_success run
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at run
  obtain ⟨⟨opened, fresh⟩, openedState, openRun, run⟩ := bind_success run
  obtain ⟨bodyType, bodyState, bodyRun, run⟩ := bind_success run
  change EStateM.Result.ok _ _ = .ok result finished at run
  obtain ⟨out, state⟩ := EStateM.Result.ok.inj run
  refine ⟨⟨validated, validation, opened, fresh, openedState, bodyType, bodyState,
    openRun, bodyRun, out.symm, ?_⟩⟩
  rw [cleanup, ← state]
  rfl

/-- Every successful production let branch yields the entire operational
trace in either policy. No cache-miss tree, syntactic sort result, conversion
shortcut or precomputed trace is supplied. -/
theorem LetInferenceTrace.of_success
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)} {methods : Methods .anon}
    {inferOnly : Bool} {name : Mode.anon.F Name}
    {type value body result : KExpr .anon} {nonDep : Bool} {info : ExprInfo .anon}
    {before after : TcState .anon}
    (run : RecM.inferUncached inferRec inferOnly (.letE name type value body nonDep info)
      methods before = .ok result after) :
    Nonempty (LetInferenceTrace inferRec methods inferOnly name type value body before result after) := by
  change (RecM.inferUncached inferRec inferOnly (.letE name type value body nonDep info)).run
    methods before = .ok result after at run
  unfold RecM.inferUncached at run
  cases inferOnly with
  | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false] at run
      exact let_scope_success (.skipped before) run
  | false =>
      simp only [Bool.not_false, if_true, ReaderT.run_bind] at run
      obtain ⟨typeType, typeState, typeRun, run⟩ := bind_success run
      obtain ⟨level, sorted, sortRun, run⟩ := bind_success run
      obtain ⟨valueType, valueState, valueRun, run⟩ := bind_success run
      obtain ⟨equal, checked, conversion, run⟩ := bind_success run
      cases equal with
      | false => contradiction
      | true =>
          simp only [Bool.not_true, Bool.false_eq_true, if_false] at run
          exact let_scope_success (.full typeRun sortRun valueRun conversion) run

open Theory Theory.Model

universe u v

/-- The actual opening and closing sequence transports the recursive body's
typing to the original let expression and its substituted type. The final
cheap-beta pass remains a separate reduction obligation. -/
theorem LetInferenceTrace.beforeBeta_typing
    {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {values : LocalValues β} {context : Model.Context β}
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)} {methods : Methods .anon}
    {inferOnly : Bool} {name : Mode.anon.F Name} {type value body result : KExpr .anon}
    {before after : TcState .anon} {A e : AExpr β} {b : VExpr β}
    (trace : LetInferenceTrace inferRec methods inferOnly name type value body before result after)
    (support : BinderOpeningSupport trace.validated body)
    (agreement : LocalContextValues.{u,v} resolve entries values trace.validated.lctx context)
    (below : values.Below trace.validated.env.nextFVarId)
    (typeReads : readLocalExpr? resolve values type = some A.erase)
    (valueReads : readLocalExpr? resolve values value = some e.erase)
    (bodyReads : readLocalExpr? resolve values body 1 = some b)
    (valueTyped : TypingClaim.{u,v} entries context e A)
    (bodyTyped : LocalModelTyping.{u,v} resolve entries (values.pushLet trace.fresh e)
      context trace.opened trace.bodyType)
    (constructed : trace.bodyType.Constructed) (valueConstructed : value.Constructed)
    (bound : trace.bodyType.lbr.toNat + trace.bodyType.size + 1 < UInt64.size)
    (valueBound : value.size < UInt64.size) (coherent : trace.bodyState.env.intern.WF)
    (abstractFaithful : KExpr.CollisionFree fun term => trace.bodyState.env.intern.ExprSupport term ∨
      KExpr.AbstractReach ((∅ : Std.HashMap FVarId UInt64).insert trace.fresh 0) 1 trace.bodyType 0 term)
    (substFaithful :
      let abstracted := abstractFVars trace.bodyType #[trace.fresh] trace.bodyState.env.intern
      KExpr.CollisionFree fun term => abstracted.2.ExprSupport term ∨
        KExpr.SubstReach value abstracted.1 0 term)
    (nonDep : Bool) (info : ExprInfo .anon) :
    let abstracted := abstractFVars trace.bodyType #[trace.fresh] trace.bodyState.env.intern
    let substituted := subst abstracted.1 value 0 abstracted.2
    LocalModelTyping.{u,v} resolve entries values context
      (.letE name type value body nonDep info) substituted.1 ∧ substituted.2.WF := by
  have opened := openLet_local_sound support agreement below typeReads valueReads bodyReads
    valueTyped trace.openRun
  obtain ⟨source, inferred, sourceReads, inferredReads, typed⟩ := bodyTyped
  have sameSource : b.inst e.erase = source.erase :=
    Option.some.inj (opened.2.1.symm.trans sourceReads)
  have closed := closeLetType_readLocalExpr? constructed valueConstructed bound valueBound
    coherent abstractFaithful substFaithful inferredReads valueReads
  refine ⟨⟨source, inferred, ?_, closed.1, typed⟩, closed.2⟩
  simp [readLocalExpr?, typeReads, valueReads, bodyReads, sameSource]

end Ix.Kernel.Consistency
