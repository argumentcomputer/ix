/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.LetOpening
import Ix.Kernel.Verify.Consistency.InferenceCache
import Ix.Kernel.Verify.Consistency.CheapBetaReading
import Ix.Kernel.Verify.Consistency.LocalStateReading

/-! The full production let branch checks the declared type and value,
opens a let local, and infers the body. Its result is obtained by abstraction,
value substitution, and the selected cheap-beta operation, in that order. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

theorem UncachedInference.keyedLocalState {before : TcState .anon} {source : KExpr .anon}
    (miss : UncachedInference before source) (valid : LocalStateInvariant before) :
    LocalStateInvariant miss.keyed :=
  ((FramesLocalState.inferKey _).ok valid miss.keyRun).invariant valid

/-- Actual recursive calls and their states. Scope restoration is derived
from these runs; no child typing or returned-type reading is assumed. -/
structure LetInferenceTrace (fuel : Nat) (before : TcState .anon)
    (name : Mode.anon.F Name) (domain value body : KExpr .anon) where
  domainLevel : KUniv .anon
  domainInfo : ExprInfo .anon
  domainState : TcState .anon
  valueType : KExpr .anon
  valueState : TcState .anon
  comparedState : TcState .anon
  opened : KExpr .anon
  fresh : FVarId
  openedState : TcState .anon
  bodyType : KExpr .anon
  bodyState : TcState .anon
  domainRun : RecM.infer domain (methodsN fuel) before =
    .ok (.sort domainLevel domainInfo) domainState
  valueRun : RecM.infer value (methodsN fuel) domainState = .ok valueType valueState
  compareRun : RecM.isDefEq valueType domain (methodsN fuel) valueState = .ok true comparedState
  openRun : TcM.openLet name domain value body comparedState = .ok (opened, fresh) openedState
  bodyRun : RecM.infer opened (methodsN fuel) openedState = .ok bodyType bodyState

namespace LetInferenceTrace

variable {fuel : Nat} {before : TcState .anon} {name : Mode.anon.F Name}
  {domain value body : KExpr .anon}

theorem domainFrame (trace : LetInferenceTrace fuel before name domain value body)
    (valid : LocalStateInvariant before) : LocalStateFrame before trace.domainState :=
  (infer_methodsN_framesLocalState fuel domain).ok valid trace.domainRun

theorem valueFrame (trace : LetInferenceTrace fuel before name domain value body)
    (valid : LocalStateInvariant before) : LocalStateFrame before trace.valueState :=
  (trace.domainFrame valid).trans ((infer_methodsN_framesLocalState fuel value).ok
    ((trace.domainFrame valid).invariant valid) trace.valueRun)

theorem openingFrame (trace : LetInferenceTrace fuel before name domain value body)
    (valid : LocalStateInvariant before) : LocalStateFrame before trace.comparedState :=
  (trace.valueFrame valid).trans ((isDefEq_methodsN_framesLocalState fuel trace.valueType domain).ok
    ((trace.valueFrame valid).invariant valid) trace.compareRun)

theorem domainContext (trace : LetInferenceTrace fuel before name domain value body)
    (valid : LocalStateInvariant before) : trace.domainState.lctx.Equiv before.lctx :=
  (trace.domainFrame valid).context

theorem openingContext (trace : LetInferenceTrace fuel before name domain value body)
    (valid : LocalStateInvariant before) : trace.comparedState.lctx.Equiv before.lctx :=
  (trace.openingFrame valid).context

/-- All consumers use the same executed opening and its derived freshness. -/
theorem opened_reading {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {context : Model.Context β} {A : AExpr β} {b : VExpr β}
    (trace : LetInferenceTrace fuel before name domain value body)
    (opening : BinderOpeningSupport trace.comparedState body)
    (valid : LocalStateInvariant before)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (domainReading : readScopedExpr? resolve locals domain = some A.erase)
    (bodyReading : readScopedExpr? resolve locals body 1 = some b) :
    readScopedExpr? resolve (trace.fresh :: locals) trace.opened = some b ∧
      LocalContextReading resolve (trace.fresh :: locals) trace.openedState.lctx (context.push A) ∧
      trace.openedState.env.intern.WF := by
  have frame := trace.openingFrame valid
  have openingAgreement := agreement.congr frame.context.symm
  exact (openLet_sound opening openingAgreement
    ((frame.invariant valid).freshReading openingAgreement) domainReading bodyReading trace.openRun).2

def abstracted (trace : LetInferenceTrace fuel before name domain value body) :=
  abstractFVars trace.bodyType #[trace.fresh] trace.bodyState.env.intern

def substituted (trace : LetInferenceTrace fuel before name domain value body) :=
  subst trace.abstracted.1 value 0 trace.abstracted.2

def reduced (trace : LetInferenceTrace fuel before name domain value body) :=
  cheapBetaReduce trace.substituted.1 trace.substituted.2

def after (trace : LetInferenceTrace fuel before name domain value body) : TcState .anon :=
  {trace.bodyState with
    env := {trace.bodyState.env with intern := trace.reduced.2}
    lctx := trace.bodyState.lctx.truncate trace.comparedState.lctx.size}

/-- The whole let scope restores the incoming declarations while retaining
the fresh counter and the body computation's final intern table. -/
theorem restores (trace : LetInferenceTrace fuel before name domain value body)
    (valid : LocalStateInvariant before) : LocalStateFrame before trace.after := by
  have compared := trace.openingFrame valid
  have opened := PreservesLocalState.openLet name domain value body trace.comparedState
    (compared.invariant valid)
  rw [trace.openRun] at opened
  have bodyFrame := (infer_methodsN_framesLocalState fuel trace.opened).ok opened.valid trace.bodyRun
  have restored := (opened.trans (.of_frame opened.valid bodyFrame)).restore
  exact compared.trans ⟨restored.counter, restored.context, restored.loader⟩

private theorem withLctxScope_success {action : RecM .anon α}
    {methods : Methods .anon} {before finished : TcState .anon} {result : α}
    (accepted : action.withLctxScope.run methods before = .ok result finished) :
    ∃ middle, action.run methods before = .ok result middle ∧
      finished = {middle with lctx := middle.lctx.truncate before.lctx.size} := by
  rw [withLctxScope_eq] at accepted
  cases step : action.run methods before with
  | error error failed => rw [step] at accepted; contradiction
  | ok value middle => rw [step] at accepted; cases accepted; exact ⟨middle, rfl, rfl⟩

/-- Invert the production branch through all three calls and both walkers.
Scope cleanup retains the final intern table and all child cache writes. -/
theorem output_state {result : KExpr .anon} {finished : TcState .anon}
    {nonDep : Bool} {info : ExprInfo .anon}
    (trace : LetInferenceTrace fuel before name domain value body)
    (accepted : RecM.inferUncached RecM.inferCall false (.letE name domain value body nonDep info)
      (methodsN (fuel + 1)) before = .ok result finished) :
    result = trace.reduced.1 ∧ finished = trace.after := by
  change (RecM.inferUncached RecM.inferCall false (.letE name domain value body nonDep info)).run
    (methodsN (fuel + 1)) before = _ at accepted
  unfold RecM.inferUncached at accepted
  simp only [Bool.not_false, if_true, ReaderT.run_bind] at accepted
  change EStateM.bind (RecM.infer domain (methodsN fuel)) _ before = _ at accepted
  rw [EStateM.bind, trace.domainRun] at accepted
  change EStateM.bind (RecM.infer value (methodsN fuel)) _ trace.domainState = _ at accepted
  rw [EStateM.bind, trace.valueRun] at accepted
  change EStateM.bind (RecM.isDefEq trace.valueType domain (methodsN fuel)) _ trace.valueState = _ at accepted
  rw [EStateM.bind, trace.compareRun] at accepted
  change (RecM.withLctxScope _).run (methodsN (fuel + 1)) trace.comparedState = _ at accepted
  obtain ⟨middle, accepted, cleanup⟩ := withLctxScope_success accepted
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at accepted
  change EStateM.bind (TcM.openLet name domain value body) _ trace.comparedState =
    .ok result middle at accepted
  rw [EStateM.bind, trace.openRun] at accepted
  have bodyRun : (RecM.inferCall trace.opened).run (methodsN (fuel + 1)) trace.openedState =
      .ok trace.bodyType trace.bodyState := trace.bodyRun
  change EStateM.bind ((RecM.inferCall trace.opened).run (methodsN (fuel + 1)))
    _ trace.openedState = .ok result middle at accepted
  rw [EStateM.bind, bodyRun] at accepted
  cases accepted
  exact ⟨rfl, cleanup⟩

/-- Finite resources for the two production binder walkers. The second
walker uses the table produced by the first one, not the entry table. -/
structure SubstitutionSupport (trace : LetInferenceTrace fuel before name domain value body) : Prop where
  bodyConstructed : trace.bodyType.Constructed
  bodyBound : trace.bodyType.size + 1 < UInt64.size
  coherent : trace.bodyState.env.intern.WF
  closingFaithful : KExpr.CollisionFree fun term => trace.bodyState.env.intern.ExprSupport term ∨
    KExpr.AbstractReach ((∅ : Std.HashMap FVarId UInt64).insert trace.fresh 0) 1 trace.bodyType 0 term
  abstractedConstructed : trace.abstracted.1.Constructed
  abstractedBound : trace.abstracted.1.size + 1 < UInt64.size
  valueConstructed : value.Constructed
  valueBound : value.size < UInt64.size
  substitutionFaithful : KExpr.CollisionFree fun term => trace.abstracted.2.ExprSupport term ∨
    KExpr.SubstReach value trace.abstracted.1 0 term

/-- Abstraction and substitution remove the fresh let local from the
inferred body type, using the exact value supplied to the production branch. -/
theorem substituted_reading {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {B v : AExpr β}
    (trace : LetInferenceTrace fuel before name domain value body)
    (support : trace.SubstitutionSupport)
    (bodyReading : readScopedExpr? resolve (trace.fresh :: locals) trace.bodyType = some B.erase)
    (valueReading : readScopedExpr? resolve locals value = some v.erase) :
    readScopedExpr? resolve locals trace.substituted.1 = some (B.inst v).erase ∧
      trace.substituted.2.WF := by
  obtain ⟨closedReading, closedCoherent⟩ := abstractFVars_readScopedExpr?
    support.bodyConstructed support.bodyBound support.coherent support.closingFaithful bodyReading
  obtain ⟨resultReading, resultCoherent⟩ := subst_readScopedExpr?
    support.abstractedConstructed support.valueConstructed support.abstractedBound support.valueBound
    closedCoherent support.substitutionFaithful closedReading valueReading
  exact ⟨by simpa only [substituted, abstracted, AExpr.erase_inst] using resultReading, resultCoherent⟩

end LetInferenceTrace

end Ix.Kernel.Consistency
