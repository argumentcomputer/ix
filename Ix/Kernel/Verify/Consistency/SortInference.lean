/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BinderInference
import Ix.Kernel.Verify.Consistency.LetInference
import Ix.Kernel.Verify.Consistency.WhnfCacheFrame

/-! Actual binder inference calls with explicit sort exposure. The inferred
type may require reduction before the checker obtains its universe level.
Context restoration and freshness follow from the complete recursive checker. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

/-- The recursive inference call and the following real sort-exposure call.
No syntactic shape or semantic typing is assumed for the inferred expression. -/
structure SortInferenceTrace (fuel : Nat) (before : TcState .anon) (source : KExpr .anon) where
  inferred : KExpr .anon
  inferredState : TcState .anon
  level : KUniv .anon
  after : TcState .anon
  inferRun : RecM.infer source (methodsN fuel) before = .ok inferred inferredState
  exposureRun : (RecM.ensureSortDirect inferred).run (methodsN (fuel + 1)) inferredState = .ok level after

namespace SortInferenceTrace

variable {fuel : Nat} {before : TcState .anon} {source : KExpr .anon}

def direct {level : KUniv .anon} {info : ExprInfo .anon} {after : TcState .anon}
    (accepted : RecM.infer source (methodsN fuel) before = .ok (.sort level info) after) :
    SortInferenceTrace fuel before source :=
  ⟨.sort level info, after, level, after, accepted, rfl⟩

/-- Successful execution determines the inferred type, exposure level,
and both intermediate states; callers need not supply those observations. -/
theorem success {next : KUniv .anon → RecM .anon α} {result : α} {finished : TcState .anon}
    (accepted : (RecM.inferCall source >>= fun type => RecM.ensureSortDirect type >>= next).run
      (methodsN (fuel + 1)) before = .ok result finished) :
    ∃ trace : SortInferenceTrace fuel before source,
      (next trace.level).run (methodsN (fuel + 1)) trace.after = .ok result finished := by
  simp only [ReaderT.run_bind] at accepted
  change EStateM.bind (RecM.infer source (methodsN fuel)) _ before = _ at accepted
  cases inferredRun : RecM.infer source (methodsN fuel) before with
  | error error failed => rw [EStateM.bind, inferredRun] at accepted; contradiction
  | ok type inferredState =>
      rw [EStateM.bind, inferredRun] at accepted
      change EStateM.bind ((RecM.ensureSortDirect type).run (methodsN (fuel + 1))) _ inferredState = _ at accepted
      cases exposedRun : (RecM.ensureSortDirect type).run (methodsN (fuel + 1)) inferredState with
      | error error failed => rw [EStateM.bind, exposedRun] at accepted; contradiction
      | ok level after =>
          rw [EStateM.bind, exposedRun] at accepted
          exact ⟨⟨type, inferredState, level, after, inferredRun, exposedRun⟩, accepted⟩

theorem inferenceFrame (trace : SortInferenceTrace fuel before source)
    (valid : LocalStateInvariant before) : LocalStateFrame before trace.inferredState :=
  (infer_methodsN_framesLocalState fuel source).ok valid trace.inferRun

theorem frame (trace : SortInferenceTrace fuel before source)
    (valid : LocalStateInvariant before) : LocalStateFrame before trace.after :=
  (trace.inferenceFrame valid).trans
    ((FramesLocalState.ensureSortDirect (FramesLocalState.whnf (MethodsLocalState.methodsN (fuel + 1)))
      trace.inferred).ok ((trace.inferenceFrame valid).invariant valid) trace.exposureRun)

abbrev Exposure {β : Type u} (trace : SortInferenceTrace fuel before source)
    (resolve : Address → Option (ConstRef β)) (locals : List FVarId) (term : AExpr β) :=
  BetaSortExposure resolve locals fuel trace.inferredState trace.inferred term trace.level

theorem exposure_state {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {term : AExpr β} (trace : SortInferenceTrace fuel before source)
    (exposure : trace.Exposure resolve locals term) : trace.after = exposure.after := by
  have run := trace.exposureRun
  rw [exposure.run] at run
  exact (EStateM.Result.ok.inj run).2.symm

theorem exposure_frame {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {term : AExpr β} (trace : SortInferenceTrace fuel before source)
    (exposure : trace.Exposure resolve locals term) (key : Address × Address) :
    InferenceCacheFrame key trace.inferredState trace.after :=
  trace.exposure_state exposure ▸ exposure.inference_frame key

theorem exposure_policy {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {term : AExpr β} (trace : SortInferenceTrace fuel before source)
    (exposure : trace.Exposure resolve locals term) : trace.after.inferOnly = trace.inferredState.inferOnly :=
  trace.exposure_state exposure ▸ exposure.policy

theorem exposure_maps {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {term : AExpr β} (trace : SortInferenceTrace fuel before source)
    (exposure : trace.Exposure resolve locals term) :
    trace.after.env.inferCache = trace.inferredState.env.inferCache ∧
      trace.after.env.inferOnlyCache = trace.inferredState.env.inferOnlyCache :=
  trace.exposure_state exposure ▸ exposure.inference_maps

end SortInferenceTrace

private theorem withLctxScope_success {action : RecM .anon α}
    {methods : Methods .anon} {before finished : TcState .anon} {result : α}
    (accepted : action.withLctxScope.run methods before = .ok result finished) :
    ∃ middle, action.run methods before = .ok result middle ∧
      finished = {middle with lctx := middle.lctx.truncate before.lctx.size} := by
  rw [withLctxScope_eq] at accepted
  cases step : action.run methods before with
  | error error failed => rw [step] at accepted; contradiction
  | ok value middle => rw [step] at accepted; cases accepted; exact ⟨middle, rfl, rfl⟩

/-- Both dependent-function children may need WHNF to expose their sort. -/
structure ForallSortInferenceTrace (fuel : Nat) (before : TcState .anon)
    (name : Mode.anon.F Name) (bi : Mode.anon.F Lean.BinderInfo)
    (domain body : KExpr .anon) where
  localState : LocalStateInvariant before
  domainCheck : SortInferenceTrace fuel before domain
  opened : KExpr .anon
  fresh : FVarId
  openedState : TcState .anon
  openRun : TcM.openBinder name bi domain body domainCheck.after = .ok (opened, fresh) openedState
  bodyCheck : SortInferenceTrace fuel openedState opened

namespace ForallSortInferenceTrace

variable {fuel : Nat} {before : TcState .anon} {name : Mode.anon.F Name}
  {bi : Mode.anon.F Lean.BinderInfo} {domain body : KExpr .anon}

theorem domainFrame (trace : ForallSortInferenceTrace fuel before name bi domain body) :
    LocalStateFrame before trace.domainCheck.after := trace.domainCheck.frame trace.localState

theorem opened_reading {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {context : Model.Context β} {A : AExpr β} {b : VExpr β}
    (trace : ForallSortInferenceTrace fuel before name bi domain body)
    (opening : BinderOpeningSupport trace.domainCheck.after body)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (domainReading : readScopedExpr? resolve locals domain = some A.erase)
    (bodyReading : readScopedExpr? resolve locals body 1 = some b) :
    readScopedExpr? resolve (trace.fresh :: locals) trace.opened = some b ∧
      LocalContextReading resolve (trace.fresh :: locals) trace.openedState.lctx (context.push A) ∧
      trace.openedState.env.intern.WF := by
  have frame := trace.domainFrame
  have domainAgreement := agreement.congr frame.context.symm
  exact (openBinder_sound opening domainAgreement
    ((frame.invariant trace.localState).freshReading domainAgreement) domainReading bodyReading trace.openRun).2

def interned (trace : ForallSortInferenceTrace fuel before name bi domain body) :=
  trace.bodyCheck.after.env.intern.internExpr
    (KExpr.mkSort (KUniv.mkIMax trace.domainCheck.level trace.bodyCheck.level))

def after (trace : ForallSortInferenceTrace fuel before name bi domain body) : TcState .anon :=
  {trace.bodyCheck.after with
    env := {trace.bodyCheck.after.env with intern := trace.interned.2}
    lctx := trace.bodyCheck.after.lctx.truncate trace.domainCheck.after.lctx.size}

/-- Invert successful production inference to recover the complete call
trace, including either sort-exposure branch at both children. -/
theorem success {finished : TcState .anon} {result : KExpr .anon}
    {info : ExprInfo .anon} {inferOnly : Bool} (valid : LocalStateInvariant before)
    (accepted : RecM.inferUncached RecM.inferCall inferOnly (.all name bi domain body info)
      (methodsN (fuel + 1)) before = .ok result finished) :
    Nonempty (ForallSortInferenceTrace fuel before name bi domain body) := by
  change (RecM.inferUncached RecM.inferCall inferOnly (.all name bi domain body info)).run
    (methodsN (fuel + 1)) before = _ at accepted
  unfold RecM.inferUncached at accepted
  obtain ⟨domainCheck, accepted⟩ := SortInferenceTrace.success accepted
  change (RecM.withLctxScope _).run (methodsN (fuel + 1)) domainCheck.after = _ at accepted
  obtain ⟨middle, accepted, _⟩ := withLctxScope_success accepted
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at accepted
  change EStateM.bind (TcM.openBinder name bi domain body) _ domainCheck.after = _ at accepted
  cases openRun : TcM.openBinder name bi domain body domainCheck.after with
  | error error failed => rw [EStateM.bind, openRun] at accepted; contradiction
  | ok pair openedState =>
      rcases pair with ⟨opened, fresh⟩
      rw [EStateM.bind, openRun] at accepted
      obtain ⟨bodyCheck, _⟩ := SortInferenceTrace.success (fuel := fuel) (before := openedState)
        (source := opened) (next := fun level =>
          liftM (TcM.intern (KExpr.mkSort (KUniv.mkIMax domainCheck.level level)))) accepted
      exact ⟨⟨valid, domainCheck, opened, fresh, openedState, openRun, bodyCheck⟩⟩

noncomputable def ofSuccess {finished : TcState .anon} {result : KExpr .anon}
    {info : ExprInfo .anon} {inferOnly : Bool} (valid : LocalStateInvariant before)
    (accepted : RecM.inferUncached RecM.inferCall inferOnly (.all name bi domain body info)
      (methodsN (fuel + 1)) before = .ok result finished) :
    ForallSortInferenceTrace fuel before name bi domain body :=
  Classical.choice (success valid accepted)

/-- A successful cache miss supplies the branch trace and its initial
local invariant from the ordinary inference entry point. -/
noncomputable def ofInference {finished : TcState .anon} {result : KExpr .anon} {info : ExprInfo .anon}
    (miss : UncachedInference before (.all name bi domain body info))
    (valid : LocalStateInvariant before)
    (accepted : RecM.infer (.all name bi domain body info) (methodsN (fuel + 1)) before = .ok result finished) :
    ForallSortInferenceTrace fuel miss.keyed name bi domain body :=
  Classical.choice (by
    obtain ⟨middle, run⟩ := infer_uncached_success miss accepted
    exact success (miss.keyedLocalState valid) run)

theorem output_state {finished : TcState .anon} {result : KExpr .anon}
    {info : ExprInfo .anon} {inferOnly : Bool}
    (trace : ForallSortInferenceTrace fuel before name bi domain body)
    (accepted : RecM.inferUncached RecM.inferCall inferOnly (.all name bi domain body info)
      (methodsN (fuel + 1)) before = .ok result finished) :
    result = trace.interned.1 ∧ finished = trace.after := by
  change (RecM.inferUncached RecM.inferCall inferOnly (.all name bi domain body info)).run
    (methodsN (fuel + 1)) before = _ at accepted
  unfold RecM.inferUncached at accepted
  simp only [ReaderT.run_bind] at accepted
  change EStateM.bind (RecM.infer domain (methodsN fuel)) _ before = _ at accepted
  rw [EStateM.bind, trace.domainCheck.inferRun] at accepted
  change EStateM.bind ((RecM.ensureSortDirect trace.domainCheck.inferred).run (methodsN (fuel + 1)))
    _ trace.domainCheck.inferredState = _ at accepted
  rw [EStateM.bind, trace.domainCheck.exposureRun] at accepted
  change (RecM.withLctxScope _).run (methodsN (fuel + 1)) trace.domainCheck.after = _ at accepted
  obtain ⟨middle, accepted, cleanup⟩ := withLctxScope_success accepted
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at accepted
  change EStateM.bind (TcM.openBinder name bi domain body) _ trace.domainCheck.after =
    .ok result middle at accepted
  rw [EStateM.bind, trace.openRun] at accepted
  change EStateM.bind (RecM.infer trace.opened (methodsN fuel)) _ trace.openedState = _ at accepted
  rw [EStateM.bind, trace.bodyCheck.inferRun] at accepted
  change EStateM.bind ((RecM.ensureSortDirect trace.bodyCheck.inferred).run (methodsN (fuel + 1)))
    _ trace.bodyCheck.inferredState = _ at accepted
  rw [EStateM.bind, trace.bodyCheck.exposureRun] at accepted
  cases accepted
  exact ⟨rfl, cleanup⟩

end ForallSortInferenceTrace

/-- Lambda inference validates its domain through the actual sort exposure,
then infers its opened body before cheap beta and abstraction. -/
structure LambdaSortInferenceTrace (fuel : Nat) (before : TcState .anon)
    (name : Mode.anon.F Name) (bi : Mode.anon.F Lean.BinderInfo)
    (domain body : KExpr .anon) where
  localState : LocalStateInvariant before
  domainCheck : SortInferenceTrace fuel before domain
  opened : KExpr .anon
  fresh : FVarId
  openedState : TcState .anon
  bodyType : KExpr .anon
  bodyState : TcState .anon
  openRun : TcM.openBinder name bi domain body domainCheck.after = .ok (opened, fresh) openedState
  bodyRun : RecM.infer opened (methodsN fuel) openedState = .ok bodyType bodyState

namespace LambdaSortInferenceTrace

variable {fuel : Nat} {before : TcState .anon} {name : Mode.anon.F Name}
  {bi : Mode.anon.F Lean.BinderInfo} {domain body : KExpr .anon}

theorem domainFrame (trace : LambdaSortInferenceTrace fuel before name bi domain body) :
    LocalStateFrame before trace.domainCheck.after := trace.domainCheck.frame trace.localState

theorem opened_reading {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {context : Model.Context β} {A : AExpr β} {b : VExpr β}
    (trace : LambdaSortInferenceTrace fuel before name bi domain body)
    (opening : BinderOpeningSupport trace.domainCheck.after body)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (domainReading : readScopedExpr? resolve locals domain = some A.erase)
    (bodyReading : readScopedExpr? resolve locals body 1 = some b) :
    readScopedExpr? resolve (trace.fresh :: locals) trace.opened = some b ∧
      LocalContextReading resolve (trace.fresh :: locals) trace.openedState.lctx (context.push A) ∧
      trace.openedState.env.intern.WF := by
  have frame := trace.domainFrame
  have domainAgreement := agreement.congr frame.context.symm
  exact (openBinder_sound opening domainAgreement
    ((frame.invariant trace.localState).freshReading domainAgreement) domainReading bodyReading trace.openRun).2

def reduced (trace : LambdaSortInferenceTrace fuel before name bi domain body) :=
  cheapBetaReduce trace.bodyType trace.bodyState.env.intern

def abstracted (trace : LambdaSortInferenceTrace fuel before name bi domain body) :=
  abstractFVars trace.reduced.1 #[trace.fresh] trace.reduced.2

def interned (trace : LambdaSortInferenceTrace fuel before name bi domain body) :=
  trace.abstracted.2.internExpr (KExpr.mkAll () () domain trace.abstracted.1)

def after (trace : LambdaSortInferenceTrace fuel before name bi domain body) : TcState .anon :=
  {trace.bodyState with
    env := {trace.bodyState.env with intern := trace.interned.2}
    lctx := trace.bodyState.lctx.truncate trace.domainCheck.after.lctx.size}

theorem success {finished : TcState .anon} {result : KExpr .anon} {info : ExprInfo .anon}
    (valid : LocalStateInvariant before)
    (accepted : RecM.inferUncached RecM.inferCall false (.lam name bi domain body info)
      (methodsN (fuel + 1)) before = .ok result finished) :
    Nonempty (LambdaSortInferenceTrace fuel before name bi domain body) := by
  change (RecM.inferUncached RecM.inferCall false (.lam name bi domain body info)).run
    (methodsN (fuel + 1)) before = _ at accepted
  unfold RecM.inferUncached at accepted
  simp only [Bool.not_false, if_true] at accepted
  obtain ⟨domainCheck, accepted⟩ := SortInferenceTrace.success accepted
  change (RecM.withLctxScope _).run (methodsN (fuel + 1)) domainCheck.after = _ at accepted
  obtain ⟨middle, accepted, _⟩ := withLctxScope_success accepted
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at accepted
  change EStateM.bind (TcM.openBinder name bi domain body) _ domainCheck.after = _ at accepted
  cases openRun : TcM.openBinder name bi domain body domainCheck.after with
  | error error failed => rw [EStateM.bind, openRun] at accepted; contradiction
  | ok pair openedState =>
      rcases pair with ⟨opened, fresh⟩
      rw [EStateM.bind, openRun] at accepted
      change EStateM.bind (RecM.infer opened (methodsN fuel)) _ openedState = _ at accepted
      cases bodyRun : RecM.infer opened (methodsN fuel) openedState with
      | error error failed => rw [EStateM.bind, bodyRun] at accepted; contradiction
      | ok bodyType bodyState =>
          exact ⟨⟨valid, domainCheck, opened, fresh, openedState, bodyType, bodyState, openRun, bodyRun⟩⟩

noncomputable def ofSuccess {finished : TcState .anon} {result : KExpr .anon} {info : ExprInfo .anon}
    (valid : LocalStateInvariant before)
    (accepted : RecM.inferUncached RecM.inferCall false (.lam name bi domain body info)
      (methodsN (fuel + 1)) before = .ok result finished) :
    LambdaSortInferenceTrace fuel before name bi domain body := Classical.choice (success valid accepted)

noncomputable def ofInference {finished : TcState .anon} {result : KExpr .anon} {info : ExprInfo .anon}
    (full : before.inferOnly = false)
    (miss : UncachedInference before (.lam name bi domain body info))
    (valid : LocalStateInvariant before)
    (accepted : RecM.infer (.lam name bi domain body info) (methodsN (fuel + 1)) before = .ok result finished) :
    LambdaSortInferenceTrace fuel miss.keyed name bi domain body :=
  Classical.choice (by
    obtain ⟨middle, run⟩ := infer_uncached_success miss accepted
    rw [full] at run
    exact success (miss.keyedLocalState valid) run)

theorem output_state {finished : TcState .anon} {result : KExpr .anon} {info : ExprInfo .anon}
    (trace : LambdaSortInferenceTrace fuel before name bi domain body)
    (accepted : RecM.inferUncached RecM.inferCall false (.lam name bi domain body info)
      (methodsN (fuel + 1)) before = .ok result finished) :
    result = trace.interned.1 ∧ finished = trace.after := by
  change (RecM.inferUncached RecM.inferCall false (.lam name bi domain body info)).run
    (methodsN (fuel + 1)) before = _ at accepted
  unfold RecM.inferUncached at accepted
  simp only [Bool.not_false, if_true, ReaderT.run_bind] at accepted
  change EStateM.bind (RecM.infer domain (methodsN fuel)) _ before = _ at accepted
  rw [EStateM.bind, trace.domainCheck.inferRun] at accepted
  change EStateM.bind ((RecM.ensureSortDirect trace.domainCheck.inferred).run (methodsN (fuel + 1)))
    _ trace.domainCheck.inferredState = _ at accepted
  rw [EStateM.bind, trace.domainCheck.exposureRun] at accepted
  change (RecM.withLctxScope _).run (methodsN (fuel + 1)) trace.domainCheck.after = _ at accepted
  obtain ⟨middle, accepted, cleanup⟩ := withLctxScope_success accepted
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at accepted
  change EStateM.bind (TcM.openBinder name bi domain body) _ trace.domainCheck.after =
    .ok result middle at accepted
  rw [EStateM.bind, trace.openRun] at accepted
  change EStateM.bind (RecM.infer trace.opened (methodsN fuel)) _ trace.openedState = _ at accepted
  rw [EStateM.bind, trace.bodyRun] at accepted
  cases accepted
  exact ⟨rfl, cleanup⟩

end LambdaSortInferenceTrace

/-- Full let inference records domain sort exposure before the value check. -/
structure LetSortInferenceTrace (fuel : Nat) (before : TcState .anon)
    (name : Mode.anon.F Name) (domain value body : KExpr .anon) where
  domainCheck : SortInferenceTrace fuel before domain
  valueType : KExpr .anon
  valueState : TcState .anon
  comparedState : TcState .anon
  opened : KExpr .anon
  fresh : FVarId
  openedState : TcState .anon
  bodyType : KExpr .anon
  bodyState : TcState .anon
  valueRun : RecM.infer value (methodsN fuel) domainCheck.after = .ok valueType valueState
  compareRun : RecM.isDefEq valueType domain (methodsN fuel) valueState = .ok true comparedState
  openRun : TcM.openLet name domain value body comparedState = .ok (opened, fresh) openedState
  bodyRun : RecM.infer opened (methodsN fuel) openedState = .ok bodyType bodyState

namespace LetSortInferenceTrace

variable {fuel : Nat} {before : TcState .anon} {name : Mode.anon.F Name}
  {domain value body : KExpr .anon}

theorem domainFrame (trace : LetSortInferenceTrace fuel before name domain value body)
    (valid : LocalStateInvariant before) : LocalStateFrame before trace.domainCheck.after :=
  trace.domainCheck.frame valid

theorem valueFrame (trace : LetSortInferenceTrace fuel before name domain value body)
    (valid : LocalStateInvariant before) : LocalStateFrame before trace.valueState :=
  (trace.domainFrame valid).trans ((infer_methodsN_framesLocalState fuel value).ok
    ((trace.domainFrame valid).invariant valid) trace.valueRun)

theorem openingFrame (trace : LetSortInferenceTrace fuel before name domain value body)
    (valid : LocalStateInvariant before) : LocalStateFrame before trace.comparedState :=
  (trace.valueFrame valid).trans ((isDefEq_methodsN_framesLocalState fuel trace.valueType domain).ok
    ((trace.valueFrame valid).invariant valid) trace.compareRun)

theorem domainContext (trace : LetSortInferenceTrace fuel before name domain value body)
    (valid : LocalStateInvariant before) : trace.domainCheck.after.lctx.Equiv before.lctx :=
  (trace.domainFrame valid).context

theorem openingContext (trace : LetSortInferenceTrace fuel before name domain value body)
    (valid : LocalStateInvariant before) : trace.comparedState.lctx.Equiv before.lctx :=
  (trace.openingFrame valid).context

/-- All consumers use the same executed opening and its derived freshness. -/
theorem opened_reading {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {context : Model.Context β} {A : AExpr β} {b : VExpr β}
    (trace : LetSortInferenceTrace fuel before name domain value body)
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

def abstracted (trace : LetSortInferenceTrace fuel before name domain value body) :=
  abstractFVars trace.bodyType #[trace.fresh] trace.bodyState.env.intern

def substituted (trace : LetSortInferenceTrace fuel before name domain value body) :=
  subst trace.abstracted.1 value 0 trace.abstracted.2

def reduced (trace : LetSortInferenceTrace fuel before name domain value body) :=
  cheapBetaReduce trace.substituted.1 trace.substituted.2

def after (trace : LetSortInferenceTrace fuel before name domain value body) : TcState .anon :=
  {trace.bodyState with
    env := {trace.bodyState.env with intern := trace.reduced.2}
    lctx := trace.bodyState.lctx.truncate trace.comparedState.lctx.size}

/-- The whole let scope restores the incoming declarations while retaining
the fresh counter and the body computation's final intern table. -/
theorem restores (trace : LetSortInferenceTrace fuel before name domain value body)
    (valid : LocalStateInvariant before) : LocalStateFrame before trace.after := by
  have compared := trace.openingFrame valid
  have opened := PreservesLocalState.openLet name domain value body trace.comparedState
    (compared.invariant valid)
  rw [trace.openRun] at opened
  have bodyFrame := (infer_methodsN_framesLocalState fuel trace.opened).ok opened.valid trace.bodyRun
  have restored := (opened.trans (.of_frame opened.valid bodyFrame)).restore
  exact compared.trans ⟨restored.counter, restored.context, restored.loader⟩

/-- Invert the production branch through all three calls and both walkers.
Scope cleanup retains the final intern table and all child cache writes. -/
theorem success {result : KExpr .anon} {finished : TcState .anon}
    {nonDep : Bool} {info : ExprInfo .anon}
    (accepted : RecM.inferUncached RecM.inferCall false (.letE name domain value body nonDep info)
      (methodsN (fuel + 1)) before = .ok result finished) :
    Nonempty (LetSortInferenceTrace fuel before name domain value body) := by
  change (RecM.inferUncached RecM.inferCall false (.letE name domain value body nonDep info)).run
    (methodsN (fuel + 1)) before = _ at accepted
  unfold RecM.inferUncached at accepted
  simp only [Bool.not_false, if_true] at accepted
  obtain ⟨domainCheck, accepted⟩ := SortInferenceTrace.success accepted
  change EStateM.bind (RecM.infer value (methodsN fuel)) _ domainCheck.after = _ at accepted
  cases valueRun : RecM.infer value (methodsN fuel) domainCheck.after with
  | error error failed => rw [EStateM.bind, valueRun] at accepted; contradiction
  | ok valueType valueState =>
      rw [EStateM.bind, valueRun] at accepted
      change EStateM.bind (RecM.isDefEq valueType domain (methodsN fuel)) _ valueState = _ at accepted
      cases compareRun : RecM.isDefEq valueType domain (methodsN fuel) valueState with
      | error error failed => rw [EStateM.bind, compareRun] at accepted; contradiction
      | ok equal comparedState =>
          cases equal
          · rw [EStateM.bind, compareRun] at accepted; contradiction
          · rw [EStateM.bind, compareRun] at accepted
            change (RecM.withLctxScope _).run (methodsN (fuel + 1)) comparedState = _ at accepted
            obtain ⟨middle, accepted, _⟩ := withLctxScope_success accepted
            simp only [ReaderT.run_bind, ReaderT.run_monadLift] at accepted
            change EStateM.bind (TcM.openLet name domain value body) _ comparedState = _ at accepted
            cases openRun : TcM.openLet name domain value body comparedState with
            | error error failed => rw [EStateM.bind, openRun] at accepted; contradiction
            | ok pair openedState =>
                rcases pair with ⟨opened, fresh⟩
                rw [EStateM.bind, openRun] at accepted
                change EStateM.bind (RecM.infer opened (methodsN fuel)) _ openedState = _ at accepted
                cases bodyRun : RecM.infer opened (methodsN fuel) openedState with
                | error error failed => rw [EStateM.bind, bodyRun] at accepted; contradiction
                | ok bodyType bodyState =>
                    exact ⟨⟨domainCheck, valueType, valueState, comparedState, opened, fresh, openedState,
                      bodyType, bodyState, valueRun, compareRun, openRun, bodyRun⟩⟩

noncomputable def ofSuccess {result : KExpr .anon} {finished : TcState .anon}
    {nonDep : Bool} {info : ExprInfo .anon}
    (accepted : RecM.inferUncached RecM.inferCall false (.letE name domain value body nonDep info)
      (methodsN (fuel + 1)) before = .ok result finished) :
    LetSortInferenceTrace fuel before name domain value body := Classical.choice (success accepted)

noncomputable def ofInference {result : KExpr .anon} {finished : TcState .anon}
    {nonDep : Bool} {info : ExprInfo .anon} (full : before.inferOnly = false)
    (miss : UncachedInference before (.letE name domain value body nonDep info))
    (accepted : RecM.infer (.letE name domain value body nonDep info) (methodsN (fuel + 1)) before =
      .ok result finished) : LetSortInferenceTrace fuel miss.keyed name domain value body :=
  Classical.choice (by
    obtain ⟨middle, run⟩ := infer_uncached_success miss accepted
    rw [full] at run
    exact success run)

theorem output_state {result : KExpr .anon} {finished : TcState .anon}
    {nonDep : Bool} {info : ExprInfo .anon}
    (trace : LetSortInferenceTrace fuel before name domain value body)
    (accepted : RecM.inferUncached RecM.inferCall false (.letE name domain value body nonDep info)
      (methodsN (fuel + 1)) before = .ok result finished) :
    result = trace.reduced.1 ∧ finished = trace.after := by
  change (RecM.inferUncached RecM.inferCall false (.letE name domain value body nonDep info)).run
    (methodsN (fuel + 1)) before = _ at accepted
  unfold RecM.inferUncached at accepted
  simp only [Bool.not_false, if_true, ReaderT.run_bind] at accepted
  change EStateM.bind (RecM.infer domain (methodsN fuel)) _ before = _ at accepted
  rw [EStateM.bind, trace.domainCheck.inferRun] at accepted
  change EStateM.bind ((RecM.ensureSortDirect trace.domainCheck.inferred).run (methodsN (fuel + 1)))
    _ trace.domainCheck.inferredState = _ at accepted
  rw [EStateM.bind, trace.domainCheck.exposureRun] at accepted
  change EStateM.bind (RecM.infer value (methodsN fuel)) _ trace.domainCheck.after = _ at accepted
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
structure SubstitutionSupport (trace : LetSortInferenceTrace fuel before name domain value body) : Prop where
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
    (trace : LetSortInferenceTrace fuel before name domain value body)
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

end LetSortInferenceTrace

end Ix.Kernel.Consistency
