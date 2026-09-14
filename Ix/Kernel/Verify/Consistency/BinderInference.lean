/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Application
import Ix.Kernel.Verify.Consistency.ConstantCache
import Ix.Kernel.Verify.Consistency.SortCache
import Ix.Theory.Model.Checking

/-!
# Production dependent function inference

Finite inference trees follow the production method table's decreasing fuel.
Their premises record cache observations, actual execution prefixes, initial
structural local state, finite interning support, and index bounds. Scope frames
and freshness follow from the actual recursive calls. Semantic checking is
derived from these trees. A declaration's separate type inference supplies
the expected type's hereditary validity before checking becomes typing.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- Application spines whose type validity comes from the current local
declaration or an admitted constant. Lambda arguments may still be checked
against the domain supplied by such a function. -/
inductive SynthesisHead {β : Type u} : AExpr β → Prop
  | bvar (index : Nat) : SynthesisHead (.bvar index)
  | const (ref : ConstRef β) (levels : List VLevel) : SynthesisHead (.const ref levels)
  | app {fn arg : AExpr β} (head : SynthesisHead fn) : SynthesisHead (.app fn arg)

/-- Empty universe instantiation returns the exact declaration type reached
by lazy lookup. The scoped reading can include dependent Pi types. -/
theorem inferUncached_monomorphic_const_scoped {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {id : KId .anon} {info : ExprInfo .anon} {type : AExpr β}
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)} {inferOnly : Bool}
    {methods : Methods .anon} {before after : TcState .anon} {result : KExpr .anon}
    (lookup : ∀ concrete loaded, TcM.getConst id before = .ok concrete loaded →
      readScopedExpr? resolve locals concrete.ty = some type.erase)
    (accepted : RecM.inferUncached inferRec inferOnly (.const id #[] info)
      methods before = .ok result after) :
    readScopedExpr? resolve locals result = some type.erase := by
  change (RecM.inferUncached inferRec inferOnly (.const id #[] info)).run
    methods before = .ok result after at accepted
  unfold RecM.inferUncached at accepted
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at accepted
  change EStateM.bind (TcM.getConst id) _ before = _ at accepted
  cases got : TcM.getConst id before with
  | error err failed => rw [EStateM.bind, got] at accepted; contradiction
  | ok concrete loaded =>
      rw [EStateM.bind, got] at accepted
      simp only at accepted
      split at accepted
      · contradiction
      · change EStateM.Result.ok concrete.ty loaded = .ok result after at accepted
        cases accepted
        exact lookup concrete _ got

private theorem withLctxScope_success {action : RecM .anon α}
    {methods : Methods .anon} {before after : TcState .anon} {result : α}
    (accepted : (RecM.withLctxScope action).run methods before = .ok result after) :
    ∃ state, action.run methods before = .ok result state ∧
      after = {state with lctx := state.lctx.truncate before.lctx.size} := by
  rw [withLctxScope_eq] at accepted
  cases run : action.run methods before with
  | error err state => rw [run] at accepted; contradiction
  | ok value state =>
      rw [run] at accepted
      cases accepted
      exact ⟨state, rfl, rfl⟩

/-- The exact recursive calls and opening prefix of a forall branch.
Both sort exposures take the production syntactic fast path. -/
structure ForallInferenceTrace (fuel : Nat) (before : TcState .anon)
    (name : Mode.anon.F Name) (bi : Mode.anon.F Lean.BinderInfo)
    (domain body : KExpr .anon) where
  localState : LocalStateInvariant before
  domainLevel : KUniv .anon
  domainInfo : ExprInfo .anon
  domainState : TcState .anon
  opened : KExpr .anon
  fresh : FVarId
  openedState : TcState .anon
  bodyLevel : KUniv .anon
  bodyInfo : ExprInfo .anon
  bodyState : TcState .anon
  domainRun : RecM.infer domain (methodsN fuel) before =
    .ok (.sort domainLevel domainInfo) domainState
  openRun : TcM.openBinder name bi domain body domainState = .ok (opened, fresh) openedState
  bodyRun : RecM.infer opened (methodsN fuel) openedState =
    .ok (.sort bodyLevel bodyInfo) bodyState

theorem ForallInferenceTrace.domainFrame {fuel : Nat} {before : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo} {domain body : KExpr .anon}
    (trace : ForallInferenceTrace fuel before name bi domain body) :
    LocalStateFrame before trace.domainState :=
  (infer_methodsN_framesLocalState fuel domain).ok trace.localState trace.domainRun

theorem ForallInferenceTrace.domainValid {fuel : Nat} {before : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo} {domain body : KExpr .anon}
    (trace : ForallInferenceTrace fuel before name bi domain body) :
    LocalStateInvariant trace.domainState := trace.domainFrame.invariant trace.localState

theorem ForallInferenceTrace.contextPreserved {fuel : Nat} {before : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo} {domain body : KExpr .anon}
    (trace : ForallInferenceTrace fuel before name bi domain body) :
    trace.domainState.lctx.Equiv before.lctx := trace.domainFrame.context

theorem ForallInferenceTrace.absent {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {context : Model.Context β} {fuel : Nat} {before : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo} {domain body : KExpr .anon}
    (trace : ForallInferenceTrace fuel before name bi domain body)
    (agreement : LocalContextReading resolve locals before.lctx context) :
    (⟨trace.domainState.env.nextFVarId⟩ : FVarId) ∉ locals :=
  trace.domainValid.freshReading (agreement.congr trace.contextPreserved.symm)

/-- Inversion reaches the actual final interning operation after both recursive
calls, sort exposures, and binder opening. -/
theorem ForallInferenceTrace.output_state {fuel : Nat} {before after : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body result : KExpr .anon} {info : ExprInfo .anon} {inferOnly : Bool}
    (trace : ForallInferenceTrace fuel before name bi domain body)
    (accepted : RecM.inferUncached RecM.inferCall inferOnly (.all name bi domain body info)
      (methodsN (fuel + 1)) before = .ok result after) :
    result = (trace.bodyState.env.intern.internExpr
      (KExpr.mkSort (KUniv.mkIMax trace.domainLevel trace.bodyLevel))).1 ∧
      after = {trace.bodyState with
        env := {trace.bodyState.env with intern := (trace.bodyState.env.intern.internExpr
          (KExpr.mkSort (KUniv.mkIMax trace.domainLevel trace.bodyLevel))).2}
        lctx := trace.bodyState.lctx.truncate trace.domainState.lctx.size} := by
  change (RecM.inferUncached RecM.inferCall inferOnly (.all name bi domain body info)).run
    (methodsN (fuel + 1)) before = .ok result after at accepted
  unfold RecM.inferUncached at accepted
  simp only [ReaderT.run_bind] at accepted
  change EStateM.bind (RecM.infer domain (methodsN fuel)) _ before = _ at accepted
  rw [EStateM.bind, trace.domainRun] at accepted
  change (RecM.withLctxScope _).run (methodsN (fuel + 1)) trace.domainState = _ at accepted
  obtain ⟨scopedState, accepted, cleanup⟩ := withLctxScope_success accepted
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at accepted
  change EStateM.bind (TcM.openBinder name bi domain body) _ trace.domainState =
    .ok result scopedState at accepted
  rw [EStateM.bind, trace.openRun] at accepted
  have bodyRun : (RecM.inferCall trace.opened).run (methodsN (fuel + 1))
      trace.openedState = .ok (.sort trace.bodyLevel trace.bodyInfo) trace.bodyState := trace.bodyRun
  change EStateM.bind ((RecM.inferCall trace.opened).run (methodsN (fuel + 1)))
    _ trace.openedState = .ok result scopedState at accepted
  rw [EStateM.bind, bodyRun] at accepted
  cases accepted
  exact ⟨rfl, cleanup⟩

theorem ForallInferenceTrace.output {fuel : Nat} {before after : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body result : KExpr .anon} {info : ExprInfo .anon} {inferOnly : Bool}
    (trace : ForallInferenceTrace fuel before name bi domain body)
    (accepted : RecM.inferUncached RecM.inferCall inferOnly (.all name bi domain body info)
      (methodsN (fuel + 1)) before = .ok result after) :
    result = (trace.bodyState.env.intern.internExpr
      (KExpr.mkSort (KUniv.mkIMax trace.domainLevel trace.bodyLevel))).1 :=
  (trace.output_state accepted).1

/-- The executed checks before lambda inference reduces its body type. -/
structure LambdaBodyTrace (fuel : Nat) (before : TcState .anon)
    (name : Mode.anon.F Name) (bi : Mode.anon.F Lean.BinderInfo)
    (domain body : KExpr .anon) where
  localState : LocalStateInvariant before
  domainLevel : KUniv .anon
  domainInfo : ExprInfo .anon
  domainState : TcState .anon
  opened : KExpr .anon
  fresh : FVarId
  openedState : TcState .anon
  bodyType : KExpr .anon
  bodyState : TcState .anon
  domainRun : RecM.infer domain (methodsN fuel) before =
    .ok (.sort domainLevel domainInfo) domainState
  openRun : TcM.openBinder name bi domain body domainState = .ok (opened, fresh) openedState
  bodyRun : RecM.infer opened (methodsN fuel) openedState = .ok bodyType bodyState

theorem LambdaBodyTrace.domainFrame {fuel : Nat} {before : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo} {domain body : KExpr .anon}
    (trace : LambdaBodyTrace fuel before name bi domain body) :
    LocalStateFrame before trace.domainState :=
  (infer_methodsN_framesLocalState fuel domain).ok trace.localState trace.domainRun

theorem LambdaBodyTrace.domainValid {fuel : Nat} {before : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo} {domain body : KExpr .anon}
    (trace : LambdaBodyTrace fuel before name bi domain body) :
    LocalStateInvariant trace.domainState := trace.domainFrame.invariant trace.localState

theorem LambdaBodyTrace.contextPreserved {fuel : Nat} {before : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo} {domain body : KExpr .anon}
    (trace : LambdaBodyTrace fuel before name bi domain body) :
    trace.domainState.lctx.Equiv before.lctx := trace.domainFrame.context

theorem LambdaBodyTrace.absent {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {context : Model.Context β} {fuel : Nat} {before : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo} {domain body : KExpr .anon}
    (trace : LambdaBodyTrace fuel before name bi domain body)
    (agreement : LocalContextReading resolve locals before.lctx context) :
    (⟨trace.domainState.env.nextFVarId⟩ : FVarId) ∉ locals :=
  trace.domainValid.freshReading (agreement.congr trace.contextPreserved.symm)

/-- The original no-op specialization of the general lambda-body trace. -/
structure LambdaInferenceTrace (fuel : Nat) (before : TcState .anon)
    (name : Mode.anon.F Name) (bi : Mode.anon.F Lean.BinderInfo)
    (domain body : KExpr .anon) extends LambdaBodyTrace fuel before name bi domain body where
  betaUnchanged : cheapBetaPlan? bodyType = none

theorem LambdaInferenceTrace.domainValid {fuel : Nat} {before : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo} {domain body : KExpr .anon}
    (trace : LambdaInferenceTrace fuel before name bi domain body) :
    LocalStateInvariant trace.domainState := trace.toLambdaBodyTrace.domainValid

theorem LambdaInferenceTrace.contextPreserved {fuel : Nat} {before : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo} {domain body : KExpr .anon}
    (trace : LambdaInferenceTrace fuel before name bi domain body) :
    trace.domainState.lctx.Equiv before.lctx := trace.toLambdaBodyTrace.contextPreserved

theorem LambdaInferenceTrace.absent {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {context : Model.Context β} {fuel : Nat} {before : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo} {domain body : KExpr .anon}
    (trace : LambdaInferenceTrace fuel before name bi domain body)
    (agreement : LocalContextReading resolve locals before.lctx context) :
    (⟨trace.domainState.env.nextFVarId⟩ : FVarId) ∉ locals :=
  trace.toLambdaBodyTrace.absent agreement

def LambdaBodyTrace.reduced {fuel : Nat} {before : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body : KExpr .anon} (trace : LambdaBodyTrace fuel before name bi domain body) :=
  cheapBetaReduce trace.bodyType trace.bodyState.env.intern

def LambdaBodyTrace.abstracted {fuel : Nat} {before : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body : KExpr .anon} (trace : LambdaBodyTrace fuel before name bi domain body) :=
  abstractFVars trace.reduced.1 #[trace.fresh] trace.reduced.2

/-- The returned lambda type is the actual abstracted body type, wrapped in
the production Pi constructor and passed through the final intern table. -/
theorem LambdaBodyTrace.output_state {fuel : Nat} {before after : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body result : KExpr .anon} {info : ExprInfo .anon}
    (trace : LambdaBodyTrace fuel before name bi domain body)
    (accepted : RecM.inferUncached RecM.inferCall false (.lam name bi domain body info)
      (methodsN (fuel + 1)) before = .ok result after) :
    result = (trace.abstracted.2.internExpr (KExpr.mkAll () () domain trace.abstracted.1)).1 ∧
      after = {trace.bodyState with
        env := {trace.bodyState.env with
          intern := (trace.abstracted.2.internExpr (KExpr.mkAll () () domain trace.abstracted.1)).2}
        lctx := trace.bodyState.lctx.truncate trace.domainState.lctx.size} := by
  change (RecM.inferUncached RecM.inferCall false (.lam name bi domain body info)).run
    (methodsN (fuel + 1)) before = .ok result after at accepted
  unfold RecM.inferUncached at accepted
  simp only [Bool.not_false, if_true, ReaderT.run_bind] at accepted
  change EStateM.bind (RecM.infer domain (methodsN fuel)) _ before = _ at accepted
  rw [EStateM.bind, trace.domainRun] at accepted
  change (RecM.withLctxScope _).run (methodsN (fuel + 1)) trace.domainState = _ at accepted
  obtain ⟨scopedState, accepted, cleanup⟩ := withLctxScope_success accepted
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at accepted
  change EStateM.bind (TcM.openBinder name bi domain body) _ trace.domainState =
    .ok result scopedState at accepted
  rw [EStateM.bind, trace.openRun] at accepted
  have bodyRun : (RecM.inferCall trace.opened).run (methodsN (fuel + 1))
      trace.openedState = .ok trace.bodyType trace.bodyState := trace.bodyRun
  change EStateM.bind ((RecM.inferCall trace.opened).run (methodsN (fuel + 1)))
    _ trace.openedState = .ok result scopedState at accepted
  rw [EStateM.bind, bodyRun] at accepted
  cases accepted
  exact ⟨rfl, cleanup⟩

theorem LambdaBodyTrace.output {fuel : Nat} {before after : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body result : KExpr .anon} {info : ExprInfo .anon}
    (trace : LambdaBodyTrace fuel before name bi domain body)
    (accepted : RecM.inferUncached RecM.inferCall false (.lam name bi domain body info)
      (methodsN (fuel + 1)) before = .ok result after) :
    result = (trace.abstracted.2.internExpr (KExpr.mkAll () () domain trace.abstracted.1)).1 :=
  (trace.output_state accepted).1

def LambdaInferenceTrace.abstracted {fuel : Nat} {before : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body : KExpr .anon} (trace : LambdaInferenceTrace fuel before name bi domain body) :=
  abstractFVars trace.bodyType #[trace.fresh] trace.bodyState.env.intern

/-- The returned lambda type is the actual abstracted body type, wrapped in
the production Pi constructor and passed through the final intern table. -/
theorem LambdaInferenceTrace.output_state {fuel : Nat} {before after : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body result : KExpr .anon} {info : ExprInfo .anon}
    (trace : LambdaInferenceTrace fuel before name bi domain body)
    (accepted : RecM.inferUncached RecM.inferCall false (.lam name bi domain body info)
      (methodsN (fuel + 1)) before = .ok result after) :
    result = (trace.abstracted.2.internExpr (KExpr.mkAll () () domain trace.abstracted.1)).1 ∧
      after = {trace.bodyState with
        env := {trace.bodyState.env with
          intern := (trace.abstracted.2.internExpr (KExpr.mkAll () () domain trace.abstracted.1)).2}
        lctx := trace.bodyState.lctx.truncate trace.domainState.lctx.size} := by
  change (RecM.inferUncached RecM.inferCall false (.lam name bi domain body info)).run
    (methodsN (fuel + 1)) before = .ok result after at accepted
  unfold RecM.inferUncached at accepted
  simp only [Bool.not_false, if_true, ReaderT.run_bind] at accepted
  change EStateM.bind (RecM.infer domain (methodsN fuel)) _ before = _ at accepted
  rw [EStateM.bind, trace.domainRun] at accepted
  change (RecM.withLctxScope _).run (methodsN (fuel + 1)) trace.domainState = _ at accepted
  obtain ⟨scopedState, accepted, cleanup⟩ := withLctxScope_success accepted
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at accepted
  change EStateM.bind (TcM.openBinder name bi domain body) _ trace.domainState =
    .ok result scopedState at accepted
  rw [EStateM.bind, trace.openRun] at accepted
  have bodyRun : (RecM.inferCall trace.opened).run (methodsN (fuel + 1))
      trace.openedState = .ok trace.bodyType trace.bodyState := trace.bodyRun
  change EStateM.bind ((RecM.inferCall trace.opened).run (methodsN (fuel + 1)))
    _ trace.openedState = .ok result scopedState at accepted
  rw [EStateM.bind, bodyRun] at accepted
  simp only [cheapBetaReduce, trace.betaUnchanged] at accepted
  cases accepted
  exact ⟨rfl, cleanup⟩

theorem LambdaInferenceTrace.output {fuel : Nat} {before after : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body result : KExpr .anon} {info : ExprInfo .anon}
    (trace : LambdaInferenceTrace fuel before name bi domain body)
    (accepted : RecM.inferUncached RecM.inferCall false (.lam name bi domain body info)
      (methodsN (fuel + 1)) before = .ok result after) :
    result = (trace.abstracted.2.internExpr (KExpr.mkAll () () domain trace.abstracted.1)).1 :=
  (trace.output_state accepted).1

/-- Structural and operational support for a finite production inference
tree. The source reading and local-context agreement are inputs to soundness,
so each recursive body's reading must be derived by opening its binder. -/
inductive BinderInference {β : Type u}
    (resolve : Address → Option (ConstRef β)) (entries : Model.Environment β) :
    List FVarId → Model.Context β → Nat → TcState .anon → KExpr .anon →
      AExpr β → AExpr β → Type u
  | sort {locals context fuel before level info}
      (miss : UncachedInference before (.sort level info))
      (coherent : miss.keyed.env.intern.WF)
      (faithful : KExpr.KeyCollisionFree fun term =>
        miss.keyed.env.intern.ExprSupport term ∨ term = KExpr.mkSort (KUniv.mkSucc level)) :
      BinderInference resolve entries locals context fuel before (.sort level info)
        (.sort (readLevel level)) (.sort (.succ (readLevel level)))
  | cachedSort {locals context fuel before level info}
      (hit : InferenceCacheHit before (.sort level info))
      (canonical : hit.cached = KExpr.mkSort (KUniv.mkSucc level)) :
      BinderInference resolve entries locals context fuel before (.sort level info)
        (.sort (readLevel level)) (.sort (.succ (readLevel level)))
  | fvar {locals context fuel before id name info index A}
      (cache : FVarInferenceSupport before id name info)
      (registered : localIndex? locals id = some index)
      (atIndex : context[index]? = some A) :
      BinderInference resolve entries locals context fuel before (.fvar id name info) (.bvar index) A
  | const {locals context fuel before id info ref entry}
      (miss : UncachedInference before (.const id #[] info))
      (resolved : resolve id.addr = some ref)
      (found : entries ref = some entry)
      (monomorphic : entry.universes = 0)
      (stable : entry.type.instL [] = entry.type)
      (lookup : ∀ concrete loaded, TcM.getConst id miss.keyed = .ok concrete loaded →
        readScopedExpr? resolve locals concrete.ty = some entry.type.erase) :
      BinderInference resolve entries locals context fuel before (.const id #[] info)
        (.const ref []) entry.type
  | polymorphic {locals context fuel before id arguments info ref entry type}
      (miss : UncachedInference before (.const id arguments info))
      (support : ScopedConstantInferenceSupport resolve entries miss.keyed id arguments ref entry)
      (prediction : ∀ concrete loaded, TcM.getConst id miss.keyed = .ok concrete loaded →
        readInstantiatedType? resolve concrete.ty arguments = some type.erase)
      (conditions : (entry.type.instL (arguments.toList.map readLevel)).annotations = type.annotations) :
      BinderInference resolve entries locals context fuel before (.const id arguments info)
        (.const ref (arguments.toList.map readLevel)) type
  | cachedConst {locals context fuel before id arguments info ref entry type}
      (cache : CachedConstantInferenceSupport resolve entries before id arguments info ref entry type) :
      BinderInference resolve entries locals context fuel before (.const id arguments info)
        (.const ref (arguments.toList.map readLevel)) type
  | app {locals context fuel before fn arg info f a A A' B condition}
      (full : before.inferOnly = false)
      (miss : UncachedInference before (.app fn arg info))
      (trace : ApplicationInferenceTrace fuel miss.keyed fn arg)
      (functionTree : BinderInference resolve entries locals context fuel miss.keyed fn
        f (.forallE condition A B))
      (head : SynthesisHead f)
      (argumentTree : BinderInference resolve entries locals context fuel trace.functionState arg a A')
      (conditions : A'.annotations = A.annotations)
      (hashPath : (trace.argumentType == trace.domain) = true)
      (comparisonFaithful : trace.argumentType.AddrFaithful trace.domain)
      (bodyConstructed : trace.codomain.Constructed)
      (argConstructed : arg.Constructed)
      (bodyBound : trace.codomain.size + 1 < UInt64.size)
      (argBound : arg.size < UInt64.size)
      (coherent : trace.comparedState.env.intern.WF)
      (faithful : KExpr.CollisionFree fun term => trace.comparedState.env.intern.ExprSupport term ∨
        KExpr.SubstReach arg trace.codomain 0 term) :
      BinderInference resolve entries locals context (fuel + 1) before (.app fn arg info)
        (.app f a) (B.inst a)
  | forallE {locals context fuel before name bi domain body info A B}
      (miss : UncachedInference before (.all name bi domain body info))
      (trace : ForallInferenceTrace fuel miss.keyed name bi domain body)
      (opening : BinderOpeningSupport trace.domainState body)
      (domainTree : BinderInference resolve entries locals context fuel miss.keyed domain
        A (.sort (readLevel trace.domainLevel)))
      (bodyTree : BinderInference resolve entries (trace.fresh :: locals) (context.push A)
        fuel trace.openedState trace.opened B (.sort (readLevel trace.bodyLevel)))
      (levelFaithful : ∀ a b,
        (KUniv.Sub a trace.domainLevel ∨ KUniv.Sub a trace.bodyLevel) →
        (KUniv.Sub b trace.domainLevel ∨ KUniv.Sub b trace.bodyLevel) → a.AddrFaithful b)
      (domainBound : trace.domainLevel.size < UInt64.size)
      (bodyBound : trace.bodyLevel.size < UInt64.size)
      (coherent : trace.bodyState.env.intern.WF)
      (faithful : KExpr.KeyCollisionFree fun term => trace.bodyState.env.intern.ExprSupport term ∨
        term = KExpr.mkSort (KUniv.mkIMax trace.domainLevel trace.bodyLevel)) :
      BinderInference resolve entries locals context (fuel + 1) before (.all name bi domain body info)
        (.forallE (Certified.zeroCondition (readLevel trace.bodyLevel)) A B)
        (.sort (readLevel (KUniv.mkIMax trace.domainLevel trace.bodyLevel)))
  | lam {locals context fuel before name bi domain body info A b B condition}
      (full : before.inferOnly = false)
      (miss : UncachedInference before (.lam name bi domain body info))
      (trace : LambdaInferenceTrace fuel miss.keyed name bi domain body)
      (opening : BinderOpeningSupport trace.domainState body)
      (bodyTree : BinderInference resolve entries (trace.fresh :: locals) (context.push A)
        fuel trace.openedState trace.opened b B)
      (constructed : trace.bodyType.Constructed)
      (bound : trace.bodyType.size + 1 < UInt64.size)
      (coherent : trace.bodyState.env.intern.WF)
      (closingFaithful : KExpr.CollisionFree fun term => trace.bodyState.env.intern.ExprSupport term ∨
        KExpr.AbstractReach ((∅ : Std.HashMap FVarId UInt64).insert trace.fresh 0)
          1 trace.bodyType 0 term)
      (faithful : KExpr.KeyCollisionFree fun term => trace.abstracted.2.ExprSupport term ∨
        term = KExpr.mkAll () () domain trace.abstracted.1) :
      BinderInference resolve entries locals context (fuel + 1) before (.lam name bi domain body info)
        (.lam condition A b) (.forallE condition A B)

/-- Construct the sort leaf from a maintained cache invariant. The production
key and eligible hit/miss observation are derived, including when only the
ignored partition is populated in full mode. -/
def BinderInference.sortOfAgreement {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {fuel : Nat}
    {before : TcState .anon} {level : KUniv .anon} {info : ExprInfo .anon}
    (closed : (KExpr.sort level info).lbr = 0)
    (agreement : InferenceCacheAgreement before ((KExpr.sort level info).addr, emptyCtxAddr)
      (KExpr.mkSort (KUniv.mkSucc level)))
    (coherent : before.env.intern.WF)
    (faithful : KExpr.KeyCollisionFree fun term => before.env.intern.ExprSupport term ∨
      term = KExpr.mkSort (KUniv.mkSucc level)) :
    BinderInference resolve entries locals context fuel before (.sort level info)
      (.sort (readLevel level)) (.sort (.succ (readLevel level))) := by
  rcases observeInferenceCache (inferKey_closed closed before) with
    ⟨hit, keyEq, stateEq⟩ | ⟨miss, _, stateEq⟩
  · refine .cachedSort hit (InferenceCacheAgreement.selected hit ?_)
    simpa only [keyEq, stateEq] using agreement
  · exact .sort miss (by simpa only [stateEq] using coherent)
      (by simpa only [stateEq] using faithful)

/-- Successful production inference reads the expected model type and checks
the actual source term against it. No recursive semantic premise is supplied
by the caller: induction follows the finite operational support tree. -/
theorem BinderInference.soundWithSynthesis {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {fuel : Nat}
    {before after : TcState .anon} {term result : KExpr .anon} {e A : AExpr β}
    (support : BinderInference resolve entries locals context fuel before term e A)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals term = some e.erase)
    (accepted : RecM.infer term (methodsN fuel) before = .ok result after) :
    readScopedExpr? resolve locals result = some A.erase ∧
      CheckingClaim.{u,v} entries context e A ∧
      (SynthesisHead e → TypingClaim.{u,v} entries context e A) := by
  induction support generalizing result after with
  | sort miss coherent faithful =>
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      change EStateM.Result.ok
        (miss.keyed.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc _))).1 _ =
          .ok result state at run
      cases run
      refine ⟨?_, (TypingClaim.sort _).checking, fun head => by cases head⟩
      rw [internExpr_readScopedExpr? coherent faithful]
      simp [AExpr.erase]
  | cachedSort hit canonical =>
      obtain ⟨typeReads, typed⟩ := infer_sort_cached_sound hit canonical accepted
      exact ⟨typeReads, typed.checking, fun head => by cases head⟩
  | fvar cache registered atIndex =>
      obtain ⟨typeReads, typed⟩ := cache.sound agreement registered atIndex accepted
      exact ⟨typeReads, typed.checking, fun _ => typed⟩
  | @const locals context fuel before id info ref entry miss resolved found monomorphic stable lookup =>
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      have typed : TypingClaim.{u,v} entries context (.const ref []) entry.type := by
        simpa only [stable] using
          (TypingClaim.const (Γ := context) (ls := []) found (by simpa using monomorphic.symm))
      exact ⟨inferUncached_monomorphic_const_scoped lookup run, typed.checking, fun _ => typed⟩
  | polymorphic miss support prediction conditions =>
      obtain ⟨typeReads, typed⟩ := infer_const_scoped_annotated miss support prediction conditions accepted
      exact ⟨typeReads, typed.checking, fun _ => typed⟩
  | cachedConst cache =>
      obtain ⟨typeReads, typed⟩ := cache.sound accepted
      exact ⟨typeReads, typed.checking, fun _ => typed⟩
  | @app locals context fuel before fn arg info f a A A' B condition
      full miss trace functionTree head argumentTree conditions hashPath comparisonFaithful
      bodyConstructed argConstructed bodyBound argBound coherent faithful ihFunction ihArgument =>
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      rw [full] at run
      obtain ⟨fnReads, argReads⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨functionTypeReads, _, functionTyped⟩ := ihFunction keyedAgreement fnReads trace.functionRun
      obtain ⟨domainReads, codomainReads⟩ := readScopedExpr?_all_parts functionTypeReads
      have argumentAgreement := keyedAgreement.congr trace.contextPreserved.symm
      obtain ⟨argumentTypeReads, argumentChecked, _⟩ := ihArgument argumentAgreement argReads trace.argumentRun
      have sameReading := beq_readScopedExpr? (resolve := resolve) (locals := locals)
        (depth := 0) comparisonFaithful hashPath
      have sameType := AExpr.eq_of_erase_annotations
        (Option.some.inj (argumentTypeReads.symm.trans (sameReading.trans domainReads))) conditions
      have checked := sameType ▸ argumentChecked
      have typed := (functionTyped head).appChecking checked
      refine ⟨?_, typed.checking, fun _ => typed⟩
      rw [trace.output run, AExpr.erase_inst]
      exact (subst_readScopedExpr? bodyConstructed argConstructed bodyBound argBound
        coherent faithful codomainReads argReads).1
  | forallE miss trace opening domainTree bodyTree levelFaithful domainBound bodyBound
      coherent faithful ihDomain ihBody =>
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_all_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨_, domainChecked, _⟩ := ihDomain keyedAgreement domainReads trace.domainRun
      have domainAgreement := keyedAgreement.congr trace.contextPreserved.symm
      obtain ⟨_, openedReads, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement (trace.domainValid.freshReading domainAgreement) domainReads bodyReads trace.openRun
      obtain ⟨_, bodyChecked, _⟩ := ihBody openedAgreement openedReads trace.bodyRun
      refine ⟨?_, ?_, fun head => by cases head⟩
      · rw [trace.output run, internExpr_readScopedExpr? coherent faithful]
        rfl
      · have formed := TypingClaim.forallE domainChecked.typingSort bodyChecked.typingSort rfl
        exact (AExpr.LevelEquivalent.sort
          (Theory.VLevel.equiv_def.mpr fun levels =>
            (Theory.VLevel.equiv_def.mp (readLevel_mkIMax levelFaithful domainBound bodyBound)
              levels).symm) |>.typing formed).checking
  | lam full miss trace opening bodyTree constructed bound coherent closingFaithful
      faithful ihBody =>
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      rw [full] at run
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_lam_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have domainAgreement := keyedAgreement.congr trace.contextPreserved.symm
      obtain ⟨_, openedReads, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement (trace.domainValid.freshReading domainAgreement) domainReads bodyReads trace.openRun
      obtain ⟨bodyTypeReads, bodyChecked, _⟩ := ihBody openedAgreement openedReads trace.bodyRun
      obtain ⟨closedReads, closedCoherent⟩ := abstractFVars_readScopedExpr? constructed bound coherent
        closingFaithful bodyTypeReads
      refine ⟨?_, bodyChecked.lam, fun head => by cases head⟩
      rw [trace.output run,
        internExpr_readScopedExpr? (table := trace.abstracted.2) closedCoherent faithful]
      simp [LambdaInferenceTrace.abstracted, domainReads, closedReads, AExpr.erase]

/-- The checking conclusion applies to all supported finite trees. -/
theorem BinderInference.sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {fuel : Nat}
    {before after : TcState .anon} {term result : KExpr .anon} {e A : AExpr β}
    (support : BinderInference resolve entries locals context fuel before term e A)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals term = some e.erase)
    (accepted : RecM.infer term (methodsN fuel) before = .ok result after) :
    readScopedExpr? resolve locals result = some A.erase ∧
      CheckingClaim.{u,v} entries context e A := by
  obtain ⟨reads, checked, _⟩ := support.soundWithSynthesis agreement reading accepted
  exact ⟨reads, checked⟩

/-- Constant- and local-headed application spines synthesize full typing,
including hereditary validity of the exact returned dependent type. -/
theorem BinderInference.synthesis {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {fuel : Nat}
    {before after : TcState .anon} {term result : KExpr .anon} {e A : AExpr β}
    (support : BinderInference resolve entries locals context fuel before term e A)
    (head : SynthesisHead e)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals term = some e.erase)
    (accepted : RecM.infer term (methodsN fuel) before = .ok result after) :
    readScopedExpr? resolve locals result = some A.erase ∧ TypingClaim.{u,v} entries context e A := by
  obtain ⟨reads, _, typed⟩ := support.soundWithSynthesis agreement reading accepted
  exact ⟨reads, typed head⟩

end Ix.Kernel.Consistency
