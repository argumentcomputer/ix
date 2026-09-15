/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.SynthesisCacheHistory
import Ix.Kernel.Verify.Consistency.SynthesisCoherence

/-! The original synthesis recursion supplies the annotations of actual cache
publications. Supplementary data concerns only operational resources and child
calls omitted by the older, checking-only BinderInference interface. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

structure SynthesisCacheRun {β : Type u} (resolve : Address → Option (ConstRef β))
    (anchor entries : Model.Environment β) {fuel : Nat} {before after : TcState .anon}
    {source result : KExpr .anon}
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) where
  trace : InferenceCacheTrace.{u} fuel before source
  checks : SynthesisEventChecks resolve anchor entries (trace.events accepted)
  whnf : before.env.intern.WF → trace.WhnfData β
  coherent : before.env.intern.WF → after.env.intern.WF

/-- The older checking-only interface can omit executed domain checks and
loader resources. This supplement records its actual operational tree and
the checks of its child publications. The root check is supplied separately
by the original SynthesisInference node. -/
structure SynthesisCacheSupplement {β : Type u} (resolve : Address → Option (ConstRef β))
    (anchor entries : Model.Environment β) (fuel : Nat) (state : TcState .anon) (source : KExpr .anon) where
  trace : InferenceCacheTrace.{u} fuel state source
  children : SynthesisEventChecks resolve anchor entries trace.childEvents
  whnf : state.env.intern.WF → trace.WhnfData β

namespace SynthesisCacheSupplement

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {fuel : Nat} {before : TcState .anon} {source : KExpr .anon}

def ofLeaf (trace : InferenceCacheTrace.{u} fuel before source) (leaf : trace.childEvents = [])
    (whnf : before.env.intern.WF → trace.WhnfData β) :
    SynthesisCacheSupplement resolve anchor entries fuel before source := ⟨trace, leaf.symm ▸ .nil, whnf⟩

/-- Primitive cache observations require no supplementary checking trees. -/
def sortOfKey {keyed : TcState .anon} {level : KUniv .anon} {info : ExprInfo .anon}
    {key : Address × Address} (run : TcM.inferKey (.sort level info) before = .ok key keyed) :
    SynthesisCacheSupplement resolve anchor entries fuel before (.sort level info) :=
  ofLeaf (.sortOfKey run) (by
    unfold InferenceCacheTrace.sortOfKey
    rcases observeInferenceCache run with ⟨hit, _, _⟩ | ⟨miss, _, _⟩ <;> rfl) (by
    intro _
    unfold InferenceCacheTrace.sortOfKey
    rcases observeInferenceCache run with ⟨hit, _, _⟩ | ⟨miss, _, _⟩ <;> exact PUnit.unit)

def fvarOfKey {keyed : TcState .anon} {id : FVarId} {name : Mode.anon.F Name} {info : ExprInfo .anon}
    {key : Address × Address} (run : TcM.inferKey (.fvar id name info) before = .ok key keyed) :
    SynthesisCacheSupplement resolve anchor entries fuel before (.fvar id name info) :=
  ofLeaf (.fvarOfKey run) (by
    unfold InferenceCacheTrace.fvarOfKey
    rcases observeInferenceCache run with ⟨hit, _, _⟩ | ⟨miss, _, _⟩ <;> rfl) (by
    intro _
    unfold InferenceCacheTrace.fvarOfKey
    rcases observeInferenceCache run with ⟨hit, _, _⟩ | ⟨miss, _, _⟩ <;> exact PUnit.unit)

def verifiedConstOfKey {keyed : TcState .anon} {id : KId .anon} {arguments : Array (KUniv .anon)}
    {info : ExprInfo .anon} {key : Address × Address}
    (run : TcM.inferKey (.const id arguments info) before = .ok key keyed)
    (loader : VerifiedLazySupport keyed id.addr)
    (resources : ∀ concrete loaded, TcM.getConst id keyed = .ok concrete loaded →
      UniverseInstantiationSupport loaded concrete.ty arguments) :
    SynthesisCacheSupplement resolve anchor entries fuel before (.const id arguments info) :=
  ofLeaf (.verifiedConstOfKey run loader resources) (by
    unfold InferenceCacheTrace.verifiedConstOfKey
    rcases observeInferenceCache run with ⟨hit, _, _⟩ | ⟨miss, _, _⟩ <;> rfl) (by
    intro _
    unfold InferenceCacheTrace.verifiedConstOfKey
    rcases observeInferenceCache run with ⟨hit, _, _⟩ | ⟨miss, _, _⟩ <;> exact PUnit.unit)

def complete (data : SynthesisCacheSupplement resolve anchor entries fuel before source)
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel}
    {term type : AExpr β} {level : VLevel} {result : KExpr .anon} {after : TcState .anon}
    (tree : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (contextOrigin : SynthesisContext resolve anchor [] [] entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
    SynthesisCacheRun resolve anchor entries accepted :=
  { trace := data.trace
    whnf := data.whnf
    coherent := fun initial => tree.outputCoherent data.trace initial agreement reading accepted
    checks := by
      rcases data with ⟨trace, children, whnf⟩
      cases trace with
      | hit => exact .nil
      | sort miss | fvar miss | const miss concrete loaded resources | lazyConst miss loader resources =>
          exact .singleton (.ofSource tree contextOrigin agreement reading miss accepted)
      | app full miss trace hashPath functionTree argumentTree =>
          exact children.append (.singleton (.ofSource tree contextOrigin agreement reading miss accepted))
      | appBeta full miss trace exposure hashPath functionTree argumentTree =>
          exact children.append (.singleton (.ofSource tree contextOrigin agreement reading miss accepted))
      | forallE miss trace domainTree bodyTree =>
          exact children.append (.singleton (.ofSource tree contextOrigin agreement reading miss accepted))
      | lam full miss trace domainTree bodyTree =>
          exact children.append (.singleton (.ofSource tree contextOrigin agreement reading miss accepted))
      | lamBody full miss trace domainTree bodyTree =>
          exact children.append (.singleton (.ofSource tree contextOrigin agreement reading miss accepted))
      | letE full miss trace hashPath domainTree valueTree bodyTree =>
          exact children.append (.singleton (.ofSource tree contextOrigin agreement reading miss accepted))
      | forallSort miss trace domainExposure bodyExposure domainTree bodyTree =>
          exact children.append (.singleton (.ofSource tree contextOrigin agreement reading miss accepted))
      | lamSort full miss trace domainExposure domainTree bodyTree =>
          exact children.append (.singleton (.ofSource tree contextOrigin agreement reading miss accepted))
      | letSort full miss trace domainExposure hashPath domainTree valueTree bodyTree =>
          exact children.append (.singleton (.ofSource tree contextOrigin agreement reading miss accepted)) }

end SynthesisCacheSupplement

mutual

/-- Rich synthesis nodes already retain both actual children. Additional
checking annotations are needed only at the older BinderInference wrappers;
primitive leaves supply none. Existing cache hits add no publications. -/
def SynthesisInference.CacheData {β : Type u} {resolve : Address → Option (ConstRef β)}
    (anchor : Model.Environment β) {entries : Model.Environment β} {locals : List FVarId}
    {context : Model.Context β} {bounds : List VLevel} {fuel : Nat} {before : TcState .anon}
    {source : KExpr .anon} {term type : AExpr β} {level : VLevel}
    (tree : SynthesisInference resolve entries locals context bounds fuel before source term type level) : Type (u + 1) :=
  match tree with
  | .known .. | .reuseType .. | .fvar .. => SynthesisCacheSupplement resolve anchor entries fuel before source
  | .cached .. | .cachedFrom .. => PUnit
  | .app _ _ _ first second .. | .appBeta _ _ _ first _ _ _ second .. =>
      first.CacheData anchor × second.CacheData anchor
  | .forallE _ _ _ first second .. | .lam _ _ _ _ first second .. |
    .lamBeta _ _ _ _ first second .. => first.CacheData anchor × second.CacheData anchor
  | .letE _ _ _ _ _ domain value body .. =>
      domain.CacheData anchor × value.CacheData anchor × body.CacheData anchor
  | .forallSort _ _ _ domain body .. => domain.CacheData anchor × body.CacheData anchor
  | .lamSort _ _ _ _ domain body .. => domain.CacheData anchor × body.CacheData anchor
  | .letSort _ _ _ _ _ domain value body .. =>
      domain.CacheData anchor × value.CacheData anchor × body.CacheData anchor
termination_by structural tree

def SynthesisSortCheck.CacheData {β : Type u} {resolve : Address → Option (ConstRef β)}
    (anchor : Model.Environment β) {entries : Model.Environment β} {locals : List FVarId}
    {context : Model.Context β} {bounds : List VLevel} {fuel : Nat} {before : TcState .anon}
    {source : KExpr .anon} {trace : SortInferenceTrace fuel before source} {term : AExpr β}
    (check : SynthesisSortCheck resolve entries locals context bounds trace term) : Type (u + 1) :=
  match check with
  | .checked tree .. => tree.CacheData anchor
termination_by structural check

end

mutual

/-- Extract every full publication's checking origin from the original
synthesis recursion. Binder contexts come from its executed domain checks,
and all child readings and local agreements are derived along the same run. -/
def SynthesisInference.cacheExecution {β : Type u} {resolve : Address → Option (ConstRef β)}
    {anchor entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β}
    {bounds : List VLevel} {fuel : Nat} {before after : TcState .anon} {source result : KExpr .anon}
    {term type : AExpr β} {level : VLevel}
    (tree : SynthesisInference resolve entries locals context bounds fuel before source term type level) :
    tree.CacheData anchor →
    SynthesisContext resolve anchor [] [] entries context bounds →
    LocalContextReading resolve locals before.lctx context →
    readScopedExpr? resolve locals source = some term.erase →
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) →
    SynthesisCacheRun resolve anchor entries accepted :=
  match tree with
  | .known inference formation => fun data contextOrigin agreement reading accepted =>
      data.complete (.known inference formation) contextOrigin agreement reading accepted
  | .reuseType inference typeTree extension typeReading typeRun same =>
      fun data contextOrigin agreement reading accepted =>
        data.complete (.reuseType inference typeTree extension typeReading typeRun same)
          contextOrigin agreement reading accepted
  | .fvar inference atIndex boundAtIndex => fun data contextOrigin agreement reading accepted =>
      data.complete (.fvar inference atIndex boundAtIndex) contextOrigin agreement reading accepted
  | .cached _ _ _ _ hit _ _ | .cachedFrom _ hit _ => fun _ _ _ _ accepted =>
      ⟨.hit hit, .nil, fun _ => PUnit.unit, fun initial => by
        rw [hit.run] at accepted
        cases accepted
        simpa only [inferKey_environment hit.keyRun] using initial⟩
  | .app full miss trace functionTree argumentTree conditions hashPath comparisonFaithful
      bodyConstructed argConstructed bodyBound argBound coherent faithful =>
      fun data contextOrigin agreement reading accepted => by
      obtain ⟨functionReads, argumentReads⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      let functionRun := functionTree.cacheExecution data.1 contextOrigin keyedAgreement functionReads trace.functionRun
      let argumentRun := argumentTree.cacheExecution data.2 contextOrigin
        (keyedAgreement.congr trace.contextPreserved.symm) argumentReads trace.argumentRun
      exact (SynthesisCacheSupplement.mk (.app full miss trace hashPath functionRun.trace argumentRun.trace)
        (functionRun.checks.append argumentRun.checks) (fun initial =>
          let keyed := miss.keyedCoherent initial
          (functionRun.whnf keyed, argumentRun.whnf (functionRun.coherent keyed)))).complete
          (.app full miss trace functionTree argumentTree conditions hashPath comparisonFaithful
            bodyConstructed argConstructed bodyBound argBound coherent faithful)
          contextOrigin agreement reading accepted
  | .appBeta full miss trace functionTree exposure exposureCoherent reduction argumentTree conditions hashPath
      comparisonFaithful bodyConstructed argConstructed bodyBound argBound coherent faithful =>
      fun data contextOrigin agreement reading accepted => by
      obtain ⟨functionReads, argumentReads⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      let functionRun := functionTree.cacheExecution data.1 contextOrigin keyedAgreement functionReads trace.functionRun
      let argumentRun := argumentTree.cacheExecution data.2 contextOrigin
        (keyedAgreement.congr trace.exposure_context.symm) argumentReads trace.argumentRun
      have functionReading := functionTree.outputReading keyedAgreement functionReads trace.functionRun
      exact (SynthesisCacheSupplement.mk (.appBeta full miss trace exposure hashPath functionRun.trace argumentRun.trace)
        (functionRun.checks.append argumentRun.checks) (fun initial =>
          let keyed := miss.keyedCoherent initial
          let functionCoherent := functionRun.coherent keyed
          (functionRun.whnf keyed, ⟨_, _, _, functionReading, functionCoherent⟩,
            argumentRun.whnf (by
              rw [trace.exposure_state exposure]
              exact (exposure.reading functionReading functionCoherent).2.2)))).complete
          (.appBeta full miss trace functionTree exposure exposureCoherent reduction argumentTree conditions hashPath
            comparisonFaithful bodyConstructed argConstructed bodyBound argBound coherent faithful)
          contextOrigin agreement reading accepted
  | .forallE miss trace opening domainTree bodyTree levelFaithful domainBound bodyBound coherent faithful =>
      fun data contextOrigin agreement reading accepted => by
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_all_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      let domainRun := domainTree.cacheExecution data.1 contextOrigin keyedAgreement domainReads trace.domainRun
      obtain ⟨_, openedReads, openedAgreement, openedCoherent⟩ := openBinder_sound opening
        (keyedAgreement.congr trace.contextPreserved.symm) (trace.absent keyedAgreement) domainReads bodyReads trace.openRun
      let bodyRun := bodyTree.cacheExecution data.2
        (.push contextOrigin domainTree keyedAgreement domainReads trace.domainRun) openedAgreement openedReads trace.bodyRun
      exact (SynthesisCacheSupplement.mk (.forallE miss trace domainRun.trace bodyRun.trace)
        (domainRun.checks.append bodyRun.checks) (fun initial =>
          (domainRun.whnf (miss.keyedCoherent initial), bodyRun.whnf openedCoherent))).complete
          (.forallE miss trace opening domainTree bodyTree levelFaithful domainBound bodyBound coherent faithful)
          contextOrigin agreement reading accepted
  | .lam full miss trace opening domainTree bodyTree conditionAgrees constructed bound coherent
      closingFaithful faithful =>
      fun data contextOrigin agreement reading accepted => by
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_lam_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      let domainRun := domainTree.cacheExecution data.1 contextOrigin keyedAgreement domainReads trace.domainRun
      obtain ⟨_, openedReads, openedAgreement, openedCoherent⟩ := openBinder_sound opening
        (keyedAgreement.congr trace.contextPreserved.symm) (trace.absent keyedAgreement) domainReads bodyReads trace.openRun
      let bodyRun := bodyTree.cacheExecution data.2
        (.push contextOrigin domainTree keyedAgreement domainReads trace.domainRun) openedAgreement openedReads trace.bodyRun
      exact (SynthesisCacheSupplement.mk (.lam full miss trace domainRun.trace bodyRun.trace)
        (domainRun.checks.append bodyRun.checks) (fun initial =>
          (domainRun.whnf (miss.keyedCoherent initial), bodyRun.whnf openedCoherent))).complete
          (.lam full miss trace opening domainTree bodyTree conditionAgrees constructed bound coherent
            closingFaithful faithful) contextOrigin agreement reading accepted
  | .lamBeta full miss trace opening domainTree bodyTree origin reduction conditionAgrees
      constructed bound closingFaithful faithful =>
      fun data contextOrigin agreement reading accepted => by
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_lam_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      let domainRun := domainTree.cacheExecution data.1 contextOrigin keyedAgreement domainReads trace.domainRun
      obtain ⟨_, openedReads, openedAgreement, openedCoherent⟩ := openBinder_sound opening
        (keyedAgreement.congr trace.contextPreserved.symm) (trace.absent keyedAgreement) domainReads bodyReads trace.openRun
      let bodyRun := bodyTree.cacheExecution data.2
        (.push contextOrigin domainTree keyedAgreement domainReads trace.domainRun) openedAgreement openedReads trace.bodyRun
      exact (SynthesisCacheSupplement.mk (.lamBody full miss trace domainRun.trace bodyRun.trace)
        (domainRun.checks.append bodyRun.checks) (fun initial =>
          (domainRun.whnf (miss.keyedCoherent initial), bodyRun.whnf openedCoherent))).complete
          (.lamBeta full miss trace opening domainTree bodyTree origin reduction conditionAgrees
            constructed bound closingFaithful faithful) contextOrigin agreement reading accepted
  | .letE full localState miss trace opening domainTree valueTree bodyTree domainReading valueReading bodyReading
      conditions hashPath comparisonFaithful substitution reduction =>
      fun data contextOrigin agreement reading accepted => by
      have keyedValid := miss.keyedLocalState localState
      have keyedAgreement := miss.localContext.symm ▸ agreement
      let domainRun := domainTree.cacheExecution data.1 contextOrigin keyedAgreement domainReading trace.domainRun
      let valueRun := valueTree.cacheExecution data.2.1 contextOrigin
        (keyedAgreement.congr (trace.domainContext keyedValid).symm) valueReading trace.valueRun
      obtain ⟨openedReading, openedAgreement, openedCoherent⟩ :=
        trace.opened_reading opening keyedValid keyedAgreement domainReading bodyReading
      let bodyRun := bodyTree.cacheExecution data.2.2
        (.push contextOrigin domainTree keyedAgreement domainReading trace.domainRun)
        openedAgreement openedReading trace.bodyRun
      exact (SynthesisCacheSupplement.mk
        (.letE full miss trace hashPath domainRun.trace valueRun.trace bodyRun.trace)
        ((domainRun.checks.append valueRun.checks).append bodyRun.checks) (fun initial =>
          let keyed := miss.keyedCoherent initial
          (domainRun.whnf keyed, valueRun.whnf (domainRun.coherent keyed), bodyRun.whnf openedCoherent))).complete
          (.letE full localState miss trace opening domainTree valueTree bodyTree domainReading valueReading bodyReading
            conditions hashPath comparisonFaithful substitution reduction) contextOrigin agreement reading accepted
  | .forallSort miss trace opening domainCheck bodyCheck levelFaithful domainBound bodyBound coherent faithful =>
      fun data contextOrigin agreement reading accepted => by
      obtain ⟨domainReading, bodyReading⟩ := readScopedExpr?_all_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      let domainRun := domainCheck.cacheExecution data.1 contextOrigin keyedAgreement domainReading
      obtain ⟨openedReading, openedAgreement, openedCoherent⟩ :=
        trace.opened_reading opening keyedAgreement domainReading bodyReading
      let bodyRun := bodyCheck.cacheExecution data.2
        (.pushSort contextOrigin domainCheck keyedAgreement domainReading) openedAgreement openedReading
      exact (SynthesisCacheSupplement.mk
        (.forallSort miss trace domainCheck.exposure bodyCheck.exposure domainRun.trace bodyRun.trace)
        (domainRun.checks.append bodyRun.checks) (fun initial =>
          let keyed := miss.keyedCoherent initial
          (domainRun.whnf keyed, domainCheck.historyReading keyedAgreement domainReading (domainRun.coherent keyed),
            bodyRun.whnf openedCoherent,
            bodyCheck.historyReading openedAgreement openedReading (bodyRun.coherent openedCoherent)))).complete
          (.forallSort miss trace opening domainCheck bodyCheck levelFaithful domainBound bodyBound coherent faithful)
          contextOrigin agreement reading accepted
  | .lamSort full miss trace opening domainCheck bodyTree reduction conditionAgrees
      constructed bound coherent closingFaithful faithful => fun data contextOrigin agreement reading accepted => by
      obtain ⟨domainReading, bodyReading⟩ := readScopedExpr?_lam_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      let domainRun := domainCheck.cacheExecution data.1 contextOrigin keyedAgreement domainReading
      obtain ⟨openedReading, openedAgreement, openedCoherent⟩ :=
        trace.opened_reading opening keyedAgreement domainReading bodyReading
      let bodyRun := bodyTree.cacheExecution data.2
        (.pushSort contextOrigin domainCheck keyedAgreement domainReading)
        openedAgreement openedReading trace.bodyRun
      exact (SynthesisCacheSupplement.mk
        (.lamSort full miss trace domainCheck.exposure domainRun.trace bodyRun.trace)
        (domainRun.checks.append bodyRun.checks) (fun initial =>
          let keyed := miss.keyedCoherent initial
          (domainRun.whnf keyed, domainCheck.historyReading keyedAgreement domainReading (domainRun.coherent keyed),
            bodyRun.whnf openedCoherent))).complete
          (.lamSort full miss trace opening domainCheck bodyTree reduction conditionAgrees
            constructed bound coherent closingFaithful faithful) contextOrigin agreement reading accepted
  | .letSort full localState miss trace opening domainCheck valueTree bodyTree domainReading valueReading bodyReading
      conditions hashPath comparisonFaithful substitution reduction =>
      fun data contextOrigin agreement reading accepted => by
      have keyedValid := miss.keyedLocalState localState
      have keyedAgreement := miss.localContext.symm ▸ agreement
      let domainRun := domainCheck.cacheExecution data.1 contextOrigin keyedAgreement domainReading
      let valueRun := valueTree.cacheExecution data.2.1 contextOrigin
        (keyedAgreement.congr (trace.domainContext keyedValid).symm) valueReading trace.valueRun
      obtain ⟨openedReading, openedAgreement, openedCoherent⟩ :=
        trace.opened_reading opening keyedValid keyedAgreement domainReading bodyReading
      let bodyRun := bodyTree.cacheExecution data.2.2
        (.pushSort contextOrigin domainCheck keyedAgreement domainReading)
        openedAgreement openedReading trace.bodyRun
      exact (SynthesisCacheSupplement.mk
        (.letSort full miss trace domainCheck.exposure hashPath domainRun.trace valueRun.trace bodyRun.trace)
        ((domainRun.checks.append valueRun.checks).append bodyRun.checks) (fun initial =>
          let keyed := miss.keyedCoherent initial
          (domainRun.whnf keyed, domainCheck.historyReading keyedAgreement domainReading (domainRun.coherent keyed),
            valueRun.whnf (domainCheck.afterCoherent keyedAgreement domainReading (domainRun.coherent keyed)),
            bodyRun.whnf openedCoherent))).complete
          (.letSort full localState miss trace opening domainCheck valueTree bodyTree domainReading valueReading bodyReading
            conditions hashPath comparisonFaithful substitution reduction) contextOrigin agreement reading accepted
termination_by structural tree

/-- Sort exposure adds no inference-cache writes. The producing inference
event retains the original tree at its actual, possibly unreduced, result type. -/
def SynthesisSortCheck.cacheExecution {β : Type u} {resolve : Address → Option (ConstRef β)}
    {anchor entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β}
    {bounds : List VLevel} {fuel : Nat} {before : TcState .anon} {source : KExpr .anon}
    {trace : SortInferenceTrace fuel before source} {term : AExpr β}
    (check : SynthesisSortCheck resolve entries locals context bounds trace term) :
    check.CacheData anchor →
    SynthesisContext resolve anchor [] [] entries context bounds →
    LocalContextReading resolve locals before.lctx context →
    readScopedExpr? resolve locals source = some term.erase →
    SynthesisCacheRun resolve anchor entries trace.inferRun :=
  match check with
  | .checked tree .. => fun data contextOrigin agreement reading =>
      tree.cacheExecution data contextOrigin agreement reading trace.inferRun
termination_by structural check

end

/-- A successful synthesis call extends the complete typed cache history.
New event annotations are extracted from its original checking tree. -/
def SynthesisCacheHistory.afterSynthesis {β : Type u} {resolve : Address → Option (ConstRef β)}
    {anchor entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β}
    {bounds : List VLevel} {fuel : Nat} {before after : TcState .anon} {source result : KExpr .anon}
    {term type : AExpr β} {level : VLevel}
    (history : SynthesisCacheHistory resolve anchor entries before)
    (tree : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (data : tree.CacheData anchor)
    (contextOrigin : SynthesisContext resolve anchor [] [] entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
    SynthesisCacheHistory resolve anchor entries after :=
  let executed := tree.cacheExecution data contextOrigin agreement reading accepted
  history.afterInference executed.trace accepted executed.checks

end Ix.Kernel.Consistency
