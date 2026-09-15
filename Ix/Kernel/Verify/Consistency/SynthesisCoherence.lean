/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.InferenceWhnfHistory

/-! Original checking resources preserve intern coherence at the returned
state. The operational cache tree supplies loader and universe-walk data at
primitive constants; no semantic typing invariant is assumed. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

theorem UncachedInference.keyedCoherent {before : TcState .anon} {source : KExpr .anon}
    (miss : UncachedInference before source) (initial : before.env.intern.WF) : miss.keyed.env.intern.WF := by
  simpa only [inferKey_environment miss.keyRun] using initial

theorem infer_miss_coherent {fuel : Nat} {before after : TcState .anon} {source result : KExpr .anon}
    (miss : UncachedInference before source)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after)
    (body : ∀ middle,
      RecM.inferUncached RecM.inferCall before.inferOnly source (methodsN fuel) miss.keyed = .ok result middle →
      middle.env.intern.WF) : after.env.intern.WF := by
  obtain ⟨middle, run, written⟩ := infer_uncached_success_state miss accepted
  have coherent := body middle run
  rw [written]
  split <;> exact coherent

theorem InferenceCacheTrace.const_coherent {fuel : Nat} {before after : TcState .anon}
    {id : KId .anon} {arguments : Array (KUniv .anon)} {info : ExprInfo .anon} {result : KExpr .anon}
    (tree : InferenceCacheTrace.{u} fuel before (.const id arguments info)) (coherent : before.env.intern.WF)
    (accepted : RecM.infer (.const id arguments info) (methodsN fuel) before = .ok result after) :
    after.env.intern.WF := by
  cases tree with
  | hit cached =>
      rw [cached.run] at accepted
      cases accepted
      simpa only [inferKey_environment cached.keyRun] using coherent
  | const miss concrete loaded resources =>
      apply infer_miss_coherent miss accepted
      intro middle run
      obtain ⟨actual, foundState, got, _, instantiated⟩ := inferUncached_const_instantiation run
      rw [getConst_loaded loaded] at got
      cases got
      have post := TcM.instantiateUnivParams_wf resources.faithful
        (fun _ h => Or.inr h) ⟨resources.coherent, fun _ h => Or.inl h⟩
      rw [instantiated] at post
      exact post.1.1
  | lazyConst miss loader resources =>
      apply infer_miss_coherent miss accepted
      intro middle run
      obtain ⟨concrete, foundState, got, _, instantiated⟩ := inferUncached_const_instantiation run
      have resource := resources concrete foundState got
      have post := TcM.instantiateUnivParams_wf resource.faithful
        (fun _ h => Or.inr h) ⟨resource.coherent, fun _ h => Or.inl h⟩
      rw [instantiated] at post
      exact post.1.1

theorem InferenceCacheTrace.fvar_coherent {fuel : Nat} {before after : TcState .anon}
    {id : FVarId} {name : Mode.anon.F Name} {info : ExprInfo .anon} {result : KExpr .anon}
    (tree : InferenceCacheTrace.{u} fuel before (.fvar id name info)) (coherent : before.env.intern.WF)
    (accepted : RecM.infer (.fvar id name info) (methodsN fuel) before = .ok result after) :
    after.env.intern.WF := by
  cases tree with
  | hit cached =>
      rw [cached.run] at accepted
      cases accepted
      simpa only [inferKey_environment cached.keyRun] using coherent
  | fvar miss =>
      apply infer_miss_coherent miss accepted
      intro middle run
      change (RecM.inferUncached RecM.inferCall before.inferOnly (.fvar id name info)).run (methodsN fuel) miss.keyed = _ at run
      unfold RecM.inferUncached at run
      simp only [ReaderT.run_bind] at run
      change EStateM.bind (get : TcM .anon (TcState .anon)) _ miss.keyed = _ at run
      rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) miss.keyed = .ok miss.keyed miss.keyed from rfl] at run
      dsimp only at run
      split at run
      · cases run
        simpa only [inferKey_environment miss.keyRun] using coherent
      · contradiction

theorem BinderInference.outputCoherent {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {fuel : Nat}
    {before after : TcState .anon} {source result : KExpr .anon} {term type : AExpr β}
    (support : BinderInference resolve entries locals context fuel before source term type)
    (tree : InferenceCacheTrace.{u} fuel before source) (initial : before.env.intern.WF)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) : after.env.intern.WF := by
  cases support with
  | @sort locals context fuel before level info miss coherent faithful =>
      apply infer_miss_coherent miss accepted
      intro middle run
      change EStateM.Result.ok (miss.keyed.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).1
        {miss.keyed with env := {miss.keyed.env with intern :=
          (miss.keyed.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).2}} = .ok result middle at run
      cases run
      exact coherent.internExpr _
  | cachedSort cached canonical =>
      rw [cached.run] at accepted
      cases accepted
      simpa only [inferKey_environment cached.keyRun] using initial
  | fvar => exact tree.fvar_coherent initial accepted
  | const | polymorphic | cachedConst => exact tree.const_coherent initial accepted
  | app full miss trace functionTree head argumentTree conditions hashPath comparisonFaithful
      bodyConstructed argConstructed bodyBound argBound coherent faithful =>
      apply infer_miss_coherent miss accepted
      intro middle run
      rw [full] at run
      rw [(trace.output_state run).2]
      exact (subst_spec (depth := 0) faithful bodyConstructed argConstructed
        (by simpa using (show trace.codomain.size < UInt64.size by omega)) argBound
        (fun _ h => Or.inr h) coherent (fun _ h => Or.inl h)).2.1
  | forallE miss trace opening domainTree bodyTree levelFaithful domainBound bodyBound coherent faithful =>
      apply infer_miss_coherent miss accepted
      intro middle run
      rw [(trace.output_state run).2]
      exact coherent.internExpr _
  | lam full miss trace opening bodyTree constructed bound coherent closingFaithful faithful =>
      apply infer_miss_coherent miss accepted
      intro middle run
      rw [full] at run
      have closed := (abstractFVars_singleton_spec constructed (by omega) closingFaithful coherent
        (fun _ h => Or.inl h) (fun _ h => Or.inr h)).2
      rw [(trace.output_state run).2]
      exact closed.internExpr _

/-- Coherence follows the actual final construction of each checking node.
In particular, returning a cached type uses the current table's coherence. -/
theorem SynthesisInference.outputCoherent {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {fuel : Nat}
    {before after : TcState .anon} {source result : KExpr .anon}
    {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (tree : InferenceCacheTrace.{u} fuel before source) (initial : before.env.intern.WF)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) : after.env.intern.WF :=
  match support with
  | .known inference _ | .reuseType inference .. | .fvar inference .. =>
      inference.outputCoherent tree initial accepted
  | .cached _ _ _ _ observed _ _ | .cachedFrom _ observed _ => by
      rw [observed.run] at accepted
      cases accepted
      simpa only [inferKey_environment observed.keyRun] using initial
  | .app full miss trace _ _ _ _ _ bodyConstructed argConstructed bodyBound argBound coherent faithful |
    .appBeta full miss trace _ _ _ _ _ _ _ _ bodyConstructed argConstructed bodyBound argBound coherent faithful => by
      apply infer_miss_coherent miss accepted
      intro middle run
      rw [full] at run
      rw [(trace.output_state run).2]
      exact (subst_spec (depth := 0) faithful bodyConstructed argConstructed
        (by simpa using (show trace.codomain.size < UInt64.size by omega)) argBound
        (fun _ h => Or.inr h) coherent (fun _ h => Or.inl h)).2.1
  | .forallE miss trace _ _ _ _ _ _ coherent _ |
    .forallSort miss trace _ _ _ _ _ _ coherent _ => by
      apply infer_miss_coherent miss accepted
      intro middle run
      rw [(trace.output_state run).2]
      exact coherent.internExpr _
  | .lam full miss trace _ _ _ _ constructed bound coherent closingFaithful _ => by
      apply infer_miss_coherent miss accepted
      intro middle run
      rw [full] at run
      have closed := (abstractFVars_singleton_spec constructed (by omega) closingFaithful coherent
        (fun _ h => Or.inl h) (fun _ h => Or.inr h)).2
      rw [(trace.output_state run).2]
      exact closed.internExpr _
  | .lamBeta full miss trace opening _ bodyTree _ reduction _ constructed bound closingFaithful _ => by
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_lam_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have domainAgreement := keyedAgreement.congr trace.contextPreserved.symm
      obtain ⟨_, openedReads, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement (trace.absent keyedAgreement) domainReads bodyReads trace.openRun
      have bodyTypeReads := bodyTree.outputReading openedAgreement openedReads trace.bodyRun
      obtain ⟨_, reducedReads, reducedCoherent⟩ := reduction.reading bodyTypeReads
      have closed := (abstractFVars_singleton_spec constructed (by omega) closingFaithful reducedCoherent
        (fun _ h => Or.inl h) (fun _ h => Or.inr h)).2
      apply infer_miss_coherent miss accepted
      intro middle run
      rw [full] at run
      rw [(trace.output_state run).2]
      exact closed.internExpr _
  | .letE full localState miss trace opening _ _ bodyTree domainReading valueReading bodyReading
      _ _ _ substitution reduction => by
      have keyedValid := miss.keyedLocalState localState
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨openedReading, openedAgreement, _⟩ :=
        trace.opened_reading opening keyedValid keyedAgreement domainReading bodyReading
      have bodyTypeReading := bodyTree.outputReading openedAgreement openedReading trace.bodyRun
      obtain ⟨substitutedReading, substitutedCoherent⟩ :=
        trace.substituted_reading substitution bodyTypeReading valueReading
      have reduced := (reduction.reading substitutedCoherent substitutedReading).2
      apply infer_miss_coherent miss accepted
      intro middle run
      rw [full] at run
      rw [(trace.output_state run).2]
      exact reduced
  | .lamSort full miss trace opening _ bodyTree reduction _ constructed bound coherent closingFaithful _ => by
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_lam_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨openedReads, openedAgreement, _⟩ := trace.opened_reading opening keyedAgreement domainReads bodyReads
      have bodyTypeReads := bodyTree.outputReading openedAgreement openedReads trace.bodyRun
      obtain ⟨reducedReads, reducedCoherent⟩ := reduction.reading coherent bodyTypeReads
      have closed := (abstractFVars_singleton_spec constructed (by omega) closingFaithful reducedCoherent
        (fun _ h => Or.inl h) (fun _ h => Or.inr h)).2
      apply infer_miss_coherent miss accepted
      intro middle run
      rw [full] at run
      rw [(trace.output_state run).2]
      exact closed.internExpr _
  | .letSort full localState miss trace opening _ _ bodyTree domainReading valueReading bodyReading
      _ _ _ substitution reduction => by
      have keyedValid := miss.keyedLocalState localState
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨openedReading, openedAgreement, _⟩ :=
        trace.opened_reading opening keyedValid keyedAgreement domainReading bodyReading
      have bodyTypeReading := bodyTree.outputReading openedAgreement openedReading trace.bodyRun
      obtain ⟨substitutedReading, substitutedCoherent⟩ :=
        trace.substituted_reading substitution bodyTypeReading valueReading
      have reduced := (reduction.reading substitutedCoherent substitutedReading).2
      apply infer_miss_coherent miss accepted
      intro middle run
      rw [full] at run
      rw [(trace.output_state run).2]
      exact reduced

/-- The inferred type's reading comes from the executed source check. -/
def SynthesisSortCheck.historyReading {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel}
    {fuel : Nat} {before : TcState .anon} {source : KExpr .anon}
    {trace : SortInferenceTrace fuel before source} {term : AExpr β}
    (check : SynthesisSortCheck resolve entries locals context bounds trace term)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : trace.inferredState.env.intern.WF) : BetaHistoryReading β trace.inferredState trace.inferred :=
  match check with
  | .checked tree .. => ⟨resolve, locals, _, tree.outputReading agreement reading trace.inferRun, coherent⟩

/-- Sort exposure preserves coherence at the executed check's exit state. -/
theorem SynthesisSortCheck.afterCoherent {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel}
    {fuel : Nat} {before : TcState .anon} {source : KExpr .anon}
    {trace : SortInferenceTrace fuel before source} {term : AExpr β}
    (check : SynthesisSortCheck resolve entries locals context bounds trace term)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : trace.inferredState.env.intern.WF) : trace.after.env.intern.WF :=
  match check with
  | .checked tree exposure _ => by
      rw [trace.exposure_state exposure]
      exact exposure.coherent (tree.outputReading agreement reading trace.inferRun) coherent

end Ix.Kernel.Consistency
