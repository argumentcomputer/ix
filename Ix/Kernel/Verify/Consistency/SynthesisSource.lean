/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.SynthesisReduction
import Ix.Kernel.Verify.Consistency.SynthesisReading
import Ix.Kernel.Verify.Consistency.BinderMeaning

/-! Recover the complete head-beta typing derivation from the source
inference tree. No checks of intermediate reduction results are supplied. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

def BinderInference.betaTyping {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {locals : List FVarId} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon} {term type : AExpr β}
    (support : BinderInference resolve entries locals context fuel before source term type) :
    SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type →
    LocalContextReading resolve locals before.lctx context →
    readScopedExpr? resolve locals source = some term.erase →
    SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context term type :=
  match support with
  | .sort .. | .cachedSort .. | .const .. | .polymorphic .. | .cachedConst .. =>
      fun origin _ _ => .atom origin (by constructor)
  | .forallE miss trace opening domainTree bodyTree .. => fun origin agreement reading => by
      obtain ⟨domainReading, bodyReading⟩ := readScopedExpr?_all_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have domainAgreement := keyedAgreement.congr trace.contextPreserved.symm
      obtain ⟨_, openedReading, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement (trace.absent keyedAgreement)
          domainReading bodyReading trace.openRun
      exact .forallE origin
        (domainTree.betaTyping (.source (.binderType domainTree keyedAgreement domainReading trace.domainRun))
          keyedAgreement domainReading)
        (bodyTree.betaTyping (.source (.binderType bodyTree openedAgreement openedReading trace.bodyRun))
          openedAgreement openedReading) rfl
  | .fvar _ _ atIndex => fun origin _ _ => .bvar origin atIndex
  | .app _ miss trace functionTree head argumentTree conditions hashPath comparisonFaithful _ _ _ _ _ _ =>
      fun _ agreement reading => by
        obtain ⟨functionReading, argumentReading⟩ := readScopedExpr?_app_parts reading
        have keyedAgreement := miss.localContext.symm ▸ agreement
        have argumentAgreement := keyedAgreement.congr trace.contextPreserved.symm
        have functionTypeReads :=
          (BinderInference.synthesis.{u,u} functionTree head keyedAgreement functionReading trace.functionRun).1
        have argumentTypeReads :=
          (BinderInference.sound.{u,u} argumentTree argumentAgreement argumentReading trace.argumentRun).1
        have sameType := AExpr.eq_of_erase_annotations
          (Option.some.inj (argumentTypeReads.symm.trans
            ((beq_readScopedExpr? comparisonFaithful hashPath).trans
              (readScopedExpr?_all_parts functionTypeReads).1))) conditions
        have functionOrigin := SynthesisTypingOrigin.source
          (SynthesisCheckedOrigin.binderHead (incoming := incoming) (incomingContext := incomingContext)
            (incomingBounds := incomingBounds) functionTree head keyedAgreement functionReading trace.functionRun)
        have argumentOrigin := SynthesisTypingOrigin.source
          (SynthesisCheckedOrigin.binderArgument (incoming := incoming) (incomingContext := incomingContext)
            (incomingBounds := incomingBounds) trace functionTree head argumentTree keyedAgreement
            functionReading argumentReading conditions hashPath comparisonFaithful)
        exact .app (functionTree.betaTyping functionOrigin keyedAgreement functionReading)
          (sameType ▸ argumentTree.betaTyping (sameType.symm ▸ argumentOrigin) argumentAgreement argumentReading)
  | .lam _ miss trace opening bodyTree _ _ _ _ _ => fun origin agreement reading => by
      obtain ⟨domainReading, bodyReading⟩ := readScopedExpr?_lam_parts reading
      have domainAgreement := (miss.localContext.symm ▸ agreement).congr trace.contextPreserved.symm
      obtain ⟨_, openedReading, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement (trace.domainValid.freshReading domainAgreement) domainReading bodyReading trace.openRun
      exact .lam origin (bodyTree.betaTyping (.lambdaBody origin) openedAgreement openedReading)
termination_by structural support

mutual

/-- Every currently supported source-inference branch supplies its own
beta derivation. Lambda inference's changed body type becomes a forward
conversion node, retaining the original body's complete checked structure. -/
def SynthesisInference.betaTyping {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds bounds : List VLevel} {locals : List FVarId} {fuel : Nat}
    {before after : TcState .anon} {source result : KExpr .anon} {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source term type level) :
    (contextOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds) →
    LocalContextReading resolve locals before.lctx context →
    readScopedExpr? resolve locals source = some term.erase →
    RecM.infer source (methodsN fuel) before = .ok result after →
    SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context term type :=
  match support with
  | .cached tree priorAgreement priorReading priorRun _ _ _ => fun contextOrigin _ _ _ =>
      tree.betaTyping contextOrigin priorAgreement priorReading priorRun
  | .cachedFrom check _ _ => fun contextOrigin _ _ _ =>
      check.betaTyping.rebase contextOrigin
  | node@(.known inference _) => fun contextOrigin agreement reading accepted =>
      inference.betaTyping (.source (.checked contextOrigin node agreement reading accepted)) agreement reading
  | node@(.reuseType inference ..) => fun contextOrigin agreement reading accepted =>
      inference.betaTyping (.source (.checked contextOrigin node agreement reading accepted)) agreement reading
  | node@(.fvar _ atIndex _) => fun contextOrigin agreement reading accepted =>
      .bvar (.source (.checked contextOrigin node agreement reading accepted)) atIndex
  | .forallE miss trace opening domainTree bodyTree levelFaithful domainBound bodyBound coherent faithful =>
      fun contextOrigin agreement reading accepted => by
        let node := SynthesisInference.forallE miss trace opening domainTree bodyTree levelFaithful
          domainBound bodyBound coherent faithful
        obtain ⟨domainReading, bodyReading⟩ := readScopedExpr?_all_parts reading
        have keyedAgreement := miss.localContext.symm ▸ agreement
        have domainAgreement := keyedAgreement.congr trace.contextPreserved.symm
        obtain ⟨_, openedReading, openedAgreement, _⟩ :=
          openBinder_sound opening domainAgreement (trace.absent keyedAgreement)
            domainReading bodyReading trace.openRun
        exact .forallE (.source (.checked contextOrigin node agreement reading accepted))
          (domainTree.betaTyping contextOrigin keyedAgreement domainReading trace.domainRun)
          (bodyTree.betaTyping (contextOrigin.push domainTree keyedAgreement domainReading trace.domainRun)
            openedAgreement openedReading trace.bodyRun) rfl
  | .app _ miss trace functionTree argumentTree conditions hashPath comparisonFaithful _ _ _ _ _ _ =>
      fun contextOrigin agreement reading _ => by
        obtain ⟨functionReading, argumentReading⟩ := readScopedExpr?_app_parts reading
        have keyedAgreement := miss.localContext.symm ▸ agreement
        have argumentAgreement := keyedAgreement.congr trace.contextPreserved.symm
        have functionTypeReads :=
          functionTree.outputReading keyedAgreement functionReading trace.functionRun
        have argumentTypeReads :=
          argumentTree.outputReading argumentAgreement argumentReading trace.argumentRun
        have sameType := AExpr.eq_of_erase_annotations
          (Option.some.inj (argumentTypeReads.symm.trans
            ((beq_readScopedExpr? comparisonFaithful hashPath).trans
              (readScopedExpr?_all_parts functionTypeReads).1))) conditions
        exact .app (functionTree.betaTyping contextOrigin keyedAgreement functionReading trace.functionRun)
          (sameType ▸ argumentTree.betaTyping contextOrigin argumentAgreement argumentReading trace.argumentRun)
  | .appBeta _ miss trace functionTree exposure exposureCoherent reduction argumentTree conditions hashPath
      comparisonFaithful _ _ _ _ _ _ =>
      fun contextOrigin agreement reading _ => by
        obtain ⟨functionReading, argumentReading⟩ := readScopedExpr?_app_parts reading
        have keyedAgreement := miss.localContext.symm ▸ agreement
        have argumentAgreement := keyedAgreement.congr trace.exposure_context.symm
        have functionTypeReads :=
          functionTree.outputReading keyedAgreement functionReading trace.functionRun
        have argumentTypeReads :=
          argumentTree.outputReading argumentAgreement argumentReading trace.argumentRun
        have sameType := AExpr.eq_of_erase_annotations
          (Option.some.inj (argumentTypeReads.symm.trans
            ((beq_readScopedExpr? comparisonFaithful hashPath).trans
              (exposure.reading functionTypeReads exposureCoherent).1))) conditions
        exact .app
          (.convert (functionTree.betaTyping contextOrigin keyedAgreement functionReading trace.functionRun)
            (.rebase contextOrigin reduction))
          (sameType ▸ argumentTree.betaTyping contextOrigin argumentAgreement argumentReading trace.argumentRun)
  | .lam full miss trace opening domainTree bodyTree conditionAgrees constructed bound coherent
      closingFaithful faithful =>
      fun contextOrigin agreement reading accepted => by
        let node := SynthesisInference.lam full miss trace opening domainTree bodyTree conditionAgrees
          constructed bound coherent closingFaithful faithful
        obtain ⟨domainReading, bodyReading⟩ := readScopedExpr?_lam_parts reading
        have keyedAgreement := miss.localContext.symm ▸ agreement
        have domainAgreement := keyedAgreement.congr trace.contextPreserved.symm
        obtain ⟨_, openedReading, openedAgreement, _⟩ :=
          openBinder_sound opening domainAgreement (trace.domainValid.freshReading domainAgreement) domainReading bodyReading trace.openRun
        exact .lam (.source (.checked contextOrigin node agreement reading accepted))
          (bodyTree.betaTyping (contextOrigin.push domainTree keyedAgreement domainReading trace.domainRun)
            openedAgreement openedReading trace.bodyRun)
  | .lamBeta full miss trace opening domainTree bodyTree reductionOrigin reduction conditionAgrees
      constructed bound closingFaithful faithful =>
      fun contextOrigin agreement reading accepted => by
        let node := SynthesisInference.lamBeta full miss trace opening domainTree bodyTree reductionOrigin reduction
          conditionAgrees constructed bound closingFaithful faithful
        obtain ⟨domainReading, bodyReading⟩ := readScopedExpr?_lam_parts reading
        have keyedAgreement := miss.localContext.symm ▸ agreement
        have domainAgreement := keyedAgreement.congr trace.contextPreserved.symm
        obtain ⟨_, openedReading, openedAgreement, _⟩ :=
          openBinder_sound opening domainAgreement (trace.domainValid.freshReading domainAgreement) domainReading bodyReading trace.openRun
        have inner := bodyTree.betaTyping
          (contextOrigin.push domainTree keyedAgreement domainReading trace.domainRun)
          openedAgreement openedReading trace.bodyRun
        exact .lam (.source (.checked contextOrigin node agreement reading accepted))
          (.convert inner (.rebase contextOrigin (.origin reductionOrigin)))
  | .letE _ localState miss trace opening domainTree valueTree bodyTree domainReading valueReading bodyReading
      conditions hashPath comparisonFaithful _ reduction => fun contextOrigin agreement _ _ => by
        have keyedValid := miss.keyedLocalState localState
        have keyedAgreement := miss.localContext.symm ▸ agreement
        have valueAgreement := keyedAgreement.congr (trace.domainContext keyedValid).symm
        obtain ⟨openedReading, openedAgreement, _⟩ :=
          trace.opened_reading opening keyedValid keyedAgreement domainReading bodyReading
        have valueTypeReading := valueTree.outputReading valueAgreement valueReading trace.valueRun
        have sameType := AExpr.eq_of_erase_annotations
          (Option.some.inj (valueTypeReading.symm.trans
            ((beq_readScopedExpr? comparisonFaithful hashPath).trans domainReading))) conditions
        have bodyContext := SynthesisContext.push .current domainTree keyedAgreement domainReading trace.domainRun
        have bodyTypeOrigin := SynthesisTypingOrigin.inferredType bodyContext bodyTree
          openedAgreement openedReading trace.bodyRun
        have valueOrigin := SynthesisTypingOrigin.source
          (SynthesisCheckedOrigin.checked .current valueTree valueAgreement valueReading trace.valueRun)
        have substitutedType := SynthesisTypingOrigin.substituteAt bodyTypeOrigin (sameType ▸ valueOrigin)
          ContextSubstitution.root
        exact .convert
          ((bodyTree.betaTyping (contextOrigin.push domainTree keyedAgreement domainReading trace.domainRun)
            openedAgreement openedReading trace.bodyRun).substituteAt
              (sameType ▸ valueTree.betaTyping contextOrigin valueAgreement valueReading trace.valueRun) .root)
          (.rebase contextOrigin (reduction.trace substitutedType))
  | .forallSort miss trace opening domainCheck bodyCheck levelFaithful domainBound bodyBound coherent faithful =>
      fun contextOrigin agreement reading accepted => by
        let node := SynthesisInference.forallSort miss trace opening domainCheck bodyCheck
          levelFaithful domainBound bodyBound coherent faithful
        obtain ⟨domainReading, bodyReading⟩ := readScopedExpr?_all_parts reading
        have keyedAgreement := miss.localContext.symm ▸ agreement
        obtain ⟨openedReading, openedAgreement, _⟩ :=
          trace.opened_reading opening keyedAgreement domainReading bodyReading
        exact .forallE (.source (.checked contextOrigin node agreement reading accepted))
          (domainCheck.betaTyping contextOrigin keyedAgreement domainReading)
          (bodyCheck.betaTyping (.pushSort contextOrigin domainCheck keyedAgreement domainReading)
            openedAgreement openedReading) rfl
  | .lamSort full miss trace opening domainCheck bodyTree reduction conditionAgrees
      constructed bound coherent closingFaithful faithful => fun contextOrigin agreement reading accepted => by
        let node := SynthesisInference.lamSort full miss trace opening domainCheck bodyTree reduction
          conditionAgrees constructed bound coherent closingFaithful faithful
        obtain ⟨domainReading, bodyReading⟩ := readScopedExpr?_lam_parts reading
        have keyedAgreement := miss.localContext.symm ▸ agreement
        obtain ⟨openedReading, openedAgreement, _⟩ :=
          trace.opened_reading opening keyedAgreement domainReading bodyReading
        have bodyContext := SynthesisContext.pushSort contextOrigin domainCheck keyedAgreement domainReading
        have typeOrigin := SynthesisTypingOrigin.inferredType .current bodyTree
          openedAgreement openedReading trace.bodyRun
        exact .lam (.source (.checked contextOrigin node agreement reading accepted))
          (.convert (bodyTree.betaTyping bodyContext openedAgreement openedReading trace.bodyRun)
            (.rebase bodyContext (reduction.trace typeOrigin)))
  | .letSort _ localState miss trace opening domainCheck valueTree bodyTree domainReading valueReading bodyReading
      conditions hashPath comparisonFaithful _ reduction => fun contextOrigin agreement _ _ => by
        have keyedValid := miss.keyedLocalState localState
        have keyedAgreement := miss.localContext.symm ▸ agreement
        have valueAgreement := keyedAgreement.congr (trace.domainContext keyedValid).symm
        obtain ⟨openedReading, openedAgreement, _⟩ :=
          trace.opened_reading opening keyedValid keyedAgreement domainReading bodyReading
        have valueTypeReading := valueTree.outputReading valueAgreement valueReading trace.valueRun
        have sameType := AExpr.eq_of_erase_annotations
          (Option.some.inj (valueTypeReading.symm.trans
            ((beq_readScopedExpr? comparisonFaithful hashPath).trans domainReading))) conditions
        have bodyContext := SynthesisContext.pushSort .current domainCheck keyedAgreement domainReading
        have bodyTypeOrigin := SynthesisTypingOrigin.inferredType bodyContext bodyTree
          openedAgreement openedReading trace.bodyRun
        have valueOrigin := SynthesisTypingOrigin.source
          (SynthesisCheckedOrigin.checked .current valueTree valueAgreement valueReading trace.valueRun)
        have substitutedType := SynthesisTypingOrigin.substituteAt bodyTypeOrigin (sameType ▸ valueOrigin)
          ContextSubstitution.root
        exact .convert
          ((bodyTree.betaTyping (contextOrigin.pushSort domainCheck keyedAgreement domainReading)
            openedAgreement openedReading trace.bodyRun).substituteAt
              (sameType ▸ valueTree.betaTyping contextOrigin valueAgreement valueReading trace.valueRun) .root)
          (.rebase contextOrigin (reduction.trace substitutedType))
termination_by structural support

/-- The exposed sort is justified by the original inferred-type conversion;
the source derivation retains the checked term before and after that conversion. -/
def SynthesisSortCheck.betaTyping {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds bounds : List VLevel} {locals : List FVarId} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon} {trace : SortInferenceTrace fuel before source}
    {term : AExpr β} (check : SynthesisSortCheck resolve entries locals context bounds trace term) :
    (contextOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds) →
    LocalContextReading resolve locals before.lctx context →
    readScopedExpr? resolve locals source = some term.erase →
    SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context
      term (.sort (readLevel trace.level)) :=
  match check with
  | .checked tree _ reduction => fun contextOrigin agreement reading =>
      .convert (tree.betaTyping contextOrigin agreement reading trace.inferRun) (.rebase contextOrigin reduction)
termination_by structural check

def SynthesisRetainedCheck.betaTyping {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β} {level : VLevel}
    (check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type level) :
      SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context term type :=
  match check with
  | .source contextOrigin tree agreement reading accepted =>
      tree.betaTyping contextOrigin agreement reading accepted
  | .extend prior extension => prior.betaTyping.extend extension
  | .weakenAt prior insertion => prior.betaTyping.weakenAt insertion
  | .rebase origin prior => prior.betaTyping.rebase origin
termination_by structural check

end


end Ix.Kernel.Consistency
