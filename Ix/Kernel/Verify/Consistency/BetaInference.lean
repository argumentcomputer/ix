/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaTyping

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
  | .sort .. | .cachedSort .. | .const .. | .polymorphic .. | .cachedConst .. | .forallE .. =>
      fun origin _ _ => .atom origin (by constructor)
  | .fvar _ _ atIndex => fun origin _ _ => .bvar origin atIndex
  | .app _ miss trace functionTree head argumentTree conditions hashPath comparisonFaithful _ _ _ _ _ _ =>
      fun _ agreement reading => by
        obtain ⟨functionReading, argumentReading⟩ := readScopedExpr?_app_parts reading
        have keyedAgreement := miss.localContext.symm ▸ agreement
        have argumentAgreement := trace.contextPreserved.symm ▸ keyedAgreement
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
  | .lam _ miss trace opening absent bodyTree _ _ _ _ _ => fun origin agreement reading => by
      obtain ⟨domainReading, bodyReading⟩ := readScopedExpr?_lam_parts reading
      have domainAgreement := trace.contextPreserved.symm ▸ (miss.localContext.symm ▸ agreement)
      obtain ⟨_, openedReading, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement absent domainReading bodyReading trace.openRun
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
    ContextFormation.{u,v} incoming incomingContext incomingBounds →
    SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context term type :=
  match support with
  | .cached tree priorAgreement priorReading priorRun _ _ _ => fun contextOrigin _ _ _ formed =>
      tree.betaTyping contextOrigin priorAgreement priorReading priorRun formed
  | .cachedFrom check _ _ => fun contextOrigin _ _ _ formed =>
      (check.betaTyping (contextOrigin.sound formed)).rebase contextOrigin
  | node@(.known inference _) => fun contextOrigin agreement reading accepted _ =>
      inference.betaTyping (.source (.checked contextOrigin node agreement reading accepted)) agreement reading
  | node@(.reuseType inference ..) => fun contextOrigin agreement reading accepted _ =>
      inference.betaTyping (.source (.checked contextOrigin node agreement reading accepted)) agreement reading
  | node@(.fvar _ atIndex _) => fun contextOrigin agreement reading accepted _ =>
      .bvar (.source (.checked contextOrigin node agreement reading accepted)) atIndex
  | node@(.forallE ..) => fun contextOrigin agreement reading accepted _ =>
      .atom (.source (.checked contextOrigin node agreement reading accepted)) (by constructor)
  | .app _ miss trace functionTree argumentTree conditions hashPath comparisonFaithful _ _ _ _ _ _ =>
      fun contextOrigin agreement reading _ formed => by
        obtain ⟨functionReading, argumentReading⟩ := readScopedExpr?_app_parts reading
        have keyedAgreement := miss.localContext.symm ▸ agreement
        have argumentAgreement := trace.contextPreserved.symm ▸ keyedAgreement
        have contextFormation := contextOrigin.sound formed
        have functionTypeReads :=
          (functionTree.soundWithSpine contextFormation keyedAgreement functionReading trace.functionRun).1
        have argumentTypeReads :=
          (argumentTree.soundWithSpine contextFormation argumentAgreement argumentReading trace.argumentRun).1
        have sameType := AExpr.eq_of_erase_annotations
          (Option.some.inj (argumentTypeReads.symm.trans
            ((beq_readScopedExpr? comparisonFaithful hashPath).trans
              (readScopedExpr?_all_parts functionTypeReads).1))) conditions
        exact .app (functionTree.betaTyping contextOrigin keyedAgreement functionReading trace.functionRun formed)
          (sameType ▸ argumentTree.betaTyping contextOrigin argumentAgreement argumentReading trace.argumentRun formed)
  | .appBeta _ miss trace functionTree exposure exposureCoherent reduction argumentTree conditions hashPath
      comparisonFaithful _ _ _ _ _ _ =>
      fun contextOrigin agreement reading _ formed => by
        obtain ⟨functionReading, argumentReading⟩ := readScopedExpr?_app_parts reading
        have keyedAgreement := miss.localContext.symm ▸ agreement
        have argumentAgreement := (trace.exposure_context exposure).symm ▸ keyedAgreement
        have contextFormation := contextOrigin.sound formed
        have functionTypeReads :=
          (functionTree.soundWithSpine contextFormation keyedAgreement functionReading trace.functionRun).1
        have argumentTypeReads :=
          (argumentTree.soundWithSpine contextFormation argumentAgreement argumentReading trace.argumentRun).1
        have sameType := AExpr.eq_of_erase_annotations
          (Option.some.inj (argumentTypeReads.symm.trans
            ((beq_readScopedExpr? comparisonFaithful hashPath).trans
              (exposure.reading functionTypeReads exposureCoherent).1))) conditions
        exact .app
          (.convert (functionTree.betaTyping contextOrigin keyedAgreement functionReading trace.functionRun formed)
            (.rebase contextOrigin reduction))
          (sameType ▸ argumentTree.betaTyping contextOrigin argumentAgreement argumentReading trace.argumentRun formed)
  | .lam full miss trace opening absent domainTree bodyTree conditionAgrees constructed bound coherent
      closingFaithful faithful =>
      fun contextOrigin agreement reading accepted formed => by
        let node := SynthesisInference.lam full miss trace opening absent domainTree bodyTree conditionAgrees
          constructed bound coherent closingFaithful faithful
        obtain ⟨domainReading, bodyReading⟩ := readScopedExpr?_lam_parts reading
        have keyedAgreement := miss.localContext.symm ▸ agreement
        have domainAgreement := trace.contextPreserved.symm ▸ keyedAgreement
        obtain ⟨_, openedReading, openedAgreement, _⟩ :=
          openBinder_sound opening domainAgreement absent domainReading bodyReading trace.openRun
        exact .lam (.source (.checked contextOrigin node agreement reading accepted))
          (bodyTree.betaTyping (contextOrigin.push domainTree keyedAgreement domainReading trace.domainRun)
            openedAgreement openedReading trace.bodyRun formed)
  | .lamBeta full miss trace opening absent domainTree bodyTree reductionOrigin reduction conditionAgrees
      constructed bound closingFaithful faithful =>
      fun contextOrigin agreement reading accepted formed => by
        let node := SynthesisInference.lamBeta full miss trace opening absent domainTree bodyTree reductionOrigin reduction
          conditionAgrees constructed bound closingFaithful faithful
        obtain ⟨domainReading, bodyReading⟩ := readScopedExpr?_lam_parts reading
        have keyedAgreement := miss.localContext.symm ▸ agreement
        have domainAgreement := trace.contextPreserved.symm ▸ keyedAgreement
        obtain ⟨_, openedReading, openedAgreement, _⟩ :=
          openBinder_sound opening domainAgreement absent domainReading bodyReading trace.openRun
        have inner := bodyTree.betaTyping
          (contextOrigin.push domainTree keyedAgreement domainReading trace.domainRun)
          openedAgreement openedReading trace.bodyRun formed
        exact .lam (.source (.checked contextOrigin node agreement reading accepted))
          (.convert inner (.rebase contextOrigin (.origin reductionOrigin)))
termination_by structural support

def SynthesisRetainedCheck.betaTyping {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β} {level : VLevel}
    (check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type level) :
    ContextFormation.{u,v} incoming incomingContext incomingBounds →
      SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context term type :=
  match check with
  | .source contextOrigin tree agreement reading accepted => fun formed =>
      tree.betaTyping contextOrigin agreement reading accepted formed
  | .extend prior extension => fun formed => (prior.betaTyping formed).extend extension
  | .weakenAt prior insertion => fun formed => (prior.betaTyping formed).weakenAt insertion
  | .rebase origin prior => fun formed => (prior.betaTyping (origin.sound formed)).rebase origin
termination_by structural check

end

theorem SynthesisInference.beta_steps_sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β} {bounds : List VLevel} {locals : List FVarId}
    {fuel : Nat} {before after : TcState .anon} {source result : KExpr .anon}
    {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) (count : Nat) :
    ConversionClaim.{u,v} entries context term (BetaSyntax.steps count term) ∧
      TypingClaim.{u,v} entries context (BetaSyntax.steps count term) type :=
  ((support.betaTyping .current agreement reading accepted formed).betaSteps count).2.sound formed

end Ix.Kernel.Consistency
