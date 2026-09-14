/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.SynthesisInference
import Ix.Kernel.Verify.Consistency.BetaSubstitution
import Ix.Kernel.Verify.Whnf.Beta.DirectStep
import Ix.Theory.Model.Substitution

/-!
Beta reduction from the actual inference of a source redex. Inverting the
finite inference tree retains the checked lambda domain, which semantic
typing alone cannot recover when proof values have been identified.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- Lambda inference returns a product with the source lambda's domain
and condition. This fact comes from the executed inference tree. -/
theorem BinderInference.lambda_type {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon}
    {condition : Certified.PropWhen} {domain body type : AExpr β}
    (support : BinderInference resolve entries locals context fuel before source
      (.lam condition domain body) type) :
    ∃ codomain, type = .forallE condition domain codomain := by
  cases support with
  | lam => exact ⟨_, rfl⟩

theorem SynthesisInference.lambda_type {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon} {level : VLevel}
    {condition : Certified.PropWhen} {domain body type : AExpr β}
    (support : SynthesisInference resolve entries locals context bounds fuel before source
      (.lam condition domain body) type level) :
    ∃ codomain, type = .forallE condition domain codomain := by
  have leading := support.lambdaPrefix
  cases leading with
  | lam => exact ⟨_, rfl⟩

private theorem BinderInference.no_direct_beta {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon}
    {condition : Certified.PropWhen} {domain body argument type : AExpr β}
    (support : BinderInference resolve entries locals context fuel before source
      (.app (.lam condition domain body) argument) type) : False := by
  cases support with
  | app _ _ _ _ head => cases head

private theorem lambda_inference_domain {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β}
    {bounds : List VLevel} {fuel : Nat} {before : TcState .anon} {source : KExpr .anon}
    {condition inferredCondition : Certified.PropWhen} {domain body inferredDomain codomain : AExpr β}
    {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source
      (.lam condition domain body) (.forallE inferredCondition inferredDomain codomain) level) :
    condition = inferredCondition ∧ domain = inferredDomain := by
  obtain ⟨actualBody, same⟩ := support.lambda_type
  cases same
  exact ⟨rfl, rfl⟩

/-- A beta result retains the lambda's original check and the actual
argument check. No inference call on the substituted body is introduced. -/
def SynthesisInference.betaResultOrigin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds bounds : List VLevel} {locals : List FVarId} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon} {level : VLevel}
    {condition : Certified.PropWhen} {domain body argument type : AExpr β}
    (support : SynthesisInference resolve entries locals context bounds fuel before source
      (.app (.lam condition domain body) argument) type level)
    (contextOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source =
      some (AExpr.app (.lam condition domain body) argument).erase) :
    SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context (body.inst argument) type := by
  cases support with
  | known inference _ => exact False.elim inference.no_direct_beta
  | reuseType inference => exact False.elim inference.no_direct_beta
  | cached tree priorAgreement priorReading _ _ _ _ =>
      exact tree.betaResultOrigin contextOrigin priorAgreement priorReading
  | cachedFrom check _ _ =>
      have trace := (check.spineOrigin (.lam condition domain body) [argument] rfl).betaTrace
        (count := 1) (by simp only [AExpr.lambdaDepth]; omega)
      simpa only [AExpr.betaPrefix, AExpr.appN_cons, AExpr.appN_nil] using
        SynthesisTypingOrigin.rebase contextOrigin (.reduced trace)
  | app full miss trace functionTree argumentTree conditions hashPath comparisonFaithful
      bodyConstructed argConstructed bodyBound argBound coherent faithful =>
      obtain ⟨rfl, rfl⟩ := lambda_inference_domain functionTree
      obtain ⟨functionReads, argumentReads⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      exact (SynthesisTypingOrigin.lambdaBody
        (.source (.checked contextOrigin functionTree keyedAgreement functionReads trace.functionRun))).substituteAt
        (.source (.applicationArgument contextOrigin trace functionTree argumentTree keyedAgreement
          functionReads argumentReads conditions hashPath comparisonFaithful)) .root
  | appBeta full miss trace functionTree exposure exposureCoherent reduction argumentTree conditions hashPath
      comparisonFaithful bodyConstructed argConstructed bodyBound argBound coherent faithful =>
      have same := reduction.rigid (by
        obtain ⟨_, rfl⟩ := functionTree.lambda_type
        intro fn arg same
        cases same)
      cases same
      obtain ⟨rfl, rfl⟩ := lambda_inference_domain functionTree
      obtain ⟨functionReads, argumentReads⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      exact (SynthesisTypingOrigin.lambdaBody
        (.source (.checked contextOrigin functionTree keyedAgreement functionReads trace.functionRun))).substituteAt
        (.source (.applicationBetaArgument contextOrigin trace functionTree exposure exposureCoherent argumentTree
          keyedAgreement functionReads argumentReads conditions hashPath comparisonFaithful)) .root

termination_by sizeOf support

/-- Inserting a local preserves both ends of a retained reduction and
all arguments in its checked prefix. -/
def SynthesisReductionOrigin.weakenAt {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext source target : Model.Context β}
    {incomingBounds : List VLevel} {head : AExpr β} {arguments : List (AExpr β)}
    {count cutoff : Nat} {level : VLevel}
    (origin : SynthesisReductionOrigin resolve incoming incomingContext incomingBounds entries source
      head arguments count level) (insertion : ContextInsertion source target cutoff) :
    SynthesisReductionOrigin resolve incoming incomingContext incomingBounds entries target
      (head.liftN 1 cutoff) (arguments.map (AExpr.liftN 1 · cutoff)) count level :=
  .traced (by simpa only [AExpr.liftN_appN, AExpr.liftN_betaPrefix, AExpr.liftN] using
    SynthesisBetaTrace.weakenAt (.origin origin) insertion)

mutual

/-- When the lambda body applies its parameter, its actual body checks
supply the next reduction origin after beta exposes the supplied lambda.
The source's result type comes from the preceding check even if the body
was originally inferred at a type requiring cheap-beta conversion. -/
private def SynthesisInference.betaNextOriginAux {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds bounds : List VLevel} {locals : List FVarId} {fuel count : Nat}
    {before : TcState .anon} {source : KExpr .anon} {level bound : VLevel}
    {condition headCondition : Certified.PropWhen} {term domain binder inner type : AExpr β}
    {initialArguments arguments : List (AExpr β)}
    (support : SynthesisInference resolve entries locals context bounds fuel before source term type bound)
    (contextOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (enough : count ≤ inner.lambdaDepth + 1) (resultEquation : AExpr.sort level = type) :
    term = .app (.lam condition domain ((AExpr.bvar 0).appN arguments))
      ((AExpr.lam headCondition binder inner).appN initialArguments) →
    SynthesisReductionOrigin resolve incoming incomingContext incomingBounds entries context
      (.lam headCondition binder inner)
      (initialArguments ++ arguments.map (AExpr.inst · ((AExpr.lam headCondition binder inner).appN initialArguments)))
      count level :=
  match support with
  | .known inference _ | .reuseType inference .. => fun same => by
      cases same
      exact False.elim inference.no_direct_beta
  | .cached tree priorAgreement priorReading _ _ _ _ => fun same =>
      tree.betaNextOriginAux contextOrigin priorAgreement priorReading enough resultEquation same
  | .cachedFrom check _ _ => fun same =>
      .traced (.rebase contextOrigin (.origin (check.betaNextOrigin enough resultEquation same)))
  | node@(.app full miss trace functionTree argumentTree conditions hashPath comparisonFaithful
      bodyConstructed argConstructed bodyBound argBound coherent faithful) => fun same => by
      cases same
      have resultOrigin := node.betaResultOrigin contextOrigin agreement reading
      rw [← resultEquation] at resultOrigin
      obtain ⟨rfl, rfl⟩ := lambda_inference_domain functionTree
      obtain ⟨functionReads, argumentReads⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨_, bodySpine⟩ := functionTree.lambdaBodyVariableSpine contextOrigin keyedAgreement functionReads
      have flattened := SynthesisReductionOrigin.substitutedResult bodySpine.spine bodySpine.atIndex
        (.applicationArgument contextOrigin trace functionTree argumentTree keyedAgreement functionReads argumentReads
          conditions hashPath comparisonFaithful) .root enough
        (by simpa only [AExpr.inst_variable_appN] using resultOrigin)
      simpa only [AExpr.liftN_zero, List.map_id'] using flattened
  | node@(.appBeta full miss trace functionTree exposure exposureCoherent reduction argumentTree conditions hashPath
      comparisonFaithful bodyConstructed argConstructed bodyBound argBound coherent faithful) => fun shape => by
      cases shape
      have resultOrigin := node.betaResultOrigin contextOrigin agreement reading
      rw [← resultEquation] at resultOrigin
      have same := reduction.rigid (by
        obtain ⟨_, rfl⟩ := functionTree.lambda_type
        intro fn arg same
        cases same)
      cases same
      obtain ⟨rfl, rfl⟩ := lambda_inference_domain functionTree
      obtain ⟨functionReads, argumentReads⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨_, bodySpine⟩ := functionTree.lambdaBodyVariableSpine contextOrigin keyedAgreement functionReads
      have flattened := SynthesisReductionOrigin.substitutedResult bodySpine.spine bodySpine.atIndex
        (.applicationBetaArgument contextOrigin trace functionTree exposure exposureCoherent argumentTree
          keyedAgreement functionReads argumentReads conditions hashPath comparisonFaithful) .root enough
        (by simpa only [AExpr.inst_variable_appN] using resultOrigin)
      simpa only [AExpr.liftN_zero, List.map_id'] using flattened

  | .fvar .. | .forallE .. | .lam .. | .lamBeta .. => fun same => by cases same
termination_by structural support

def SynthesisRetainedCheck.betaNextOrigin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β} {level bound : VLevel} {count : Nat}
    {condition headCondition : Certified.PropWhen} {domain binder inner : AExpr β}
    {initialArguments arguments : List (AExpr β)}
    (check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type bound)
    (enough : count ≤ inner.lambdaDepth + 1) (resultEquation : AExpr.sort level = type) :
    term = .app (.lam condition domain ((AExpr.bvar 0).appN arguments))
      ((AExpr.lam headCondition binder inner).appN initialArguments) →
    SynthesisReductionOrigin resolve incoming incomingContext incomingBounds entries context
      (.lam headCondition binder inner)
      (initialArguments ++ arguments.map (AExpr.inst · ((AExpr.lam headCondition binder inner).appN initialArguments)))
      count level :=
  match check with
  | .source contextOrigin tree agreement reading _ => fun same =>
      tree.betaNextOriginAux contextOrigin agreement reading enough resultEquation same
  | .extend prior extension => fun same =>
      (prior.betaNextOrigin enough resultEquation same).map (.pure (.extend .refl extension))
  | .rebase origin prior => fun same =>
      .traced (.rebase origin (.origin (prior.betaNextOrigin enough resultEquation same)))
  | .weakenAt (cutoff := cutoff) prior insertion => fun same => by
      let application := liftedApplicationView same
      let lambda := liftedLambdaView application.functionEq.symm
      let body := liftedVariableSpineView lambda.bodyEq.symm
      let argument := liftedSpineView application.argumentEq.symm
      let head := liftedLambdaView argument.headEq.symm
      have originalIndex : body.originalIndex = 0 := by
        have shifted := body.indexEq
        simp only [liftVar] at shifted
        split at shifted <;> omega
      have bodyEq : lambda.originalBody = (AExpr.bvar 0).appN body.originalArguments := by
        simpa only [originalIndex] using body.sourceEq
      have functionEq := lambda.sourceEq.trans
        (congrArg (AExpr.lam condition lambda.originalDomain) bodyEq)
      have argumentEq := argument.sourceEq.trans
        (congrArg (AExpr.appN · argument.originalArguments) head.sourceEq)
      have originalEnough : count ≤ head.originalBody.lambdaDepth + 1 := by
        simpa only [head.bodyEq, AExpr.lambdaDepth_liftN] using enough
      have originalResult := (liftN_sort_inv resultEquation.symm).symm
      let child := prior.betaNextOrigin originalEnough originalResult
        (application.sourceEq.trans (congr (congrArg AExpr.app functionEq) argumentEq))
      have lifted := child.weakenAt insertion
      simpa only [AExpr.liftN_appN, AExpr.liftN_betaPrefix, List.map_append, List.map_map,
        Function.comp_def, AExpr.liftN_inst_zero, AExpr.liftN, head.domainEq, head.bodyEq,
        argument.argumentsEq, body.argumentsEq] using lifted
termination_by structural check

end

/-- Retain the next lambda origin through any number of actual inference
cache hits, with the same source type and dependent argument checks. -/
def SynthesisInference.betaNextOrigin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds bounds : List VLevel} {locals : List FVarId} {fuel count : Nat}
    {before : TcState .anon} {source : KExpr .anon} {level bound : VLevel}
    {condition headCondition : Certified.PropWhen} {domain binder inner : AExpr β}
    {initialArguments arguments : List (AExpr β)}
    (support : SynthesisInference resolve entries locals context bounds fuel before source
      (.app (.lam condition domain ((AExpr.bvar 0).appN arguments))
        ((AExpr.lam headCondition binder inner).appN initialArguments)) (.sort level) bound)
    (contextOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source =
      some (AExpr.app (.lam condition domain ((AExpr.bvar 0).appN arguments))
        ((AExpr.lam headCondition binder inner).appN initialArguments)).erase)
    (enough : count ≤ inner.lambdaDepth + 1) :
    SynthesisReductionOrigin resolve incoming incomingContext incomingBounds entries context
      (.lam headCondition binder inner)
      (initialArguments ++ arguments.map (AExpr.inst · ((AExpr.lam headCondition binder inner).appN initialArguments)))
      count level :=
  support.betaNextOriginAux contextOrigin agreement reading enough rfl rfl

/-- A supported successful inference of a source beta redex derives both
equality with the substitution result and typing of that result. No run
of inference on the generated substitution is required. -/
theorem SynthesisInference.beta_sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {fuel : Nat}
    {before after : TcState .anon} {source result : KExpr .anon} {level : VLevel}
    {condition : Certified.PropWhen} {domain body argument type : AExpr β}
    (support : SynthesisInference resolve entries locals context bounds fuel before source
      (.app (.lam condition domain body) argument) type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source =
      some (AExpr.app (.lam condition domain body) argument).erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
    ConversionClaim.{u,v} entries context
      (.app (.lam condition domain body) argument) (body.inst argument) ∧
      TypingClaim.{u,v} entries context (body.inst argument) type := by
  cases support with
  | known inference => exact False.elim inference.no_direct_beta
  | reuseType inference => exact False.elim inference.no_direct_beta
  | cached tree priorAgreement priorReading priorRun _ _ _ =>
      exact tree.beta_sound formed priorAgreement priorReading priorRun
  | cachedFrom check _ _ =>
      have spine := (check.soundWithSpine formed).2.2
      simpa only [AExpr.betaPrefix, AExpr.appN_cons, AExpr.appN_nil] using
        spine.betaPrefix (arguments := [argument]) (count := 1) (by omega)
  | app full miss trace functionTree argumentTree conditions hashPath comparisonFaithful
      bodyConstructed argConstructed bodyBound argBound coherent faithful =>
      obtain ⟨codomain, sameProduct⟩ := functionTree.lambda_type
      cases sameProduct
      obtain ⟨fnReads, argReads⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨functionTypeReads, functionTyped, _⟩ :=
        functionTree.sound formed keyedAgreement fnReads trace.functionRun
      obtain ⟨domainReads, _⟩ := readScopedExpr?_all_parts functionTypeReads
      have argumentAgreement := trace.contextPreserved.symm ▸ keyedAgreement
      obtain ⟨argumentTypeReads, argumentTyped, _⟩ :=
        argumentTree.sound formed argumentAgreement argReads trace.argumentRun
      have sameReading := beq_readScopedExpr? (resolve := resolve) (locals := locals)
        (depth := 0) comparisonFaithful hashPath
      have sameType := AExpr.eq_of_erase_annotations
        (Option.some.inj (argumentTypeReads.symm.trans (sameReading.trans domainReads))) conditions
      have typedArgument := sameType ▸ argumentTyped
      exact ⟨ConversionClaim.beta functionTyped typedArgument,
        TypingClaim.betaResult functionTyped typedArgument⟩
  | appBeta full miss trace functionTree exposure exposureCoherent reduction argumentTree conditions hashPath
      comparisonFaithful bodyConstructed argConstructed bodyBound argBound coherent faithful =>
      have same := reduction.rigid (by
        obtain ⟨_, rfl⟩ := functionTree.lambda_type
        intro fn arg same
        cases same)
      cases same
      obtain ⟨rfl, rfl⟩ := lambda_inference_domain functionTree
      obtain ⟨fnReads, argReads⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨_, functionTyped, _⟩ := functionTree.sound formed keyedAgreement fnReads trace.functionRun
      have checked := SynthesisCheckedOrigin.applicationBetaArgument .current trace functionTree exposure
        exposureCoherent argumentTree keyedAgreement fnReads argReads conditions hashPath comparisonFaithful
      have typedArgument := (checked.soundWithSpine formed).1
      exact ⟨ConversionClaim.beta functionTyped typedArgument,
        TypingClaim.betaResult functionTyped typedArgument⟩

termination_by sizeOf support

/-- Two successive beta prefixes can use different lambda origins. The
second comes from an actual supplied argument, rather than a fresh check
of the intermediate reduction result. -/
theorem SynthesisInference.beta_twice_sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β} {bounds : List VLevel}
    {locals : List FVarId} {fuel count : Nat} {before after : TcState .anon} {source result : KExpr .anon}
    {level bound : VLevel} {condition headCondition : Certified.PropWhen} {domain binder inner : AExpr β}
    {initialArguments arguments : List (AExpr β)}
    (support : SynthesisInference resolve entries locals context bounds fuel before source
      (.app (.lam condition domain ((AExpr.bvar 0).appN arguments))
        ((AExpr.lam headCondition binder inner).appN initialArguments)) (.sort level) bound)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source =
      some (AExpr.app (.lam condition domain ((AExpr.bvar 0).appN arguments))
        ((AExpr.lam headCondition binder inner).appN initialArguments)).erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after)
    (enough : count ≤ inner.lambdaDepth + 1) :
    ConversionClaim.{u,v} entries context
      (.app (.lam condition domain ((AExpr.bvar 0).appN arguments))
        ((AExpr.lam headCondition binder inner).appN initialArguments))
      (AExpr.betaPrefix count (.lam headCondition binder inner)
        (initialArguments ++ arguments.map (AExpr.inst · ((AExpr.lam headCondition binder inner).appN initialArguments)))) ∧
      TypingClaim.{u,v} entries context
        (AExpr.betaPrefix count (.lam headCondition binder inner)
          (initialArguments ++ arguments.map (AExpr.inst · ((AExpr.lam headCondition binder inner).appN initialArguments))))
        (.sort level) := by
  have first := support.beta_sound formed agreement reading accepted
  have next := (support.betaNextOrigin .current agreement reading enough).sound formed
  refine ⟨?_, next.2⟩
  apply ConversionClaim.trans (b := (AExpr.lam headCondition binder inner).appN
    (initialArguments ++ arguments.map (AExpr.inst · ((AExpr.lam headCondition binder inner).appN initialArguments))))
      ?_ next.1
  simpa only [AExpr.inst_variable_appN, AExpr.liftN_zero, List.map_id'] using first.1

/-- The real one-argument structural-WHNF step returns the well-typed beta
result justified by source inference. The production method table supplies
the lambda-head callback; finite walker resources supply the exact result
reading and the updated intern-table invariant. -/
theorem SynthesisInference.beta_step {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {fuel : Nat}
    {inferenceBefore inferenceAfter : TcState .anon} {inferred : KExpr .anon} {level : VLevel}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {rawDomain rawBody rawArgument : KExpr .anon} {lambdaInfo appInfo : ExprInfo .anon}
    {condition : Certified.PropWhen} {domain body argument type : AExpr β}
    (support : SynthesisInference resolve entries locals context bounds fuel inferenceBefore
      (.app (.lam name bi rawDomain rawBody lambdaInfo) rawArgument appInfo)
      (.app (.lam condition domain body) argument) type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals inferenceBefore.lctx context)
    (reading : readScopedExpr? resolve locals
      (.app (.lam name bi rawDomain rawBody lambdaInfo) rawArgument appInfo) =
      some (AExpr.app (.lam condition domain body) argument).erase)
    (accepted : RecM.infer (.app (.lam name bi rawDomain rawBody lambdaInfo) rawArgument appInfo)
      (methodsN fuel) inferenceBefore = .ok inferred inferenceAfter)
    (before : TcState .anon) (reductionFuel : Nat) (flags : WhnfFlags)
    (bodyConstructed : rawBody.Constructed) (argumentConstructed : rawArgument.Constructed)
    (bodyBound : rawBody.size + 1 < UInt64.size) (argumentBound : rawArgument.size < UInt64.size)
    (coherent : before.env.intern.WF)
    (faithful : KExpr.CollisionFree fun term => before.env.intern.ExprSupport term ∨
      KExpr.SimulSubstReach #[rawArgument] rawBody 0 term) :
    ∃ result after,
      (RecM.whnfCoreWithFlagsStep
        (.app (.lam name bi rawDomain rawBody lambdaInfo) rawArgument appInfo) flags).run
        (methodsN (reductionFuel + 1)) before = .ok (.next result) after ∧
      readScopedExpr? resolve locals result = some (body.inst argument).erase ∧
      ConversionClaim.{u,v} entries context
        (.app (.lam condition domain body) argument) (body.inst argument) ∧
      TypingClaim.{u,v} entries context (body.inst argument) type ∧ after.env.intern.WF := by
  obtain ⟨fnReads, argumentReads⟩ := readScopedExpr?_app_parts reading
  obtain ⟨_, bodyReads⟩ := readScopedExpr?_lam_parts fnReads
  obtain ⟨resultReads, resultCoherent⟩ := simulSubst_singleton_readScopedExpr?
    bodyConstructed argumentConstructed bodyBound argumentBound coherent faithful bodyReads argumentReads
  obtain ⟨conversion, typed⟩ := support.beta_sound formed agreement reading accepted
  let walk := simulSubst rawBody #[rawArgument] 0 before.env.intern
  refine ⟨walk.1, { before with env := { before.env with intern := walk.2 } }, ?_,
    ?_, conversion, typed, resultCoherent⟩
  · exact RecM.whnfCoreWithFlagsStep_betaOne rfl rfl
  · simpa only [AExpr.erase_inst] using resultReads

end Ix.Kernel.Consistency
