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
  cases support with
  | known inference => exact inference.lambda_type
  | reuseType inference => exact inference.lambda_type
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
