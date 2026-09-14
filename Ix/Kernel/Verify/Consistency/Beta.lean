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
    {before after : TcState .anon} {source result : KExpr .anon} {level : VLevel}
    {condition : Certified.PropWhen} {domain body type : AExpr β}
    (support : SynthesisInference resolve entries locals context bounds fuel before source
      (.lam condition domain body) type level)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some (AExpr.lam condition domain body).erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
    ∃ codomain, type = .forallE condition domain codomain := by
  let view := (support.betaTyping .current agreement reading accepted).lambdaView rfl
  exact ⟨view.codomain, view.typeEq⟩

/-- The complete retained derivation supplies the original lambda body and
argument even when a let or cache lookup exposes the source redex. -/
def SynthesisInference.betaResultOrigin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds bounds : List VLevel} {locals : List FVarId} {fuel : Nat}
    {before after : TcState .anon} {source result : KExpr .anon} {level : VLevel}
    {condition : Certified.PropWhen} {domain body argument type : AExpr β}
    (support : SynthesisInference resolve entries locals context bounds fuel before source
      (.app (.lam condition domain body) argument) type level)
    (contextOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source =
      some (AExpr.app (.lam condition domain body) argument).erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
    SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context (body.inst argument) type :=
  .reduced (support.betaTyping contextOrigin agreement reading accepted).betaStep.2

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

/-- Substitution keeps the next exposed lambda's entire derivation,
so a subsequent prefix can consume any of its retained argument checks. -/
def SynthesisRetainedCheck.betaNextOrigin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β} {level bound : VLevel} {count : Nat}
    {condition headCondition : Certified.PropWhen} {domain binder inner : AExpr β}
    {initialArguments arguments : List (AExpr β)}
    (check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type bound)
    (enough : count ≤ inner.lambdaDepth + 1) (resultEquation : AExpr.sort level = type)
    (same : term = .app (.lam condition domain ((AExpr.bvar 0).appN arguments))
      ((AExpr.lam headCondition binder inner).appN initialArguments)) :
    SynthesisReductionOrigin resolve incoming incomingContext incomingBounds entries context
      (.lam headCondition binder inner)
      (initialArguments ++ arguments.map (AExpr.inst · ((AExpr.lam headCondition binder inner).appN initialArguments)))
      count level := by
  subst term
  subst type
  have next := check.betaTyping.betaStep.1
  have flattened : SynthesisBetaTyping resolve incoming incomingContext incomingBounds entries context
      ((AExpr.lam headCondition binder inner).appN
        (initialArguments ++ arguments.map (AExpr.inst · ((AExpr.lam headCondition binder inner).appN initialArguments))))
      (.sort level) := by
    simpa only [BetaSyntax.step, AExpr.inst_variable_appN, AExpr.liftN_zero, List.map_id'] using next
  exact .traced ((flattened.spineOrigin _ _ rfl).betaTrace enough)

def SynthesisInference.betaNextOrigin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds bounds : List VLevel} {locals : List FVarId} {fuel count : Nat}
    {before after : TcState .anon} {source result : KExpr .anon} {level bound : VLevel}
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
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after)
    (enough : count ≤ inner.lambdaDepth + 1) :
    SynthesisReductionOrigin resolve incoming incomingContext incomingBounds entries context
      (.lam headCondition binder inner)
      (initialArguments ++ arguments.map (AExpr.inst · ((AExpr.lam headCondition binder inner).appN initialArguments)))
      count level :=
  (SynthesisRetainedCheck.source contextOrigin support agreement reading accepted).betaNextOrigin enough rfl rfl

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
  exact (support.betaTyping .current agreement reading accepted).betaStep.2.sound formed

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
  have next := (support.betaNextOrigin .current agreement reading accepted enough).sound formed
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
