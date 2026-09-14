/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.ContextTransport
import Ix.Kernel.Verify.Consistency.CheapBetaReading
import Ix.Kernel.Verify.Consistency.ApplicationWhnf
import Ix.Theory.Model.UniverseBounds
import Ix.Theory.Model.BetaSpine

/-!
Inference with formation of the returned type. Local bounds come from the
executed checks of binder domains; external type bounds retain their actual
checking origin. Applications recover a codomain bound from an inhabited
product. Lambdas therefore synthesize full typing, including when they occur
directly in function position.

The recorded level is an upper bound for the inferred type. It preserves the
exact zero condition, but its positive value need not be the sort the kernel
would infer on a separate call. No such extra call is assumed.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

mutual

/-- Finite support for the actual production calls, enriched with the
origins and syntactic levels needed to derive formation. There are no
semantic typing or conversion fields. -/
inductive SynthesisInference {β : Type u}
    (resolve : Address → Option (ConstRef β)) :
    Model.Environment β → List FVarId → Model.Context β → List VLevel → Nat → TcState .anon → KExpr .anon →
      AExpr β → AExpr β → VLevel → Type u
  | known {entries locals context bounds fuel before source term type level}
      (inference : BinderInference resolve entries locals context fuel before source term type)
      (formation : TypeFormation resolve entries context type level) :
      SynthesisInference resolve entries locals context bounds fuel before source term type level
  | cached {entries locals context bounds fuel before source term type level
      priorLocals priorFuel priorBefore priorAfter priorResult}
      (tree : SynthesisInference resolve entries priorLocals context bounds priorFuel priorBefore source term type level)
      (priorAgreement : LocalContextReading resolve priorLocals priorBefore.lctx context)
      (priorReading : readScopedExpr? resolve priorLocals source = some term.erase)
      (priorRun : RecM.infer source (methodsN priorFuel) priorBefore = .ok priorResult priorAfter)
      (hit : InferenceCacheHit before source)
      (cacheMatch : hit.cached = priorResult)
      (resultReading : readScopedExpr? resolve locals priorResult = some type.erase) :
      SynthesisInference resolve entries locals context bounds fuel before source term type level
  | cachedFrom {entries locals context bounds fuel before source term type level}
      (check : SynthesisRetainedCheck resolve entries context bounds entries context term type level)
      (hit : InferenceCacheHit before source)
      (resultReading : readScopedExpr? resolve locals hit.cached = some type.erase) :
      SynthesisInference resolve entries locals context bounds fuel before source term type level
  | reuseType {earlier entries locals context bounds fuel before source term type
      typeFuel typeBefore typeAfter typeSource typeResult declaredType level typeBound arguments}
      (inference : BinderInference resolve entries locals context fuel before source term type)
      (typeTree : SynthesisInference resolve earlier [] [] [] typeFuel typeBefore typeSource
        declaredType (.sort level) typeBound)
      (extension : InterfaceExtends earlier entries)
      (typeReading : readScopedExpr? resolve [] typeSource = some declaredType.erase)
      (typeRun : RecM.infer typeSource (methodsN typeFuel) typeBefore = .ok typeResult typeAfter)
      (same : AExpr.LevelEquivalent (declaredType.instL arguments) type) :
      SynthesisInference resolve entries locals context bounds fuel before source term type (level.inst arguments)
  | fvar {entries locals context bounds fuel before source index type level}
      (inference : BinderInference resolve entries locals context fuel before source (.bvar index) type)
      (atIndex : context[index]? = some type)
      (boundAtIndex : bounds[index]? = some level) :
      SynthesisInference resolve entries locals context bounds fuel before source (.bvar index) type level
  | app {entries locals context bounds fuel before fn arg info f a A A' B condition functionLevel argumentLevel}
      (full : before.inferOnly = false)
      (miss : UncachedInference before (.app fn arg info))
      (trace : ApplicationInferenceTrace fuel miss.keyed fn arg)
      (functionTree : SynthesisInference resolve entries locals context bounds fuel miss.keyed fn
        f (.forallE condition A B) functionLevel)
      (argumentTree : SynthesisInference resolve entries locals context bounds fuel trace.functionState
        arg a A' argumentLevel)
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
      SynthesisInference resolve entries locals context bounds (fuel + 1) before (.app fn arg info)
        (.app f a) (B.inst a) (applicationLevel functionLevel condition)
  | appBeta {entries locals context bounds fuel before fn arg info f a T A A' B condition
      functionLevel argumentLevel reductionLevel}
      (full : before.inferOnly = false)
      (miss : UncachedInference before (.app fn arg info))
      (trace : ApplicationWhnfInferenceTrace fuel miss.keyed fn arg)
      (functionTree : SynthesisInference resolve entries locals context bounds fuel miss.keyed fn
        f T functionLevel)
      (exposure : BetaPiExposure resolve locals fuel trace.functionState trace.functionType T
        condition A B trace.domain trace.codomain)
      (exposureCoherent : trace.functionState.env.intern.WF)
      (reduction : SynthesisBetaTrace resolve entries context bounds entries context
        T (.forallE condition A B) (.sort reductionLevel))
      (argumentTree : SynthesisInference resolve entries locals context bounds fuel trace.exposedState
        arg a A' argumentLevel)
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
      SynthesisInference resolve entries locals context bounds (fuel + 1) before (.app fn arg info)
        (.app f a) (B.inst a) (applicationLevel reductionLevel condition)
  | forallE {entries locals context bounds fuel before name bi domain body info A B domainBoundLevel bodyBoundLevel}
      (miss : UncachedInference before (.all name bi domain body info))
      (trace : ForallInferenceTrace fuel miss.keyed name bi domain body)
      (opening : BinderOpeningSupport trace.domainState body)
      (domainTree : SynthesisInference resolve entries locals context bounds fuel miss.keyed domain
        A (.sort (readLevel trace.domainLevel)) domainBoundLevel)
      (bodyTree : SynthesisInference resolve entries (trace.fresh :: locals) (context.push A)
        (readLevel trace.domainLevel :: bounds) fuel trace.openedState trace.opened
        B (.sort (readLevel trace.bodyLevel)) bodyBoundLevel)
      (levelFaithful : ∀ a b,
        (KUniv.Sub a trace.domainLevel ∨ KUniv.Sub a trace.bodyLevel) →
        (KUniv.Sub b trace.domainLevel ∨ KUniv.Sub b trace.bodyLevel) → a.AddrFaithful b)
      (domainBound : trace.domainLevel.size < UInt64.size)
      (bodyBound : trace.bodyLevel.size < UInt64.size)
      (coherent : trace.bodyState.env.intern.WF)
      (faithful : KExpr.KeyCollisionFree fun term => trace.bodyState.env.intern.ExprSupport term ∨
        term = KExpr.mkSort (KUniv.mkIMax trace.domainLevel trace.bodyLevel)) :
      SynthesisInference resolve entries locals context bounds (fuel + 1) before (.all name bi domain body info)
        (.forallE (Certified.zeroCondition (readLevel trace.bodyLevel)) A B)
        (.sort (readLevel (KUniv.mkIMax trace.domainLevel trace.bodyLevel)))
        (.succ (readLevel (KUniv.mkIMax trace.domainLevel trace.bodyLevel)))
  | lam {entries locals context bounds fuel before name bi domain body info A b B condition domainBoundLevel bodyLevel}
      (full : before.inferOnly = false)
      (miss : UncachedInference before (.lam name bi domain body info))
      (trace : LambdaInferenceTrace fuel miss.keyed name bi domain body)
      (opening : BinderOpeningSupport trace.domainState body)
      (domainTree : SynthesisInference resolve entries locals context bounds fuel miss.keyed domain
        A (.sort (readLevel trace.domainLevel)) domainBoundLevel)
      (bodyTree : SynthesisInference resolve entries (trace.fresh :: locals) (context.push A)
        (readLevel trace.domainLevel :: bounds) fuel trace.openedState trace.opened b B bodyLevel)
      (conditionAgrees : condition = Certified.zeroCondition bodyLevel)
      (constructed : trace.bodyType.Constructed)
      (bound : trace.bodyType.size + 1 < UInt64.size)
      (coherent : trace.bodyState.env.intern.WF)
      (closingFaithful : KExpr.CollisionFree fun term => trace.bodyState.env.intern.ExprSupport term ∨
        KExpr.AbstractReach ((∅ : Std.HashMap FVarId UInt64).insert trace.fresh 0)
          1 trace.bodyType 0 term)
      (faithful : KExpr.KeyCollisionFree fun term => trace.abstracted.2.ExprSupport term ∨
        term = KExpr.mkAll () () domain trace.abstracted.1) :
      SynthesisInference resolve entries locals context bounds (fuel + 1) before (.lam name bi domain body info)
        (.lam condition A b) (.forallE condition A B) (.imax (readLevel trace.domainLevel) bodyLevel)
  | lamBeta {entries locals context bounds fuel before name bi domain body info A b condition
      domainBoundLevel bodyLevel headCondition headDomain headBody arguments reducedLevel}
      (full : before.inferOnly = false)
      (miss : UncachedInference before (.lam name bi domain body info))
      (trace : LambdaBodyTrace fuel miss.keyed name bi domain body)
      (opening : BinderOpeningSupport trace.domainState body)
      (domainTree : SynthesisInference resolve entries locals context bounds fuel miss.keyed domain
        A (.sort (readLevel trace.domainLevel)) domainBoundLevel)
      (bodyTree : SynthesisInference resolve entries (trace.fresh :: locals) (context.push A)
        (readLevel trace.domainLevel :: bounds) fuel trace.openedState trace.opened b
        ((AExpr.lam headCondition headDomain headBody).appN arguments) bodyLevel)
      (origin : SynthesisReductionOrigin resolve entries context bounds entries (context.push A)
        (.lam headCondition headDomain headBody) arguments (cheapBetaCount trace.bodyType) reducedLevel)
      (reduction : CheapBetaSupport trace.bodyType trace.bodyState.env.intern)
      (conditionAgrees : condition = Certified.zeroCondition reducedLevel)
      (constructed : trace.reduced.1.Constructed)
      (bound : trace.reduced.1.size + 1 < UInt64.size)
      (closingFaithful : KExpr.CollisionFree fun term => trace.reduced.2.ExprSupport term ∨
        KExpr.AbstractReach ((∅ : Std.HashMap FVarId UInt64).insert trace.fresh 0)
          1 trace.reduced.1 0 term)
      (faithful : KExpr.KeyCollisionFree fun term => trace.abstracted.2.ExprSupport term ∨
        term = KExpr.mkAll () () domain trace.abstracted.1) :
      SynthesisInference resolve entries locals context bounds (fuel + 1) before (.lam name bi domain body info)
        (.lam condition A b)
        (.forallE condition A
          (AExpr.betaPrefix (cheapBetaCount trace.bodyType) (.lam headCondition headDomain headBody) arguments))
        (.imax (readLevel trace.domainLevel) reducedLevel)

/-- A complete executed inference check transported to a later use site.
The source tree remains available beneath interface and context changes;
none of these constructors accepts semantic typing or conversion evidence. -/
inductive SynthesisRetainedCheck {β : Type u} (resolve : Address → Option (ConstRef β)) :
    Model.Environment β → Model.Context β → List VLevel →
      Model.Environment β → Model.Context β → AExpr β → AExpr β → VLevel → Type u
  | source {incoming incomingContext incomingBounds entries context bounds locals fuel before after
      source result term type level}
      (contextOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
      (tree : SynthesisInference resolve entries locals context bounds fuel before source term type level)
      (agreement : LocalContextReading resolve locals before.lctx context)
      (reading : readScopedExpr? resolve locals source = some term.erase)
      (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
      SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type level
  | extend {incoming incomingContext incomingBounds earlier entries context term type level}
      (prior : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds earlier context term type level)
      (extension : InterfaceExtends earlier entries) :
      SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type level
  | weakenAt {incoming incomingContext incomingBounds entries source target cutoff term type level}
      (prior : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries source term type level)
      (insertion : ContextInsertion source target cutoff) :
      SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries target
        (term.liftN 1 cutoff) (type.liftN 1 cutoff) level
  | rebase {incoming incomingContext incomingBounds middle middleContext middleBounds entries context term type level}
      (origin : SynthesisContext resolve incoming incomingContext incomingBounds middle middleContext middleBounds)
      (prior : SynthesisRetainedCheck resolve middle middleContext middleBounds entries context term type level) :
      SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type level

/-- Contexts of retained checking origins come from the incoming context,
the empty context, or actual checks of their binder domains. This records
earlier checks even when a generated type is used several binders later. -/
inductive SynthesisContext {β : Type u} (resolve : Address → Option (ConstRef β)) :
    Model.Environment β → Model.Context β → List VLevel →
      Model.Environment β → Model.Context β → List VLevel → Type u
  | current {entries context bounds} :
      SynthesisContext resolve entries context bounds entries context bounds
  | empty {entries context bounds} (earlier : Model.Environment β) :
      SynthesisContext resolve entries context bounds earlier [] []
  | push {entries context bounds earlier priorContext priorBounds locals fuel before after source result
      domain level bound}
      (prior : SynthesisContext resolve entries context bounds earlier priorContext priorBounds)
      (domainTree : SynthesisInference resolve earlier locals priorContext priorBounds fuel before source
        domain (.sort level) bound)
      (agreement : LocalContextReading resolve locals before.lctx priorContext)
      (reading : readScopedExpr? resolve locals source = some domain.erase)
      (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
      SynthesisContext resolve entries context bounds earlier (priorContext.push domain) (level :: priorBounds)
  | extend {entries context bounds earlier later priorContext priorBounds}
      (prior : SynthesisContext resolve entries context bounds earlier priorContext priorBounds)
      (extension : InterfaceExtends earlier later) :
      SynthesisContext resolve entries context bounds later priorContext priorBounds
  | compose {entries context bounds middle middleContext middleBounds earlier priorContext priorBounds}
      (prior : SynthesisContext resolve entries context bounds middle middleContext middleBounds)
      (next : SynthesisContext resolve middle middleContext middleBounds earlier priorContext priorBounds) :
      SynthesisContext resolve entries context bounds earlier priorContext priorBounds

/-- A checking origin may also cross a dependent term substitution. The
substituted argument retains its actual inference call, whose typing is
derived in the same recursion as the enclosing lambda. -/
inductive SynthesisTypeTransport {β : Type u} (resolve : Address → Option (ConstRef β)) :
    Model.Environment β → Model.Context β → List VLevel →
      Model.Environment β → Model.Context β → AExpr β → AExpr β → VLevel →
        Model.Environment β → Model.Context β → AExpr β → AExpr β → VLevel → Type u
  | pure {incoming incomingContext incomingBounds origin originContext source reduced level
      entries context current result bound}
      (transport : TypeReductionTransport origin originContext source reduced level
        entries context current result bound) :
      SynthesisTypeTransport resolve incoming incomingContext incomingBounds
        origin originContext source reduced level entries context current result bound
  | map {incoming incomingContext incomingBounds origin originContext source reduced level
      middle middleContext current result bound entries context current' result' bound'}
      (prior : SynthesisTypeTransport resolve incoming incomingContext incomingBounds
        origin originContext source reduced level middle middleContext current result bound)
      (transport : TypeReductionTransport middle middleContext current result bound
        entries context current' result' bound') :
      SynthesisTypeTransport resolve incoming incomingContext incomingBounds
        origin originContext source reduced level entries context current' result' bound'
  | substituteAt {incoming incomingContext incomingBounds origin originContext source reduced level
      entries base sourceContext targetContext current result bound domain argument cutoff}
      (prior : SynthesisTypeTransport resolve incoming incomingContext incomingBounds
        origin originContext source reduced level entries sourceContext current result bound)
      (argumentOrigin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds
        entries base argument domain)
      (substitution : ContextSubstitution base domain argument sourceContext targetContext cutoff) :
      SynthesisTypeTransport resolve incoming incomingContext incomingBounds
        origin originContext source reduced level entries targetContext
        (current.inst argument cutoff) (result.inst argument cutoff) bound

/-- Internal typing origins for generated expressions. Leaves are actual
source inference calls. Application, conversion, finite beta traces, and
context substitutions retain those calls, including when an argument crosses
still-open parameters of an earlier type. No semantic typing field is accepted. -/
inductive SynthesisTypingOrigin {β : Type u} (resolve : Address → Option (ConstRef β)) :
    Model.Environment β → Model.Context β → List VLevel →
      Model.Environment β → Model.Context β → AExpr β → AExpr β → Type u
  | source {incoming incomingContext incomingBounds entries context term type}
      (check : SynthesisCheckedOrigin resolve incoming incomingContext incomingBounds entries context term type) :
      SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type
  | inferredType {incoming incomingContext incomingBounds entries context bounds locals fuel before after source result
      term type level}
      (contextOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
      (tree : SynthesisInference resolve entries locals context bounds fuel before source term type level)
      (agreement : LocalContextReading resolve locals before.lctx context)
      (reading : readScopedExpr? resolve locals source = some term.erase)
      (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
      SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context type (.sort level)
  | lambdaBody {incoming incomingContext incomingBounds entries context condition domain body codomain}
      (check : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context
        (.lam condition domain body) (.forallE condition domain codomain)) :
      SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries (context.push domain) body codomain
  | application {incoming incomingContext incomingBounds entries context function argument condition domain body}
      (functionOrigin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context
        function (.forallE condition domain body))
      (argumentOrigin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context argument domain) :
      SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context
        (.app function argument) (body.inst argument)
  | reduced {incoming incomingContext incomingBounds entries context source result type}
      (trace : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context source result type) :
      SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context result type
  | convert {incoming incomingContext incomingBounds entries context term sourceType resultType level}
      (value : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term sourceType)
      (trace : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context sourceType resultType (.sort level)) :
      SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term resultType
  | weaken {incoming incomingContext incomingBounds entries context term type}
      (prior : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type)
      (domain : AExpr β) :
      SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries (context.push domain)
        (term.liftN 1) (type.liftN 1)
  | weakenAt {incoming incomingContext incomingBounds entries source target cutoff term type}
      (prior : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries source term type)
      (insertion : ContextInsertion source target cutoff) :
      SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries target
        (term.liftN 1 cutoff) (type.liftN 1 cutoff)
  | instantiate {incoming incomingContext incomingBounds entries context term type}
      (prior : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type)
      (arguments : List VLevel) :
      SynthesisTypingOrigin resolve incoming incomingContext incomingBounds
        entries (context.map (AExpr.instL arguments)) (term.instL arguments) (type.instL arguments)
  | appendContext {incoming incomingContext incomingBounds entries context term type}
      (prior : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type)
      (outer : Model.Context β) :
      SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries (context ++ outer) term type
  | extend {incoming incomingContext incomingBounds earlier entries context term type}
      (prior : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds earlier context term type)
      (extension : InterfaceExtends earlier entries) :
      SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type
  | rebase {incoming incomingContext incomingBounds middle middleContext middleBounds entries context term type}
      (origin : SynthesisContext resolve incoming incomingContext incomingBounds middle middleContext middleBounds)
      (prior : SynthesisTypingOrigin resolve middle middleContext middleBounds entries context term type) :
      SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type
  | termEquivalent {incoming incomingContext incomingBounds entries context term term' type}
      (prior : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type)
      (same : AExpr.LevelEquivalent term term') :
      SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term' type
  | typeEquivalent {incoming incomingContext incomingBounds entries context term type type'}
      (prior : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type)
      (same : AExpr.LevelEquivalent type type') :
      SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type'
  | substituteAt {incoming incomingContext incomingBounds entries base sourceContext targetContext
      domain term type argument cutoff}
      (body : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds
        entries sourceContext term type)
      (value : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries base argument domain)
      (substitution : ContextSubstitution base domain argument sourceContext targetContext cutoff) :
      SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries targetContext
        (term.inst argument cutoff) (type.inst argument cutoff)

/-- Actual inference calls retain their source's syntactic lambda domains
and argument checks. Application arguments additionally retain the comparison with
the function's domain, before any later transport of this checking origin. -/
inductive SynthesisCheckedOrigin {β : Type u} (resolve : Address → Option (ConstRef β)) :
    Model.Environment β → Model.Context β → List VLevel →
      Model.Environment β → Model.Context β → AExpr β → AExpr β → Type u
  | checked {incoming incomingContext incomingBounds entries context bounds locals fuel before after source result
      term type level}
      (contextOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
      (tree : SynthesisInference resolve entries locals context bounds fuel before source term type level)
      (agreement : LocalContextReading resolve locals before.lctx context)
      (reading : readScopedExpr? resolve locals source = some term.erase)
      (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
      SynthesisCheckedOrigin resolve incoming incomingContext incomingBounds entries context term type
  | binderHead {incoming incomingContext incomingBounds entries context locals fuel before after source result term type}
      (tree : BinderInference resolve entries locals context fuel before source term type)
      (head : SynthesisHead term)
      (agreement : LocalContextReading resolve locals before.lctx context)
      (reading : readScopedExpr? resolve locals source = some term.erase)
      (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
      SynthesisCheckedOrigin resolve incoming incomingContext incomingBounds entries context term type
  | applicationArgument {incoming incomingContext incomingBounds entries context bounds locals fuel before fn arg
      f a domain argumentType body condition functionLevel argumentLevel}
      (contextOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
      (trace : ApplicationInferenceTrace fuel before fn arg)
      (functionTree : SynthesisInference resolve entries locals context bounds fuel before fn
        f (.forallE condition domain body) functionLevel)
      (argumentTree : SynthesisInference resolve entries locals context bounds fuel trace.functionState arg
        a argumentType argumentLevel)
      (agreement : LocalContextReading resolve locals before.lctx context)
      (functionReading : readScopedExpr? resolve locals fn = some f.erase)
      (argumentReading : readScopedExpr? resolve locals arg = some a.erase)
      (conditions : argumentType.annotations = domain.annotations)
      (hashPath : (trace.argumentType == trace.domain) = true)
      (comparisonFaithful : trace.argumentType.AddrFaithful trace.domain) :
      SynthesisCheckedOrigin resolve incoming incomingContext incomingBounds entries context a domain
  | applicationBetaArgument {incoming incomingContext incomingBounds entries context bounds locals fuel before fn arg
      f a T domain argumentType body condition functionLevel argumentLevel}
      (contextOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
      (trace : ApplicationWhnfInferenceTrace fuel before fn arg)
      (functionTree : SynthesisInference resolve entries locals context bounds fuel before fn f T functionLevel)
      (exposure : BetaPiExposure resolve locals fuel trace.functionState trace.functionType T
        condition domain body trace.domain trace.codomain)
      (exposureCoherent : trace.functionState.env.intern.WF)
      (argumentTree : SynthesisInference resolve entries locals context bounds fuel trace.exposedState arg
        a argumentType argumentLevel)
      (agreement : LocalContextReading resolve locals before.lctx context)
      (functionReading : readScopedExpr? resolve locals fn = some f.erase)
      (argumentReading : readScopedExpr? resolve locals arg = some a.erase)
      (conditions : argumentType.annotations = domain.annotations)
      (hashPath : (trace.argumentType == trace.domain) = true)
      (comparisonFaithful : trace.argumentType.AddrFaithful trace.domain) :
      SynthesisCheckedOrigin resolve incoming incomingContext incomingBounds entries context a domain
  | binderArgument {incoming incomingContext incomingBounds entries context locals fuel before fn arg
      f a domain argumentType body condition}
      (trace : ApplicationInferenceTrace fuel before fn arg)
      (functionTree : BinderInference resolve entries locals context fuel before fn
        f (.forallE condition domain body))
      (head : SynthesisHead f)
      (argumentTree : BinderInference resolve entries locals context fuel trace.functionState arg a argumentType)
      (agreement : LocalContextReading resolve locals before.lctx context)
      (functionReading : readScopedExpr? resolve locals fn = some f.erase)
      (argumentReading : readScopedExpr? resolve locals arg = some a.erase)
      (conditions : argumentType.annotations = domain.annotations)
      (hashPath : (trace.argumentType == trace.domain) = true)
      (comparisonFaithful : trace.argumentType.AddrFaithful trace.domain) :
      SynthesisCheckedOrigin resolve incoming incomingContext incomingBounds entries context a domain

/-- The argument checks along an actual application spine, retained in
application order so later substitutions can update each dependent type. -/
inductive SynthesisArgumentSpineOrigin {β : Type u} (resolve : Address → Option (ConstRef β)) :
    Model.Environment β → Model.Context β → List VLevel →
      Model.Environment β → Model.Context β → AExpr β → List (AExpr β) → AExpr β → Type u
  | nil {incoming incomingContext incomingBounds entries context} (type : AExpr β) :
      SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds entries context type [] type
  | snoc {incoming incomingContext incomingBounds entries context start arguments condition domain body argument}
      (prior : SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds entries context
        start arguments (.forallE condition domain body))
      (checked : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context argument domain) :
      SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds entries context
        start (arguments ++ [argument]) (body.inst argument)
  | convert {incoming incomingContext incomingBounds entries context start arguments source target level}
      (prior : SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds entries context
        start arguments source)
      (trace : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context source target (.sort level)) :
      SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds entries context start arguments target

/-- A beta reduction can come from an earlier checked lambda prefix, or
from an actual lambda or lambda application substituted for a checked
variable head. Both cases retain the checks of all applied arguments. -/
inductive SynthesisReductionOrigin {β : Type u} (resolve : Address → Option (ConstRef β)) :
    Model.Environment β → Model.Context β → List VLevel →
      Model.Environment β → Model.Context β → AExpr β → List (AExpr β) → Nat → VLevel → Type u
  | traced {incoming incomingContext incomingBounds entries context head arguments count level}
      (trace : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context
        (head.appN arguments) (AExpr.betaPrefix count head arguments) (.sort level)) :
      SynthesisReductionOrigin resolve incoming incomingContext incomingBounds entries context head arguments count level
  | checked {incoming incomingContext incomingBounds entries context head arguments count level
      earlier typeLocals typeContext typeBounds typeFuel typeBefore typeAfter typeSource typeResult
      originCondition originDomain originBody originArguments originLevel originBound}
      (typeContextSupport : SynthesisContext resolve incoming incomingContext incomingBounds
        earlier typeContext typeBounds)
      (typeTree : SynthesisInference resolve earlier typeLocals typeContext typeBounds typeFuel typeBefore
        typeSource ((AExpr.lam originCondition originDomain originBody).appN originArguments)
        (.sort originLevel) originBound)
      (typeAgreement : LocalContextReading resolve typeLocals typeBefore.lctx typeContext)
      (typeReading : readScopedExpr? resolve typeLocals typeSource =
        some ((AExpr.lam originCondition originDomain originBody).appN originArguments).erase)
      (typeRun : RecM.infer typeSource (methodsN typeFuel) typeBefore = .ok typeResult typeAfter)
      (originPrefix : count ≤ originBody.lambdaDepth + 1)
      (transport : SynthesisTypeTransport resolve incoming incomingContext incomingBounds earlier typeContext
        ((AExpr.lam originCondition originDomain originBody).appN originArguments)
        (AExpr.betaPrefix count (.lam originCondition originDomain originBody) originArguments) originLevel
        entries context (head.appN arguments) (AExpr.betaPrefix count head arguments) level) :
      SynthesisReductionOrigin resolve incoming incomingContext incomingBounds entries context head arguments count level
  | substitutedVariable {incoming incomingContext incomingBounds entries base source target
      type domain argument arguments cutoff count level}
      (spine : SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds
        entries source type arguments (.sort level))
      (atIndex : source[cutoff]? = some type)
      (checked : SynthesisCheckedOrigin resolve incoming incomingContext incomingBounds entries base argument domain)
      (substitution : ContextSubstitution base domain argument source target cutoff)
      (enough : count ≤ argument.lambdaDepth) :
      SynthesisReductionOrigin resolve incoming incomingContext incomingBounds entries target
        (argument.liftN cutoff) (arguments.map (AExpr.inst · argument cutoff)) count level
  | substitutedApplication {incoming incomingContext incomingBounds entries base source target
      type domain binder body condition initialArguments arguments cutoff count level}
      (spine : SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds
        entries source type arguments (.sort level))
      (atIndex : source[cutoff]? = some type)
      (checked : SynthesisCheckedOrigin resolve incoming incomingContext incomingBounds entries base
        ((AExpr.lam condition binder body).appN initialArguments) domain)
      (substitution : ContextSubstitution base domain
        ((AExpr.lam condition binder body).appN initialArguments) source target cutoff)
      (enough : count ≤ body.lambdaDepth + 1) :
      SynthesisReductionOrigin resolve incoming incomingContext incomingBounds entries target
        ((AExpr.lam condition binder body).liftN cutoff)
        (initialArguments.map (AExpr.liftN cutoff ·) ++
          arguments.map (AExpr.inst · ((AExpr.lam condition binder body).appN initialArguments) cutoff)) count level
  | substitutedResult {incoming incomingContext incomingBounds entries base source target
      type domain binder body condition initialArguments arguments cutoff count resultType level}
      (spine : SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds
        entries source type arguments resultType)
      (atIndex : source[cutoff]? = some type)
      (checked : SynthesisCheckedOrigin resolve incoming incomingContext incomingBounds entries base
        ((AExpr.lam condition binder body).appN initialArguments) domain)
      (substitution : ContextSubstitution base domain
        ((AExpr.lam condition binder body).appN initialArguments) source target cutoff)
      (enough : count ≤ body.lambdaDepth + 1)
      (sourceOrigin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries target
        (((AExpr.lam condition binder body).liftN cutoff).appN
          (initialArguments.map (AExpr.liftN cutoff ·) ++
            arguments.map (AExpr.inst · ((AExpr.lam condition binder body).appN initialArguments) cutoff)))
        (.sort level)) :
      SynthesisReductionOrigin resolve incoming incomingContext incomingBounds entries target
        ((AExpr.lam condition binder body).liftN cutoff)
        (initialArguments.map (AExpr.liftN cutoff ·) ++
          arguments.map (AExpr.inst · ((AExpr.lam condition binder body).appN initialArguments) cutoff)) count level
  | map {incoming incomingContext incomingBounds earlier priorContext head arguments count bound
      entries context current currentArguments level}
      (prior : SynthesisReductionOrigin resolve incoming incomingContext incomingBounds
        earlier priorContext head arguments count bound)
      (transport : SynthesisTypeTransport resolve incoming incomingContext incomingBounds earlier priorContext
        (head.appN arguments) (AExpr.betaPrefix count head arguments) bound entries context
        (current.appN currentArguments) (AExpr.betaPrefix count current currentArguments) level) :
      SynthesisReductionOrigin resolve incoming incomingContext incomingBounds
        entries context current currentArguments count level

/-- Finite beta traces retain the actual checks behind each lambda and
argument. Results can supply later typing origins, so composition never
requires an inference call on an intermediate expression. Types at adjacent
steps may differ; the trace preserves the type retained by its first step. -/
inductive SynthesisBetaTrace {β : Type u} (resolve : Address → Option (ConstRef β)) :
    Model.Environment β → Model.Context β → List VLevel →
      Model.Environment β → Model.Context β → AExpr β → AExpr β → AExpr β → Type u
  | refl {incoming incomingContext incomingBounds entries context term type}
      (origin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type) :
      SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context term term type
  | prefix {incoming incomingContext incomingBounds entries context head headType arguments count type}
      (headOrigin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context head headType)
      (leading : LambdaPrefix head headType count)
      (argumentsOrigin : SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds
        entries context headType arguments type) :
      SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context
        (head.appN arguments) (AExpr.betaPrefix count head arguments) type
  | origin {incoming incomingContext incomingBounds entries context head arguments count level}
      (retained : SynthesisReductionOrigin resolve incoming incomingContext incomingBounds
        entries context head arguments count level) :
      SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context
        (head.appN arguments) (AExpr.betaPrefix count head arguments) (.sort level)
  | trans {incoming incomingContext incomingBounds entries context source middle result type otherType}
      (prior : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context source middle type)
      (next : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context middle result otherType) :
      SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context source result type
  | atType {incoming incomingContext incomingBounds entries context source result type otherType}
      (sourceOrigin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context source type)
      (trace : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context source result otherType) :
      SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context source result type
  | application {incoming incomingContext incomingBounds entries context source result argument condition domain body}
      (functionTrace : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context
        source result (.forallE condition domain body))
      (argumentOrigin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context argument domain) :
      SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context
        (.app source argument) (.app result argument) (body.inst argument)
  | argument {incoming incomingContext incomingBounds entries context function source result condition domain body otherType}
      (functionOrigin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context
        function (.forallE condition domain body))
      (argumentOrigin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context source domain)
      (argumentTrace : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context source result otherType) :
      SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context
        (.app function source) (.app function result) (body.inst source)
  | substituteAt {incoming incomingContext incomingBounds entries base sourceContext targetContext
      domain source result type argument cutoff}
      (trace : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries sourceContext source result type)
      (value : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries base argument domain)
      (substitution : ContextSubstitution base domain argument sourceContext targetContext cutoff) :
      SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries targetContext
        (source.inst argument cutoff) (result.inst argument cutoff) (type.inst argument cutoff)
  | weakenAt {incoming incomingContext incomingBounds entries sourceContext targetContext cutoff source result type}
      (trace : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries sourceContext source result type)
      (insertion : ContextInsertion sourceContext targetContext cutoff) :
      SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries targetContext
        (source.liftN 1 cutoff) (result.liftN 1 cutoff) (type.liftN 1 cutoff)
  | rebase {incoming incomingContext incomingBounds middle middleContext middleBounds entries context source result type}
      (origin : SynthesisContext resolve incoming incomingContext incomingBounds middle middleContext middleBounds)
      (trace : SynthesisBetaTrace resolve middle middleContext middleBounds entries context source result type) :
      SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context source result type
  | convertType {incoming incomingContext incomingBounds entries context source result sourceType targetType level}
      (trace : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context source result sourceType)
      (typeTrace : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context
        sourceType targetType (.sort level)) :
      SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context source result targetType
  | instantiate {incoming incomingContext incomingBounds entries context source result type}
      (trace : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context source result type)
      (arguments : List VLevel) :
      SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries (context.map (AExpr.instL arguments))
        (source.instL arguments) (result.instL arguments) (type.instL arguments)
  | appendContext {incoming incomingContext incomingBounds entries context source result type}
      (trace : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context source result type)
      (outer : Model.Context β) :
      SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries (context ++ outer) source result type
  | extend {incoming incomingContext incomingBounds earlier entries context source result type}
      (trace : SynthesisBetaTrace resolve incoming incomingContext incomingBounds earlier context source result type)
      (extension : InterfaceExtends earlier entries) :
      SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context source result type

end

private theorem trace_appN_last {β : Type u} {head : AExpr β} {arguments : List (AExpr β)}
    (nonempty : arguments ≠ []) :
    head.appN arguments = (head.appN arguments.dropLast).app (arguments.getLast nonempty) := by
  calc
    head.appN arguments = head.appN (arguments.dropLast ++ [arguments.getLast nonempty]) :=
      congrArg (AExpr.appN head) (List.dropLast_concat_getLast nonempty).symm
    _ = _ := by simp only [AExpr.appN_append, AExpr.appN_cons, AExpr.appN_nil]

private theorem betaPrefix_eq_of_not_app {β : Type u} {head : AExpr β}
    {arguments : List (AExpr β)} {count : Nat}
    (notApp : ∀ fn arg, head.appN arguments ≠ .app fn arg) :
    AExpr.betaPrefix count head arguments = head.appN arguments := by
  cases arguments with
  | nil => cases count <;> cases head <;> rfl
  | cons argument arguments =>
      exact False.elim (notApp _ _ (trace_appN_last (by simp)))

/-- These traces reduce applications and their subapplications. They do
not change a source whose outer constructor is a lambda, product, or atom.
In particular, a forward beta conversion cannot change a lambda's product type. -/
theorem SynthesisBetaTrace.rigid {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {source result type : AExpr β}
    (trace : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context source result type) :
    (∀ fn arg, source ≠ .app fn arg) → result = source :=
  match trace with
  | .refl _ => fun _ => rfl
  | .prefix .. | .origin .. => fun notApp => betaPrefix_eq_of_not_app notApp
  | .trans prior next => fun notApp => by
      have middle := prior.rigid notApp
      exact (next.rigid (by simpa only [middle] using notApp)).trans middle
  | .atType _ trace => trace.rigid
  | .application .. | .argument .. => fun notApp => False.elim (notApp _ _ rfl)
  | .substituteAt trace _ _ => fun notApp => by
      have same := trace.rigid (by
        intro fn arg equal
        cases equal
        exact notApp _ _ rfl)
      rw [same]
  | .weakenAt trace _ => fun notApp => by
      have same := trace.rigid (by
        intro fn arg equal
        cases equal
        exact notApp _ _ rfl)
      rw [same]
  | .rebase _ trace => trace.rigid
  | .convertType trace _ => trace.rigid
  | .instantiate trace arguments =>
      AExpr.HeadRigid.map trace.rigid (AExpr.instL arguments) (by intros; rfl)
  | .appendContext trace _ | .extend trace _ => trace.rigid
termination_by structural trace

/-- Earlier argument checks can cross another local binder without any
new inference of their lifted expressions. -/
def SynthesisArgumentSpineOrigin.weaken {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {start result : AExpr β} {arguments : List (AExpr β)}
    (support : SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds
      entries context start arguments result) (domain : AExpr β) :
    SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds entries (context.push domain)
      (start.liftN 1) (arguments.map (AExpr.liftN 1 ·)) (result.liftN 1) :=
  match support with
  | .nil _ => .nil _
  | .snoc prior checked => by
      simpa only [List.map_append, List.map_cons, List.map_nil, AExpr.liftN_inst_zero] using
        (prior.weaken domain).snoc (checked.weaken domain)
  | .convert prior trace =>
      .convert (prior.weaken domain) (.weakenAt trace (ContextInsertion.root context domain))
termination_by structural support

def SynthesisArgumentSpineOrigin.instantiate {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {start result : AExpr β} {arguments : List (AExpr β)}
    (support : SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds
      entries context start arguments result) (levels : List VLevel) :
    SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds
      entries (context.map (AExpr.instL levels)) (start.instL levels)
      (arguments.map (AExpr.instL levels)) (result.instL levels) :=
  match support with
  | .nil _ => .nil _
  | .snoc prior checked => by
      simpa only [List.map_append, List.map_cons, List.map_nil, AExpr.instL_inst] using
        (prior.instantiate levels).snoc (checked.instantiate levels)
  | .convert prior trace => .convert (prior.instantiate levels) (.instantiate trace levels)
termination_by structural support

def SynthesisArgumentSpineOrigin.weakenAt {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext source target : Model.Context β}
    {incomingBounds : List VLevel} {cutoff : Nat} {start result : AExpr β} {arguments : List (AExpr β)}
    (support : SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds
      entries source start arguments result) (insertion : ContextInsertion source target cutoff) :
    SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds entries target
      (start.liftN 1 cutoff) (arguments.map (AExpr.liftN 1 · cutoff)) (result.liftN 1 cutoff) :=
  match support with
  | .nil _ => .nil _
  | .snoc prior checked => by
      simpa only [List.map_append, List.map_cons, List.map_nil, AExpr.liftN_inst_zero] using
        (prior.weakenAt insertion).snoc (.weakenAt checked insertion)
  | .convert prior trace => .convert (prior.weakenAt insertion) (.weakenAt trace insertion)
termination_by structural support

def SynthesisArgumentSpineOrigin.rebase {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming middle entries : Model.Environment β} {incomingContext middleContext context : Model.Context β}
    {incomingBounds middleBounds : List VLevel} {start result : AExpr β} {arguments : List (AExpr β)}
    (origin : SynthesisContext resolve incoming incomingContext incomingBounds middle middleContext middleBounds)
    (support : SynthesisArgumentSpineOrigin resolve middle middleContext middleBounds entries context start arguments result) :
    SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds entries context start arguments result :=
  match support with
  | .nil _ => .nil _
  | .snoc prior checked => (prior.rebase origin).snoc (.rebase origin checked)
  | .convert prior trace => .convert (prior.rebase origin) (.rebase origin trace)
termination_by structural support

def SynthesisArgumentSpineOrigin.appendContext {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {start result : AExpr β} {arguments : List (AExpr β)}
    (support : SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds
      entries context start arguments result) (outer : Model.Context β) :
    SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds
      entries (context ++ outer) start arguments result :=
  match support with
  | .nil _ => .nil _
  | .snoc prior checked => (prior.appendContext outer).snoc (checked.appendContext outer)
  | .convert prior trace => .convert (prior.appendContext outer) (.appendContext trace outer)
termination_by structural support

def SynthesisArgumentSpineOrigin.extend {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming earlier entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {start result : AExpr β} {arguments : List (AExpr β)}
    (support : SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds
      earlier context start arguments result) (extension : InterfaceExtends earlier entries) :
    SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds entries context start arguments result :=
  match support with
  | .nil _ => .nil _
  | .snoc prior checked => (prior.extend extension).snoc (checked.extend extension)
  | .convert prior trace => .convert (prior.extend extension) (.extend trace extension)
termination_by structural support

def SynthesisArgumentSpineOrigin.substituteAt {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext base source target : Model.Context β}
    {incomingBounds : List VLevel} {start result domain argument : AExpr β}
    {arguments : List (AExpr β)} {cutoff : Nat}
    (support : SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds
      entries source start arguments result)
    (value : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries base argument domain)
    (substitution : ContextSubstitution base domain argument source target cutoff) :
    SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds entries target
      (start.inst argument cutoff) (arguments.map (AExpr.inst · argument cutoff)) (result.inst argument cutoff) :=
  match support with
  | .nil _ => .nil _
  | .snoc prior checked => by
      simpa only [List.map_append, List.map_cons, List.map_nil, AExpr.inst_inst_zero] using
        (prior.substituteAt value substitution).snoc (checked.substituteAt value substitution)
  | .convert prior trace => .convert (prior.substituteAt value substitution) (.substituteAt trace value substitution)
termination_by structural support

/-- The head of a checked variable application uses the exact local type;
its argument checks remain available after leaving the original scope. -/
structure SynthesisVariableSpineOrigin {β : Type u} (resolve : Address → Option (ConstRef β))
    (incoming : Model.Environment β) (incomingContext : Model.Context β) (incomingBounds : List VLevel)
    (entries : Model.Environment β) (context : Model.Context β) (index : Nat)
    (arguments : List (AExpr β)) (type : AExpr β) where
  headType : AExpr β
  atIndex : context[index]? = some headType
  spine : SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds
    entries context headType arguments type

def SynthesisVariableSpineOrigin.appendContext {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {type : AExpr β} {arguments : List (AExpr β)} {index : Nat}
    (support : SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds
      entries context index arguments type) (outer : Model.Context β) :
    SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds
      entries (context ++ outer) index arguments type :=
  { headType := support.headType
    atIndex := by
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp support.atIndex).1]
      exact support.atIndex
    spine := support.spine.appendContext outer }

def SynthesisVariableSpineOrigin.instantiate {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {type : AExpr β} {arguments : List (AExpr β)} {index : Nat}
    (support : SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds
      entries context index arguments type) (levels : List VLevel) :
    SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds
      entries (context.map (AExpr.instL levels)) index (arguments.map (AExpr.instL levels)) (type.instL levels) :=
  { headType := support.headType.instL levels
    atIndex := by simp only [List.getElem?_map, support.atIndex, Option.map_some]
    spine := support.spine.instantiate levels }

def SynthesisVariableSpineOrigin.extend {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming earlier entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {type : AExpr β} {arguments : List (AExpr β)} {index : Nat}
    (support : SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds
      earlier context index arguments type) (extension : InterfaceExtends earlier entries) :
    SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds entries context index arguments type :=
  { headType := support.headType
    atIndex := support.atIndex
    spine := support.spine.extend extension }

/-- Applying an earlier parameter preserves a later variable-headed
codomain and updates every retained argument check in its dependent context. -/
def SynthesisVariableSpineOrigin.substituteAt {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext base source target : Model.Context β}
    {incomingBounds : List VLevel} {type domain argument : AExpr β}
    {arguments : List (AExpr β)} {index cutoff : Nat}
    (support : SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds
      entries source index arguments type)
    (value : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries base argument domain)
    (substitution : ContextSubstitution base domain argument source target cutoff)
    (distinct : index ≠ cutoff) :
    SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds entries target
      (if index < cutoff then index else index - 1)
      (arguments.map (AExpr.inst · argument cutoff)) (type.inst argument cutoff) :=
  { headType := support.headType.inst argument cutoff
    atIndex := substitution.lookup_other support.atIndex distinct
    spine := support.spine.substituteAt value substitution }

/-- The checked argument transports an already justified original beta
prefix to its substituted application result. The two resulting expressions
are computed by the proved substitution laws. -/
def SynthesisTypeTransport.substitutePrefixAt {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming origin entries : Model.Environment β}
    {incomingContext originContext base sourceContext targetContext : Model.Context β}
    {incomingBounds : List VLevel} {source reduced head domain argument : AExpr β}
    {arguments : List (AExpr β)} {level bound : VLevel} {count cutoff : Nat}
    (prior : SynthesisTypeTransport resolve incoming incomingContext incomingBounds
      origin originContext source reduced level entries sourceContext
      (head.appN arguments) (AExpr.betaPrefix count head arguments) bound)
    (enough : count ≤ head.lambdaDepth)
    (argumentOrigin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds
      entries base argument domain)
    (substitution : ContextSubstitution base domain argument sourceContext targetContext cutoff) :
    SynthesisTypeTransport resolve incoming incomingContext incomingBounds
      origin originContext source reduced level entries targetContext
      ((head.inst argument cutoff).appN (arguments.map (AExpr.inst · argument cutoff)))
      (AExpr.betaPrefix count (head.inst argument cutoff)
        (arguments.map (AExpr.inst · argument cutoff))) bound := by
  simpa only [AExpr.inst_appN, AExpr.inst_betaPrefix count head arguments argument cutoff enough] using
    prior.substituteAt argumentOrigin substitution

/-- Follow an actual argument call through the remaining dependent
parameters of a previously checked function type. The context relation
computes their updated domains at the same substitution cutoff. -/
def ApplicationInferenceTrace.substituteTypeOriginAt {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming origin entries : Model.Environment β}
    {incomingContext originContext context sourceContext targetContext : Model.Context β}
    {incomingBounds bounds : List VLevel} {source reduced head domain argumentType argument f body : AExpr β}
    {condition : Certified.PropWhen} {arguments : List (AExpr β)}
    {level bound functionBound argumentBound : VLevel} {count cutoff fuel : Nat}
    {locals : List FVarId} {before : TcState .anon} {fn rawArgument : KExpr .anon}
    (trace : ApplicationInferenceTrace fuel before fn rawArgument)
    (prior : SynthesisTypeTransport resolve incoming incomingContext incomingBounds
      origin originContext source reduced level entries sourceContext
      (head.appN arguments) (AExpr.betaPrefix count head arguments) bound)
    (enough : count ≤ head.lambdaDepth)
    (argumentContext : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
    (functionTree : SynthesisInference resolve entries locals context bounds fuel before fn
      f (.forallE condition domain body) functionBound)
    (argumentTree : SynthesisInference resolve entries locals context bounds fuel trace.functionState rawArgument
      argument argumentType argumentBound)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (functionReading : readScopedExpr? resolve locals fn = some f.erase)
    (argumentReading : readScopedExpr? resolve locals rawArgument = some argument.erase)
    (conditions : argumentType.annotations = domain.annotations)
    (hashPath : (trace.argumentType == trace.domain) = true)
    (comparisonFaithful : trace.argumentType.AddrFaithful trace.domain)
    (substitution : ContextSubstitution context domain argument sourceContext targetContext cutoff) :
    SynthesisTypeTransport resolve incoming incomingContext incomingBounds
      origin originContext source reduced level entries targetContext
      ((head.inst argument cutoff).appN (arguments.map (AExpr.inst · argument cutoff)))
      (AExpr.betaPrefix count (head.inst argument cutoff)
        (arguments.map (AExpr.inst · argument cutoff))) bound :=
  prior.substitutePrefixAt enough
    (.source (.applicationArgument argumentContext trace functionTree argumentTree agreement
      functionReading argumentReading conditions hashPath comparisonFaithful)) substitution

/-- Reuse a codomain check from an earlier closed function type at the
actual application site. The old function parameter keeps index zero while
the caller's locals are added outside it, then the actual argument call
supplies the substitution. -/
def ApplicationInferenceTrace.substituteTypeOrigin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming origin entries : Model.Environment β} {incomingContext originContext context : Model.Context β}
    {incomingBounds bounds : List VLevel} {source reduced head domain argumentType argument f body : AExpr β}
    {condition : Certified.PropWhen} {arguments : List (AExpr β)}
    {level bound functionBound argumentBound : VLevel} {count fuel : Nat}
    {locals : List FVarId} {before : TcState .anon} {fn rawArgument : KExpr .anon}
    (trace : ApplicationInferenceTrace fuel before fn rawArgument)
    (prior : TypeReductionTransport origin originContext source reduced level
      entries (Context.push domain [])
      (head.appN arguments) (AExpr.betaPrefix count head arguments) bound)
    (enough : count ≤ head.lambdaDepth)
    (argumentContext : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
    (functionTree : SynthesisInference resolve entries locals context bounds fuel before fn
      f (.forallE condition domain body) functionBound)
    (argumentTree : SynthesisInference resolve entries locals context bounds fuel trace.functionState rawArgument
      argument argumentType argumentBound)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (functionReading : readScopedExpr? resolve locals fn = some f.erase)
    (argumentReading : readScopedExpr? resolve locals rawArgument = some argument.erase)
    (conditions : argumentType.annotations = domain.annotations)
    (hashPath : (trace.argumentType == trace.domain) = true)
    (comparisonFaithful : trace.argumentType.AddrFaithful trace.domain) :
    SynthesisTypeTransport resolve incoming incomingContext incomingBounds
      origin originContext source reduced level entries context
      ((head.inst argument).appN (arguments.map (AExpr.inst · argument)))
      (AExpr.betaPrefix count (head.inst argument) (arguments.map (AExpr.inst · argument))) bound := by
  have imported : TypeReductionTransport origin originContext source reduced level
      entries (context.push domain) (head.appN arguments) (AExpr.betaPrefix count head arguments) bound := by
    simpa only [Context.push, List.map_nil, List.cons_append, List.nil_append] using
      prior.appendContext (context.map (AExpr.liftN 1 ·))
  exact trace.substituteTypeOriginAt (.pure imported) enough argumentContext functionTree argumentTree
    agreement functionReading argumentReading conditions hashPath comparisonFaithful .root

/-- Substituting an actual lambda argument for a checked variable head
exposes its own checked prefix, even though the original type had no leading
lambda. Remaining dependent parameters are handled at the same cutoff. -/
def ApplicationInferenceTrace.exposedTypeOriginAt {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β}
    {incomingContext context sourceContext targetContext : Model.Context β}
    {incomingBounds bounds : List VLevel} {domain argumentType argument f body : AExpr β}
    {condition : Certified.PropWhen} {arguments : List (AExpr β)}
    {level functionBound argumentBound : VLevel} {count cutoff fuel : Nat}
    {locals : List FVarId} {before : TcState .anon} {fn rawArgument : KExpr .anon}
    (trace : ApplicationInferenceTrace fuel before fn rawArgument)
    (origin : SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds
      entries sourceContext cutoff arguments (.sort level))
    (enough : count ≤ argument.lambdaDepth)
    (argumentContext : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
    (functionTree : SynthesisInference resolve entries locals context bounds fuel before fn
      f (.forallE condition domain body) functionBound)
    (argumentTree : SynthesisInference resolve entries locals context bounds fuel trace.functionState rawArgument
      argument argumentType argumentBound)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (functionReading : readScopedExpr? resolve locals fn = some f.erase)
    (argumentReading : readScopedExpr? resolve locals rawArgument = some argument.erase)
    (conditions : argumentType.annotations = domain.annotations)
    (hashPath : (trace.argumentType == trace.domain) = true)
    (comparisonFaithful : trace.argumentType.AddrFaithful trace.domain)
    (substitution : ContextSubstitution context domain argument sourceContext targetContext cutoff) :
    SynthesisReductionOrigin resolve incoming incomingContext incomingBounds entries targetContext
      (argument.liftN cutoff) (arguments.map (AExpr.inst · argument cutoff)) count level :=
  .substitutedVariable origin.spine origin.atIndex
    (.applicationArgument argumentContext trace functionTree argumentTree agreement functionReading argumentReading
      conditions hashPath comparisonFaithful) substitution enough

/-- A supplied lambda application contributes its existing arguments
before the original variable application's arguments. Both sets of checks
come from the actual inference calls retained at this application. -/
def ApplicationInferenceTrace.exposedApplicationOriginAt {β : Type u}
    {resolve : Address → Option (ConstRef β)} {incoming entries : Model.Environment β}
    {incomingContext context sourceContext targetContext : Model.Context β}
    {incomingBounds bounds : List VLevel} {domain argumentType binder inner f body : AExpr β}
    {condition headCondition : Certified.PropWhen} {initialArguments arguments : List (AExpr β)}
    {level functionBound argumentBound : VLevel} {count cutoff fuel : Nat}
    {locals : List FVarId} {before : TcState .anon} {fn rawArgument : KExpr .anon}
    (trace : ApplicationInferenceTrace fuel before fn rawArgument)
    (origin : SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds
      entries sourceContext cutoff arguments (.sort level))
    (enough : count ≤ inner.lambdaDepth + 1)
    (argumentContext : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
    (functionTree : SynthesisInference resolve entries locals context bounds fuel before fn
      f (.forallE condition domain body) functionBound)
    (argumentTree : SynthesisInference resolve entries locals context bounds fuel trace.functionState rawArgument
      ((AExpr.lam headCondition binder inner).appN initialArguments) argumentType argumentBound)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (functionReading : readScopedExpr? resolve locals fn = some f.erase)
    (argumentReading : readScopedExpr? resolve locals rawArgument =
      some ((AExpr.lam headCondition binder inner).appN initialArguments).erase)
    (conditions : argumentType.annotations = domain.annotations)
    (hashPath : (trace.argumentType == trace.domain) = true)
    (comparisonFaithful : trace.argumentType.AddrFaithful trace.domain)
    (substitution : ContextSubstitution context domain
      ((AExpr.lam headCondition binder inner).appN initialArguments) sourceContext targetContext cutoff) :
    SynthesisReductionOrigin resolve incoming incomingContext incomingBounds entries targetContext
      ((AExpr.lam headCondition binder inner).liftN cutoff)
      (initialArguments.map (AExpr.liftN cutoff ·) ++
        arguments.map (AExpr.inst · ((AExpr.lam headCondition binder inner).appN initialArguments) cutoff)) count level :=
  .substitutedApplication origin.spine origin.atIndex
    (.applicationArgument argumentContext trace functionTree argumentTree agreement functionReading argumentReading
      conditions hashPath comparisonFaithful) substitution enough

/-- Later actual arguments continue transporting an exposed prefix and
its reduction, including through dependent domains still left open. -/
def ApplicationInferenceTrace.substituteReductionOriginAt {β : Type u}
    {resolve : Address → Option (ConstRef β)} {incoming entries : Model.Environment β}
    {incomingContext context sourceContext targetContext : Model.Context β}
    {incomingBounds bounds : List VLevel} {head domain argumentType argument f body : AExpr β}
    {condition : Certified.PropWhen} {arguments : List (AExpr β)}
    {level functionBound argumentBound : VLevel} {count cutoff fuel : Nat}
    {locals : List FVarId} {before : TcState .anon} {fn rawArgument : KExpr .anon}
    (trace : ApplicationInferenceTrace fuel before fn rawArgument)
    (origin : SynthesisReductionOrigin resolve incoming incomingContext incomingBounds
      entries sourceContext head arguments count level)
    (enough : count ≤ head.lambdaDepth)
    (argumentContext : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
    (functionTree : SynthesisInference resolve entries locals context bounds fuel before fn
      f (.forallE condition domain body) functionBound)
    (argumentTree : SynthesisInference resolve entries locals context bounds fuel trace.functionState rawArgument
      argument argumentType argumentBound)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (functionReading : readScopedExpr? resolve locals fn = some f.erase)
    (argumentReading : readScopedExpr? resolve locals rawArgument = some argument.erase)
    (conditions : argumentType.annotations = domain.annotations)
    (hashPath : (trace.argumentType == trace.domain) = true)
    (comparisonFaithful : trace.argumentType.AddrFaithful trace.domain)
    (substitution : ContextSubstitution context domain argument sourceContext targetContext cutoff) :
    SynthesisReductionOrigin resolve incoming incomingContext incomingBounds entries targetContext
      (head.inst argument cutoff) (arguments.map (AExpr.inst · argument cutoff)) count level :=
  origin.map (trace.substituteTypeOriginAt (.pure .refl) enough argumentContext functionTree argumentTree
    agreement functionReading argumentReading conditions hashPath comparisonFaithful substitution)

/-- The domain and codomain retain their actual checks after interface
growth or insertion beneath any number of dependent binders. -/
structure SynthesisRetainedForall {β : Type u} (resolve : Address → Option (ConstRef β))
    (incoming : Model.Environment β) (incomingContext : Model.Context β) (incomingBounds : List VLevel)
    (entries : Model.Environment β) (context : Model.Context β)
    (condition : Certified.PropWhen) (domain body : AExpr β) where
  domainLevel : VLevel
  bodyLevel : VLevel
  domainBound : VLevel
  bound : VLevel
  domainCheck : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries
    context domain (.sort domainLevel) domainBound
  check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries
    (context.push domain) body (.sort bodyLevel) bound
  conditionAgrees : condition = Certified.zeroCondition bodyLevel

/-- A function-type check at the caller's current inference context. -/
abbrev SynthesisForallBodyCheck {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (context : Model.Context β) (bounds : List VLevel)
    (condition : Certified.PropWhen) (domain body : AExpr β) :=
  SynthesisRetainedForall resolve entries context bounds entries context condition domain body

private def ForallInferenceTrace.bodyCheck {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel}
    {fuel : Nat} {before : TcState .anon} {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body : KExpr .anon} {A B : AExpr β} {domainBound bodyBound : VLevel}
    (trace : ForallInferenceTrace fuel before name bi domain body)
    (opening : BinderOpeningSupport trace.domainState body)
    (domainTree : SynthesisInference resolve entries locals context bounds fuel before domain
      A (.sort (readLevel trace.domainLevel)) domainBound)
    (bodyTree : SynthesisInference resolve entries (trace.fresh :: locals) (context.push A)
      (readLevel trace.domainLevel :: bounds) fuel trace.openedState trace.opened
      B (.sort (readLevel trace.bodyLevel)) bodyBound)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (domainReading : readScopedExpr? resolve locals domain = some A.erase)
    (bodyReading : readScopedExpr? resolve locals body 1 = some B.erase) :
    SynthesisForallBodyCheck resolve entries context bounds
      (Certified.zeroCondition (readLevel trace.bodyLevel)) A B := by
  have opened := openBinder_sound opening (agreement.congr trace.contextPreserved.symm)
    (trace.absent agreement) domainReading bodyReading trace.openRun
  exact {
    domainLevel := readLevel trace.domainLevel
    bodyLevel := readLevel trace.bodyLevel
    domainBound := domainBound
    bound := bodyBound
    domainCheck := .source .current domainTree agreement domainReading trace.domainRun
    check := .source (.push .current domainTree agreement domainReading trace.domainRun)
      bodyTree opened.2.2.1 opened.2.1 trace.bodyRun
    conditionAgrees := rfl }

def BinderInference.forallBodyCheck {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β}
    {bounds : List VLevel} {fuel : Nat} {before : TcState .anon} {source : KExpr .anon}
    {condition : Certified.PropWhen} {domain body type : AExpr β}
    (support : BinderInference resolve entries locals context fuel before source
      (.forallE condition domain body) type)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some (AExpr.forallE condition domain body).erase) :
    SynthesisForallBodyCheck resolve entries context bounds condition domain body := by
  cases support with
  | forallE miss trace opening domainTree bodyTree =>
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_all_parts reading
      exact trace.bodyCheck opening (.known domainTree (.sort _)) (.known bodyTree (.sort _))
        (miss.localContext.symm ▸ agreement) domainReads bodyReads

mutual

/-- Recover the recorded codomain check by inspecting the production
inference tree. This does not assume a new call on an inferred codomain. -/
private def SynthesisInference.forallBodyCheckAux {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β}
    {bounds : List VLevel} {fuel : Nat} {before : TcState .anon} {source : KExpr .anon}
    {condition : Certified.PropWhen} {term domain body type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase) :
    term = .forallE condition domain body → SynthesisForallBodyCheck resolve entries context bounds condition domain body :=
  match support with
  | .known inference _ | .reuseType inference .. => fun same => by
      cases same
      exact inference.forallBodyCheck agreement reading
  | .cached tree priorAgreement priorReading _ _ _ _ => fun same =>
      tree.forallBodyCheckAux priorAgreement priorReading same
  | .cachedFrom check _ _ => fun same => check.forallBody same
  | .forallE miss trace opening domainTree bodyTree .. => fun same => by
      cases same
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_all_parts reading
      exact trace.bodyCheck opening domainTree bodyTree
        (miss.localContext.symm ▸ agreement) domainReads bodyReads
  | .fvar .. | .app .. | .appBeta .. | .lam .. | .lamBeta .. => fun same => by cases same
termination_by structural support

def SynthesisRetainedCheck.forallBody {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β} {level : VLevel}
    {condition : Certified.PropWhen} {domain body : AExpr β}
    (check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type level) :
    term = .forallE condition domain body →
      SynthesisRetainedForall resolve incoming incomingContext incomingBounds entries context condition domain body :=
  match check with
  | .source contextOrigin tree agreement reading _ => fun same =>
      let child := tree.forallBodyCheckAux agreement reading same
      ⟨child.domainLevel, child.bodyLevel, child.domainBound, child.bound,
        .rebase contextOrigin child.domainCheck, .rebase contextOrigin child.check,
        child.conditionAgrees⟩
  | .extend prior extension => fun same =>
      let child := prior.forallBody same
      ⟨child.domainLevel, child.bodyLevel, child.domainBound, child.bound,
        child.domainCheck.extend extension, child.check.extend extension, child.conditionAgrees⟩
  | .weakenAt prior insertion => fun same => by
      let view := liftedForallView same
      let child := prior.forallBody view.sourceEq
      refine ⟨child.domainLevel, child.bodyLevel, child.domainBound, child.bound, ?_, ?_, child.conditionAgrees⟩
      · simpa only [view.domainEq, AExpr.liftN] using child.domainCheck.weakenAt insertion
      · simpa only [view.domainEq, view.bodyEq, AExpr.liftN] using
          child.check.weakenAt (insertion.push view.originalDomain)
  | .rebase origin prior => fun same =>
      let child := prior.forallBody same
      ⟨child.domainLevel, child.bodyLevel, child.domainBound, child.bound,
        .rebase origin child.domainCheck, .rebase origin child.check, child.conditionAgrees⟩
termination_by structural check

end

def SynthesisInference.forallBodyCheck {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β}
    {bounds : List VLevel} {fuel : Nat} {before : TcState .anon} {source : KExpr .anon}
    {condition : Certified.PropWhen} {domain body type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source
      (.forallE condition domain body) type level)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some (AExpr.forallE condition domain body).erase) :
    SynthesisForallBodyCheck resolve entries context bounds condition domain body :=
  support.forallBodyCheckAux agreement reading rfl

private theorem list_reverse_induction {α : Type u} {motive : List α → Prop}
    (nil : motive [])
    (append_singleton : ∀ tail last, motive tail → motive (tail ++ [last]))
    (values : List α) : motive values := by
  have reversed : ∀ items : List α, motive items.reverse := by
    intro items
    induction items with
    | nil => exact nil
    | cons item items ih =>
        simpa only [List.reverse_cons] using append_singleton items.reverse item ih
  simpa using reversed values.reverse

private theorem not_variable_spine {β : Type u} {term : AExpr β}
    (notApp : ∀ fn arg, term ≠ .app fn arg) (notVar : ∀ index, term ≠ .bvar index)
    (index : Nat) (arguments : List (AExpr β)) : term ≠ (AExpr.bvar index).appN arguments := by
  intro same
  induction arguments using list_reverse_induction with
  | nil => exact notVar index same
  | append_singleton arguments argument ih =>
      exact notApp _ _ (by simpa only [AExpr.appN_append, AExpr.appN_cons, AExpr.appN_nil] using same)

private theorem bvar_variable_spine {β : Type u} {left right : Nat} {arguments : List (AExpr β)}
    (same : AExpr.bvar left = (AExpr.bvar right).appN arguments) : arguments = [] ∧ left = right := by
  induction arguments using list_reverse_induction with
  | nil => exact ⟨rfl, AExpr.bvar.inj same⟩
  | append_singleton arguments argument ih =>
      simp only [AExpr.appN_append, AExpr.appN_cons, AExpr.appN_nil] at same
      cases same

private theorem app_variable_spine {β : Type u} {fn arg : AExpr β} {index : Nat}
    {arguments : List (AExpr β)} (same : fn.app arg = (AExpr.bvar index).appN arguments) :
    arguments = arguments.dropLast ++ [arg] ∧ fn = (AExpr.bvar index).appN arguments.dropLast := by
  induction arguments using list_reverse_induction with
  | nil => cases same
  | append_singleton arguments argument ih =>
      simp only [AExpr.appN_append, AExpr.appN_cons, AExpr.appN_nil, AExpr.app.injEq] at same
      simp only [List.dropLast_concat]
      exact ⟨by rw [same.2], same.1⟩

/-- Extract the actual argument calls from a checked variable application.
No type check on the generated substitutions is added. -/
def BinderInference.variableSpineOrigin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {locals : List FVarId} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon} {term type : AExpr β}
    (support : BinderInference resolve entries locals context fuel before source term type)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (index : Nat) (arguments : List (AExpr β)) (headEquals : term = (AExpr.bvar index).appN arguments) :
    SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds entries context index arguments type :=
  match support with
  | .fvar _ _ atIndex => by
      obtain ⟨rfl, rfl⟩ := bvar_variable_spine headEquals
      exact ⟨_, atIndex, .nil _⟩
  | .app _ miss trace functionTree head argumentTree conditions hashPath comparisonFaithful
      _ _ _ _ _ _ => by
      obtain ⟨functionReading, argumentReading⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have parts := app_variable_spine headEquals
      have prior := functionTree.variableSpineOrigin (incoming := incoming) (incomingContext := incomingContext)
        (incomingBounds := incomingBounds) keyedAgreement functionReading index arguments.dropLast parts.2
      have spine := prior.spine.snoc (.source (.binderArgument trace functionTree head argumentTree
        keyedAgreement functionReading argumentReading conditions hashPath comparisonFaithful))
      exact ⟨prior.headType, prior.atIndex, by simpa only [← parts.1] using spine⟩
  | .sort .. | .cachedSort .. | .const .. | .polymorphic .. | .cachedConst .. | .forallE .. | .lam .. => by
      exact False.elim (not_variable_spine (by intro fn arg same; cases same)
        (by intro index same; cases same) index arguments headEquals)
termination_by structural support

def SynthesisVariableSpineOrigin.weakenAt {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext source target : Model.Context β}
    {incomingBounds : List VLevel} {cutoff index : Nat} {arguments : List (AExpr β)} {type : AExpr β}
    (spine : SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds entries source index arguments type)
    (insertion : ContextInsertion source target cutoff) :
    SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds entries target (liftVar 1 index cutoff)
      (arguments.map (AExpr.liftN 1 · cutoff)) (type.liftN 1 cutoff) :=
  ⟨spine.headType.liftN 1 cutoff,
    by simpa only [liftVar, Nat.add_comm 1] using insertion.lookup spine.atIndex,
    spine.spine.weakenAt insertion⟩

def SynthesisVariableSpineOrigin.rebase {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming middle entries : Model.Environment β} {incomingContext middleContext context : Model.Context β}
    {incomingBounds middleBounds : List VLevel} {index : Nat} {arguments : List (AExpr β)} {type : AExpr β}
    (spine : SynthesisVariableSpineOrigin resolve middle middleContext middleBounds entries context index arguments type)
    (origin : SynthesisContext resolve incoming incomingContext incomingBounds middle middleContext middleBounds) :
    SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds entries context index arguments type :=
  ⟨spine.headType, spine.atIndex, spine.spine.rebase origin⟩

mutual

def SynthesisInference.variableSpineOrigin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds bounds : List VLevel} {locals : List FVarId} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon} {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (contextOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (index : Nat) (arguments : List (AExpr β)) (headEquals : term = (AExpr.bvar index).appN arguments) :
    SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds entries context index arguments type :=
  match support with
  | .known inference _ | .reuseType inference .. | .fvar inference .. =>
      inference.variableSpineOrigin agreement reading index arguments headEquals
  | .cached tree priorAgreement priorReading _ _ _ _ =>
      tree.variableSpineOrigin contextOrigin priorAgreement priorReading index arguments headEquals
  | .cachedFrom check _ _ => (check.variableSpineOrigin index arguments headEquals).rebase contextOrigin
  | .app _ miss trace functionTree argumentTree conditions hashPath comparisonFaithful _ _ _ _ _ _ => by
      obtain ⟨functionReading, argumentReading⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have parts := app_variable_spine headEquals
      have prior := functionTree.variableSpineOrigin contextOrigin keyedAgreement functionReading
        index arguments.dropLast parts.2
      have spine := prior.spine.snoc (.source (.applicationArgument contextOrigin trace functionTree argumentTree
        keyedAgreement functionReading argumentReading conditions hashPath comparisonFaithful))
      exact ⟨prior.headType, prior.atIndex, by simpa only [← parts.1] using spine⟩
  | .appBeta _ miss trace functionTree exposure exposureCoherent reduction argumentTree conditions hashPath
      comparisonFaithful _ _ _ _ _ _ => by
      obtain ⟨functionReading, argumentReading⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have parts := app_variable_spine headEquals
      have prior := functionTree.variableSpineOrigin contextOrigin keyedAgreement functionReading
        index arguments.dropLast parts.2
      have spine := (prior.spine.convert (.rebase contextOrigin reduction)).snoc
        (.source (.applicationBetaArgument contextOrigin trace functionTree exposure exposureCoherent argumentTree
          keyedAgreement functionReading argumentReading conditions hashPath comparisonFaithful))
      exact ⟨prior.headType, prior.atIndex, by simpa only [← parts.1] using spine⟩
  | .forallE .. | .lam .. | .lamBeta .. => by
      exact False.elim (not_variable_spine (by intro fn arg same; cases same)
        (by intro index same; cases same) index arguments headEquals)
termination_by structural support

def SynthesisRetainedCheck.variableSpineOrigin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β} {level : VLevel}
    (check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type level)
    (index : Nat) (arguments : List (AExpr β)) (same : term = (AExpr.bvar index).appN arguments) :
    SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds entries context index arguments type :=
  match check with
  | .source contextOrigin tree agreement reading _ =>
      tree.variableSpineOrigin contextOrigin agreement reading index arguments same
  | .extend prior extension => (prior.variableSpineOrigin index arguments same).extend extension
  | .weakenAt prior insertion => by
      let view := liftedVariableSpineView same
      let old := prior.variableSpineOrigin view.originalIndex view.originalArguments view.sourceEq
      simpa only [view.indexEq, view.argumentsEq] using old.weakenAt insertion
  | .rebase origin prior => (prior.variableSpineOrigin index arguments same).rebase origin
termination_by structural check

end

def SynthesisForallBodyCheck.variableSpine {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds bounds : List VLevel} {condition : Certified.PropWhen} {domain : AExpr β}
    {index : Nat} {arguments : List (AExpr β)}
    (check : SynthesisForallBodyCheck resolve entries context bounds condition domain
      ((AExpr.bvar index).appN arguments))
    (parentOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds) :
    SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds entries
      (context.push domain) index arguments (.sort check.bodyLevel) :=
  (check.check.variableSpineOrigin index arguments rfl).rebase parentOrigin

/-- Keep the actual variable-application checks inside a lambda body.
The body's inferred type is retained separately from the lambda's eventual
codomain, which synthesis may obtain by reducing that type. -/
def BinderInference.lambdaBodyVariableSpine {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {locals : List FVarId} {fuel index : Nat}
    {before : TcState .anon} {source : KExpr .anon} {domain type : AExpr β}
    {condition : Certified.PropWhen} {arguments : List (AExpr β)}
    (support : BinderInference resolve entries locals context fuel before source
      (.lam condition domain ((AExpr.bvar index).appN arguments)) type)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source =
      some (AExpr.lam condition domain ((AExpr.bvar index).appN arguments)).erase) :
    Σ resultType, SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds
      entries (context.push domain) index arguments resultType := by
  cases support with
  | lam full miss trace opening bodyTree constructed bound coherent closingFaithful faithful =>
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_lam_parts reading
      have domainAgreement := (miss.localContext.symm ▸ agreement).congr trace.contextPreserved.symm
      obtain ⟨_, openedReads, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement (trace.domainValid.freshReading domainAgreement) domainReads bodyReads trace.openRun
      exact ⟨_, bodyTree.variableSpineOrigin openedAgreement openedReads index arguments rfl⟩

mutual

private def SynthesisInference.lambdaBodyVariableSpineAux {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds bounds : List VLevel} {locals : List FVarId} {fuel index : Nat}
    {before : TcState .anon} {source : KExpr .anon} {term domain type : AExpr β}
    {condition : Certified.PropWhen} {arguments : List (AExpr β)} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (contextOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase) :
    term = .lam condition domain ((AExpr.bvar index).appN arguments) →
      Σ resultType, SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds
        entries (context.push domain) index arguments resultType :=
  match support with
  | .known inference _ => fun same => by
      cases same
      exact inference.lambdaBodyVariableSpine agreement reading
  | .reuseType inference .. => fun same => by
      cases same
      exact inference.lambdaBodyVariableSpine agreement reading
  | .cached tree priorAgreement priorReading _ _ _ _ => fun same =>
      tree.lambdaBodyVariableSpineAux contextOrigin priorAgreement priorReading same
  | .cachedFrom check _ _ => fun same =>
      let child := check.lambdaBodyVariableSpine same
      ⟨child.1, child.2.rebase contextOrigin⟩
  | .lam full miss trace opening domainTree bodyTree conditionAgrees constructed bound coherent
      closingFaithful faithful => fun same => by
      cases same
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_lam_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have domainAgreement := keyedAgreement.congr trace.contextPreserved.symm
      obtain ⟨_, openedReads, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement (trace.domainValid.freshReading domainAgreement) domainReads bodyReads trace.openRun
      exact ⟨_, bodyTree.variableSpineOrigin
        (contextOrigin.push domainTree keyedAgreement domainReads trace.domainRun)
        openedAgreement openedReads index arguments rfl⟩
  | .lamBeta full miss trace opening domainTree bodyTree origin reduction conditionAgrees
      constructed bound closingFaithful faithful => fun same => by
      cases same
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_lam_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have domainAgreement := keyedAgreement.congr trace.contextPreserved.symm
      obtain ⟨_, openedReads, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement (trace.domainValid.freshReading domainAgreement) domainReads bodyReads trace.openRun
      exact ⟨_, bodyTree.variableSpineOrigin
        (contextOrigin.push domainTree keyedAgreement domainReads trace.domainRun)
        openedAgreement openedReads index arguments rfl⟩

  | .fvar .. | .app .. | .appBeta .. | .forallE .. => fun same => by cases same
termination_by structural support

def SynthesisRetainedCheck.lambdaBodyVariableSpine {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type domain : AExpr β} {level : VLevel}
    {condition : Certified.PropWhen} {index : Nat} {arguments : List (AExpr β)}
    (check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type level) :
    term = .lam condition domain ((AExpr.bvar index).appN arguments) →
      Σ resultType, SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds
        entries (context.push domain) index arguments resultType :=
  match check with
  | .source contextOrigin tree agreement reading _ => fun same =>
      tree.lambdaBodyVariableSpineAux contextOrigin agreement reading same
  | .extend prior extension => fun same =>
      let child := prior.lambdaBodyVariableSpine same
      ⟨child.1, child.2.extend extension⟩
  | .weakenAt (cutoff := cutoff) prior insertion => fun same => by
      let lambda := liftedLambdaView same
      let body := liftedVariableSpineView lambda.bodyEq.symm
      let child := prior.lambdaBodyVariableSpine
        (lambda.sourceEq.trans (congrArg (AExpr.lam condition lambda.originalDomain) body.sourceEq))
      refine ⟨child.1.liftN 1 (cutoff + 1), ?_⟩
      simpa only [lambda.domainEq, body.indexEq, body.argumentsEq] using
        child.2.weakenAt (insertion.push lambda.originalDomain)
  | .rebase origin prior => fun same =>
      let child := prior.lambdaBodyVariableSpine same
      ⟨child.1, child.2.rebase origin⟩
termination_by structural check

end

def SynthesisInference.lambdaBodyVariableSpine {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds bounds : List VLevel} {locals : List FVarId} {fuel index : Nat}
    {before : TcState .anon} {source : KExpr .anon} {domain type : AExpr β}
    {condition : Certified.PropWhen} {arguments : List (AExpr β)} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source
      (.lam condition domain ((AExpr.bvar index).appN arguments)) type level)
    (contextOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source =
      some (AExpr.lam condition domain ((AExpr.bvar index).appN arguments)).erase) :
    Σ resultType, SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds
      entries (context.push domain) index arguments resultType :=
  support.lambdaBodyVariableSpineAux contextOrigin agreement reading rfl

theorem BinderInference.lambdaPrefix {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon} {term type : AExpr β}
    (support : BinderInference resolve entries locals context fuel before source term type) :
    LambdaPrefix term type term.lambdaDepth := by
  induction support with
  | lam _ _ _ _ _ _ _ _ _ _ ih => exact .lam ih
  | _ => exact .zero _ _

mutual

theorem SynthesisInference.lambdaPrefix {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon} {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source term type level) :
    LambdaPrefix term type term.lambdaDepth :=
  match support with
  | .known inference _ => inference.lambdaPrefix
  | .cached tree .. => tree.lambdaPrefix
  | .cachedFrom check _ _ => check.lambdaPrefix
  | .reuseType inference _ _ _ _ _ => inference.lambdaPrefix
  | .lam _ _ _ _ _ bodyTree _ _ _ _ _ _ => .lam bodyTree.lambdaPrefix
  | .lamBeta _ _ _ _ _ bodyTree _ _ _ _ _ _ _ => by
      have depth := bodyTree.lambdaPrefix.lambdaDepth_zero
        (AExpr.appN_ne_forallE (by intro condition domain body same; cases same) _)
      simpa only [AExpr.lambdaDepth, depth] using LambdaPrefix.lam (LambdaPrefix.zero _ _)
  | .fvar .. | .app .. | .appBeta .. | .forallE .. => .zero _ _
termination_by structural support

theorem SynthesisRetainedCheck.lambdaPrefix {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β} {level : VLevel}
    (check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type level) :
    LambdaPrefix term type term.lambdaDepth :=
  match check with
  | .source _ tree _ _ _ => tree.lambdaPrefix
  | .extend prior _ | .rebase _ prior => prior.lambdaPrefix
  | .weakenAt prior _ => by
      simpa only [AExpr.lambdaDepth_liftN] using prior.lambdaPrefix.liftN 1 _
termination_by structural check

end

def SynthesisRetainedCheck.origin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β} {level : VLevel}
    (check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type level) :
    SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type :=
  match check with
  | .source contextOrigin tree agreement reading accepted =>
      .source (.checked contextOrigin tree agreement reading accepted)
  | .extend prior extension => prior.origin.extend extension
  | .weakenAt prior insertion => .weakenAt prior.origin insertion
  | .rebase origin prior => .rebase origin prior.origin
termination_by structural check

def SynthesisRetainedCheck.typeOrigin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β} {level : VLevel}
    (check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type level) :
    SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context type (.sort level) :=
  match check with
  | .source contextOrigin tree agreement reading accepted =>
      .inferredType contextOrigin tree agreement reading accepted
  | .extend prior extension => prior.typeOrigin.extend extension
  | .weakenAt prior insertion => .weakenAt prior.typeOrigin insertion
  | .rebase origin prior => .rebase origin prior.typeOrigin
termination_by structural check

/-- The head's check and every argument check of an actual application
spine, retained as data for subsequent reductions and substitutions. -/
structure SynthesisSpineOrigin {β : Type u} (resolve : Address → Option (ConstRef β))
    (incoming : Model.Environment β) (incomingContext : Model.Context β) (incomingBounds : List VLevel)
    (entries : Model.Environment β) (context : Model.Context β)
    (head : AExpr β) (arguments : List (AExpr β)) (type : AExpr β) where
  headType : AExpr β
  headOrigin : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context head headType
  leading : LambdaPrefix head headType head.lambdaDepth
  argumentsOrigin : SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds
    entries context headType arguments type

private theorem appN_last {β : Type u} {head : AExpr β} {arguments : List (AExpr β)}
    (nonempty : arguments ≠ []) :
    head.appN arguments = (head.appN arguments.dropLast).app (arguments.getLast nonempty) := by
  calc
    head.appN arguments = head.appN (arguments.dropLast ++ [arguments.getLast nonempty]) :=
      congrArg (AExpr.appN head) (List.dropLast_concat_getLast nonempty).symm
    _ = _ := by simp only [AExpr.appN_append, AExpr.appN_cons, AExpr.appN_nil]

private theorem nonapp_spine_empty {β : Type u} {term head : AExpr β} {arguments : List (AExpr β)}
    (notApp : ∀ fn arg, term ≠ .app fn arg) (same : term = head.appN arguments) : arguments = [] := by
  by_contra nonempty
  exact notApp _ _ (same.trans (appN_last nonempty))

private theorem app_spine_parts {β : Type u} {fn arg head : AExpr β} {arguments : List (AExpr β)}
    (nonempty : arguments ≠ []) (same : fn.app arg = head.appN arguments) :
    arguments = arguments.dropLast ++ [arg] ∧ fn = head.appN arguments.dropLast := by
  have parts := AExpr.app.inj (same.trans (appN_last nonempty))
  exact ⟨by rw [parts.2]; exact (List.dropLast_concat_getLast nonempty).symm, parts.1⟩

def BinderInference.spineOrigin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {locals : List FVarId} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon} {term type : AExpr β}
    (support : BinderInference resolve entries locals context fuel before source term type)
    (checked : SynthesisCheckedOrigin resolve incoming incomingContext incomingBounds entries context term type)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (head : AExpr β) (arguments : List (AExpr β)) (same : term = head.appN arguments) :
    SynthesisSpineOrigin resolve incoming incomingContext incomingBounds entries context head arguments type :=
  if empty : arguments = [] then by
    subst arguments
    simp only [AExpr.appN_nil] at same
    subst head
    exact ⟨type, .source checked, support.lambdaPrefix, .nil _⟩
  else match support with
  | .app _ miss trace functionTree functionHead argumentTree conditions hashPath comparisonFaithful
      _ _ _ _ _ _ => by
      obtain ⟨functionReading, argumentReading⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have parts := app_spine_parts empty same
      have prior := functionTree.spineOrigin (incoming := incoming) (incomingContext := incomingContext)
        (incomingBounds := incomingBounds)
        (.binderHead functionTree functionHead keyedAgreement functionReading trace.functionRun)
        keyedAgreement functionReading head arguments.dropLast parts.2
      refine ⟨prior.headType, prior.headOrigin, prior.leading, ?_⟩
      simpa only [← parts.1] using prior.argumentsOrigin.snoc
        (.source (.binderArgument trace functionTree functionHead argumentTree keyedAgreement
          functionReading argumentReading conditions hashPath comparisonFaithful))
  | .sort .. | .cachedSort .. | .fvar .. | .const .. | .polymorphic .. | .cachedConst .. | .forallE .. | .lam .. => by
      exact False.elim (empty (nonapp_spine_empty (by intro fn arg same; cases same) same))
termination_by structural support

def SynthesisSpineOrigin.extend {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming earlier entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {head type : AExpr β} {arguments : List (AExpr β)}
    (spine : SynthesisSpineOrigin resolve incoming incomingContext incomingBounds earlier context head arguments type)
    (extension : InterfaceExtends earlier entries) :
    SynthesisSpineOrigin resolve incoming incomingContext incomingBounds entries context head arguments type :=
  ⟨spine.headType, spine.headOrigin.extend extension, spine.leading, spine.argumentsOrigin.extend extension⟩

def SynthesisSpineOrigin.weakenAt {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext source target : Model.Context β}
    {incomingBounds : List VLevel} {cutoff : Nat} {head type : AExpr β} {arguments : List (AExpr β)}
    (spine : SynthesisSpineOrigin resolve incoming incomingContext incomingBounds entries source head arguments type)
    (insertion : ContextInsertion source target cutoff) :
    SynthesisSpineOrigin resolve incoming incomingContext incomingBounds entries target (head.liftN 1 cutoff)
      (arguments.map (AExpr.liftN 1 · cutoff)) (type.liftN 1 cutoff) :=
  ⟨spine.headType.liftN 1 cutoff, .weakenAt spine.headOrigin insertion,
    by simpa only [AExpr.lambdaDepth_liftN] using spine.leading.liftN 1 cutoff,
    spine.argumentsOrigin.weakenAt insertion⟩

def SynthesisSpineOrigin.rebase {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming middle entries : Model.Environment β} {incomingContext middleContext context : Model.Context β}
    {incomingBounds middleBounds : List VLevel} {head type : AExpr β} {arguments : List (AExpr β)}
    (spine : SynthesisSpineOrigin resolve middle middleContext middleBounds entries context head arguments type)
    (origin : SynthesisContext resolve incoming incomingContext incomingBounds middle middleContext middleBounds) :
    SynthesisSpineOrigin resolve incoming incomingContext incomingBounds entries context head arguments type :=
  ⟨spine.headType, .rebase origin spine.headOrigin, spine.leading, spine.argumentsOrigin.rebase origin⟩

mutual

/-- Recover every application argument and the head's original checked
lambda prefix from the executed source inference, including binder-backed
local and constant spines. -/
def SynthesisInference.spineOrigin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds bounds : List VLevel} {locals : List FVarId} {fuel : Nat}
    {before after : TcState .anon} {source result : KExpr .anon} {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (contextOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after)
    (head : AExpr β) (arguments : List (AExpr β)) (same : term = head.appN arguments) :
    SynthesisSpineOrigin resolve incoming incomingContext incomingBounds entries context head arguments type :=
  if empty : arguments = [] then by
    subst arguments
    simp only [AExpr.appN_nil] at same
    subst head
    exact ⟨type, .source (.checked contextOrigin support agreement reading accepted), support.lambdaPrefix, .nil _⟩
  else match support with
  | .cached tree priorAgreement priorReading priorRun _ _ _ =>
      tree.spineOrigin contextOrigin priorAgreement priorReading priorRun head arguments same
  | .cachedFrom check _ _ => (check.spineOrigin head arguments same).rebase contextOrigin
  | .known inference formation =>
      inference.spineOrigin (.checked contextOrigin (.known inference formation) agreement reading accepted)
        agreement reading head arguments same
  | .reuseType inference typeTree extension typeReading typeRun equivalent =>
      inference.spineOrigin
        (.checked contextOrigin (.reuseType inference typeTree extension typeReading typeRun equivalent)
          agreement reading accepted) agreement reading head arguments same
  | .app _ miss trace functionTree argumentTree conditions hashPath comparisonFaithful _ _ _ _ _ _ => by
      obtain ⟨functionReading, argumentReading⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have parts := app_spine_parts empty same
      have prior := functionTree.spineOrigin contextOrigin keyedAgreement functionReading trace.functionRun
        head arguments.dropLast parts.2
      refine ⟨prior.headType, prior.headOrigin, prior.leading, ?_⟩
      simpa only [← parts.1] using prior.argumentsOrigin.snoc
        (.source (.applicationArgument contextOrigin trace functionTree argumentTree keyedAgreement
          functionReading argumentReading conditions hashPath comparisonFaithful))
  | .appBeta _ miss trace functionTree exposure exposureCoherent reduction argumentTree conditions hashPath
      comparisonFaithful _ _ _ _ _ _ => by
      obtain ⟨functionReading, argumentReading⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have parts := app_spine_parts empty same
      have prior := functionTree.spineOrigin contextOrigin keyedAgreement functionReading trace.functionRun
        head arguments.dropLast parts.2
      refine ⟨prior.headType, prior.headOrigin, prior.leading, ?_⟩
      simpa only [← parts.1] using (prior.argumentsOrigin.convert (.rebase contextOrigin reduction)).snoc
        (.source (.applicationBetaArgument contextOrigin trace functionTree exposure exposureCoherent argumentTree
          keyedAgreement functionReading argumentReading conditions hashPath comparisonFaithful))
  | .fvar .. | .forallE .. | .lam .. | .lamBeta .. => by
      exact False.elim (empty (nonapp_spine_empty (by intro fn arg same; cases same) same))
termination_by structural support

def SynthesisRetainedCheck.spineOrigin {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β} {level : VLevel}
    (check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type level)
    (head : AExpr β) (arguments : List (AExpr β)) (same : term = head.appN arguments) :
    SynthesisSpineOrigin resolve incoming incomingContext incomingBounds entries context head arguments type :=
  match check with
  | .source contextOrigin tree agreement reading accepted =>
      tree.spineOrigin contextOrigin agreement reading accepted head arguments same
  | .extend prior extension => (prior.spineOrigin head arguments same).extend extension
  | .weakenAt prior insertion => by
      let view := liftedSpineView same
      let old := prior.spineOrigin view.originalHead view.originalArguments view.sourceEq
      simpa only [view.headEq, view.argumentsEq] using old.weakenAt insertion
  | .rebase origin prior => (prior.spineOrigin head arguments same).rebase origin
termination_by structural check

end

def SynthesisSpineOrigin.betaTrace {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {head type : AExpr β} {arguments : List (AExpr β)} {count : Nat}
    (origin : SynthesisSpineOrigin resolve incoming incomingContext incomingBounds entries context head arguments type)
    (enough : count ≤ head.lambdaDepth) :
    SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context
      (head.appN arguments) (AExpr.betaPrefix count head arguments) type :=
  .prefix origin.headOrigin (origin.leading.truncate enough) origin.argumentsOrigin

theorem SynthesisHead.appN_head {β : Type u} {head : AExpr β} {arguments : List (AExpr β)}
    (support : SynthesisHead (head.appN arguments)) : SynthesisHead head := by
  induction arguments generalizing head with
  | nil => exact support
  | cons argument arguments ih =>
      have applied := ih support
      cases applied with
      | app head => exact head

private theorem BinderInference.no_lambda_spine {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon}
    {condition : Certified.PropWhen} {domain body type : AExpr β} {arguments : List (AExpr β)}
    (support : BinderInference resolve entries locals context fuel before source
      ((AExpr.lam condition domain body).appN arguments) type)
    (nonempty : arguments ≠ []) : False := by
  induction arguments using list_reverse_induction with
  | nil => exact nonempty rfl
  | append_singleton arguments argument ih =>
      simp only [AExpr.appN_append, AExpr.appN_cons, AExpr.appN_nil] at support
      cases support with
      | app _ _ _ _ head => cases head.appN_head

theorem BinderInference.lambdaSpineTyping {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon} {term type : AExpr β}
    (support : BinderInference resolve entries locals context fuel before source term type)
    (typed : TypingClaim.{u,v} entries context term type) :
    LambdaSpineTyping.{u,v} entries context term type := by
  intro condition domain body arguments same
  subst term
  by_cases empty : arguments = []
  · subst arguments
    exact ⟨type, typed, support.lambdaPrefix, .nil _⟩
  · exact False.elim (support.no_lambda_spine empty)

mutual

/-- Simultaneous soundness of the term and formation of its returned type.
The context hypothesis is discharged by actual domain inference at each
binder, and by the empty context at the production declaration boundary. -/
theorem SynthesisInference.soundWithSpine {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {fuel : Nat}
    {before after : TcState .anon} {source result : KExpr .anon}
    {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
    readScopedExpr? resolve locals result = some type.erase ∧
      TypingClaim.{u,v} entries context term type ∧
      TypingClaim.{u,v} entries context type (.sort level) ∧
      LambdaSpineTyping.{u,v} entries context term type :=
  match support with
  | .known inference formation => by
      obtain ⟨reads, checked⟩ := inference.sound agreement reading accepted
      have typed := checked.typing formation.sound
      exact ⟨reads, typed, formation.sound, inference.lambdaSpineTyping typed⟩
  | .cached tree priorAgreement priorReading priorRun hit cacheMatch resultReading => by
      obtain ⟨_, typed, formation, spine⟩ :=
        tree.soundWithSpine formed priorAgreement priorReading priorRun
      rw [hit.run] at accepted
      cases accepted
      exact ⟨cacheMatch.symm ▸ resultReading, typed, formation, spine⟩
  | .cachedFrom check hit resultReading => by
      obtain ⟨typed, formation, spine⟩ := check.soundWithSpine formed
      rw [hit.run] at accepted
      cases accepted
      exact ⟨resultReading, typed, formation, spine⟩
  | .reuseType inference typeTree extension typeReading typeRun same => by
      obtain ⟨reads, checked⟩ := inference.sound agreement reading accepted
      obtain ⟨_, typeTyped, _, _⟩ :=
        typeTree.soundWithSpine (.empty _) (.empty _ _) typeReading typeRun
      have typeFormed := same.termTyping
        (typing_instL_closed (context := context) (extension.typing typeTyped) _)
      have typed := checked.typing typeFormed
      exact ⟨reads, typed, typeFormed, inference.lambdaSpineTyping typed⟩
  | .fvar inference atIndex boundAtIndex => by
      obtain ⟨reads, typed⟩ := inference.synthesis (.bvar _) agreement reading accepted
      exact ⟨reads, typed, formed _ _ _ atIndex boundAtIndex,
        LambdaSpineTyping.non_application (by intro fn arg same; cases same)
          (by intro condition domain body same; cases same)⟩
  | .app full miss trace functionTree argumentTree conditions hashPath comparisonFaithful
      bodyConstructed argConstructed bodyBound argBound coherent faithful => by
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      rw [full] at run
      obtain ⟨fnReads, argReads⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨functionTypeReads, functionTyped, functionFormed, functionSpine⟩ :=
        functionTree.soundWithSpine formed keyedAgreement fnReads trace.functionRun
      obtain ⟨domainReads, codomainReads⟩ := readScopedExpr?_all_parts functionTypeReads
      have argumentAgreement := keyedAgreement.congr trace.contextPreserved.symm
      obtain ⟨argumentTypeReads, argumentTyped, _, _⟩ :=
        argumentTree.soundWithSpine formed argumentAgreement argReads trace.argumentRun
      have sameReading := beq_readScopedExpr? (resolve := resolve) (locals := locals)
        (depth := 0) comparisonFaithful hashPath
      have sameType := AExpr.eq_of_erase_annotations
        (Option.some.inj (argumentTypeReads.symm.trans (sameReading.trans domainReads))) conditions
      have checked := sameType ▸ argumentTyped.checking
      refine ⟨?_, functionTyped.appChecking checked,
        functionTyped.applicationType functionFormed checked,
        functionSpine.app (sameType ▸ argumentTyped)⟩
      rw [trace.output run, AExpr.erase_inst]
      exact (subst_readScopedExpr? bodyConstructed argConstructed bodyBound argBound
        coherent faithful codomainReads argReads).1
  | .appBeta full miss trace functionTree exposure exposureCoherent reduction argumentTree conditions hashPath
      comparisonFaithful bodyConstructed argConstructed bodyBound argBound coherent faithful => by
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      rw [full] at run
      obtain ⟨fnReads, argReads⟩ := readScopedExpr?_app_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨functionTypeReads, functionTyped, _, functionSpine⟩ :=
        functionTree.soundWithSpine formed keyedAgreement fnReads trace.functionRun
      obtain ⟨domainReads, codomainReads, _⟩ := exposure.reading functionTypeReads exposureCoherent
      have argumentAgreement := keyedAgreement.congr trace.exposure_context.symm
      obtain ⟨argumentTypeReads, argumentTyped, _, _⟩ :=
        argumentTree.soundWithSpine formed argumentAgreement argReads trace.argumentRun
      have sameType := AExpr.eq_of_erase_annotations
        (Option.some.inj (argumentTypeReads.symm.trans
          ((beq_readScopedExpr? comparisonFaithful hashPath).trans domainReads))) conditions
      obtain ⟨converted, functionFormed⟩ := reduction.sound formed
      have exposedTyped := functionTyped.conv functionFormed converted
      have checked := sameType ▸ argumentTyped.checking
      refine ⟨?_, exposedTyped.appChecking checked,
        exposedTyped.applicationType functionFormed checked,
        (functionSpine.convert reduction.rigid converted functionFormed).app (sameType ▸ argumentTyped)⟩
      rw [trace.output run, AExpr.erase_inst]
      exact (subst_readScopedExpr? bodyConstructed argConstructed bodyBound argBound
        coherent faithful codomainReads argReads).1
  | .forallE miss trace opening domainTree bodyTree levelFaithful domainBound bodyBound
      coherent faithful => by
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_all_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨_, domainTyped, _, _⟩ :=
        domainTree.soundWithSpine formed keyedAgreement domainReads trace.domainRun
      have domainAgreement := keyedAgreement.congr trace.contextPreserved.symm
      obtain ⟨_, openedReads, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement (trace.domainValid.freshReading domainAgreement) domainReads bodyReads trace.openRun
      obtain ⟨_, bodyTyped, _, _⟩ :=
        bodyTree.soundWithSpine (formed.push domainTyped) openedAgreement openedReads trace.bodyRun
      refine ⟨?_, ?_, TypingClaim.sort _,
        LambdaSpineTyping.non_application (by intro fn arg same; cases same)
          (by intro condition domain body same; cases same)⟩
      · rw [trace.output run, internExpr_readScopedExpr? coherent faithful]
        rfl
      · exact AExpr.LevelEquivalent.sort
          (Theory.VLevel.equiv_def.mpr fun levels =>
            (Theory.VLevel.equiv_def.mp (readLevel_mkIMax levelFaithful domainBound bodyBound)
              levels).symm) |>.typing (TypingClaim.forallE domainTyped bodyTyped rfl)
  | .lam full miss trace opening domainTree bodyTree conditionAgrees constructed bound coherent
      closingFaithful faithful => by
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      rw [full] at run
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_lam_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨_, domainTyped, _, _⟩ :=
        domainTree.soundWithSpine formed keyedAgreement domainReads trace.domainRun
      have domainAgreement := keyedAgreement.congr trace.contextPreserved.symm
      obtain ⟨_, openedReads, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement (trace.domainValid.freshReading domainAgreement) domainReads bodyReads trace.openRun
      obtain ⟨bodyTypeReads, bodyTyped, bodyFormed, _⟩ :=
        bodyTree.soundWithSpine (formed.push domainTyped) openedAgreement openedReads trace.bodyRun
      obtain ⟨closedReads, closedCoherent⟩ := abstractFVars_readScopedExpr? constructed bound coherent
        closingFaithful bodyTypeReads
      have typed := TypingClaim.lam domainTyped bodyFormed bodyTyped conditionAgrees
      refine ⟨?_, typed, TypingClaim.forallE domainTyped bodyFormed conditionAgrees,
        LambdaSpineTyping.lam typed (.lam bodyTree.lambdaPrefix)⟩
      rw [trace.output run,
        internExpr_readScopedExpr? (table := trace.abstracted.2) closedCoherent faithful]
      simp [LambdaInferenceTrace.abstracted, domainReads, closedReads, AExpr.erase]
  | .lamBeta full miss trace opening domainTree bodyTree origin reduction conditionAgrees
      constructed bound closingFaithful faithful => by
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      rw [full] at run
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_lam_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨_, domainTyped, _, _⟩ :=
        domainTree.soundWithSpine formed keyedAgreement domainReads trace.domainRun
      have domainAgreement := keyedAgreement.congr trace.contextPreserved.symm
      obtain ⟨_, openedReads, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement (trace.domainValid.freshReading domainAgreement) domainReads bodyReads trace.openRun
      obtain ⟨bodyTypeReads, bodyTyped, _, _⟩ :=
        bodyTree.soundWithSpine (formed.push domainTyped) openedAgreement openedReads trace.bodyRun
      obtain ⟨conversion, reducedTyped⟩ := origin.sound formed
      obtain ⟨_, reducedReads, reducedCoherent⟩ := reduction.reading bodyTypeReads
      obtain ⟨closedReads, closedCoherent⟩ := abstractFVars_readScopedExpr? constructed bound
        reducedCoherent closingFaithful reducedReads
      have typed := TypingClaim.lam domainTyped reducedTyped
        (bodyTyped.conv reducedTyped conversion) conditionAgrees
      have bodyDepth := bodyTree.lambdaPrefix.lambdaDepth_zero
        (AExpr.appN_ne_forallE (by intro condition domain body same; cases same) _)
      refine ⟨?_, typed, TypingClaim.forallE domainTyped reducedTyped conditionAgrees,
        LambdaSpineTyping.lam typed ?_⟩
      · rw [trace.output run,
          internExpr_readScopedExpr? (table := trace.abstracted.2) closedCoherent faithful]
        simp [LambdaBodyTrace.abstracted, LambdaBodyTrace.reduced, domainReads,
          AExpr.erase] at ⊢ closedReads
        exact closedReads
      · simpa only [bodyDepth] using LambdaPrefix.lam (LambdaPrefix.zero _ _)
termination_by structural support

theorem SynthesisContext.sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries earlier : Model.Environment β} {context priorContext : Model.Context β}
    {bounds priorBounds : List VLevel}
    (support : SynthesisContext resolve entries context bounds earlier priorContext priorBounds)
    (formed : ContextFormation.{u,v} entries context bounds) :
    ContextFormation.{u,v} earlier priorContext priorBounds :=
  match support with
  | .current => formed
  | .empty earlier => .empty earlier
  | .push prior domainTree agreement reading accepted => by
      have priorFormation := prior.sound formed
      obtain ⟨_, domainTyped, _, _⟩ :=
        domainTree.soundWithSpine priorFormation agreement reading accepted
      exact priorFormation.push domainTyped
  | .extend prior extension => by
      intro index type bound found indexed
      exact extension.typing (prior.sound formed index type bound found indexed)
  | .compose prior next => next.sound (prior.sound formed)
termination_by structural support

theorem SynthesisTypeTransport.sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming origin entries : Model.Environment β} {incomingContext originContext context : Model.Context β}
    {incomingBounds : List VLevel} {source reduced current result : AExpr β} {level bound : VLevel}
    (support : SynthesisTypeTransport resolve incoming incomingContext incomingBounds
      origin originContext source reduced level entries context current result bound)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds)
    (converted : ConversionClaim.{u,v} origin originContext source reduced)
    (typed : TypingClaim.{u,v} origin originContext reduced (.sort level)) :
    ConversionClaim.{u,v} entries context current result ∧
      TypingClaim.{u,v} entries context result (.sort bound) :=
  match support with
  | .pure transport => transport.sound converted typed
  | .map prior transport => by
      obtain ⟨conversion, resultTyped⟩ := prior.sound formed converted typed
      exact transport.sound conversion resultTyped
  | .substituteAt prior argumentOrigin substitution => by
      obtain ⟨conversion, resultTyped⟩ := prior.sound formed converted typed
      have argumentAtDomain := argumentOrigin.sound formed
      exact ⟨conversion.instAt argumentAtDomain substitution, resultTyped.instAt argumentAtDomain substitution⟩
termination_by structural support

theorem SynthesisRetainedCheck.soundWithSpine {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β} {level : VLevel}
    (check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context term type level)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds) :
    TypingClaim.{u,v} entries context term type ∧ TypingClaim.{u,v} entries context type (.sort level) ∧
      LambdaSpineTyping.{u,v} entries context term type :=
  match check with
  | .source contextOrigin tree agreement reading accepted =>
      (tree.soundWithSpine (contextOrigin.sound formed) agreement reading accepted).2
  | .extend prior extension => by
      obtain ⟨typed, typeFormed, spine⟩ := prior.soundWithSpine formed
      exact ⟨extension.typing typed, extension.typing typeFormed, extension.lambdaSpine spine⟩
  | .weakenAt prior insertion => by
      obtain ⟨typed, typeFormed, spine⟩ := prior.soundWithSpine formed
      exact ⟨insertion.typing typed, insertion.typing typeFormed, insertion.lambdaSpine spine⟩
  | .rebase origin prior => prior.soundWithSpine (origin.sound formed)
termination_by structural check

theorem SynthesisTypingOrigin.sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β}
    (support : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds) :
    TypingClaim.{u,v} entries context term type :=
  match support with
  | .source check => (check.soundWithSpine formed).1
  | .inferredType contextOrigin tree agreement reading accepted =>
      (tree.soundWithSpine (contextOrigin.sound formed) agreement reading accepted).2.2.1
  | .lambdaBody check => (check.sound formed).lambdaBody
  | .application functionOrigin argumentOrigin => (functionOrigin.sound formed).app (argumentOrigin.sound formed)
  | .reduced trace => (trace.sound formed).2
  | .convert value trace => by
      obtain ⟨converted, typeTyped⟩ := trace.sound formed
      exact (value.sound formed).conv typeTyped converted
  | .weaken prior domain => typing_weaken (prior.sound formed)
  | .weakenAt prior insertion => insertion.typing (prior.sound formed)
  | .instantiate prior arguments => typing_instL_context (prior.sound formed) arguments
  | .appendContext prior outer => typing_append_context (prior.sound formed) outer
  | .extend prior extension => extension.typing (prior.sound formed)
  | .rebase origin prior => prior.sound (origin.sound formed)
  | .termEquivalent prior same => same.termTyping (prior.sound formed)
  | .typeEquivalent prior same => same.typing (prior.sound formed)
  | .substituteAt body value substitution => (body.sound formed).instAt (value.sound formed) substitution
termination_by structural support

theorem SynthesisCheckedOrigin.soundWithSpine {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β}
    (support : SynthesisCheckedOrigin resolve incoming incomingContext incomingBounds entries context term type)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds) :
    TypingClaim.{u,v} entries context term type ∧ LambdaPrefix term type term.lambdaDepth ∧
      LambdaSpineTyping.{u,v} entries context term type :=
  match support with
  | .checked contextOrigin tree agreement reading accepted => by
      obtain ⟨_, typed, _, spine⟩ := tree.soundWithSpine (contextOrigin.sound formed) agreement reading accepted
      exact ⟨typed, tree.lambdaPrefix, spine⟩
  | .binderHead tree head agreement reading accepted => by
      have typed := (tree.synthesis head agreement reading accepted).2
      exact ⟨typed, tree.lambdaPrefix, tree.lambdaSpineTyping typed⟩
  | .applicationArgument contextOrigin trace functionTree argumentTree agreement functionReading argumentReading
      conditions hashPath comparisonFaithful => by
      have contextFormation := contextOrigin.sound formed
      have functionTypeReads :=
        (functionTree.soundWithSpine contextFormation agreement functionReading trace.functionRun).1
      have domainReads := (readScopedExpr?_all_parts functionTypeReads).1
      obtain ⟨argumentTypeReads, argumentTyped, _, argumentSpine⟩ :=
        argumentTree.soundWithSpine contextFormation (agreement.congr trace.contextPreserved.symm)
          argumentReading trace.argumentRun
      have sameType := AExpr.eq_of_erase_annotations
        (Option.some.inj (argumentTypeReads.symm.trans
          ((beq_readScopedExpr? comparisonFaithful hashPath).trans domainReads))) conditions
      exact ⟨sameType ▸ argumentTyped, sameType ▸ argumentTree.lambdaPrefix, sameType ▸ argumentSpine⟩
  | .applicationBetaArgument contextOrigin trace functionTree exposure exposureCoherent argumentTree agreement
      functionReading argumentReading conditions hashPath comparisonFaithful => by
      have contextFormation := contextOrigin.sound formed
      have functionTypeReads :=
        (functionTree.soundWithSpine contextFormation agreement functionReading trace.functionRun).1
      have domainReads := (exposure.reading functionTypeReads exposureCoherent).1
      obtain ⟨argumentTypeReads, argumentTyped, _, argumentSpine⟩ :=
        argumentTree.soundWithSpine contextFormation (agreement.congr trace.exposure_context.symm)
          argumentReading trace.argumentRun
      have sameType := AExpr.eq_of_erase_annotations
        (Option.some.inj (argumentTypeReads.symm.trans
          ((beq_readScopedExpr? comparisonFaithful hashPath).trans domainReads))) conditions
      exact ⟨sameType ▸ argumentTyped, sameType ▸ argumentTree.lambdaPrefix, sameType ▸ argumentSpine⟩
  | .binderArgument trace functionTree head argumentTree agreement functionReading argumentReading
      conditions hashPath comparisonFaithful => by
      obtain ⟨functionTypeReads, functionTyped⟩ :=
        functionTree.synthesis head agreement functionReading trace.functionRun
      have domainReads := (readScopedExpr?_all_parts functionTypeReads).1
      obtain ⟨argumentTypeReads, argumentChecked⟩ :=
        argumentTree.sound (agreement.congr trace.contextPreserved.symm) argumentReading trace.argumentRun
      have sameType := AExpr.eq_of_erase_annotations
        (Option.some.inj (argumentTypeReads.symm.trans
          ((beq_readScopedExpr? comparisonFaithful hashPath).trans domainReads))) conditions
      have checked := sameType ▸ argumentChecked
      have typed : TypingClaim.{u,v} entries context term type := by
        intro V _ constants realizes levels env valid
        have domainValid := (functionTyped V constants realizes levels env valid).2.1.1
        have checkedAt := checked V constants realizes levels env valid domainValid
        exact ⟨checkedAt.1, domainValid, checkedAt.2⟩
      exact ⟨typed, sameType ▸ argumentTree.lambdaPrefix,
        sameType ▸ argumentTree.lambdaSpineTyping (sameType.symm ▸ typed)⟩
termination_by structural support

theorem SynthesisArgumentSpineOrigin.sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {start result : AExpr β} {arguments : List (AExpr β)}
    (support : SynthesisArgumentSpineOrigin resolve incoming incomingContext incomingBounds
      entries context start arguments result)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds) :
    ArgumentSpine.{u,v} entries context start arguments result :=
  match support with
  | .nil _ => .nil _
  | .snoc prior checked => (prior.sound formed).append (.cons (checked.sound formed) (.nil _))
  | .convert prior trace => by
      obtain ⟨converted, typed⟩ := trace.sound formed
      simpa only [List.append_nil] using
        (prior.sound formed).append (ArgumentSpine.convert trace.rigid converted typed (.nil _))
termination_by structural support

theorem SynthesisReductionOrigin.sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {head : AExpr β} {arguments : List (AExpr β)} {count : Nat} {level : VLevel}
    (support : SynthesisReductionOrigin resolve incoming incomingContext incomingBounds
      entries context head arguments count level)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds) :
    ConversionClaim.{u,v} entries context (head.appN arguments) (AExpr.betaPrefix count head arguments) ∧
      TypingClaim.{u,v} entries context (AExpr.betaPrefix count head arguments) (.sort level) :=
  match support with
  | .traced trace => trace.sound formed
  | .checked typeContextSupport typeTree typeAgreement typeReading typeRun originPrefix transport => by
      obtain ⟨_, _, _, originSpine⟩ := typeTree.soundWithSpine
        (typeContextSupport.sound formed) typeAgreement typeReading typeRun
      obtain ⟨originConversion, originReducedTyped⟩ := originSpine.betaPrefix originPrefix
      exact transport.sound formed originConversion originReducedTyped
  | .substitutedVariable spine atIndex checked substitution enough => by
      obtain ⟨typed, leading, _⟩ := checked.soundWithSpine formed
      have instantiated := (spine.sound formed).instAt typed substitution
      rw [substitution.instantiate_removed_type atIndex] at instantiated
      exact ((leading.liftN _ 0).truncate enough).beta_sound (substitution.lift_typing typed) instantiated
  | .substitutedApplication spine atIndex checked substitution enough =>
      (checked.soundWithSpine formed).2.2.substituteHead (spine.sound formed) atIndex substitution enough
  | .substitutedResult spine atIndex checked substitution enough sourceOrigin => by
      obtain ⟨converted, resultTyped⟩ :=
        (checked.soundWithSpine formed).2.2.substituteHead (spine.sound formed) atIndex substitution enough
      exact ⟨converted, (sourceOrigin.sound formed).termConv resultTyped converted⟩
  | .map prior transport => by
      obtain ⟨converted, typed⟩ := prior.sound formed
      exact transport.sound formed converted typed
termination_by structural support

theorem SynthesisBetaTrace.sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {source result type : AExpr β}
    (support : SynthesisBetaTrace resolve incoming incomingContext incomingBounds entries context source result type)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds) :
    ConversionClaim.{u,v} entries context source result ∧ TypingClaim.{u,v} entries context result type :=
  match support with
  | .refl origin => ⟨.refl _, origin.sound formed⟩
  | .prefix headOrigin leading argumentsOrigin =>
      leading.beta_sound (headOrigin.sound formed) (argumentsOrigin.sound formed)
  | .origin retained => retained.sound formed
  | .trans prior next => by
      obtain ⟨first, middleTyped⟩ := prior.sound formed
      obtain ⟨second, resultTyped⟩ := next.sound formed
      exact ⟨first.trans second, middleTyped.termConv resultTyped second⟩
  | .atType sourceOrigin trace => by
      obtain ⟨converted, resultTyped⟩ := trace.sound formed
      exact ⟨converted, (sourceOrigin.sound formed).termConv resultTyped converted⟩
  | .application functionTrace argumentOrigin => by
      obtain ⟨converted, functionTyped⟩ := functionTrace.sound formed
      exact ⟨converted.app (.refl _), functionTyped.app (argumentOrigin.sound formed)⟩
  | .argument functionOrigin argumentOrigin argumentTrace => by
      obtain ⟨converted, resultTyped⟩ := argumentTrace.sound formed
      have functionTyped := functionOrigin.sound formed
      have argumentTyped := argumentOrigin.sound formed
      refine ⟨(ConversionClaim.refl _).app converted, ?_⟩
      exact (functionTyped.app argumentTyped).termConv
        (functionTyped.app (argumentTyped.termConv resultTyped converted)) ((ConversionClaim.refl _).app converted)
  | .substituteAt trace value substitution => by
      obtain ⟨converted, resultTyped⟩ := trace.sound formed
      have valueTyped := value.sound formed
      exact ⟨converted.instAt valueTyped substitution, resultTyped.instAt valueTyped substitution⟩
  | .weakenAt trace insertion => by
      obtain ⟨converted, resultTyped⟩ := trace.sound formed
      exact ⟨insertion.conversion converted, insertion.typing resultTyped⟩
  | .rebase origin trace => trace.sound (origin.sound formed)
  | .convertType trace typeTrace => by
      obtain ⟨converted, typed⟩ := trace.sound formed
      obtain ⟨typeConversion, targetFormed⟩ := typeTrace.sound formed
      exact ⟨converted, typed.conv targetFormed typeConversion⟩
  | .instantiate trace arguments => by
      obtain ⟨converted, typed⟩ := trace.sound formed
      refine ⟨?_, typing_instL_context typed arguments⟩
      intro V _ constants realizes levels env valid
      simpa only [interp_instL] using
        converted V constants realizes (arguments.map (VLevel.eval levels)) env (context_valid_instL valid)
  | .appendContext trace outer => by
      obtain ⟨converted, typed⟩ := trace.sound formed
      refine ⟨?_, typing_append_context typed outer⟩
      intro V _ constants realizes levels env valid
      exact converted V constants realizes levels env (context_valid_prefix valid)
  | .extend trace extension => by
      obtain ⟨converted, typed⟩ := trace.sound formed
      refine ⟨?_, extension.typing typed⟩
      intro V _ constants realizes levels env valid
      exact converted V constants (extension.realizes realizes) levels env valid
termination_by structural support

end

/-- Ordinary argument typing and its syntactic leading domains remain
available without exposing the stronger application-spine result. -/
theorem SynthesisCheckedOrigin.sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β}
    (support : SynthesisCheckedOrigin resolve incoming incomingContext incomingBounds entries context term type)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds) :
    TypingClaim.{u,v} entries context term type ∧ LambdaPrefix term type term.lambdaDepth := by
  obtain ⟨typed, leading, _⟩ := support.soundWithSpine formed
  exact ⟨typed, leading⟩

/-- The public inference result projects ordinary typing and formation from
the stronger induction that also retains checked lambda domains. -/
theorem SynthesisInference.sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {fuel : Nat}
    {before after : TcState .anon} {source result : KExpr .anon}
    {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
    readScopedExpr? resolve locals result = some type.erase ∧
      TypingClaim.{u,v} entries context term type ∧
      TypingClaim.{u,v} entries context type (.sort level) := by
  obtain ⟨reads, typed, formation, _⟩ := support.soundWithSpine formed agreement reading accepted
  exact ⟨reads, typed, formation⟩

/-- Closed production inference supplies its own formation facts. No local
or whole-term semantic typing premise remains at this boundary. -/
theorem SynthesisInference.closed_sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β} {fuel : Nat}
    {before after : TcState .anon} {source result : KExpr .anon}
    {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries [] [] [] fuel before source term type level)
    (reading : readScopedExpr? resolve [] source = some term.erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
    readScopedExpr? resolve [] result = some type.erase ∧
      TypingClaim.{u,v} entries [] term type ∧ TypingClaim.{u,v} entries [] type (.sort level) :=
  support.sound (.empty entries) (.empty _ _) reading accepted

/-- An already supported type-inference call is a synthesis leaf because
its returned sort has an unconditional formation rule. -/
def SynthesisInference.ofSort {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon} {term : AExpr β} {level : VLevel}
    (inference : BinderInference resolve entries locals context fuel before source term (.sort level)) :
    SynthesisInference resolve entries locals context bounds fuel before source term (.sort level) (.succ level) :=
  .known inference (.sort level)

/-- An executed type check with its original local scope. Walking a
dependent function type keeps the actual domain checks that established
each nested context. -/
structure SynthesisScopedTypeCheck {β : Type u} (resolve : Address → Option (ConstRef β))
    (incoming : Model.Environment β) (incomingContext : Model.Context β) (incomingBounds : List VLevel)
    (entries : Model.Environment β) (type : AExpr β) where
  context : Model.Context β
  level : VLevel
  bound : VLevel
  check : SynthesisRetainedCheck resolve incoming incomingContext incomingBounds entries context type (.sort level) bound

theorem SynthesisScopedTypeCheck.sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext : Model.Context β}
    {incomingBounds : List VLevel} {type : AExpr β}
    (check : SynthesisScopedTypeCheck resolve incoming incomingContext incomingBounds entries type)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds) :
    TypingClaim.{u,v} entries check.context type (.sort check.level) :=
  (check.check.soundWithSpine formed).1

def SynthesisScopedTypeCheck.forallBody {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext : Model.Context β}
    {incomingBounds : List VLevel} {condition : Certified.PropWhen} {domain body : AExpr β}
    (check : SynthesisScopedTypeCheck resolve incoming incomingContext incomingBounds
      entries (.forallE condition domain body)) :
    SynthesisScopedTypeCheck resolve incoming incomingContext incomingBounds entries body := by
  let child := check.check.forallBody rfl
  exact {
    context := Context.push domain check.context
    level := child.bodyLevel
    bound := child.bound
    check := child.check }

def SynthesisScopedTypeCheck.variableSpine {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext : Model.Context β}
    {incomingBounds : List VLevel} {index : Nat} {arguments : List (AExpr β)}
    (check : SynthesisScopedTypeCheck resolve incoming incomingContext incomingBounds
      entries ((AExpr.bvar index).appN arguments)) :
    SynthesisVariableSpineOrigin resolve incoming incomingContext incomingBounds entries
      check.context index arguments (.sort check.level) :=
  check.check.variableSpineOrigin index arguments rfl

/-- Package an executed closed type check so later declarations can retain
its origin. The check itself may contain direct lambda applications. -/
structure SynthesisTypeCheck {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (type : AExpr β) (level : VLevel) where
  fuel : Nat
  before : TcState .anon
  after : TcState .anon
  source : KExpr .anon
  result : KExpr .anon
  bound : VLevel
  inference : SynthesisInference resolve entries [] [] [] fuel before source type (.sort level) bound
  reading : readScopedExpr? resolve [] source = some type.erase
  run : RecM.infer source (methodsN fuel) before = .ok result after

theorem SynthesisTypeCheck.sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {type : AExpr β} {level : VLevel}
    (check : SynthesisTypeCheck resolve entries type level) :
    TypingClaim.{u,v} entries [] type (.sort level) :=
  (check.inference.closed_sound check.reading check.run).2.1

def SynthesisTypeCheck.scoped {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext : Model.Context β}
    {incomingBounds : List VLevel} {type : AExpr β} {level : VLevel}
    (check : SynthesisTypeCheck resolve entries type level) :
    SynthesisScopedTypeCheck resolve incoming incomingContext incomingBounds entries type :=
  { context := []
    level := level
    bound := check.bound
    check := .source (.empty entries) check.inference (.empty _ _) check.reading check.run }

def SynthesisTypeCheck.forallBody {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {condition : Certified.PropWhen} {domain body : AExpr β} {level : VLevel}
    (check : SynthesisTypeCheck resolve entries (.forallE condition domain body) level) :
    SynthesisForallBodyCheck resolve entries [] [] condition domain body :=
  check.inference.forallBodyCheck (.empty _ _) check.reading

/-- An instantiated constant can recover formation from an earlier actual
declaration type check, with exact interface preservation and structural
level congruence. -/
def SynthesisInference.ofTypeCheck {β : Type u} {resolve : Address → Option (ConstRef β)}
    {earlier entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β}
    {bounds : List VLevel} {fuel : Nat} {before : TcState .anon} {source : KExpr .anon}
    {term type declaredType : AExpr β} {level : VLevel}
    (inference : BinderInference resolve entries locals context fuel before source term type)
    (check : SynthesisTypeCheck resolve earlier declaredType level)
    (extension : InterfaceExtends earlier entries) (arguments : List VLevel)
    (same : AExpr.LevelEquivalent (declaredType.instL arguments) type) :
    SynthesisInference resolve entries locals context bounds fuel before source term type (level.inst arguments) :=
  .reuseType inference check.inference extension check.reading check.run same

end Ix.Kernel.Consistency
