/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.ContextTransport
import Ix.Kernel.Verify.Consistency.CheapBetaReading
import Ix.Kernel.Verify.Consistency.ApplicationWhnf
import Ix.Kernel.Verify.Consistency.LetInference
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

  | letE {entries locals context bounds fuel before name domain value body nonDep info
      A val b B resultType level domainBound valueLevel valueType}
      (full : before.inferOnly = false)
      (localState : LocalStateInvariant before)
      (miss : UncachedInference before (.letE name domain value body nonDep info))
      (trace : LetInferenceTrace fuel miss.keyed name domain value body)
      (opening : BinderOpeningSupport trace.comparedState body)
      (domainTree : SynthesisInference resolve entries locals context bounds fuel miss.keyed domain
        A (.sort (readLevel trace.domainLevel)) domainBound)
      (valueTree : SynthesisInference resolve entries locals context bounds fuel trace.domainState value
        val valueType valueLevel)
      (bodyTree : SynthesisInference resolve entries (trace.fresh :: locals) (context.push A)
        (readLevel trace.domainLevel :: bounds) fuel trace.openedState trace.opened b B level)
      (domainReading : readScopedExpr? resolve locals domain = some A.erase)
      (valueReading : readScopedExpr? resolve locals value = some val.erase)
      (bodyReading : readScopedExpr? resolve locals body 1 = some b.erase)
      (conditions : valueType.annotations = A.annotations)
      (hashPath : (trace.valueType == domain) = true)
      (comparisonFaithful : trace.valueType.AddrFaithful domain)
      (substitution : trace.SubstitutionSupport)
      (reduction : LetTypeReduction resolve entries context bounds trace.substituted.1 trace.substituted.2
        level (B.inst val) resultType) :
      SynthesisInference resolve entries locals context bounds (fuel + 1) before
        (.letE name domain value body nonDep info) (b.inst val) resultType level

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
  | binderType {incoming incomingContext incomingBounds entries context locals fuel before after source result term level}
      (tree : BinderInference resolve entries locals context fuel before source term (.sort level))
      (agreement : LocalContextReading resolve locals before.lctx context)
      (reading : readScopedExpr? resolve locals source = some term.erase)
      (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
      SynthesisCheckedOrigin resolve incoming incomingContext incomingBounds entries context term (.sort level)
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

/-- The actual final cheap-beta choice, with an original checking origin
for a selected reduction. The unchanged case needs only the planner result. -/
inductive LetTypeReduction {β : Type u} (resolve : Address → Option (ConstRef β)) :
    Model.Environment β → Model.Context β → List VLevel → KExpr .anon → InternTable .anon → VLevel →
      AExpr β → AExpr β → Type u
  | unchanged {entries context bounds source table level term}
      (plan : cheapBetaPlan? source = none) :
      LetTypeReduction resolve entries context bounds source table level term term
  | beta {entries context bounds source table level condition domain body arguments}
      (support : CheapBetaSupport source table)
      (origin : SynthesisBetaTrace resolve entries context bounds entries context
        ((AExpr.lam condition domain body).appN arguments)
        (AExpr.betaPrefix (cheapBetaCount source) (.lam condition domain body) arguments) (.sort level)) :
      LetTypeReduction resolve entries context bounds source table level
        ((AExpr.lam condition domain body).appN arguments)
        (AExpr.betaPrefix (cheapBetaCount source) (.lam condition domain body) arguments)

end

theorem LetTypeReduction.reading {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β} {bounds : List VLevel}
    {locals : List FVarId} {source : KExpr .anon} {table : InternTable .anon}
    {level : VLevel} {term result : AExpr β}
    (reduction : LetTypeReduction resolve entries context bounds source table level term result)
    (coherent : table.WF)
    (reading : readScopedExpr? resolve locals source = some term.erase) :
    readScopedExpr? resolve locals (cheapBetaReduce source table).1 = some result.erase ∧
      (cheapBetaReduce source table).2.WF := by
  cases reduction with
  | unchanged plan =>
      rw [cheapBetaReduce, plan]
      exact ⟨reading, coherent⟩
  | beta support _ => exact (support.reading reading).2

def LetTypeReduction.trace {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β} {bounds : List VLevel}
    {source : KExpr .anon} {table : InternTable .anon} {level : VLevel} {term result : AExpr β}
    (reduction : LetTypeReduction resolve entries context bounds source table level term result)
    (original : SynthesisTypingOrigin resolve entries context bounds entries context term (.sort level)) :
    SynthesisBetaTrace resolve entries context bounds entries context term result (.sort level) :=
  match reduction with
  | .unchanged _ => .refl original
  | .beta _ origin => origin

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

/-- The selected cheap reduction preserves every non-application type. -/
theorem LetTypeReduction.rigid {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β} {bounds : List VLevel}
    {source : KExpr .anon} {table : InternTable .anon} {level : VLevel} {term result : AExpr β}
    (reduction : LetTypeReduction resolve entries context bounds source table level term result) :
    AExpr.HeadRigid term result :=
  match reduction with
  | .unchanged _ => fun _ => rfl
  | .beta _ origin => origin.rigid

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


end Ix.Kernel.Consistency
