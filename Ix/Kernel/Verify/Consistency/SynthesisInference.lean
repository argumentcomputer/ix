/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Formation
import Ix.Kernel.Verify.Consistency.CheapBetaReading
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
  | forallE {entries locals context bounds fuel before name bi domain body info A B domainBoundLevel bodyBoundLevel}
      (miss : UncachedInference before (.all name bi domain body info))
      (trace : ForallInferenceTrace fuel miss.keyed name bi domain body)
      (opening : BinderOpeningSupport trace.domainState body)
      (absent : (⟨trace.domainState.env.nextFVarId⟩ : FVarId) ∉ locals)
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
      (absent : (⟨trace.domainState.env.nextFVarId⟩ : FVarId) ∉ locals)
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
      domainBoundLevel bodyLevel headCondition headDomain headBody arguments
      earlier typeLocals typeContext typeBounds typeFuel typeBefore typeAfter typeSource typeResult
      originCondition originDomain originBody originArguments originLevel originBound reducedLevel}
      (full : before.inferOnly = false)
      (miss : UncachedInference before (.lam name bi domain body info))
      (trace : LambdaBodyTrace fuel miss.keyed name bi domain body)
      (opening : BinderOpeningSupport trace.domainState body)
      (absent : (⟨trace.domainState.env.nextFVarId⟩ : FVarId) ∉ locals)
      (domainTree : SynthesisInference resolve entries locals context bounds fuel miss.keyed domain
        A (.sort (readLevel trace.domainLevel)) domainBoundLevel)
      (bodyTree : SynthesisInference resolve entries (trace.fresh :: locals) (context.push A)
        (readLevel trace.domainLevel :: bounds) fuel trace.openedState trace.opened b
        ((AExpr.lam headCondition headDomain headBody).appN arguments) bodyLevel)
      (typeContextSupport : SynthesisContext resolve entries context bounds earlier typeContext typeBounds)
      (typeTree : SynthesisInference resolve earlier typeLocals typeContext typeBounds typeFuel typeBefore
        typeSource ((AExpr.lam originCondition originDomain originBody).appN originArguments)
        (.sort originLevel) originBound)
      (typeAgreement : LocalContextReading resolve typeLocals typeBefore.lctx typeContext)
      (typeReading : readScopedExpr? resolve typeLocals typeSource =
        some ((AExpr.lam originCondition originDomain originBody).appN originArguments).erase)
      (typeRun : RecM.infer typeSource (methodsN typeFuel) typeBefore = .ok typeResult typeAfter)
      (originPrefix : cheapBetaCount trace.bodyType ≤ originBody.lambdaDepth + 1)
      (transport : SynthesisTypeTransport resolve entries context bounds earlier typeContext
        ((AExpr.lam originCondition originDomain originBody).appN originArguments)
        (AExpr.betaPrefix (cheapBetaCount trace.bodyType) (.lam originCondition originDomain originBody)
          originArguments) originLevel entries (context.push A)
        ((AExpr.lam headCondition headDomain headBody).appN arguments)
        (AExpr.betaPrefix (cheapBetaCount trace.bodyType) (.lam headCondition headDomain headBody) arguments)
        reducedLevel)
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
source inference calls. Subsequent context and substitution steps retain
those calls, including when an argument must cross still-open parameters
of an earlier declaration's type. No semantic typing field is accepted. -/
inductive SynthesisTypingOrigin {β : Type u} (resolve : Address → Option (ConstRef β)) :
    Model.Environment β → Model.Context β → List VLevel →
      Model.Environment β → Model.Context β → AExpr β → AExpr β → Type u
  | checked {incoming incomingContext incomingBounds entries context bounds locals fuel before after source result
      term type level}
      (contextOrigin : SynthesisContext resolve incoming incomingContext incomingBounds entries context bounds)
      (tree : SynthesisInference resolve entries locals context bounds fuel before source term type level)
      (agreement : LocalContextReading resolve locals before.lctx context)
      (reading : readScopedExpr? resolve locals source = some term.erase)
      (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
      SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type
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
      SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context a domain
  | weaken {incoming incomingContext incomingBounds entries context term type}
      (prior : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type)
      (domain : AExpr β) :
      SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries (context.push domain)
        (term.liftN 1) (type.liftN 1)
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

end

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
    (.applicationArgument argumentContext trace functionTree argumentTree agreement functionReading argumentReading
      conditions hashPath comparisonFaithful) substitution

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

/-- The actual codomain call retained inside a function-type check. Its
local context is reconstructed from that same call's domain check. -/
structure SynthesisForallBodyCheck {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (context : Model.Context β) (bounds : List VLevel)
    (condition : Certified.PropWhen) (domain body : AExpr β) where
  domainLevel : VLevel
  bodyLevel : VLevel
  bound : VLevel
  locals : List FVarId
  fuel : Nat
  before : TcState .anon
  after : TcState .anon
  source : KExpr .anon
  result : KExpr .anon
  contextOrigin : SynthesisContext resolve entries context bounds entries
    (context.push domain) (domainLevel :: bounds)
  tree : SynthesisInference resolve entries locals (context.push domain) (domainLevel :: bounds)
    fuel before source body (.sort bodyLevel) bound
  agreement : LocalContextReading resolve locals before.lctx (context.push domain)
  reading : readScopedExpr? resolve locals source = some body.erase
  run : RecM.infer source (methodsN fuel) before = .ok result after
  conditionAgrees : condition = Certified.zeroCondition bodyLevel

private def ForallInferenceTrace.bodyCheck {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel}
    {fuel : Nat} {before : TcState .anon} {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body : KExpr .anon} {A B : AExpr β} {domainBound bodyBound : VLevel}
    (trace : ForallInferenceTrace fuel before name bi domain body)
    (opening : BinderOpeningSupport trace.domainState body)
    (absent : (⟨trace.domainState.env.nextFVarId⟩ : FVarId) ∉ locals)
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
  have opened := openBinder_sound opening (trace.contextPreserved.symm ▸ agreement)
    absent domainReading bodyReading trace.openRun
  exact {
    domainLevel := readLevel trace.domainLevel
    bodyLevel := readLevel trace.bodyLevel
    bound := bodyBound
    locals := trace.fresh :: locals
    fuel := fuel
    before := trace.openedState
    after := trace.bodyState
    source := trace.opened
    result := .sort trace.bodyLevel trace.bodyInfo
    contextOrigin := .push .current domainTree agreement domainReading trace.domainRun
    tree := bodyTree
    agreement := opened.2.2.1
    reading := opened.2.1
    run := trace.bodyRun
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
  | forallE miss trace opening absent domainTree bodyTree =>
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_all_parts reading
      exact trace.bodyCheck opening absent (.known domainTree (.sort _)) (.known bodyTree (.sort _))
        (miss.localContext.symm ▸ agreement) domainReads bodyReads

/-- Recover the recorded codomain check by inspecting the production
inference tree. This does not assume a new call on an inferred codomain. -/
def SynthesisInference.forallBodyCheck {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β}
    {bounds : List VLevel} {fuel : Nat} {before : TcState .anon} {source : KExpr .anon}
    {condition : Certified.PropWhen} {domain body type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source
      (.forallE condition domain body) type level)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some (AExpr.forallE condition domain body).erase) :
    SynthesisForallBodyCheck resolve entries context bounds condition domain body := by
  cases support with
  | known inference => exact inference.forallBodyCheck agreement reading
  | reuseType inference => exact inference.forallBodyCheck agreement reading
  | forallE miss trace opening absent domainTree bodyTree =>
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_all_parts reading
      exact trace.bodyCheck opening absent domainTree bodyTree
        (miss.localContext.symm ▸ agreement) domainReads bodyReads

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

theorem BinderInference.lambdaPrefix {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon} {term type : AExpr β}
    (support : BinderInference resolve entries locals context fuel before source term type) :
    LambdaPrefix term type term.lambdaDepth := by
  induction support with
  | lam _ _ _ _ _ _ _ _ _ _ _ ih => exact .lam ih
  | _ => exact .zero _ _

theorem SynthesisInference.lambdaPrefix {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon} {term type : AExpr β} {level : VLevel}
    (support : SynthesisInference resolve entries locals context bounds fuel before source term type level) :
    LambdaPrefix term type term.lambdaDepth :=
  match support with
  | .known inference _ => inference.lambdaPrefix
  | .reuseType inference _ _ _ _ _ => inference.lambdaPrefix
  | .lam _ _ _ _ _ _ bodyTree _ _ _ _ _ _ => .lam bodyTree.lambdaPrefix
  | .lamBeta _ _ _ _ _ _ bodyTree _ _ _ _ _ _ _ _ _ _ _ _ _ => by
      have depth := bodyTree.lambdaPrefix.lambdaDepth_zero
        (AExpr.appN_ne_forallE (by intro condition domain body same; cases same) _)
      simpa only [AExpr.lambdaDepth, depth] using LambdaPrefix.lam (LambdaPrefix.zero _ _)
  | .fvar .. | .app .. | .forallE .. => .zero _ _
termination_by structural support

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
      have argumentAgreement := trace.contextPreserved.symm ▸ keyedAgreement
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
  | .forallE miss trace opening absent domainTree bodyTree levelFaithful domainBound bodyBound
      coherent faithful => by
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_all_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨_, domainTyped, _, _⟩ :=
        domainTree.soundWithSpine formed keyedAgreement domainReads trace.domainRun
      have domainAgreement := trace.contextPreserved.symm ▸ keyedAgreement
      obtain ⟨_, openedReads, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement absent domainReads bodyReads trace.openRun
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
  | .lam full miss trace opening absent domainTree bodyTree conditionAgrees constructed bound coherent
      closingFaithful faithful => by
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      rw [full] at run
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_lam_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨_, domainTyped, _, _⟩ :=
        domainTree.soundWithSpine formed keyedAgreement domainReads trace.domainRun
      have domainAgreement := trace.contextPreserved.symm ▸ keyedAgreement
      obtain ⟨_, openedReads, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement absent domainReads bodyReads trace.openRun
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
  | .lamBeta full miss trace opening absent domainTree bodyTree typeContextSupport typeTree
      typeAgreement typeReading typeRun originPrefix transport reduction conditionAgrees
      constructed bound closingFaithful faithful => by
      obtain ⟨state, run⟩ := infer_uncached_success miss accepted
      rw [full] at run
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_lam_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      obtain ⟨_, domainTyped, _, _⟩ :=
        domainTree.soundWithSpine formed keyedAgreement domainReads trace.domainRun
      have domainAgreement := trace.contextPreserved.symm ▸ keyedAgreement
      obtain ⟨_, openedReads, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement absent domainReads bodyReads trace.openRun
      obtain ⟨bodyTypeReads, bodyTyped, _, _⟩ :=
        bodyTree.soundWithSpine (formed.push domainTyped) openedAgreement openedReads trace.bodyRun
      obtain ⟨_, _, _, originSpine⟩ := typeTree.soundWithSpine
        (typeContextSupport.sound formed) typeAgreement typeReading typeRun
      obtain ⟨originConversion, originReducedTyped⟩ := originSpine.betaPrefix originPrefix
      obtain ⟨conversion, reducedTyped⟩ := transport.sound formed originConversion originReducedTyped
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

theorem SynthesisTypingOrigin.sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {term type : AExpr β}
    (support : SynthesisTypingOrigin resolve incoming incomingContext incomingBounds entries context term type)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds) :
    TypingClaim.{u,v} entries context term type :=
  match support with
  | .checked contextOrigin tree agreement reading accepted =>
      (tree.soundWithSpine (contextOrigin.sound formed) agreement reading accepted).2.1
  | .applicationArgument contextOrigin trace functionTree argumentTree agreement functionReading argumentReading
      conditions hashPath comparisonFaithful => by
      have contextFormation := contextOrigin.sound formed
      have functionTypeReads :=
        (functionTree.soundWithSpine contextFormation agreement functionReading trace.functionRun).1
      have domainReads := (readScopedExpr?_all_parts functionTypeReads).1
      obtain ⟨argumentTypeReads, argumentTyped, _, _⟩ :=
        argumentTree.soundWithSpine contextFormation (trace.contextPreserved.symm ▸ agreement)
          argumentReading trace.argumentRun
      have sameType := AExpr.eq_of_erase_annotations
        (Option.some.inj (argumentTypeReads.symm.trans
          ((beq_readScopedExpr? comparisonFaithful hashPath).trans domainReads))) conditions
      exact sameType ▸ argumentTyped
  | .weaken prior domain => typing_weaken (prior.sound formed)
  | .instantiate prior arguments => typing_instL_context (prior.sound formed) arguments
  | .appendContext prior outer => typing_append_context (prior.sound formed) outer
  | .extend prior extension => extension.typing (prior.sound formed)
  | .termEquivalent prior same => same.termTyping (prior.sound formed)
  | .typeEquivalent prior same => same.typing (prior.sound formed)
  | .substituteAt body value substitution => (body.sound formed).instAt (value.sound formed) substitution
termination_by structural support

end

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
