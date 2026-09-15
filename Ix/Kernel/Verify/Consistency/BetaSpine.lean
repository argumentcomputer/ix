/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Beta
import Ix.Kernel.Verify.Consistency.SpineReading
import Ix.Theory.Model.BetaSpine

/-! Recover the lambda and argument spines from the actual recursive
inference calls, then derive typed reduction of the original lambda prefix. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- Actual application inference supplies each dependent argument type,
while the head's inference supplies all original leading lambda domains. -/
theorem SynthesisInference.lambda_spine {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {fuel : Nat}
    {before after : TcState .anon} {source result : KExpr .anon} {level : VLevel}
    {condition : Certified.PropWhen} {domain body type : AExpr β} {arguments : List (AExpr β)}
    (support : SynthesisInference resolve entries locals context bounds fuel before source
      ((AExpr.lam condition domain body).appN arguments) type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source =
      some ((AExpr.lam condition domain body).appN arguments).erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
    readScopedExpr? resolve locals result = some type.erase ∧
      ∃ headType, TypingClaim.{u,v} entries context (.lam condition domain body) headType ∧
        LambdaPrefix (.lam condition domain body) headType (body.lambdaDepth + 1) ∧
        ArgumentSpine.{u,v} entries context headType arguments type := by
  obtain ⟨reads, _, _, spines⟩ := support.soundWithSpine formed agreement reading accepted
  exact ⟨reads, spines _ _ _ _ rfl⟩

/-- The complete original lambda prefix may be consumed without another
inference call on any intermediate beta result. -/
theorem SynthesisInference.beta_spine_sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {fuel : Nat}
    {before after : TcState .anon} {source result : KExpr .anon} {level : VLevel}
    {condition : Certified.PropWhen} {domain body type : AExpr β} {arguments : List (AExpr β)}
    (support : SynthesisInference resolve entries locals context bounds fuel before source
      ((AExpr.lam condition domain body).appN arguments) type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source =
      some ((AExpr.lam condition domain body).appN arguments).erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
    ConversionClaim.{u,v} entries context ((AExpr.lam condition domain body).appN arguments)
      (AExpr.betaPrefix (body.lambdaDepth + 1) (.lam condition domain body) arguments) ∧
      TypingClaim.{u,v} entries context
        (AExpr.betaPrefix (body.lambdaDepth + 1) (.lam condition domain body) arguments) type := by
  obtain ⟨_, _, typed, leading, spine⟩ := support.lambda_spine formed agreement reading accepted
  exact leading.beta_sound typed spine

/-- Any prefix selected by production's lambda peel has the simultaneous
substitution meaning, with the remaining arguments in their original order. -/
theorem SynthesisInference.beta_peel_sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {fuel : Nat}
    {before after : TcState .anon} {source result : KExpr .anon} {level : VLevel}
    {condition : Certified.PropWhen} {domain inner body type : AExpr β}
    {consumed trailing : List (AExpr β)}
    (support : SynthesisInference resolve entries locals context bounds fuel before source
      ((AExpr.lam condition domain inner).appN (consumed ++ trailing)) type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source =
      some ((AExpr.lam condition domain inner).appN (consumed ++ trailing)).erase)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after)
    (peeling : LambdaPeel (.lam condition domain inner) consumed.length body) :
    ConversionClaim.{u,v} entries context
      ((AExpr.lam condition domain inner).appN (consumed ++ trailing))
      ((body.instRev consumed).appN trailing) ∧
      TypingClaim.{u,v} entries context ((body.instRev consumed).appN trailing) type := by
  obtain ⟨_, _, typed, leading, spine⟩ := support.lambda_spine formed agreement reading accepted
  have result := (leading.truncate peeling.length_bound).beta_sound typed spine
  rwa [peeling.betaPrefix trailing] at result

/-- The production multi-argument beta step preserves typing and model
meaning. Its peeled body and consumed argument order come from the actual
loop, and its suffix is rebuilt by the actual interned application chain. -/
theorem SynthesisInference.beta_many_step {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {fuel : Nat}
    {inferenceBefore inferenceAfter : TcState .anon} {inferred : KExpr .anon} {level : VLevel}
    {rawFunction rawArgument : KExpr .anon} {appInfo : ExprInfo .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {rawDomain rawInner rawBody : KExpr .anon} {lambdaInfo : ExprInfo .anon}
    {rawArguments consumed : Array (KExpr .anon)}
    {condition : Certified.PropWhen} {domain inner type : AExpr β} {arguments : List (AExpr β)}
    (support : SynthesisInference resolve entries locals context bounds fuel inferenceBefore
      (.app rawFunction rawArgument appInfo)
      ((AExpr.lam condition domain inner).appN arguments) type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals inferenceBefore.lctx context)
    (spine : (KExpr.app rawFunction rawArgument appInfo).collectSpine =
      (.lam name bi rawDomain rawInner lambdaInfo, rawArguments))
    (headReads : readScopedExpr? resolve locals (.lam name bi rawDomain rawInner lambdaInfo) =
      some (AExpr.lam condition domain inner).erase)
    (argumentReads : rawArguments.toList.map (readScopedExpr? resolve locals ·) =
      arguments.map (some ·.erase))
    (accepted : RecM.infer (.app rawFunction rawArgument appInfo)
      (methodsN fuel) inferenceBefore = .ok inferred inferenceAfter)
    (peeling : RecM.consumeBetaLams (.lam name bi rawDomain rawInner lambdaInfo) rawArguments =
      (rawBody, consumed))
    (nonempty : (!consumed.isEmpty) = true)
    (before : TcState .anon) (reductionFuel : Nat) (flags : WhnfFlags)
    (walkerBounds : SimulSubstBounds rawBody consumed.reverse 0)
    (coherent : before.env.intern.WF)
    (walkerFaithful : KExpr.CollisionFree fun term => before.env.intern.ExprSupport term ∨
      KExpr.SimulSubstReach consumed.reverse rawBody 0 term)
    (suffixFaithful : KExpr.CollisionFree fun term =>
      (simulSubst rawBody consumed.reverse 0 before.env.intern).2.ExprSupport term ∨
        term ∈ cheapBetaChainList (simulSubst rawBody consumed.reverse 0 before.env.intern).1
          (rawArguments.extract consumed.size rawArguments.size).toList) :
    ∃ (body : AExpr β) (result : KExpr .anon) (after : TcState .anon),
      (RecM.whnfCoreWithFlagsStep (.app rawFunction rawArgument appInfo) flags).run
        (methodsN (reductionFuel + 1)) before = .ok (.next result) after ∧
      readScopedExpr? resolve locals result =
        some ((body.instRev (arguments.take consumed.size)).appN (arguments.drop consumed.size)).erase ∧
      ConversionClaim.{u,v} entries context ((AExpr.lam condition domain inner).appN arguments)
        ((body.instRev (arguments.take consumed.size)).appN (arguments.drop consumed.size)) ∧
      TypingClaim.{u,v} entries context
        ((body.instRev (arguments.take consumed.size)).appN (arguments.drop consumed.size)) type ∧
      after.env.intern.WF := by
  obtain ⟨result, after, run, resultReads, enough, preserved⟩ := beta_many_step_readScopedExpr?
    spine headReads argumentReads peeling nonempty before reductionFuel flags
    walkerBounds coherent walkerFaithful suffixFaithful
  have reading := readScopedExpr?_collectSpine spine headReads argumentReads
  obtain ⟨_, _, typed, leading, argumentsTyped⟩ := support.lambda_spine formed agreement reading accepted
  have conversion := (leading.truncate enough).beta_sound typed argumentsTyped
  obtain ⟨rawPeel, _, consumedBound⟩ := RecM.BetaPeel.of_consume peeling
  obtain ⟨body, modelPeel, _⟩ := betaPeel_readScopedExpr? rawPeel headReads
  have sizeAgrees : rawArguments.size = arguments.length := by
    have lengths := congrArg List.length argumentReads
    simpa using lengths
  have consumedSize : (arguments.take consumed.size).length = consumed.size := by
    simp only [List.length_take]
    omega
  have peelingMeaning := LambdaPeel.betaPrefix (arguments := arguments.take consumed.size)
    (by simpa only [consumedSize, Array.length_toList] using modelPeel) (arguments.drop consumed.size)
  simp only [consumedSize, List.take_append_drop] at peelingMeaning
  rw [peelingMeaning] at resultReads conversion
  exact ⟨body, result, after, run, resultReads, conversion.1, conversion.2, preserved⟩

/-- A retained origin justifies the actual beta step on an intermediate
type. All inference calls belong to the origin; no new check of the
intermediate source or the generated result is required. -/
theorem SynthesisReductionOrigin.beta_many_step {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {incoming entries : Model.Environment β} {incomingContext context : Model.Context β}
    {incomingBounds : List VLevel} {level : VLevel}
    {rawFunction rawArgument : KExpr .anon} {appInfo : ExprInfo .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {rawDomain rawInner rawBody : KExpr .anon} {lambdaInfo : ExprInfo .anon}
    {rawArguments consumed : Array (KExpr .anon)}
    {condition : Certified.PropWhen} {domain inner : AExpr β} {arguments : List (AExpr β)}
    (support : SynthesisReductionOrigin resolve incoming incomingContext incomingBounds
      entries context (.lam condition domain inner) arguments consumed.size level)
    (formed : ContextFormation.{u,v} incoming incomingContext incomingBounds)
    (spine : (KExpr.app rawFunction rawArgument appInfo).collectSpine =
      (.lam name bi rawDomain rawInner lambdaInfo, rawArguments))
    (headReads : readScopedExpr? resolve locals (.lam name bi rawDomain rawInner lambdaInfo) =
      some (AExpr.lam condition domain inner).erase)
    (argumentReads : rawArguments.toList.map (readScopedExpr? resolve locals ·) =
      arguments.map (some ·.erase))
    (peeling : RecM.consumeBetaLams (.lam name bi rawDomain rawInner lambdaInfo) rawArguments =
      (rawBody, consumed))
    (nonempty : (!consumed.isEmpty) = true)
    (before : TcState .anon) (reductionFuel : Nat) (flags : WhnfFlags)
    (walkerBounds : SimulSubstBounds rawBody consumed.reverse 0)
    (coherent : before.env.intern.WF)
    (walkerFaithful : KExpr.CollisionFree fun term => before.env.intern.ExprSupport term ∨
      KExpr.SimulSubstReach consumed.reverse rawBody 0 term)
    (suffixFaithful : KExpr.CollisionFree fun term =>
      (simulSubst rawBody consumed.reverse 0 before.env.intern).2.ExprSupport term ∨
        term ∈ cheapBetaChainList (simulSubst rawBody consumed.reverse 0 before.env.intern).1
          (rawArguments.extract consumed.size rawArguments.size).toList) :
    ∃ (result : KExpr .anon) (after : TcState .anon),
      (RecM.whnfCoreWithFlagsStep (.app rawFunction rawArgument appInfo) flags).run
        (methodsN (reductionFuel + 1)) before = .ok (.next result) after ∧
      readScopedExpr? resolve locals result =
        some (AExpr.betaPrefix consumed.size (.lam condition domain inner) arguments).erase ∧
      ConversionClaim.{u,v} entries context ((AExpr.lam condition domain inner).appN arguments)
        (AExpr.betaPrefix consumed.size (.lam condition domain inner) arguments) ∧
      TypingClaim.{u,v} entries context
        (AExpr.betaPrefix consumed.size (.lam condition domain inner) arguments) (.sort level) ∧
      after.env.intern.WF := by
  obtain ⟨result, after, run, reading, _, preserved⟩ := beta_many_step_readScopedExpr?
    spine headReads argumentReads peeling nonempty before reductionFuel flags
    walkerBounds coherent walkerFaithful suffixFaithful
  obtain ⟨conversion, typed⟩ := support.sound formed
  exact ⟨result, after, run, reading, conversion, typed, preserved⟩

end Ix.Kernel.Consistency
