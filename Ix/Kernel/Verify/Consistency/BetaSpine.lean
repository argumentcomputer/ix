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
  have reading := readScopedExpr?_collectSpine spine headReads argumentReads
  obtain ⟨rawPeel, consumedPrefix, consumedBound⟩ := RecM.BetaPeel.of_consume peeling
  obtain ⟨body, modelPeel, bodyReads⟩ := betaPeel_readScopedExpr? rawPeel headReads
  have sizeAgrees : rawArguments.size = arguments.length := by
    have lengths := congrArg List.length argumentReads
    simpa using lengths
  have consumedSize : (arguments.take consumed.size).length = consumed.size := by
    simp only [List.length_take]
    omega
  have consumedReads : consumed.toList.map (readScopedExpr? resolve locals ·) =
      (arguments.take consumed.size).map (some ·.erase) := by
    rw [consumedPrefix, List.map_take, argumentReads, List.map_take]
  have suffixReads : (rawArguments.extract consumed.size rawArguments.size).toList.map
      (readScopedExpr? resolve locals ·) = (arguments.drop consumed.size).map (some ·.erase) := by
    rw [RecM.BetaPeel.remaining_eq_drop peeling, List.map_drop, argumentReads, List.map_drop]
  obtain ⟨walkReads, walkCoherent⟩ := simulSubst_readScopedExpr?
    (by simpa only [Array.size_reverse] using consumedSize.symm)
    walkerBounds.1 walkerBounds.2.1 (by simpa using walkerBounds.2.2.2.1)
    walkerBounds.2.2.1 coherent walkerFaithful
    (by simpa only [Nat.zero_add, Array.length_toList, consumedSize] using bodyReads)
    (argumentsReading_reverse_get consumedReads consumedSize.symm)
  have conversion := SynthesisInference.beta_peel_sound (consumed := arguments.take consumed.size)
    (trailing := arguments.drop consumed.size)
    (by simpa only [List.take_append_drop] using support) formed agreement
    (by simpa only [List.take_append_drop] using reading) accepted
    (by simpa only [consumedSize, Array.length_toList] using modelPeel)
  let walk := simulSubst rawBody consumed.reverse 0 before.env.intern
  let middle := { before with env := { before.env with intern := walk.2 } }
  obtain ⟨result, after, finish, resultReads, preserved⟩ :=
    finishAppResult_readScopedExpr? (before := middle) walkCoherent suffixFaithful walkReads suffixReads
      (methodsN (reductionFuel + 1))
  refine ⟨body, result, after, ?_, resultReads, ?_, conversion.2, preserved⟩
  · exact RecM.whnfCoreWithFlagsStep_betaMany spine rfl peeling nonempty rfl finish
  · simpa only [List.take_append_drop] using conversion.1

end Ix.Kernel.Consistency
