/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaSpine
import Ix.Kernel.Verify.Consistency.CheapBetaReading

/-! The selected cheap-beta plan has the same typed prefix meaning as
general beta, including its variable-selection and closed-body cases. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- A changed cheap-beta result is justified by an actual check of its
source. This theorem can reuse an earlier type check; it never assumes a
new inference call on a generated substitution result. -/
theorem SynthesisInference.cheapBeta_plan_sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel} {fuel : Nat}
    {inferenceBefore inferenceAfter : TcState .anon} {source inferred : KExpr .anon} {level : VLevel}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {rawDomain rawInner : KExpr .anon} {lambdaInfo : ExprInfo .anon}
    {rawArguments : Array (KExpr .anon)} {plan : CheapBetaPlan .anon}
    {condition : Certified.PropWhen} {domain inner type : AExpr β} {arguments : List (AExpr β)}
    (support : SynthesisInference resolve entries locals context bounds fuel inferenceBefore source
      ((AExpr.lam condition domain inner).appN arguments) type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals inferenceBefore.lctx context)
    (spine : source.collectSpine = (.lam name bi rawDomain rawInner lambdaInfo, rawArguments))
    (headReads : readScopedExpr? resolve locals (.lam name bi rawDomain rawInner lambdaInfo) =
      some (AExpr.lam condition domain inner).erase)
    (argumentReads : rawArguments.toList.map (readScopedExpr? resolve locals ·) =
      arguments.map (some ·.erase))
    (accepted : RecM.infer source (methodsN fuel) inferenceBefore = .ok inferred inferenceAfter)
    (selected : cheapBetaPlan? source = some plan)
    (walkerBounds : KExpr.CheapBetaBounds source)
    (table : InternTable .anon) (coherent : table.WF)
    (faithful : KExpr.CollisionFree fun term => table.ExprSupport term ∨ KExpr.CheapBetaReach source term) :
    ∃ (body : AExpr β) (count : Nat),
      readScopedExpr? resolve locals (cheapBetaReduce source table).1 =
        some ((body.instRev (arguments.take count)).appN (arguments.drop count)).erase ∧
      ConversionClaim.{u,v} entries context ((AExpr.lam condition domain inner).appN arguments)
        ((body.instRev (arguments.take count)).appN (arguments.drop count)) ∧
      TypingClaim.{u,v} entries context
        ((body.instRev (arguments.take count)).appN (arguments.drop count)) type ∧
      (cheapBetaReduce source table).2.WF := by
  obtain ⟨head, rawBody, args, count, plannedSpine, peeling, countBound, _, _⟩ :=
    cheapBetaPlan?_simul selected walkerBounds
  obtain ⟨sameHead, sameArgs⟩ := Prod.mk.inj (spine.symm.trans plannedSpine)
  subst head args
  have reading := readScopedExpr?_collectSpine spine headReads argumentReads
  have resources : CheapBetaSupport source table := ⟨plan, selected, walkerBounds, coherent, faithful⟩
  obtain ⟨enough, resultReads, preserved⟩ := resources.reading reading
  obtain ⟨_, _, _, sourceSpine⟩ := support.soundWithSpine formed agreement reading accepted
  obtain ⟨conversion, reducedTyped⟩ := sourceSpine.betaPrefix enough
  have rawPeel := RecM.BetaPeel.of_peelLamsN
    (.lam name bi rawDomain rawInner lambdaInfo) rawArguments.toList
  rw [Array.length_toList, peeling] at rawPeel
  obtain ⟨body, modelPeel, bodyReads⟩ := betaPeel_readScopedExpr? rawPeel.1 headReads
  have sizeAgrees : rawArguments.size = arguments.length := by
    have lengths := congrArg List.length argumentReads
    simpa using lengths
  have countLength : (arguments.take count).length = count := by
    simp only [List.length_take]
    omega
  have rawCountLength : (rawArguments.toList.take count).length = count := by
    simp only [List.length_take, Array.length_toList]
    omega
  have counted : cheapBetaCount source = count := by
    simp only [cheapBetaCount, spine, peeling]
  have prefixEq := (show LambdaPeel (.lam condition domain inner) (arguments.take count).length body by
    simpa only [countLength, rawCountLength] using modelPeel).betaPrefix (arguments.drop count)
  simp only [List.take_append_drop, countLength] at prefixEq
  exact ⟨body, count, by simpa only [counted, prefixEq] using resultReads,
    by simpa only [counted, prefixEq] using conversion,
    by simpa only [counted, prefixEq] using reducedTyped, preserved⟩

end Ix.Kernel.Consistency
