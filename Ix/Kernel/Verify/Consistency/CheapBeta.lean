/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaSpine
import Ix.Kernel.Verify.Infer.CheapBetaPlan

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
  obtain ⟨head, rawBody, args, count, plannedSpine, peeling, countBound, base, trailing⟩ :=
    cheapBetaPlan?_simul selected walkerBounds
  obtain ⟨sameHead, sameArgs⟩ := Prod.mk.inj (spine.symm.trans plannedSpine)
  subst head args
  have reading := readScopedExpr?_collectSpine spine headReads argumentReads
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
  have prefixSize : (rawArguments.extract 0 count).size = count := by
    simp only [Array.size_extract]
    omega
  have prefixReads : (rawArguments.extract 0 count).toList.map (readScopedExpr? resolve locals ·) =
      (arguments.take count).map (some ·.erase) := by
    simp only [Array.toList_extract, List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero,
      List.map_take, argumentReads]
  have suffixReads : plan.trailing.map (readScopedExpr? resolve locals ·) =
      (arguments.drop count).map (some ·.erase) := by
    rw [trailing]
    simp only [Array.toList_extract, List.extract_eq_take_drop, List.map_take, List.map_drop,
      argumentReads, sizeAgrees]
    rw [← List.map_drop, ← List.map_take]
    congr 1
    have length : (arguments.drop count).length = arguments.length - count := List.length_drop
    rw [← length, List.take_length]
  have simulBounds := walkerBounds.2 spine peeling
  have baseReads : readScopedExpr? resolve locals plan.base =
      some (body.instRev (arguments.take count)).erase := by
    rw [base]
    have readSimul := readScopedExpr?_simulSubstSpec (depth := 0)
      (by simp only [Array.size_reverse, prefixSize, countLength])
      simulBounds.2.2.2.1 simulBounds.2.2.1
      (by simpa only [UInt64.toNat_zero, Nat.zero_add, countLength, rawCountLength] using bodyReads)
      (argumentsReading_reverse_get prefixReads (prefixSize.trans countLength.symm))
    simpa only [UInt64.toNat_zero, Nat.zero_add, AExpr.instRevAt_zero] using readSimul
  have chainFaithful : KExpr.CollisionFree fun term => table.ExprSupport term ∨
      term ∈ cheapBetaChainList plan.base plan.trailing := by
    apply faithful.mono
    intro term member
    rcases member with resident | candidate
    · exact Or.inl resident
    · exact Or.inr (by simpa [KExpr.CheapBetaReach, selected] using Or.inr candidate)
  obtain ⟨resultReads, preserved⟩ := internAppChain_readScopedExpr? coherent chainFaithful baseReads suffixReads
  have conversion := SynthesisInference.beta_peel_sound (consumed := arguments.take count)
    (trailing := arguments.drop count)
    (by simpa only [List.take_append_drop] using support) formed agreement
    (by simpa only [List.take_append_drop] using reading) accepted
    (by simpa only [countLength, rawCountLength] using modelPeel)
  refine ⟨body, count, ?_, ?_, conversion.2, ?_⟩
  · simpa only [cheapBetaReduce, selected] using resultReads
  · simpa only [List.take_append_drop] using conversion.1
  · simpa only [cheapBetaReduce, selected] using preserved

end Ix.Kernel.Consistency
