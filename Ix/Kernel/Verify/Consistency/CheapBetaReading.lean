/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.SpineReading
import Ix.Kernel.Verify.Infer.CheapBetaPlan

/-! Read a selected cheap-beta result independently of inference soundness.
The only inputs are its source reading and finite representation resources. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

/-- The number of original lambdas selected by the production planner. -/
def cheapBetaCount (source : KExpr .anon) : Nat :=
  (peelLamsN source.collectSpine.2.size source.collectSpine.1).2

/-- Concrete planning, arithmetic, and hash support for the actual cheap
reduction. The structure carries no typing or conversion facts. -/
structure CheapBetaSupport (source : KExpr .anon) (table : InternTable .anon) where
  plan : CheapBetaPlan .anon
  selected : cheapBetaPlan? source = some plan
  bounds : KExpr.CheapBetaBounds source
  coherent : table.WF
  faithful : KExpr.CollisionFree fun term => table.ExprSupport term ∨ KExpr.CheapBetaReach source term

theorem CheapBetaSupport.reading {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {source : KExpr .anon} {table : InternTable .anon}
    {condition : Certified.PropWhen} {domain inner : AExpr β} {arguments : List (AExpr β)}
    (support : CheapBetaSupport source table)
    (reading : readScopedExpr? resolve locals source =
      some ((AExpr.lam condition domain inner).appN arguments).erase) :
    cheapBetaCount source ≤ inner.lambdaDepth + 1 ∧
      readScopedExpr? resolve locals (cheapBetaReduce source table).1 =
        some (AExpr.betaPrefix (cheapBetaCount source) (.lam condition domain inner) arguments).erase ∧
      (cheapBetaReduce source table).2.WF := by
  obtain ⟨headReads, argumentReads⟩ :=
    readScopedExpr?_lambda_spine (cheapBetaPlan?_head_lambda support.selected) reading
  obtain ⟨head, rawBody, args, count, spine, peeling, countBound, base, trailing⟩ :=
    cheapBetaPlan?_simul support.selected support.bounds
  have counted : cheapBetaCount source = count := by
    simp only [cheapBetaCount, spine, peeling]
  rw [spine] at headReads argumentReads
  have rawPeel := RecM.BetaPeel.of_peelLamsN head args.toList
  rw [Array.length_toList, peeling] at rawPeel
  obtain ⟨body, modelPeel, bodyReads⟩ := betaPeel_readScopedExpr? rawPeel.1 headReads
  have sizeAgrees : args.size = arguments.length := by
    have lengths := congrArg List.length argumentReads
    simpa using lengths
  have countLength : (arguments.take count).length = count := by
    simp only [List.length_take]
    omega
  have rawCountLength : (args.toList.take count).length = count := by
    simp only [List.length_take, Array.length_toList]
    omega
  have prefixSize : (args.extract 0 count).size = count := by
    simp only [Array.size_extract]
    omega
  have prefixReads : (args.extract 0 count).toList.map (readScopedExpr? resolve locals ·) =
      (arguments.take count).map (some ·.erase) := by
    simp only [Array.toList_extract, List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero,
      List.map_take, argumentReads]
  have suffixReads : support.plan.trailing.map (readScopedExpr? resolve locals ·) =
      (arguments.drop count).map (some ·.erase) := by
    rw [trailing]
    simp only [Array.toList_extract, List.extract_eq_take_drop, List.map_take, List.map_drop,
      argumentReads, sizeAgrees]
    rw [← List.map_drop, ← List.map_take]
    congr 1
    have length : (arguments.drop count).length = arguments.length - count := List.length_drop
    rw [← length, List.take_length]
  have simulBounds := support.bounds.2 spine peeling
  have baseReads : readScopedExpr? resolve locals support.plan.base =
      some (body.instRev (arguments.take count)).erase := by
    rw [base]
    have readSimul := readScopedExpr?_simulSubstSpec (depth := 0)
      (by simp only [Array.size_reverse, prefixSize, countLength])
      simulBounds.2.2.2.1 simulBounds.2.2.1
      (by simpa only [UInt64.toNat_zero, Nat.zero_add, countLength, rawCountLength] using bodyReads)
      (argumentsReading_reverse_get prefixReads (prefixSize.trans countLength.symm))
    simpa only [UInt64.toNat_zero, Nat.zero_add, AExpr.instRevAt_zero] using readSimul
  have chainFaithful : KExpr.CollisionFree fun term => table.ExprSupport term ∨
      term ∈ cheapBetaChainList support.plan.base support.plan.trailing := by
    apply support.faithful.mono
    intro term member
    rcases member with resident | candidate
    · exact Or.inl resident
    · exact Or.inr (by simpa [KExpr.CheapBetaReach, support.selected] using Or.inr candidate)
  obtain ⟨resultReads, preserved⟩ :=
    internAppChain_readScopedExpr? support.coherent chainFaithful baseReads suffixReads
  have prefixEq := (show LambdaPeel (.lam condition domain inner) (arguments.take count).length body by
    simpa only [countLength, rawCountLength] using modelPeel).betaPrefix (arguments.drop count)
  simp only [List.take_append_drop, countLength] at prefixEq
  refine ⟨?_, ?_, ?_⟩
  · simpa only [counted, rawCountLength, AExpr.lambdaDepth] using modelPeel.length_bound
  · simpa only [cheapBetaReduce, support.selected, counted, prefixEq] using resultReads
  · simpa only [cheapBetaReduce, support.selected] using preserved

end Ix.Kernel.Consistency
