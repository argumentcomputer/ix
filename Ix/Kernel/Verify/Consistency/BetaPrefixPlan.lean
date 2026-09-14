/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.SpineReading

/-! The common lambda-prefix operation after a WHNF head callback.
Production peeling, substitution, and suffix interning compute its result. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

structure BetaPrefixPlan {β : Type u} (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) (before : TcState .anon) where
  name : Mode.anon.F Name
  bi : Mode.anon.F Lean.BinderInfo
  rawDomain : KExpr .anon
  rawInner : KExpr .anon
  lambdaInfo : ExprInfo .anon
  rawArguments : Array (KExpr .anon)
  rawBody : KExpr .anon
  consumed : Array (KExpr .anon)
  condition : Certified.PropWhen
  domain : AExpr β
  inner : AExpr β
  arguments : List (AExpr β)
  headReads : readScopedExpr? resolve locals (.lam name bi rawDomain rawInner lambdaInfo) =
    some (AExpr.lam condition domain inner).erase
  argumentReads : rawArguments.toList.map (readScopedExpr? resolve locals ·) = arguments.map (some ·.erase)
  peeling : RecM.consumeBetaLams (.lam name bi rawDomain rawInner lambdaInfo) rawArguments = (rawBody, consumed)
  nonempty : (!consumed.isEmpty) = true
  walkerBounds : SimulSubstBounds rawBody consumed.reverse 0
  walkerFaithful : KExpr.CollisionFree fun term => before.env.intern.ExprSupport term ∨
    KExpr.SimulSubstReach consumed.reverse rawBody 0 term
  suffixFaithful : KExpr.CollisionFree fun term =>
    (simulSubst rawBody consumed.reverse 0 before.env.intern).2.ExprSupport term ∨
      term ∈ cheapBetaChainList (simulSubst rawBody consumed.reverse 0 before.env.intern).1
        (rawArguments.extract consumed.size rawArguments.size).toList

namespace BetaPrefixPlan

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {locals : List FVarId} {before : TcState .anon}

def rawLambda (plan : BetaPrefixPlan resolve locals before) : KExpr .anon :=
  .lam plan.name plan.bi plan.rawDomain plan.rawInner plan.lambdaInfo

def modelLambda (plan : BetaPrefixPlan resolve locals before) : AExpr β :=
  .lam plan.condition plan.domain plan.inner

def modelInput (plan : BetaPrefixPlan resolve locals before) : AExpr β :=
  plan.modelLambda.appN plan.arguments

def output (plan : BetaPrefixPlan resolve locals before) : KExpr .anon × InternTable .anon :=
  let walk := simulSubst plan.rawBody plan.consumed.reverse 0 before.env.intern
  internAppChain walk.1 (plan.rawArguments.extract plan.consumed.size plan.rawArguments.size).toList walk.2

def result (plan : BetaPrefixPlan resolve locals before) : KExpr .anon := plan.output.1

def after (plan : BetaPrefixPlan resolve locals before) : TcState .anon :=
  {before with env := {before.env with intern := plan.output.2}}

def modelResult (plan : BetaPrefixPlan resolve locals before) : AExpr β :=
  AExpr.betaPrefix plan.consumed.size plan.modelLambda plan.arguments

theorem counts (plan : BetaPrefixPlan resolve locals before) :
    plan.consumed.size ≤ plan.inner.lambdaDepth + 1 ∧ plan.consumed.size ≤ plan.arguments.length := by
  obtain ⟨peeled, _, rawBound⟩ := RecM.BetaPeel.of_consume plan.peeling
  obtain ⟨_, modelPeel, _⟩ := betaPeel_readScopedExpr? peeled plan.headReads
  have sizeAgrees : plan.rawArguments.size = plan.arguments.length := by
    have lengths := congrArg List.length plan.argumentReads
    simpa using lengths
  exact ⟨by simpa only [Array.length_toList, AExpr.lambdaDepth] using modelPeel.length_bound,
    sizeAgrees ▸ rawBound⟩

theorem reading (plan : BetaPrefixPlan resolve locals before) (coherent : before.env.intern.WF) :
    readScopedExpr? resolve locals plan.result = some plan.modelResult.erase ∧ plan.after.env.intern.WF := by
  obtain ⟨rawPeel, consumedPrefix, consumedBound⟩ := RecM.BetaPeel.of_consume plan.peeling
  obtain ⟨body, modelPeel, bodyReads⟩ := betaPeel_readScopedExpr? rawPeel plan.headReads
  have consumedSize : (plan.arguments.take plan.consumed.size).length = plan.consumed.size := by
    simp only [List.length_take, Nat.min_eq_left plan.counts.2]
  have consumedReads : plan.consumed.toList.map (readScopedExpr? resolve locals ·) =
      (plan.arguments.take plan.consumed.size).map (some ·.erase) := by
    rw [consumedPrefix, List.map_take, plan.argumentReads, List.map_take]
  have suffixReads : (plan.rawArguments.extract plan.consumed.size plan.rawArguments.size).toList.map
      (readScopedExpr? resolve locals ·) = (plan.arguments.drop plan.consumed.size).map (some ·.erase) := by
    rw [RecM.BetaPeel.remaining_eq_drop plan.peeling, List.map_drop, plan.argumentReads, List.map_drop]
  obtain ⟨walkReads, walkCoherent⟩ := simulSubst_readScopedExpr?
    (by simpa only [Array.size_reverse] using consumedSize.symm)
    plan.walkerBounds.1 plan.walkerBounds.2.1 (by simpa using plan.walkerBounds.2.2.2.1)
    plan.walkerBounds.2.2.1 coherent plan.walkerFaithful
    (by simpa only [Nat.zero_add, Array.length_toList, consumedSize] using bodyReads)
    (argumentsReading_reverse_get consumedReads consumedSize.symm)
  have peelingMeaning := LambdaPeel.betaPrefix (arguments := plan.arguments.take plan.consumed.size)
    (by simpa only [consumedSize, Array.length_toList] using modelPeel) (plan.arguments.drop plan.consumed.size)
  simp only [consumedSize, List.take_append_drop] at peelingMeaning
  obtain ⟨reads, preserved⟩ := internAppChain_readScopedExpr? walkCoherent plan.suffixFaithful walkReads suffixReads
  exact ⟨by simpa only [result, output, modelResult, modelLambda, peelingMeaning] using reads, preserved⟩

/-- This equation permits a recursively reduced head and retains its exact
post-call state before simultaneous substitution starts. -/
theorem run (plan : BetaPrefixPlan resolve locals before) {methods : Methods .anon}
    {initial : TcState .anon} {fn arg head : KExpr .anon} {info : ExprInfo .anon} {flags : WhnfFlags}
    (spine : (KExpr.app fn arg info).collectSpine = (head, plan.rawArguments))
    (headRun : methods.whnfCoreFlags head flags initial = .ok plan.rawLambda before) :
    (RecM.whnfCoreWithFlagsStep (.app fn arg info) flags).run methods initial =
      .ok (.next plan.result) plan.after := by
  apply RecM.whnfCoreWithFlagsStep_betaMany spine headRun plan.peeling plan.nonempty rfl
  rw [RecM.finishAppResult_eq_internAppChain]
  rfl

end BetaPrefixPlan

end Ix.Kernel.Consistency
