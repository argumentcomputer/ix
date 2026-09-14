/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.ApplicationWhnf
import Ix.Kernel.Verify.Consistency.InferenceCache

/-! Public beta WHNF and Pi exposure preserve inference cache entries.
Their computed cache writes affect only the WHNF partitions. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

private theorem betaWhnfKey_policy (source : KExpr .anon) (before : TcState .anon) :
    (betaWhnfKey source before).2.inferOnly = before.inferOnly := by
  unfold betaWhnfKey
  split
  · rfl
  · dsimp only
    split <;> rfl

private theorem betaWhnfPrefix_policy (before : TcState .anon) :
    (betaWhnfPrefix before).inferOnly = before.inferOnly := by
  unfold betaWhnfPrefix
  split <;> rfl

private theorem betaWhnfCharge_policy (before : TcState .anon) :
    (betaWhnfCharge before).inferOnly = before.inferOnly := by
  unfold betaWhnfCharge
  split <;> rfl

theorem BetaPublicWhnfPlan.inference_frame {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr β}
    (plan : BetaPublicWhnfPlan resolve locals fuel before source term result target)
    (key : Address × Address) : InferenceCacheFrame key before plan.after := by
  obtain ⟨table, reduced⟩ := plan.path.frame
  apply InferenceCacheFrame.of_eq <;>
    simp only [BetaPublicWhnfPlan.after, BetaPublicWhnf.after, BetaPublicWhnf.noDeltaAfter,
      BetaPublicWhnf.coreAfter, reduced, (BetaPublicWhnf.coreKey_fields source before).1]

theorem BetaPublicWhnfPlan.policy {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr β}
    (plan : BetaPublicWhnfPlan resolve locals fuel before source term result target) :
    plan.after.inferOnly = before.inferOnly := by
  obtain ⟨table, reduced⟩ := plan.path.frame
  simp only [BetaPublicWhnfPlan.after, BetaPublicWhnf.after, BetaPublicWhnf.noDeltaAfter,
    BetaPublicWhnf.coreAfter, reduced, BetaPublicWhnf.coreKey, BetaPublicWhnf.noDeltaKey,
    BetaPublicWhnf.outerKey, betaWhnfKey_policy, betaWhnfPrefix_policy, betaWhnfCharge_policy]

theorem BetaPiExposure.inference_frame {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source rawDomain rawBody : KExpr .anon} {term domain body : AExpr β} {condition : Certified.PropWhen}
    (exposure : BetaPiExposure resolve locals fuel before source term condition domain body rawDomain rawBody)
    (key : Address × Address) : InferenceCacheFrame key before exposure.after := by
  cases exposure with
  | reduce plan => exact plan.inference_frame key
  | cached origin coherent hit =>
      apply InferenceCacheFrame.of_eq <;>
        simp only [BetaPiExposure.after, BetaPublicWhnf.outerKey, betaWhnfKey_environment,
          (betaWhnfPrefix_fields before).1]

theorem BetaPiExposure.policy {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source rawDomain rawBody : KExpr .anon} {term domain body : AExpr β} {condition : Certified.PropWhen}
    (exposure : BetaPiExposure resolve locals fuel before source term condition domain body rawDomain rawBody) :
    exposure.after.inferOnly = before.inferOnly := by
  cases exposure with
  | reduce plan => exact plan.policy
  | cached origin coherent hit =>
      simp only [BetaPiExposure.after, BetaPublicWhnf.outerKey, betaWhnfKey_policy, betaWhnfPrefix_policy]

/-- Public beta WHNF preserves the complete inference maps. This gives an
exact update trace for its surrounding inference, including keys written there. -/
theorem BetaPublicWhnfPlan.inference_maps {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr β}
    (plan : BetaPublicWhnfPlan resolve locals fuel before source term result target) :
    plan.after.env.inferCache = before.env.inferCache ∧
      plan.after.env.inferOnlyCache = before.env.inferOnlyCache := by
  obtain ⟨table, reduced⟩ := plan.path.frame
  constructor <;>
    simp only [BetaPublicWhnfPlan.after, BetaPublicWhnf.after, BetaPublicWhnf.noDeltaAfter,
      BetaPublicWhnf.coreAfter, reduced, (BetaPublicWhnf.coreKey_fields source before).1]

theorem BetaPiExposure.inference_maps {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source rawDomain rawBody : KExpr .anon} {term domain body : AExpr β} {condition : Certified.PropWhen}
    (exposure : BetaPiExposure resolve locals fuel before source term condition domain body rawDomain rawBody) :
    exposure.after.env.inferCache = before.env.inferCache ∧
      exposure.after.env.inferOnlyCache = before.env.inferOnlyCache := by
  cases exposure with
  | reduce plan => exact plan.inference_maps
  | cached origin coherent hit =>
      constructor <;>
        simp only [BetaPiExposure.after, BetaPublicWhnf.outerKey, betaWhnfKey_environment,
          (betaWhnfPrefix_fields before).1]

end Ix.Kernel.Consistency
