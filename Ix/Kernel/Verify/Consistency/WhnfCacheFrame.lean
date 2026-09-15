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
  apply InferenceCacheFrame.of_eq
  · change plan.reduced.env.inferCache[key]? = before.env.inferCache[key]?
    rw [plan.path.frame.full, (BetaPublicWhnf.coreKey_fields source before).1]
  · change plan.reduced.env.inferOnlyCache[key]? = before.env.inferOnlyCache[key]?
    rw [plan.path.frame.only, (BetaPublicWhnf.coreKey_fields source before).1]
  · change plan.reduced.env.consts = before.env.consts
    rw [plan.path.frame.constants, (BetaPublicWhnf.coreKey_fields source before).1]

theorem BetaPublicWhnfPlan.policy {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr β}
    (plan : BetaPublicWhnfPlan resolve locals fuel before source term result target) :
    plan.after.inferOnly = before.inferOnly := by
  change plan.reduced.inferOnly = before.inferOnly
  rw [plan.path.frame.policy]
  simp only [BetaPublicWhnf.coreKey, BetaPublicWhnf.noDeltaKey,
    BetaPublicWhnf.outerKey, betaWhnfKey_policy, betaWhnfPrefix_policy, betaWhnfCharge_policy]

theorem BetaPiExposure.inference_frame {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source rawDomain rawBody : KExpr .anon} {term domain body : AExpr β} {condition : Certified.PropWhen}
    (exposure : BetaPiExposure resolve locals fuel before source term condition domain body rawDomain rawBody)
    (key : Address × Address) : InferenceCacheFrame key before exposure.after := by
  cases exposure with
  | reduce plan => exact plan.inference_frame key
  | execute execution =>
      exact .of_eq (congrArg (·[key]?) execution.frame.full)
        (congrArg (·[key]?) execution.frame.only) execution.frame.constants
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
  | execute execution => exact execution.frame.policy
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
  constructor
  · change plan.reduced.env.inferCache = before.env.inferCache
    rw [plan.path.frame.full, (BetaPublicWhnf.coreKey_fields source before).1]
  · change plan.reduced.env.inferOnlyCache = before.env.inferOnlyCache
    rw [plan.path.frame.only, (BetaPublicWhnf.coreKey_fields source before).1]

theorem BetaPiExposure.inference_maps {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source rawDomain rawBody : KExpr .anon} {term domain body : AExpr β} {condition : Certified.PropWhen}
    (exposure : BetaPiExposure resolve locals fuel before source term condition domain body rawDomain rawBody) :
    exposure.after.env.inferCache = before.env.inferCache ∧
      exposure.after.env.inferOnlyCache = before.env.inferOnlyCache := by
  cases exposure with
  | reduce plan => exact plan.inference_maps
  | execute execution => exact ⟨execution.frame.full, execution.frame.only⟩
  | cached origin coherent hit =>
      constructor <;>
        simp only [BetaPiExposure.after, BetaPublicWhnf.outerKey, betaWhnfKey_environment,
          (betaWhnfPrefix_fields before).1]

namespace BetaSortExposure

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
  {fuel : Nat} {before : TcState .anon} {source : KExpr .anon} {term : AExpr β} {level : KUniv .anon}

theorem inference_frame (exposure : BetaSortExposure resolve locals fuel before source term level)
    (key : Address × Address) : InferenceCacheFrame key before exposure.after := by
  cases exposure with
  | direct => exact .refl key _
  | reduce plan => exact plan.inference_frame key
  | execute execution =>
      exact .of_eq (congrArg (·[key]?) execution.frame.full)
        (congrArg (·[key]?) execution.frame.only) execution.frame.constants
  | cached origin hit =>
      apply InferenceCacheFrame.of_eq <;>
        simp only [after, BetaPublicWhnf.outerKey, betaWhnfKey_environment,
          (betaWhnfPrefix_fields before).1]

theorem policy (exposure : BetaSortExposure resolve locals fuel before source term level) :
    exposure.after.inferOnly = before.inferOnly := by
  cases exposure with
  | direct => rfl
  | reduce plan => exact plan.policy
  | execute execution => exact execution.frame.policy
  | cached origin hit =>
      simp only [after, BetaPublicWhnf.outerKey, betaWhnfKey_policy, betaWhnfPrefix_policy]

theorem inference_maps (exposure : BetaSortExposure resolve locals fuel before source term level) :
    exposure.after.env.inferCache = before.env.inferCache ∧
      exposure.after.env.inferOnlyCache = before.env.inferOnlyCache := by
  cases exposure with
  | direct => exact ⟨rfl, rfl⟩
  | reduce plan => exact plan.inference_maps
  | execute execution => exact ⟨execution.frame.full, execution.frame.only⟩
  | cached origin hit =>
      constructor <;>
        simp only [after, BetaPublicWhnf.outerKey, betaWhnfKey_environment,
          (betaWhnfPrefix_fields before).1]

end BetaSortExposure

end Ix.Kernel.Consistency
