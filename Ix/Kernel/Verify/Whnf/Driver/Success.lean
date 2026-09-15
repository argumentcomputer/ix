/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Whnf

/-! Recover the actual subcalls of successful WHNF drivers. These inversions
use only the production monad and cache control flow. -/

namespace Ix.Kernel.RecM

private theorem bind_success {α γ : Type} {action : TcM .anon α}
    {next : α → TcM .anon γ} {before after : TcState .anon} {result : γ}
    (run : EStateM.bind action next before = .ok result after) :
    ∃ value middle, action before = .ok value middle ∧ next value middle = .ok result after := by
  unfold EStateM.bind at run
  cases step : action before with
  | error error state => rw [step] at run; contradiction
  | ok value middle => rw [step] at run; exact ⟨value, middle, rfl, run⟩

private theorem runBounded_first_success {α γ : Type}
    {step : α → RecM .anon (BoundedStep α γ)} {fuel : Nat}
    {methods : Methods .anon} {before after : TcState .anon} {source : α} {result : γ}
    (accepted : (runBounded step fuel source).run methods before = .ok result after) :
    ∃ outcome middle, (step source).run methods before = .ok outcome middle := by
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
      rw [runBounded, ReaderT.run_bind] at accepted
      change EStateM.bind ((step source).run methods) _ before = _ at accepted
      obtain ⟨outcome, middle, executed, _⟩ := bind_success accepted
      exact ⟨outcome, middle, executed⟩

/-- A successful structural-cache miss determines the actual uncached run
and the precise state immediately before its publication. -/
theorem whnfCoreWithFlagsNonLeaf_fullMiss_success
    {methods : Methods .anon} {s s₁ s₂ after : TcState .anon}
    {source result : KExpr .anon} {flags : WhnfFlags} {key : Address × Address}
    (hfull : flags.isFull = true)
    (hkey : TcM.whnfKey source s = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ = .ok false s₂)
    (hmiss : s₂.env.whnfCoreCache[key]? = none)
    (accepted : (whnfCoreWithFlagsNonLeaf source flags).run methods s = .ok result after) :
    ∃ reduced, (whnfCoreWithFlagsUncached source flags).run methods s₂ = .ok result reduced ∧
      after = { reduced with env := { reduced.env with whnfCoreCache := reduced.env.whnfCoreCache.insert key result } } := by
  unfold whnfCoreWithFlagsNonLeaf at accepted
  rw [ReaderT.run_bind] at accepted
  change EStateM.bind (TcM.whnfKey source) _ s = _ at accepted
  rw [EStateM.bind, hkey] at accepted
  simp only at accepted
  rw [ReaderT.run_bind] at accepted
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₁ = _ at accepted
  rw [EStateM.bind, htransient] at accepted
  simp [hfull] at accepted
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₂ = _ at accepted
  rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) s₂ = .ok s₂ s₂ from rfl] at accepted
  simp only [hmiss] at accepted
  rw [ReaderT.run_bind] at accepted
  change EStateM.bind ((whnfCoreWithFlagsUncached source flags).run methods) _ s₂ = _ at accepted
  cases raw : (whnfCoreWithFlagsUncached source flags).run methods s₂ with
  | error error failed => simp only [EStateM.bind, raw] at accepted; cases accepted
  | ok value reduced =>
      rw [EStateM.bind, raw] at accepted
      change EStateM.Result.ok value { reduced with env := { reduced.env with
        whnfCoreCache := reduced.env.whnfCoreCache.insert key value } } = .ok result after at accepted
      obtain ⟨rfl, afterEq⟩ := EStateM.Result.ok.inj accepted
      exact ⟨reduced, rfl, afterEq.symm⟩


/-- A successful no-delta miss includes a successful first structural call.
The theorem makes no assumption about which later reducer terminates. -/
theorem whnfNoDeltaImplNonLeaf_fullMiss_core_success
    {methods : Methods .anon} {s s₁ s₂ after : TcState .anon}
    {source result : KExpr .anon} {flags : WhnfFlags} {key : Address × Address}
    (hfull : flags.isFull = true)
    (hkey : TcM.whnfKey source s = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ = .ok false s₂)
    (hmiss : s₂.env.whnfNoDeltaCache[key]? = none)
    (accepted : (whnfNoDeltaImplNonLeaf source flags .collapse).run methods s = .ok result after) :
    ∃ coreResult coreAfter, (whnfCoreWithFlags source flags).run methods s₂ = .ok coreResult coreAfter := by
  unfold whnfNoDeltaImplNonLeaf at accepted
  rw [ReaderT.run_bind] at accepted
  change EStateM.bind (TcM.whnfKey source) _ s = _ at accepted
  rw [EStateM.bind, hkey] at accepted
  simp only at accepted
  rw [ReaderT.run_bind] at accepted
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₁ = _ at accepted
  rw [EStateM.bind, htransient] at accepted
  simp [hfull, show (NatSuccMode.collapse == NatSuccMode.collapse) = true from rfl] at accepted
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₂ = _ at accepted
  rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) s₂ = .ok s₂ s₂ from rfl] at accepted
  simp only [hmiss] at accepted
  rw [ReaderT.run_bind] at accepted
  change EStateM.bind ((whnfNoDeltaImplUncached source flags .collapse).run methods) _ s₂ = _ at accepted
  obtain ⟨_, _, raw, _⟩ := bind_success accepted
  obtain ⟨_, _, first⟩ := runBounded_first_success raw
  unfold whnfNoDeltaImplStep at first
  rw [ReaderT.run_bind] at first
  change EStateM.bind ((whnfCoreWithFlags source flags).run methods) _ s₂ = _ at first
  obtain ⟨coreResult, coreAfter, executed, _⟩ := bind_success first
  exact ⟨coreResult, coreAfter, executed⟩

/-- A successful public miss exposes its actual charge and first no-delta
call, regardless of the later native guard or cache publication. -/
theorem whnfWithNatSuccModeNonLeaf_miss_noDelta_success
    {methods : Methods .anon} {s s₁ s₂ s₃ after : TcState .anon}
    {source result : KExpr .anon} {key : Address × Address}
    (hprefix : (whnfWithNatSuccModePrefix source).run methods s = .ok () s₁)
    (hkey : TcM.whnfKey source s₁ = .ok key s₂)
    (htransient : (isTransientNatLiteralWork source).run methods s₂ = .ok false s₃)
    (hmiss : s₃.env.whnfCache[key]? = none)
    (accepted : (whnfWithNatSuccModeNonLeaf source .collapse).run methods s = .ok result after) :
    ∃ charged noDeltaResult noDeltaAfter,
      (whnfWithNatSuccModeMissCharge : RecM .anon Unit).run methods s₃ = .ok () charged ∧
      (whnfNoDeltaImpl source .FULL .collapse).run methods charged = .ok noDeltaResult noDeltaAfter := by
  unfold whnfWithNatSuccModeNonLeaf at accepted
  rw [ReaderT.run_bind] at accepted
  change EStateM.bind ((whnfWithNatSuccModePrefix source).run methods) _ s = _ at accepted
  rw [EStateM.bind, hprefix] at accepted
  simp only at accepted
  rw [ReaderT.run_bind] at accepted
  change EStateM.bind (TcM.whnfKey source) _ s₁ = _ at accepted
  rw [EStateM.bind, hkey] at accepted
  simp only at accepted
  rw [ReaderT.run_bind] at accepted
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₂ = _ at accepted
  rw [EStateM.bind, htransient] at accepted
  simp [show (NatSuccMode.collapse == NatSuccMode.collapse) = true from rfl] at accepted
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₃ = _ at accepted
  rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) s₃ = .ok s₃ s₃ from rfl] at accepted
  simp only [hmiss] at accepted
  rw [ReaderT.run_bind] at accepted
  change EStateM.bind ((whnfWithNatSuccModeMissCharge : RecM .anon Unit).run methods) _ s₃ = _ at accepted
  obtain ⟨⟨⟩, charged, charge, rest⟩ := bind_success accepted
  rw [ReaderT.run_bind] at rest
  change EStateM.bind ((whnfWithNatSuccModeUncached source .collapse).run methods) _ charged = _ at rest
  obtain ⟨_, _, raw, _⟩ := bind_success rest
  obtain ⟨_, _, first⟩ := runBounded_first_success raw
  unfold whnfWithNatSuccModeStep at first
  rw [ReaderT.run_bind] at first
  change EStateM.bind ((whnfNoDeltaImpl source .FULL .collapse).run methods) _ charged = _ at first
  obtain ⟨noDeltaResult, noDeltaAfter, executed, _⟩ := bind_success first
  exact ⟨charged, noDeltaResult, noDeltaAfter, charge, executed⟩

end Ix.Kernel.RecM
