/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Whnf

/-! Pure execution equations for the structural, no-delta, and full WHNF
cache layers. These statements have no semantic-interface dependencies. -/

namespace Ix.Kernel.RecM

private theorem natSuccMode_collapse_beq :
    (NatSuccMode.collapse == NatSuccMode.collapse) = true := rfl

/-- Exact full-policy cache-hit execution after key and transient checks. -/
theorem whnfCoreWithFlagsNonLeaf_fullHit
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {source cached : KExpr .anon} {flags : WhnfFlags}
    {key : Address × Address}
    (hfull : flags.isFull = true)
    (hkey : TcM.whnfKey source s = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok false s₂)
    (hhit : s₂.env.whnfCoreCache[key]? = some cached) :
    (whnfCoreWithFlagsNonLeaf source flags).run methods s =
      .ok cached s₂ := by
  unfold whnfCoreWithFlagsNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [htransient]
  simp [hfull]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₂ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₂ = .ok s₂ s₂ from rfl]
  simp only [hhit]
  rfl

/-- Exact full-policy miss execution, including the physical insertion. -/
theorem whnfCoreWithFlagsNonLeaf_fullMiss
    {methods : Methods .anon} {s s₁ s₂ s₃ : TcState .anon}
    {source result : KExpr .anon} {flags : WhnfFlags}
    {key : Address × Address}
    (hfull : flags.isFull = true)
    (hkey : TcM.whnfKey source s = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok false s₂)
    (hmiss : s₂.env.whnfCoreCache[key]? = none)
    (hrun : (whnfCoreWithFlagsUncached source flags).run methods s₂ =
      .ok result s₃) :
    (whnfCoreWithFlagsNonLeaf source flags).run methods s =
      .ok result {s₃ with env := {s₃.env with
        whnfCoreCache := s₃.env.whnfCoreCache.insert key result}} := by
  unfold whnfCoreWithFlagsNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [htransient]
  simp [hfull]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₂ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₂ = .ok s₂ s₂ from rfl]
  simp only [hmiss]
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((whnfCoreWithFlagsUncached source flags).run methods) _ s₂ = _
  unfold EStateM.bind
  rw [hrun]
  rfl

theorem whnfNoDeltaImplNonLeaf_fullHit
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {source cached : KExpr .anon} {flags : WhnfFlags}
    {key : Address × Address}
    (hfull : flags.isFull = true)
    (hkey : TcM.whnfKey source s = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok false s₂)
    (hhit : s₂.env.whnfNoDeltaCache[key]? = some cached) :
    (whnfNoDeltaImplNonLeaf source flags .collapse).run methods s =
      .ok cached s₂ := by
  unfold whnfNoDeltaImplNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [htransient]
  simp [natSuccMode_collapse_beq, hfull]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₂ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₂ = .ok s₂ s₂ from rfl]
  simp only [hhit]
  rfl

theorem whnfNoDeltaImplNonLeaf_fullMiss
    {methods : Methods .anon} {s s₁ s₂ s₃ : TcState .anon}
    {source result : KExpr .anon} {flags : WhnfFlags}
    {key : Address × Address}
    (hfull : flags.isFull = true)
    (hkey : TcM.whnfKey source s = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok false s₂)
    (hmiss : s₂.env.whnfNoDeltaCache[key]? = none)
    (hrun : (whnfNoDeltaImplUncached source flags .collapse).run methods s₂ =
      .ok result s₃)
    (hnative : s₃.inNativeReduce = false) :
    (whnfNoDeltaImplNonLeaf source flags .collapse).run methods s =
      .ok result {s₃ with env := {s₃.env with
        whnfNoDeltaCache := s₃.env.whnfNoDeltaCache.insert key result}} := by
  unfold whnfNoDeltaImplNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [htransient]
  simp [natSuccMode_collapse_beq, hfull]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₂ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₂ = .ok s₂ s₂ from rfl]
  simp only [hmiss]
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((whnfNoDeltaImplUncached source flags .collapse).run methods) _ s₂ = _
  unfold EStateM.bind
  rw [hrun]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₃ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₃ = .ok s₃ s₃ from rfl]
  simp only
  rw [if_pos hnative]
  rfl

theorem whnfWithNatSuccModeNonLeaf_hit
    {methods : Methods .anon} {s s₁ s₂ s₃ : TcState .anon}
    {source cached : KExpr .anon} {key : Address × Address}
    (hprefix : (whnfWithNatSuccModePrefix source).run methods s =
      .ok () s₁)
    (hkey : TcM.whnfKey source s₁ = .ok key s₂)
    (htransient : (isTransientNatLiteralWork source).run methods s₂ =
      .ok false s₃)
    (hhit : s₃.env.whnfCache[key]? = some cached) :
    (whnfWithNatSuccModeNonLeaf source .collapse).run methods s =
      .ok cached s₃ := by
  unfold whnfWithNatSuccModeNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((whnfWithNatSuccModePrefix source).run methods) _ s = _
  unfold EStateM.bind
  rw [hprefix]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s₁ = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₂ = _
  unfold EStateM.bind
  rw [htransient]
  simp [natSuccMode_collapse_beq]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₃ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₃ = .ok s₃ s₃ from rfl]
  simp only [hhit]
  rfl

theorem whnfWithNatSuccModeNonLeaf_miss
    {methods : Methods .anon} {s s₁ s₂ s₃ s₄ s₅ : TcState .anon}
    {source result : KExpr .anon} {key : Address × Address}
    (hprefix : (whnfWithNatSuccModePrefix source).run methods s =
      .ok () s₁)
    (hkey : TcM.whnfKey source s₁ = .ok key s₂)
    (htransient : (isTransientNatLiteralWork source).run methods s₂ =
      .ok false s₃)
    (hmiss : s₃.env.whnfCache[key]? = none)
    (hcharge : (whnfWithNatSuccModeMissCharge : RecM .anon Unit).run
      methods s₃ = .ok () s₄)
    (hrun : (whnfWithNatSuccModeUncached source .collapse).run methods s₄ =
      .ok result s₅)
    (hnative : s₅.inNativeReduce = false) :
    (whnfWithNatSuccModeNonLeaf source .collapse).run methods s =
      .ok result {s₅ with env := {s₅.env with
        whnfCache := s₅.env.whnfCache.insert key result}} := by
  unfold whnfWithNatSuccModeNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((whnfWithNatSuccModePrefix source).run methods) _ s = _
  unfold EStateM.bind
  rw [hprefix]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s₁ = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₂ = _
  unfold EStateM.bind
  rw [htransient]
  simp [natSuccMode_collapse_beq]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₃ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₃ = .ok s₃ s₃ from rfl]
  simp only [hmiss]
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((whnfWithNatSuccModeMissCharge : RecM .anon Unit).run methods) _ s₃ = _
  unfold EStateM.bind
  rw [hcharge]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((whnfWithNatSuccModeUncached source .collapse).run methods) _ s₄ = _
  unfold EStateM.bind
  rw [hrun]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₅ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₅ = .ok s₅ s₅ from rfl]
  simp only
  rw [if_pos hnative]
  rfl


end Ix.Kernel.RecM
