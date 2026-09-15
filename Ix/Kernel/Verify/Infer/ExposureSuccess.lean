/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Infer

/-! Successful exposure recovers the actual WHNF result and final state. -/

namespace Ix.Kernel.RecM

theorem ensureSortWhnf_success {methods : Methods .anon} {before after : TcState .anon}
    {source : KExpr .anon} {level : KUniv .anon}
    (accepted : (ensureSortWhnf source).run methods before = .ok level after) :
    ∃ info, (whnf source).run methods before = .ok (.sort level info) after := by
  unfold ensureSortWhnf at accepted
  rw [ReaderT.run_bind] at accepted
  change EStateM.bind ((whnf source).run methods) _ before = _ at accepted
  cases raw : (whnf source).run methods before with
  | error error failed => simp only [EStateM.bind, raw] at accepted; cases accepted
  | ok result middle =>
      rw [EStateM.bind, raw] at accepted
      cases result with
      | sort actual info =>
          obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj accepted
          exact ⟨info, rfl⟩
      | _ => cases accepted

theorem ensureForallWhnf_success {methods : Methods .anon} {before after : TcState .anon}
    {source domain body : KExpr .anon}
    (accepted : (ensureForallWhnf source).run methods before = .ok (domain, body) after) :
    ∃ name bi info, (whnf source).run methods before = .ok (.all name bi domain body info) after := by
  unfold ensureForallWhnf at accepted
  rw [ReaderT.run_bind] at accepted
  change EStateM.bind ((whnf source).run methods) _ before = _ at accepted
  cases raw : (whnf source).run methods before with
  | error error failed => simp only [EStateM.bind, raw] at accepted; cases accepted
  | ok result middle =>
      rw [EStateM.bind, raw] at accepted
      cases result with
      | all name bi actualDomain actualBody info =>
          obtain ⟨parts, rfl⟩ := EStateM.Result.ok.inj accepted
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj parts
          exact ⟨name, bi, info, rfl⟩
      | _ => cases accepted

end Ix.Kernel.RecM
