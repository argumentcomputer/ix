/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.CacheInvariant
import Ix.Kernel.Driver

/-!
# Inference-cache initialization and declaration boundaries

The real lazy driver starts with empty caches. Failed declaration checks
restore their incoming cache facts; periodic clearing also preserves the
invariant. Thus only successful declaration checking has a remaining
preservation obligation in the serial loop. This module does not assume
that loaded declarations are already semantically admitted.
-/

namespace Ix.Kernel.Consistency

namespace InferenceCacheInvariant

theorem newLazyAnon (meaning : InferenceCacheMeaning) (source : Ixon.Env) (verify : Bool) :
    InferenceCacheInvariant meaning (TcState.newLazyAnon source verify) :=
  empty rfl rfl

theorem initialAnonCheckLoopState (meaning : InferenceCacheMeaning)
    (source : Ixon.Env) (cfg : CheckCfg) :
    InferenceCacheInvariant meaning (Kernel.initialAnonCheckLoopState source cfg).checker :=
  newLazyAnon meaning source cfg.verifyHashes

/-- Every failure of the actual public constant checker returns the
restored pre-check inference maps, including a failure after recursive writes. -/
theorem checkConst_error {meaning : InferenceCacheMeaning} {before after : TcState .anon}
    {id : KId .anon} {error : TcError .anon}
    (valid : InferenceCacheInvariant meaning before)
    (run : TcM.checkConst id before = .error error after) :
    InferenceCacheInvariant meaning after := by
  unfold TcM.checkConst at run
  exact valid.isolateCheckErrors run

theorem finishAnonCheckItem {meaning : InferenceCacheMeaning} (cfg : CheckCfg)
    (before : AnonCheckLoopState) (item : AnonWorkItem) {checker : TcState .anon}
    (error : Option String) (valid : InferenceCacheInvariant meaning checker) :
    InferenceCacheInvariant meaning (Kernel.finishAnonCheckItem cfg before item checker error).checker := by
  unfold Kernel.finishAnonCheckItem
  dsimp only
  split
  · exact clearReductionCaches meaning checker
  · exact valid

/-- The loop uses one preservation contract for successful declarations.
Error isolation and cache clearing are discharged from production code. -/
theorem runAnonCheckItem {meaning : InferenceCacheMeaning} (cfg : CheckCfg)
    (item : AnonWorkItem) {before : AnonCheckLoopState}
    (valid : InferenceCacheInvariant meaning before.checker)
    (checked : ∀ after, TcM.checkConst (⟨item.primary, ()⟩ : KId .anon) before.checker =
      .ok () after → InferenceCacheInvariant meaning after) :
    InferenceCacheInvariant meaning (Kernel.runAnonCheckItem cfg before item).checker := by
  simp only [Kernel.runAnonCheckItem, EStateM.run]
  cases run : TcM.checkConst (⟨item.primary, ()⟩ : KId .anon) before.checker with
  | ok value after =>
      cases value
      exact finishAnonCheckItem cfg before item none (checked after run)
  | error error after =>
      exact finishAnonCheckItem cfg before item (some (toString error))
        (valid.checkConst_error run)

theorem runAnonCheckList {meaning : InferenceCacheMeaning} (cfg : CheckCfg)
    (work : List AnonWorkItem) {before : AnonCheckLoopState}
    (valid : InferenceCacheInvariant meaning before.checker)
    (checked : ∀ item ∈ work, ∀ state after,
      InferenceCacheInvariant meaning state →
      TcM.checkConst (⟨item.primary, ()⟩ : KId .anon) state = .ok () after →
      InferenceCacheInvariant meaning after) :
    InferenceCacheInvariant meaning (Kernel.runAnonCheckList cfg work before).checker := by
  induction work generalizing before with
  | nil => exact valid
  | cons item rest ih =>
      exact ih (runAnonCheckItem cfg item valid
        (fun after run => checked item (by simp) before.checker after valid run))
        (fun other member => checked other (by simp [member]))

theorem initialized_runAnonCheckList (meaning : InferenceCacheMeaning) (source : Ixon.Env)
    (cfg : CheckCfg) (work : List AnonWorkItem)
    (checked : ∀ item ∈ work, ∀ state after,
      InferenceCacheInvariant meaning state →
      TcM.checkConst (⟨item.primary, ()⟩ : KId .anon) state = .ok () after →
      InferenceCacheInvariant meaning after) :
    InferenceCacheInvariant meaning (Kernel.runAnonCheckList cfg work
      (Kernel.initialAnonCheckLoopState source cfg)).checker :=
  runAnonCheckList cfg work (initialAnonCheckLoopState meaning source cfg) checked

end InferenceCacheInvariant
end Ix.Kernel.Consistency
