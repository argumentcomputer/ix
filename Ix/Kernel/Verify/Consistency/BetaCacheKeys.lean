/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaPublicWhnfPlan

/-! WHNF key stability through beta reduction and cache publication. These
facts concern the actual memoized key, including loose-variable contexts. -/

namespace Ix.Kernel.Consistency

private theorem suffixStep_congr {before after : TcState .anon}
    (context : after.ctx = before.ctx) (values : after.letVals = before.letVals) (need : Nat) :
    TcM.ctxSuffixNeedStep after need = TcM.ctxSuffixNeedStep before need := by
  unfold TcM.ctxSuffixNeedStep
  simp only [context, values]

private theorem suffixNeed_congr {before after : TcState .anon}
    (context : after.ctx = before.ctx) (values : after.letVals = before.letVals) :
    ∀ fuel need, TcM.ctxSuffixNeed after fuel need = TcM.ctxSuffixNeed before fuel need
  | 0, _ => rfl
  | fuel + 1, need => by
      simp only [TcM.ctxSuffixNeed, suffixStep_congr context values]
      split
      · rfl
      · exact suffixNeed_congr context values fuel _

theorem betaWhnfKey_congr (source : KExpr .anon) {before after : TcState .anon}
    (context : after.ctx = before.ctx) (values : after.letVals = before.letVals)
    (identity : after.ctxId = before.ctxId) (memo : after.ctxAddrCache = before.ctxAddrCache) :
    (betaWhnfKey source after).1 = (betaWhnfKey source before).1 := by
  have digest (radius : UInt64) : TcM.ctxAddrForLbrUncached after radius =
      TcM.ctxAddrForLbrUncached before radius := by
    unfold TcM.ctxAddrForLbrUncached
    simp only [context, suffixNeed_congr context values, values, identity]
  unfold betaWhnfKey
  simp only [context, identity, memo, digest]
  by_cases fast : (source.lbr == 0 || before.ctx.isEmpty) = true
  · simp only [fast, if_true]
  · simp only [fast]
    cases before.ctxAddrCache[(before.ctxId, source.lbr)]? <;> rfl

/-- A freshly memoized digest is reused exactly on the next key lookup.
No collision or semantic cache premise is needed for this execution fact. -/
theorem betaWhnfKey_replay (source : KExpr .anon) (before : TcState .anon) :
    betaWhnfKey source (betaWhnfKey source before).2 = betaWhnfKey source before := by
  by_cases fast : (source.lbr == 0 || before.ctx.isEmpty) = true
  · simp [betaWhnfKey, fast]
  · cases memo : before.ctxAddrCache[(before.ctxId, source.lbr)]? <;>
      simp [betaWhnfKey, fast, memo]

theorem betaWhnfKey_prefix (source : KExpr .anon) (before : TcState .anon) :
    (betaWhnfKey source (betaWhnfPrefix before)).1 = (betaWhnfKey source before).1 := by
  unfold betaWhnfPrefix
  split <;> exact betaWhnfKey_congr source rfl rfl rfl rfl

theorem betaWhnfKey_charge (source : KExpr .anon) (before : TcState .anon) :
    (betaWhnfKey source (betaWhnfCharge before)).1 = (betaWhnfKey source before).1 := by
  unfold betaWhnfCharge
  split <;> exact betaWhnfKey_congr source rfl rfl rfl rfl

end Ix.Kernel.Consistency
