/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaWhnfState
import Ix.Kernel.Verify.Expr

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

private theorem digest_congr {before after : TcState .anon}
    (context : after.ctx = before.ctx) (values : after.letVals = before.letVals)
    (identity : after.ctxId = before.ctxId) (radius : UInt64) :
    TcM.ctxAddrForLbrUncached after radius = TcM.ctxAddrForLbrUncached before radius := by
  unfold TcM.ctxAddrForLbrUncached
  simp only [context, suffixNeed_congr context values, values, identity]

theorem betaWhnfKey_congr (source : KExpr .anon) {before after : TcState .anon}
    (context : after.ctx = before.ctx) (values : after.letVals = before.letVals)
    (identity : after.ctxId = before.ctxId) (memo : after.ctxAddrCache = before.ctxAddrCache) :
    (betaWhnfKey source after).1 = (betaWhnfKey source before).1 := by
  unfold betaWhnfKey
  simp only [context, identity, memo, digest_congr context values identity]
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

/-- Memoizing a head's context suffix preserves every surrounding WHNF key,
including a different loose-variable radius. Existing entries may be arbitrary. -/
theorem betaWhnfKey_key (source query : KExpr .anon) (before : TcState .anon) :
    (betaWhnfKey query (betaWhnfKey source before).2).1 = (betaWhnfKey query before).1 := by
  by_cases fast : (source.lbr == 0 || before.ctx.isEmpty) = true
  · simp [betaWhnfKey, fast]
  · cases memo : before.ctxAddrCache[(before.ctxId, source.lbr)]? with
    | some cached => simp [betaWhnfKey, fast, memo]
    | none =>
        by_cases radius : query.lbr = source.lbr
        · simp [betaWhnfKey, fast, memo, radius]
        · have different : (before.ctxId, query.lbr) ≠ (before.ctxId, source.lbr) := by
            intro same
            exact radius (congrArg Prod.snd same)
          have digest := digest_congr (before := before)
            (after := {before with ctxAddrCache := before.ctxAddrCache.insert (before.ctxId, source.lbr) (TcM.ctxAddrForLbrUncached before source.lbr)}) rfl rfl rfl query.lbr
          by_cases queryFast : (query.lbr == 0 || before.ctx.isEmpty) = true
          all_goals
            cases queryMemo : before.ctxAddrCache[(before.ctxId, query.lbr)]? <;>
              simp [betaWhnfKey, fast, memo, Std.HashMap.getElem?_insert,
                Ne.symm different, queryFast, queryMemo, digest]

theorem betaWhnfKey_prefix (source : KExpr .anon) (before : TcState .anon) :
    (betaWhnfKey source (betaWhnfPrefix before)).1 = (betaWhnfKey source before).1 := by
  unfold betaWhnfPrefix
  split <;> exact betaWhnfKey_congr source rfl rfl rfl rfl

theorem betaWhnfKey_charge (source : KExpr .anon) (before : TcState .anon) :
    (betaWhnfKey source (betaWhnfCharge before)).1 = (betaWhnfKey source before).1 := by
  unfold betaWhnfCharge
  split <;> exact betaWhnfKey_congr source rfl rfl rfl rfl

/-- State shared by surrounding inference is unchanged by these beta paths.
The reduction caches, intern table, key memoization, and WHNF counters
are tracked by the computed result state instead. -/
structure BetaCacheFrame (before after : TcState .anon) : Prop where
  constants : after.env.consts = before.env.consts
  full : after.env.inferCache = before.env.inferCache
  only : after.env.inferOnlyCache = before.env.inferOnlyCache
  context : after.lctx = before.lctx
  policy : after.inferOnly = before.inferOnly
  native : after.inNativeReduce = before.inNativeReduce
  keys (source : KExpr .anon) : (betaWhnfKey source after).1 = (betaWhnfKey source before).1

namespace BetaCacheFrame

theorem refl (before : TcState .anon) : BetaCacheFrame before before :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem trans {before middle after : TcState .anon}
    (first : BetaCacheFrame before middle) (second : BetaCacheFrame middle after) :
    BetaCacheFrame before after :=
  ⟨second.constants.trans first.constants, second.full.trans first.full,
    second.only.trans first.only, second.context.trans first.context,
    second.policy.trans first.policy, second.native.trans first.native,
    fun source => (second.keys source).trans (first.keys source)⟩

theorem key (source : KExpr .anon) (before : TcState .anon) :
    BetaCacheFrame before (betaWhnfKey source before).2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun query => betaWhnfKey_key source query before⟩
  all_goals
    unfold betaWhnfKey
    split
    · rfl
    · dsimp only; split <;> rfl

theorem instrument (before : TcState .anon) : BetaCacheFrame before (betaWhnfPrefix before) := by
  unfold betaWhnfPrefix
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun source => betaWhnfKey_congr source rfl rfl rfl rfl⟩

theorem charge (before : TcState .anon) : BetaCacheFrame before (betaWhnfCharge before) := by
  unfold betaWhnfCharge
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun source => betaWhnfKey_congr source rfl rfl rfl rfl⟩

theorem intern (before : TcState .anon) (table : InternTable .anon) :
    BetaCacheFrame before {before with env := {before.env with intern := table}} :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun source => betaWhnfKey_congr source rfl rfl rfl rfl⟩

theorem core (before : TcState .anon) (key : Address × Address) (result : KExpr .anon) :
    BetaCacheFrame before {before with env := {before.env with
      whnfCoreCache := before.env.whnfCoreCache.insert key result}} :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun source => betaWhnfKey_congr source rfl rfl rfl rfl⟩

theorem cheap (before : TcState .anon) (key : Address × Address) (result : KExpr .anon) :
    BetaCacheFrame before {before with env := {before.env with
      whnfCoreCheapCache := before.env.whnfCoreCheapCache.insert key result}} :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun source => betaWhnfKey_congr source rfl rfl rfl rfl⟩

end BetaCacheFrame

end Ix.Kernel.Consistency
