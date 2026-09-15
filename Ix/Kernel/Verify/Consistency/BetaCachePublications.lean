/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaCacheEvent

/-! Extract every actual WHNF publication, including recursive head calls.
The original reading supplies intern coherence along the same raw path. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}

mutual

def BetaWhnfTrace.cacheEvents {fuel steps : Nat} {flags : WhnfFlags}
    {before after : TcState .anon} {source result : KExpr .anon} {term target : AExpr β}
    (trace : BetaWhnfTrace resolve locals fuel flags steps before source term after result target)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) : List (BetaCacheEvent β) :=
  match trace with
  | .done _ => []
  | .next plan rest =>
      let next := plan.reading coherent
      BetaWhnfTrace.cacheEvents rest next.1 next.2
  | .zeta plan rest =>
      let next := plan.reading reading coherent
      BetaWhnfTrace.cacheEvents rest next.1 next.2
  | .head plan call rest =>
      let next := plan.reading (call.reading plan.sourceHeadReads coherent).2
      BetaHeadReduction.cacheEvents call plan.sourceHeadReads coherent (.lam _ _ _ _ _) ++
        BetaWhnfTrace.cacheEvents rest next.1 next.2
termination_by structural trace

def BetaHeadReduction.cacheEvents {fuel : Nat} {flags : WhnfFlags}
    {before after : TcState .anon} {source result : KExpr .anon} {term target : AExpr β}
    (call : BetaHeadReduction resolve locals fuel flags before source term after result target)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) (terminal : BetaWhnfTerminal result) : List (BetaCacheEvent β) :=
  match call with
  | .reduce path moving enough miss =>
      BetaWhnfTrace.cacheEvents path reading ((betaWhnfKey_environment _ _).symm ▸ coherent) ++
        [.head (.reduce path moving enough miss) coherent terminal]
  | .cached .. => []
termination_by structural call

end

mutual

theorem BetaWhnfTrace.cache_maps {fuel steps : Nat} {flags : WhnfFlags}
    {before after : TcState .anon} {source result : KExpr .anon} {term target : AExpr β}
    (trace : BetaWhnfTrace resolve locals fuel flags steps before source term after result target)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) (partition : WhnfCachePartition) :
    partition.cache after = BetaCacheEvent.apply (trace.cacheEvents reading coherent) partition (partition.cache before) :=
  match trace with
  | .done _ => rfl
  | .next plan rest => by
      have next := plan.reading coherent
      simpa only [BetaWhnfTrace.cacheEvents, BetaStepPlan.after, WhnfCachePartition.intern] using
        BetaWhnfTrace.cache_maps rest next.1 next.2 partition
  | .zeta plan rest => by
      have next := plan.reading reading coherent
      simpa only [BetaWhnfTrace.cacheEvents, LetStepPlan.after, WhnfCachePartition.intern] using
        BetaWhnfTrace.cache_maps rest next.1 next.2 partition
  | .head plan call rest => by
      have next := plan.reading (call.reading plan.sourceHeadReads coherent).2
      rw [BetaWhnfTrace.cacheEvents, BetaCacheEvent.apply_append,
        BetaWhnfTrace.cache_maps rest next.1 next.2 partition]
      have unchanged : partition.cache plan.after = partition.cache _ := partition.intern _ _
      rw [unchanged, BetaHeadReduction.cache_maps call plan.sourceHeadReads coherent (.lam _ _ _ _ _) partition]
termination_by structural trace

theorem BetaHeadReduction.cache_maps {fuel : Nat} {flags : WhnfFlags}
    {before after : TcState .anon} {source result : KExpr .anon} {term target : AExpr β}
    (call : BetaHeadReduction resolve locals fuel flags before source term after result target)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) (terminal : BetaWhnfTerminal result) (partition : WhnfCachePartition) :
    partition.cache after = BetaCacheEvent.apply (call.cacheEvents reading coherent terminal) partition (partition.cache before) :=
  match call with
  | .reduce path moving enough miss => by
      rw [BetaHeadReduction.cacheEvents, BetaCacheEvent.apply_append, partition.writeCore,
        BetaWhnfTrace.cache_maps path reading ((betaWhnfKey_environment _ _).symm ▸ coherent) partition,
        partition.key]
      rfl
  | .cached .. => partition.key _ _
termination_by structural call

end

def BetaCoreExecution.cacheEvents {fuel : Nat} {before : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr β}
    (execution : BetaCoreExecution resolve locals fuel before source term result target)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) : List (BetaCacheEvent β) :=
  execution.headReduction.cacheEvents reading coherent execution.terminal

theorem BetaCoreExecution.cache_maps {fuel : Nat} {before : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr β}
    (execution : BetaCoreExecution resolve locals fuel before source term result target)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) (partition : WhnfCachePartition) :
    partition.cache execution.after = BetaCacheEvent.apply (execution.cacheEvents reading coherent) partition (partition.cache before) :=
  execution.headReduction.cache_maps reading coherent execution.terminal partition

def BetaNoDeltaExecution.cacheEvents {fuel : Nat} {before : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr β}
    (execution : BetaNoDeltaExecution resolve locals fuel before source term result target)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) : List (BetaCacheEvent β) :=
  match execution with
  | .reduce core miss =>
      core.cacheEvents reading ((betaWhnfKey_environment _ _).symm ▸ coherent) ++
        if inactive : before.inNativeReduce = false then [.noDelta (.reduce core miss) coherent inactive] else []
  | .cached .. => []

theorem BetaNoDeltaExecution.cache_maps {fuel : Nat} {before : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr β}
    (execution : BetaNoDeltaExecution resolve locals fuel before source term result target)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) (partition : WhnfCachePartition) :
    partition.cache execution.after = BetaCacheEvent.apply (execution.cacheEvents reading coherent) partition (partition.cache before) := by
  cases execution with
  | reduce core miss =>
      have native := core.frame.native.trans (betaWhnfKey_native source before)
      rw [after, partition.writeNoDelta, native, cacheEvents, BetaCacheEvent.apply_append]
      rw [core.cache_maps reading ((betaWhnfKey_environment _ _).symm ▸ coherent) partition, partition.key]
      by_cases inactive : before.inNativeReduce = false
      · rw [dif_pos inactive]
        simp only [BetaCacheEvent.apply, List.foldl_cons, List.foldl_nil, BetaCacheEvent.step,
          BetaCacheEvent.noDelta, inactive, Bool.false_eq_true, if_false]
      · rw [dif_neg inactive]
        have active : before.inNativeReduce = true := by
          cases value : before.inNativeReduce <;> simp_all
        simp only [active, if_true, BetaCacheEvent.apply_nil]
  | cached => exact partition.key _ _

def BetaPublicExecution.cacheEvents {fuel : Nat} {before : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr β}
    (execution : BetaPublicExecution resolve locals fuel before source term result target)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) : List (BetaCacheEvent β) :=
  match execution with
  | .reduce inner miss enough =>
      have initial : (betaWhnfCharge (BetaPublicWhnf.outerKey source before).2).env.intern.WF := by
        simpa only [BetaPublicWhnf.outerKey, betaWhnfCharge_fields, betaWhnfKey_environment,
          betaWhnfPrefix_fields] using coherent
      inner.cacheEvents reading initial ++
        if inactive : before.inNativeReduce = false then [.full (.reduce inner miss enough) coherent inactive] else []
  | .cached .. => []

theorem BetaPublicExecution.cache_maps {fuel : Nat} {before : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr β}
    (execution : BetaPublicExecution resolve locals fuel before source term result target)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) (partition : WhnfCachePartition) :
    partition.cache execution.after = BetaCacheEvent.apply (execution.cacheEvents reading coherent) partition (partition.cache before) := by
  cases execution with
  | reduce inner miss enough =>
      have initial : (betaWhnfCharge (BetaPublicWhnf.outerKey source before).2).env.intern.WF := by
        simpa only [BetaPublicWhnf.outerKey, betaWhnfCharge_fields, betaWhnfKey_environment,
          betaWhnfPrefix_fields] using coherent
      have native : inner.after.inNativeReduce = before.inNativeReduce := by
        rw [inner.frame.native]
        simp only [BetaPublicWhnf.outerKey, betaWhnfCharge_fields, betaWhnfKey_native, betaWhnfPrefix_fields]
      rw [after, partition.writeFull, native, cacheEvents, BetaCacheEvent.apply_append,
        inner.cache_maps reading initial partition, partition.charge]
      simp only [BetaPublicWhnf.outerKey, partition.key, partition.instrument]
      by_cases inactive : before.inNativeReduce = false
      · rw [dif_pos inactive]
        simp only [BetaCacheEvent.apply, List.foldl_cons, List.foldl_nil, BetaCacheEvent.step,
          BetaCacheEvent.full, inactive, Bool.false_eq_true, if_false, BetaPublicWhnf.outerKey]
      · rw [dif_neg inactive]
        have active : before.inNativeReduce = true := by
          cases value : before.inNativeReduce <;> simp_all
        simp only [active, if_true, BetaCacheEvent.apply_nil]
  | cached =>
      simp only [after, cacheEvents, BetaCacheEvent.apply_nil, BetaPublicWhnf.outerKey,
        partition.key, partition.instrument]

end Ix.Kernel.Consistency
