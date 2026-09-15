/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaHistoryInference
import Ix.Kernel.Verify.Consistency.CacheExecution

/-! WHNF histories survive the non-reducing parts of actual inference and
verified source loading. Exposure readings can use the current annotation
type even when the retained operational trace used a different one. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

theorem LazyLookupFrame.whnf_maps {before after : TcState .anon}
    (frame : LazyLookupFrame before after) (partition : WhnfCachePartition) :
    partition.cache after = partition.cache before := by
  cases partition
  · exact frame.environment.whnfFull
  · exact frame.environment.whnfNoDelta
  · exact frame.environment.whnfNoDeltaCheap
  · exact frame.environment.whnfCore
  · exact frame.environment.whnfCoreCheap

namespace BetaCacheHistory

variable {β : Type u} {before after : TcState .anon}

def afterInferKey {source : KExpr .anon} {key : Address × Address}
    (history : BetaCacheHistory β before)
    (accepted : TcM.inferKey source before = .ok key after) : BetaCacheHistory β after :=
  history.ofMaps (fun partition => by
    cases partition <;> simp only [WhnfCachePartition.cache, inferKey_environment accepted])

/-- Verified standalone and block materialization preserve every map,
including after partial conversion and failed registration. -/
def getConst {id : KId .anon} (history : BetaCacheHistory β before)
    (loader : VerifiedLazySupport before id.addr) :
    match TcM.getConst id before with
    | .ok _ after | .error _ after => BetaCacheHistory β after := by
  have preserved := getConst_verified_cache loader
  cases run : TcM.getConst id before <;> rw [run] at preserved <;>
    exact history.ofMaps preserved.whnf_maps

def hashConversion {left right : KExpr .anon} {methods : Methods .anon}
    (history : BetaCacheHistory β before) (equal : (left.addr == right.addr) = true)
    (accepted : RecM.isDefEq left right methods before = .ok true after) : BetaCacheHistory β after := by
  rw [isDefEq_hash_state equal] at accepted
  split at accepted <;> cases accepted <;>
    exact history.ofMaps (fun partition => by cases partition <;> rfl)

/-- The inference wrapper memoizes a key and publishes only to an inference
cache. Its actual body supplies the history before that final publication. -/
noncomputable def afterMiss {fuel : Nat} {source result : KExpr .anon}
    (history : BetaCacheHistory β before) (miss : UncachedInference before source)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after)
    (body : ∀ middle,
      RecM.inferUncached RecM.inferCall before.inferOnly source (methodsN fuel) miss.keyed = .ok result middle →
      BetaCacheHistory β miss.keyed → BetaCacheHistory β middle) : BetaCacheHistory β after := by
  apply Classical.choice
  obtain ⟨middle, run, written⟩ := infer_uncached_success_state miss accepted
  let reduced := body middle run (history.afterInferKey miss.keyRun)
  refine ⟨reduced.ofMaps ?_⟩
  intro partition
  rw [written]
  split <;> cases partition <;> rfl

end BetaCacheHistory

/-- Raw annotation resources at an actual exposure input. No semantic type
or cache-origin premise is included. -/
structure BetaHistoryReading (β : Type u) (state : TcState .anon) (source : KExpr .anon) where
  resolve : Address → Option (ConstRef β)
  locals : List FVarId
  term : AExpr β
  reading : readScopedExpr? resolve locals source = some term.erase
  coherent : state.env.intern.WF

namespace BetaHistoryReading

variable {β : Type u} {γ : Type v} {before : TcState .anon} {source : KExpr .anon}
  {resolve : Address → Option (ConstRef γ)} {locals : List FVarId} {fuel : Nat}

def afterPublic {term target : AExpr γ} {result : KExpr .anon}
    (data : BetaHistoryReading β before source)
    (execution : BetaPublicExecution resolve locals fuel before source term result target)
    (history : BetaCacheHistory β before) : BetaCacheHistory β execution.after := by
  let rebuilt := execution.reannotate data.reading data.coherent
  exact rebuilt.2.2 ▸ history.afterPublic rebuilt.2.1 data.reading data.coherent

def afterPi {term domain body : AExpr γ} {condition : Certified.PropWhen}
    {rawDomain rawBody : KExpr .anon} (data : BetaHistoryReading β before source)
    (exposure : BetaPiExposure resolve locals fuel before source term condition domain body rawDomain rawBody)
    (history : BetaCacheHistory β before) : BetaCacheHistory β exposure.after := by
  cases exposure with
  | reduce plan =>
      simpa only [BetaPiExposure.after, plan.execution_after] using data.afterPublic plan.execution history
  | execute execution => exact data.afterPublic execution history
  | cached => exact history.instrument.key source

def afterSort {term : AExpr γ} {level : KUniv .anon}
    (data : BetaHistoryReading β before source)
    (exposure : BetaSortExposure resolve locals fuel before source term level)
    (history : BetaCacheHistory β before) : BetaCacheHistory β exposure.after := by
  cases exposure with
  | direct => exact history
  | reduce plan =>
      simpa only [BetaSortExposure.after, plan.execution_after] using data.afterPublic plan.execution history
  | execute execution => exact data.afterPublic execution history
  | cached => exact history.instrument.key source

end BetaHistoryReading

end Ix.Kernel.Consistency
