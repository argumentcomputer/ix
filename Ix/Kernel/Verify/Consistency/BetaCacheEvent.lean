/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaCacheExecution
import Ix.Kernel.Verify.Consistency.BetaHeadOrigin

/-! Publications retain raw producing calls independently of later source
annotations. Folding their events describes all five complete WHNF maps. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

inductive WhnfCachePartition where
  | full | noDelta | noDeltaCheap | core | coreCheap
  deriving DecidableEq

namespace WhnfCachePartition

abbrev CacheMap := Std.HashMap (Address × Address) (KExpr .anon)

def ofFlags (flags : WhnfFlags) : WhnfCachePartition :=
  if flags.isFull then .core else .coreCheap

def cache (partition : WhnfCachePartition) (state : TcState .anon) : CacheMap :=
  match partition with
  | .full => state.env.whnfCache
  | .noDelta => state.env.whnfNoDeltaCache
  | .noDeltaCheap => state.env.whnfNoDeltaCheapCache
  | .core => state.env.whnfCoreCache
  | .coreCheap => state.env.whnfCoreCheapCache

theorem key (partition : WhnfCachePartition) (source : KExpr .anon) (state : TcState .anon) :
    partition.cache (betaWhnfKey source state).2 = partition.cache state := by
  cases partition <;> simp only [cache, betaWhnfKey_environment]

theorem intern (partition : WhnfCachePartition) (state : TcState .anon) (table : InternTable .anon) :
    partition.cache {state with env := {state.env with intern := table}} = partition.cache state := by
  cases partition <;> rfl

theorem instrument (partition : WhnfCachePartition) (state : TcState .anon) :
    partition.cache (betaWhnfPrefix state) = partition.cache state := by
  unfold betaWhnfPrefix
  split <;> cases partition <;> rfl

theorem charge (partition : WhnfCachePartition) (state : TcState .anon) :
    partition.cache (betaWhnfCharge state) = partition.cache state := by
  unfold betaWhnfCharge
  split <;> cases partition <;> rfl

theorem writeCore (partition : WhnfCachePartition) (flags : WhnfFlags)
    (key : Address × Address) (result : KExpr .anon) (state : TcState .anon) :
    partition.cache (BetaCoreCache.write flags key result state) =
      if ofFlags flags = partition then (partition.cache state).insert key result else partition.cache state := by
  cases full : flags.isFull <;> cases partition <;>
    simp only [BetaCoreCache.write, full, ofFlags, cache, Bool.false_eq_true, if_false, if_true,
      reduceCtorEq]

theorem writeNoDelta (partition : WhnfCachePartition)
    (key : Address × Address) (result : KExpr .anon) (state : TcState .anon) :
    partition.cache (BetaCacheExecution.writeNoDelta key result state) =
      if state.inNativeReduce then partition.cache state else
        if .noDelta = partition then (partition.cache state).insert key result else partition.cache state := by
  unfold BetaCacheExecution.writeNoDelta
  split <;> cases partition <;> simp only [cache, reduceCtorEq, if_false, if_true]

theorem writeFull (partition : WhnfCachePartition)
    (key : Address × Address) (result : KExpr .anon) (state : TcState .anon) :
    partition.cache (BetaCacheExecution.writeFull key result state) =
      if state.inNativeReduce then partition.cache state else
        if .full = partition then (partition.cache state).insert key result else partition.cache state := by
  unfold BetaCacheExecution.writeFull
  split <;> cases partition <;> simp only [cache, reduceCtorEq, if_false, if_true]

theorem lookupCore (flags : WhnfFlags) (key : Address × Address) (state : TcState .anon) :
    BetaCoreCache.lookup flags key state = ((ofFlags flags).cache state)[key]? := by
  cases full : flags.isFull <;> simp only [BetaCoreCache.lookup, ofFlags, cache, full, Bool.false_eq_true, if_false, if_true]

end WhnfCachePartition

/-- Public structural calls and recursive head calls share the same cache.
Their retained executions therefore provide interchangeable raw origins. -/
def BetaCoreExecution.headReduction {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr β}
    (execution : BetaCoreExecution resolve locals fuel before source term result target) :
    BetaHeadReduction resolve locals (fuel + 1) .FULL before source term execution.after result target :=
  match execution with
  | .reduce path moving enough miss _ => .reduce path moving enough miss
  | .cached origin coherent hit => .cached origin.headReduction coherent hit
  | .cachedHead origin coherent _ hit => .cached origin coherent hit
termination_by structural execution

/-- Raw provenance of a stored result. The source and result annotations
belong to the producing check; no current semantic typing is assumed. -/
inductive BetaCacheEventOrigin {β : Type u} :
    WhnfCachePartition → (Address × Address) → KExpr .anon → KExpr .anon → Type u
  | head {resolve locals fuel flags before after source result term target}
      (call : BetaHeadReduction (β := β) resolve locals fuel flags before source term after result target)
      (coherent : before.env.intern.WF) (terminal : BetaWhnfTerminal result) :
      BetaCacheEventOrigin (WhnfCachePartition.ofFlags flags) (betaWhnfKey source before).1 source result
  | noDelta {resolve locals fuel before source result term target}
      (execution : BetaNoDeltaExecution (β := β) resolve locals fuel before source term result target)
      (coherent : before.env.intern.WF) (inactive : before.inNativeReduce = false) :
      BetaCacheEventOrigin .noDelta (betaWhnfKey source before).1 source result
  | full {resolve locals fuel before source result term target}
      (execution : BetaPublicExecution (β := β) resolve locals fuel before source term result target)
      (coherent : before.env.intern.WF) (inactive : before.inNativeReduce = false) :
      BetaCacheEventOrigin .full (BetaPublicWhnf.outerKey source before).1 source result

theorem BetaCacheEventOrigin.address {β : Type u} {partition : WhnfCachePartition}
    {key : Address × Address} {source result : KExpr .anon}
    (origin : BetaCacheEventOrigin (β := β) partition key source result) : key.1 = source.addr := by
  cases origin with
  | head | noDelta => exact betaWhnfKey_address _ _
  | full => exact betaWhnfKey_address _ _

structure BetaCacheEvent (β : Type u) where
  partition : WhnfCachePartition
  key : Address × Address
  source : KExpr .anon
  result : KExpr .anon
  origin : BetaCacheEventOrigin (β := β) partition key source result

namespace BetaCacheEvent

variable {β : Type u}

def head {resolve locals fuel flags before after source result term target}
    (call : BetaHeadReduction (β := β) resolve locals fuel flags before source term after result target)
    (coherent : before.env.intern.WF) (terminal : BetaWhnfTerminal result) : BetaCacheEvent β :=
  ⟨_, _, source, result, .head call coherent terminal⟩

def noDelta {resolve locals fuel before source result term target}
    (execution : BetaNoDeltaExecution (β := β) resolve locals fuel before source term result target)
    (coherent : before.env.intern.WF) (inactive : before.inNativeReduce = false) : BetaCacheEvent β :=
  ⟨_, _, source, result, .noDelta execution coherent inactive⟩

def full {resolve locals fuel before source result term target}
    (execution : BetaPublicExecution (β := β) resolve locals fuel before source term result target)
    (coherent : before.env.intern.WF) (inactive : before.inNativeReduce = false) : BetaCacheEvent β :=
  ⟨_, _, source, result, .full execution coherent inactive⟩

def step (event : BetaCacheEvent β) (partition : WhnfCachePartition)
    (cache : WhnfCachePartition.CacheMap) : WhnfCachePartition.CacheMap :=
  if event.partition = partition then cache.insert event.key event.result else cache

def apply (events : List (BetaCacheEvent β)) (partition : WhnfCachePartition)
    (cache : WhnfCachePartition.CacheMap) : WhnfCachePartition.CacheMap :=
  events.foldl (fun cache event => event.step partition cache) cache

@[simp] theorem apply_nil (partition : WhnfCachePartition) (cache : WhnfCachePartition.CacheMap) :
    apply ([] : List (BetaCacheEvent β)) partition cache = cache := rfl

theorem apply_append (first second : List (BetaCacheEvent β)) (partition : WhnfCachePartition)
    (cache : WhnfCachePartition.CacheMap) :
    apply (first ++ second) partition cache = apply second partition (apply first partition cache) :=
  List.foldl_append

/-- Repeated writes and unrelated keys are retained. A selected value was
already present or has a producing call in this finite event list. -/
theorem apply_origin (events : List (BetaCacheEvent β)) (partition : WhnfCachePartition)
    (cache : WhnfCachePartition.CacheMap) {key : Address × Address} {result : KExpr .anon}
    (stored : (apply events partition cache)[key]? = some result) :
    cache[key]? = some result ∨ ∃ event ∈ events,
      event.partition = partition ∧ event.key = key ∧ event.result = result := by
  induction events generalizing cache with
  | nil => exact .inl stored
  | cons event events ih =>
      rcases ih (event.step partition cache) stored with old | ⟨written, member, part, same, value⟩
      · unfold step at old
        split at old
        · rename_i part
          by_cases same : event.key = key
          · rw [same, Std.HashMap.getElem?_insert_self] at old
            exact .inr ⟨event, .head _, part, same, Option.some.inj old⟩
          · exact .inl (by simpa [Std.HashMap.getElem?_insert, same] using old)
        · exact .inl old
      · exact .inr ⟨written, .tail _ member, part, same, value⟩

end BetaCacheEvent

end Ix.Kernel.Consistency
