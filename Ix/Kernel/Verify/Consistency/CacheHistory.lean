/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.CacheExecution
import Ix.Kernel.Verify.Consistency.SourceCache

/-! Histories of both complete inference caches, beginning with empty maps.
Every present value has an actual successful miss in the recorded execution.
The history retains original call states when local scopes or policy change. -/

namespace Ix.Kernel.Consistency

universe u

structure InferenceCacheHistory (state : TcState .anon) where
  events : List InferenceCacheEvent
  full : state.env.inferCache = InferenceCacheEvent.applyFull events ∅
  only : state.env.inferOnlyCache = InferenceCacheEvent.applyOnly events ∅

namespace InferenceCacheHistory

def initial (source : Ixon.Env) : InferenceCacheHistory (TcState.newLazyAnon source) :=
  ⟨[], rfl, rfl⟩

def ofMaps {before after : TcState .anon} (history : InferenceCacheHistory before)
    (full : after.env.inferCache = before.env.inferCache)
    (only : after.env.inferOnlyCache = before.env.inferOnlyCache) : InferenceCacheHistory after :=
  ⟨history.events, full.trans history.full, only.trans history.only⟩

/-- The exact recursive execution appends its actual publications. -/
def afterInference {fuel : Nat} {before after : TcState .anon} {source result : KExpr .anon}
    (history : InferenceCacheHistory before) (tree : InferenceCacheTrace.{u} fuel before source)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) : InferenceCacheHistory after :=
  ⟨history.events ++ tree.events accepted,
    by rw [InferenceCacheEvent.applyFull_append, (tree.cache_maps accepted).1, history.full],
    by rw [InferenceCacheEvent.applyOnly_append, (tree.cache_maps accepted).2, history.only]⟩

def policy {state : TcState .anon} (history : InferenceCacheHistory state) (policy : Bool) :
    InferenceCacheHistory {state with inferOnly := policy} := history.ofMaps rfl rfl

def truncate {state : TcState .anon} (history : InferenceCacheHistory state) (size : Nat) :
    InferenceCacheHistory {state with lctx := state.lctx.truncate size} := history.ofMaps rfl rfl

def afterInferKey {before after : TcState .anon} {source : KExpr .anon} {key : Address × Address}
    (history : InferenceCacheHistory before)
    (accepted : TcM.inferKey source before = .ok key after) : InferenceCacheHistory after :=
  history.ofMaps (congrArg KEnv.inferCache (inferKey_environment accepted))
    (congrArg KEnv.inferOnlyCache (inferKey_environment accepted))

def openBinder {before after : TcState .anon} {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body opened : KExpr .anon} {fresh : FVarId} (history : InferenceCacheHistory before)
    (accepted : TcM.openBinder name bi domain body before = .ok (opened, fresh) after) :
    InferenceCacheHistory after :=
  ⟨history.events,
    by rw [openBinder_eq] at accepted; split at accepted
       · cases accepted; exact history.full
       · contradiction,
    by rw [openBinder_eq] at accepted; split at accepted
       · cases accepted; exact history.only
       · contradiction⟩

def openLet {before after : TcState .anon} {name : Mode.anon.F Name}
    {domain value body opened : KExpr .anon} {fresh : FVarId} (history : InferenceCacheHistory before)
    (accepted : TcM.openLet name domain value body before = .ok (opened, fresh) after) :
    InferenceCacheHistory after :=
  history.ofMaps (openLet_inference_state accepted).1 (openLet_inference_state accepted).2.1

/-- Standalone or block loading retains the history on both outcomes. -/
def getConst {before : TcState .anon} {id : KId .anon} (history : InferenceCacheHistory before)
    (loader : VerifiedLazySupport before id.addr) :
    match TcM.getConst id before with
    | .ok _ after | .error _ after => InferenceCacheHistory after := by
  have preserved := getConst_verified_cache loader
  cases run : TcM.getConst id before <;> rw [run] at preserved <;>
    exact history.ofMaps preserved.environment.full preserved.environment.only

/-- Clearing begins a new cache epoch; discarded entries need no provenance. -/
def clear {state : TcState .anon} (_history : InferenceCacheHistory state) :
    InferenceCacheHistory {state with env := state.env.clearReductionCaches} := ⟨[], rfl, rfl⟩

theorem full_origin {state : TcState .anon} (history : InferenceCacheHistory state)
    {key : Address × Address} {result : KExpr .anon}
    (stored : state.env.inferCache[key]? = some result) :
    ∃ event ∈ history.events,
      event.before.inferOnly = false ∧ event.miss.key = key ∧ event.result = result := by
  rw [history.full] at stored
  rcases InferenceCacheEvent.applyFull_origin history.events ∅ stored with empty | origin
  · simp at empty
  · exact origin

theorem only_origin {state : TcState .anon} (history : InferenceCacheHistory state)
    {key : Address × Address} {result : KExpr .anon}
    (stored : state.env.inferOnlyCache[key]? = some result) :
    ∃ event ∈ history.events,
      event.before.inferOnly = true ∧ event.miss.key = key ∧ event.result = result := by
  rw [history.only] at stored
  rcases InferenceCacheEvent.applyOnly_origin history.events ∅ stored with empty | origin
  · simp at empty
  · exact origin

/-- Collision data concerns just the query and the finite recorded inputs. -/
def KeyData {state : TcState .anon} (history : InferenceCacheHistory state) (source : KExpr .anon) : Prop :=
  KExpr.CollisionFree fun candidate => candidate = source ∨
    ∃ event ∈ history.events, candidate = event.source

theorem KeyData.same {state keyed : TcState .anon} {history : InferenceCacheHistory state}
    {source : KExpr .anon} {key : Address × Address} (data : history.KeyData source)
    {event : InferenceCacheEvent} (member : event ∈ history.events)
    (keyRun : TcM.inferKey source state = .ok key keyed) (same : event.miss.key = key) :
    event.source = source := by
  have address : event.source.addr = source.addr :=
    (inferKey_address event.miss.keyRun).symm.trans
      ((congrArg Prod.fst same).trans (inferKey_address keyRun))
  simpa only [KExpr.eraseMeta_anon] using
    data (Or.inr ⟨event, member, rfl⟩) (Or.inl rfl) address

/-- The selected value comes from an actual inference of the same source.
The old context and policy remain available in the returned event. -/
theorem selected_origin {state : TcState .anon} {source : KExpr .anon}
    (history : InferenceCacheHistory state) (data : history.KeyData source)
    (hit : InferenceCacheHit state source) :
    ∃ event ∈ history.events, event.source = source ∧ event.result = hit.cached := by
  rcases hit.selected with full | ⟨_, _, only⟩
  · rw [inferKey_environment hit.keyRun] at full
    obtain ⟨event, member, _, same, result⟩ := history.full_origin full
    exact ⟨event, member, data.same member hit.keyRun same, result⟩
  · rw [inferKey_environment hit.keyRun] at only
    obtain ⟨event, member, _, same, result⟩ := history.only_origin only
    exact ⟨event, member, data.same member hit.keyRun same, result⟩

end InferenceCacheHistory

end Ix.Kernel.Consistency
