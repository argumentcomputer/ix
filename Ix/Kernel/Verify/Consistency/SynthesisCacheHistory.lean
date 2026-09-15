/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.CacheHistory
import Ix.Kernel.Verify.Consistency.SynthesisCache

/-! Full-cache history retains the original executed synthesis checks.
Annotations are attached to actual publication events; the exact map history
then finds their origins at any selected full-cache key. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- An annotation of an actual earlier call. It retains the complete original
tree and the domain checks that formed its context. Interface growth does not
discard those origins. Cached semantics and result readings are derived. -/
structure SynthesisEventCheck {β : Type u} (resolve : Address → Option (ConstRef β))
    (anchor entries : Model.Environment β) (event : InferenceCacheEvent) where
  earlier : Model.Environment β
  locals : List FVarId
  context : Model.Context β
  bounds : List VLevel
  term : AExpr β
  type : AExpr β
  level : VLevel
  tree : SynthesisInference resolve earlier locals context bounds event.fuel event.before event.source term type level
  contextOrigin : SynthesisContext resolve anchor [] [] earlier context bounds
  extension : InterfaceExtends earlier entries
  agreement : LocalContextReading resolve locals event.before.lctx context
  reading : readScopedExpr? resolve locals event.source = some term.erase

namespace SynthesisEventCheck

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {event : InferenceCacheEvent}

def ofSource {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel}
    {fuel : Nat} {before after : TcState .anon} {source result : KExpr .anon}
    {term type : AExpr β} {level : VLevel}
    (tree : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (contextOrigin : SynthesisContext resolve anchor [] [] entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (miss : UncachedInference before source)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
    SynthesisEventCheck resolve anchor entries (.ofRun miss accepted) :=
  ⟨entries, locals, context, bounds, term, type, level, tree, contextOrigin, .refl _, agreement, reading⟩

def extend (check : SynthesisEventCheck resolve anchor entries event)
    {later : Model.Environment β} (extension : InterfaceExtends entries later) :
    SynthesisEventCheck resolve anchor later event :=
  { check with extension := check.extension.trans extension }

def retained (check : SynthesisEventCheck resolve anchor entries event) :
    SynthesisRetainedCheck resolve anchor [] [] entries check.context check.term check.type check.level :=
  (SynthesisRetainedCheck.source check.contextOrigin check.tree check.agreement check.reading event.accepted).extend
    check.extension

theorem result_reading (check : SynthesisEventCheck resolve anchor entries event) :
    readScopedExpr? resolve check.locals event.result = some check.type.erase :=
  (check.tree.soundWithSpine.{u,u} (check.contextOrigin.sound (.empty _))
    check.agreement check.reading event.accepted).1

/-- Selection supplies the physical slot; the retained original call supplies
all checking evidence and the cached result's reading. -/
def cached (check : SynthesisEventCheck resolve anchor entries event)
    {state : TcState .anon} (closed : event.source.lbr = 0)
    (stored : state.env.inferCache[(event.source.addr, emptyCtxAddr)]? = some event.result) :
    CachedSynthesisCheck resolve anchor entries check.locals check.context state event.source
      check.term check.type check.level :=
  ⟨event.result, closed, check.reading, check.result_reading, check.retained, stored⟩

end SynthesisEventCheck

/-- Only full publications need full checking trees. Inference-only values
still have operational origins in the underlying history. -/
def SynthesisEventChecks {β : Type u} (resolve : Address → Option (ConstRef β))
    (anchor entries : Model.Environment β) (events : List InferenceCacheEvent) : Prop :=
  ∀ event ∈ events, event.before.inferOnly = false → Nonempty (SynthesisEventCheck resolve anchor entries event)

namespace SynthesisEventChecks

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {anchor entries : Model.Environment β}

theorem nil : SynthesisEventChecks resolve anchor entries [] := by intro event member; cases member

theorem append {first second : List InferenceCacheEvent}
    (left : SynthesisEventChecks resolve anchor entries first)
    (right : SynthesisEventChecks resolve anchor entries second) :
    SynthesisEventChecks resolve anchor entries (first ++ second) := by
  intro event member full
  rcases List.mem_append.mp member with old | next
  · exact left event old full
  · exact right event next full

theorem singleton {event : InferenceCacheEvent} (check : SynthesisEventCheck resolve anchor entries event) :
    SynthesisEventChecks resolve anchor entries [event] := by
  intro candidate member full
  have same := List.mem_singleton.mp member
  subst candidate
  exact ⟨check⟩

theorem extend {events : List InferenceCacheEvent} (checks : SynthesisEventChecks resolve anchor entries events)
    {later : Model.Environment β} (extension : InterfaceExtends entries later) :
    SynthesisEventChecks resolve anchor later events := by
  intro event member full
  obtain ⟨check⟩ := checks event member full
  exact ⟨check.extend extension⟩

end SynthesisEventChecks

/-- A complete map history plus the actual original checks behind every full
publication. The original local contexts survive scope exits as provenance. -/
structure SynthesisCacheHistory {β : Type u} (resolve : Address → Option (ConstRef β))
    (anchor entries : Model.Environment β) (state : TcState .anon) where
  execution : InferenceCacheHistory state
  checks : SynthesisEventChecks resolve anchor entries execution.events

/-- A selected full value, with the original context and all retained checks.
The caller can subsequently use the proved interface and local transports. -/
structure SynthesisCacheSelection {β : Type u} (resolve : Address → Option (ConstRef β))
    (anchor entries : Model.Environment β) (state : TcState .anon) (source result : KExpr .anon) where
  locals : List FVarId
  context : Model.Context β
  term : AExpr β
  type : AExpr β
  level : VLevel
  cached : CachedSynthesisCheck resolve anchor entries locals context state source term type level
  result_eq : cached.result = result

namespace SynthesisCacheHistory

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {state : TcState .anon}

def initial (source : Ixon.Env) : SynthesisCacheHistory resolve anchor entries (TcState.newLazyAnon source) :=
  ⟨.initial source, .nil⟩

def ofMaps (history : SynthesisCacheHistory resolve anchor entries state) {after : TcState .anon}
    (full : after.env.inferCache = state.env.inferCache)
    (only : after.env.inferOnlyCache = state.env.inferOnlyCache) :
    SynthesisCacheHistory resolve anchor entries after := ⟨history.execution.ofMaps full only, history.checks⟩

def extend (history : SynthesisCacheHistory resolve anchor entries state)
    {later : Model.Environment β} (extension : InterfaceExtends entries later) :
    SynthesisCacheHistory resolve anchor later state := ⟨history.execution, history.checks.extend extension⟩

def afterInference (history : SynthesisCacheHistory resolve anchor entries state)
    {fuel : Nat} {after : TcState .anon} {source result : KExpr .anon}
    (tree : InferenceCacheTrace.{v} fuel state source)
    (accepted : RecM.infer source (methodsN fuel) state = .ok result after)
    (checks : SynthesisEventChecks resolve anchor entries (tree.events accepted)) :
    SynthesisCacheHistory resolve anchor entries after :=
  ⟨history.execution.afterInference tree accepted, history.checks.append checks⟩

def policy (history : SynthesisCacheHistory resolve anchor entries state) (policy : Bool) :
    SynthesisCacheHistory resolve anchor entries {state with inferOnly := policy} := history.ofMaps rfl rfl

def truncate (history : SynthesisCacheHistory resolve anchor entries state) (size : Nat) :
    SynthesisCacheHistory resolve anchor entries {state with lctx := state.lctx.truncate size} := history.ofMaps rfl rfl

def openBinder (history : SynthesisCacheHistory resolve anchor entries state)
    {after : TcState .anon} {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body opened : KExpr .anon} {fresh : FVarId}
    (accepted : TcM.openBinder name bi domain body state = .ok (opened, fresh) after) :
    SynthesisCacheHistory resolve anchor entries after := ⟨history.execution.openBinder accepted, history.checks⟩

def getConst (history : SynthesisCacheHistory resolve anchor entries state) {id : KId .anon}
    (loader : VerifiedLazySupport state id.addr) :
    match TcM.getConst id state with
    | .ok _ after | .error _ after => SynthesisCacheHistory resolve anchor entries after := by
  have preserved := getConst_verified_cache loader
  cases run : TcM.getConst id state <;> rw [run] at preserved <;>
    exact history.ofMaps preserved.environment.full preserved.environment.only

def clear (_history : SynthesisCacheHistory resolve anchor entries state) :
    SynthesisCacheHistory resolve anchor entries {state with env := state.env.clearReductionCaches} :=
  ⟨_history.execution.clear, .nil⟩

/-- Every selected full entry materializes its original synthesis cache
interface. The source is recovered from the finite collision data; no cached
typing, result reading, earlier run, or catalog membership is supplied. -/
theorem select (history : SynthesisCacheHistory resolve anchor entries state)
    {source result : KExpr .anon} (closed : source.lbr = 0)
    (data : history.execution.KeyData source)
    (stored : state.env.inferCache[(source.addr, emptyCtxAddr)]? = some result) :
    Nonempty (SynthesisCacheSelection resolve anchor entries state source result) := by
  obtain ⟨event, member, full, same, value⟩ := history.execution.full_origin stored
  obtain ⟨check⟩ := history.checks event member full
  have sourceEq := data.same member (inferKey_closed closed state) same
  have entry : state.env.inferCache[(event.source.addr, emptyCtxAddr)]? = some event.result := by
    rwa [sourceEq, value]
  let cached := check.cached (sourceEq.symm ▸ closed) entry
  refine ⟨⟨check.locals, check.context, check.term, check.type, check.level, sourceEq ▸ cached, ?_⟩⟩
  cases sourceEq
  exact value

/-- Observe the actual map. A full hit has a history-derived cache interface
under either checking policy, including when the method table has no fuel. -/
theorem observe (history : SynthesisCacheHistory resolve anchor entries state)
    {source : KExpr .anon} (closed : source.lbr = 0) (data : history.execution.KeyData source) :
    state.env.inferCache[(source.addr, emptyCtxAddr)]? = none ∨
      ∃ result, Nonempty (SynthesisCacheSelection resolve anchor entries state source result) := by
  cases stored : state.env.inferCache[(source.addr, emptyCtxAddr)]? with
  | none => exact .inl rfl
  | some result => exact .inr ⟨result, history.select closed data stored⟩

end SynthesisCacheHistory

end Ix.Kernel.Consistency
