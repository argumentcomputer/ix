/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaCachePublications
import Ix.Kernel.Verify.Consistency.LetOpening
import Ix.Kernel.Verify.Consistency.InferenceCache

/-! A complete WHNF history begins with empty maps and retains the actual
producers behind every later hit, including entries from exited scopes. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

structure BetaCacheHistory (β : Type u) (state : TcState .anon) where
  events : List (BetaCacheEvent β)
  maps (partition : WhnfCachePartition) : partition.cache state = BetaCacheEvent.apply events partition ∅

namespace BetaCacheHistory

variable {β : Type u} {state : TcState .anon}

def initial (source : Ixon.Env) : BetaCacheHistory β (TcState.newLazyAnon source) :=
  ⟨[], fun partition => by cases partition <;> rfl⟩

def ofMaps (history : BetaCacheHistory β state) {after : TcState .anon}
    (preserved : ∀ partition : WhnfCachePartition, partition.cache after = partition.cache state) :
    BetaCacheHistory β after :=
  ⟨history.events, fun partition => (preserved partition).trans (history.maps partition)⟩

def append (history : BetaCacheHistory β state) {after : TcState .anon} (events : List (BetaCacheEvent β))
    (effects : ∀ partition : WhnfCachePartition,
      partition.cache after = BetaCacheEvent.apply events partition (partition.cache state)) :
    BetaCacheHistory β after :=
  ⟨history.events ++ events, fun partition => by
    rw [BetaCacheEvent.apply_append, effects partition, history.maps partition]⟩

def intern (history : BetaCacheHistory β state) (table : InternTable .anon) :
    BetaCacheHistory β {state with env := {state.env with intern := table}} :=
  history.ofMaps (fun partition => partition.intern _ _)

def key (history : BetaCacheHistory β state) (source : KExpr .anon) :
    BetaCacheHistory β (betaWhnfKey source state).2 := history.ofMaps (fun partition => partition.key _ _)

def instrument (history : BetaCacheHistory β state) : BetaCacheHistory β (betaWhnfPrefix state) :=
  history.ofMaps (fun partition => partition.instrument _)

def charge (history : BetaCacheHistory β state) : BetaCacheHistory β (betaWhnfCharge state) :=
  history.ofMaps (fun partition => partition.charge _)

def policy (history : BetaCacheHistory β state) (policy : Bool) :
    BetaCacheHistory β {state with inferOnly := policy} :=
  history.ofMaps (fun partition => by cases partition <;> rfl)

def truncate (history : BetaCacheHistory β state) (size : Nat) :
    BetaCacheHistory β {state with lctx := state.lctx.truncate size} :=
  history.ofMaps (fun partition => by cases partition <;> rfl)

def openBinder {after : TcState .anon} {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body opened : KExpr .anon} {fresh : FVarId} (history : BetaCacheHistory β state)
    (accepted : TcM.openBinder name bi domain body state = .ok (opened, fresh) after) :
    BetaCacheHistory β after := by
  rw [openBinder_eq] at accepted
  split at accepted
  · cases accepted
    exact history.ofMaps (fun partition => by cases partition <;> rfl)
  · contradiction

def openLet {after : TcState .anon} {name : Mode.anon.F Name}
    {domain value body opened : KExpr .anon} {fresh : FVarId} (history : BetaCacheHistory β state)
    (accepted : TcM.openLet name domain value body state = .ok (opened, fresh) after) :
    BetaCacheHistory β after := by
  rw [openLet_eq] at accepted
  split at accepted
  · cases accepted
    exact history.ofMaps (fun partition => by cases partition <;> rfl)
  · contradiction

def withLctxScope {α : Type} (action : RecM .anon α) (methods : Methods .anon)
    (preserved : match action.run methods state with
      | .ok _ after | .error _ after => BetaCacheHistory β after) :
    match (RecM.withLctxScope action).run methods state with
    | .ok _ after | .error _ after => BetaCacheHistory β after := by
  rw [withLctxScope_eq]
  cases run : action.run methods state <;> rw [run] at preserved <;>
    exact preserved.truncate state.lctx.size

def clear (_history : BetaCacheHistory β state) :
    BetaCacheHistory β {state with env := state.env.clearReductionCaches} :=
  ⟨[], fun partition => by cases partition <;> rfl⟩

def afterTrace {resolve locals fuel flags steps source result term target after}
    (history : BetaCacheHistory β state)
    (trace : BetaWhnfTrace (β := β) resolve locals fuel flags steps state source term after result target)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : state.env.intern.WF) : BetaCacheHistory β after :=
  history.append (trace.cacheEvents reading coherent) (trace.cache_maps reading coherent)

def afterHead {resolve locals fuel flags source result term target after}
    (history : BetaCacheHistory β state)
    (call : BetaHeadReduction (β := β) resolve locals fuel flags state source term after result target)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : state.env.intern.WF) (terminal : BetaWhnfTerminal result) : BetaCacheHistory β after :=
  history.append (call.cacheEvents reading coherent terminal) (call.cache_maps reading coherent terminal)

def afterCore {resolve locals fuel source result term target}
    (history : BetaCacheHistory β state)
    (execution : BetaCoreExecution (β := β) resolve locals fuel state source term result target)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : state.env.intern.WF) : BetaCacheHistory β execution.after :=
  history.append (execution.cacheEvents reading coherent) (execution.cache_maps reading coherent)

def afterNoDelta {resolve locals fuel source result term target}
    (history : BetaCacheHistory β state)
    (execution : BetaNoDeltaExecution (β := β) resolve locals fuel state source term result target)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : state.env.intern.WF) : BetaCacheHistory β execution.after :=
  history.append (execution.cacheEvents reading coherent) (execution.cache_maps reading coherent)

def afterPublic {resolve locals fuel source result term target}
    (history : BetaCacheHistory β state)
    (execution : BetaPublicExecution (β := β) resolve locals fuel state source term result target)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : state.env.intern.WF) : BetaCacheHistory β execution.after :=
  history.append (execution.cacheEvents reading coherent) (execution.cache_maps reading coherent)

theorem origin (history : BetaCacheHistory β state) {partition : WhnfCachePartition}
    {key : Address × Address} {result : KExpr .anon}
    (stored : (partition.cache state)[key]? = some result) :
    ∃ event ∈ history.events, event.partition = partition ∧ event.key = key ∧ event.result = result := by
  rw [history.maps partition] at stored
  rcases BetaCacheEvent.apply_origin history.events partition ∅ stored with empty | produced
  · simp at empty
  · exact produced

/-- Only the current query and finitely many actual publication inputs
need collision freedom. Scope annotations are recovered separately. -/
def KeyData (history : BetaCacheHistory β state) (source : KExpr .anon) : Prop :=
  KExpr.CollisionFree fun candidate => candidate = source ∨
    ∃ event ∈ history.events, candidate = event.source

theorem KeyData.same {history : BetaCacheHistory β state} {source : KExpr .anon}
    (data : history.KeyData source) {event : BetaCacheEvent β} (member : event ∈ history.events)
    {key : Address × Address} (address : key.1 = source.addr) (same : event.key = key) :
    event.source = source := by
  have equal : event.source.addr = source.addr :=
    event.origin.address.symm.trans ((congrArg Prod.fst same).trans address)
  simpa only [KExpr.eraseMeta_anon] using data (Or.inr ⟨event, member, rfl⟩) (Or.inl rfl) equal

theorem selected_origin (history : BetaCacheHistory β state) {source : KExpr .anon}
    (data : history.KeyData source) {partition : WhnfCachePartition} {key : Address × Address}
    {result : KExpr .anon} (address : key.1 = source.addr)
    (stored : (partition.cache state)[key]? = some result) :
    ∃ event ∈ history.events,
      event.partition = partition ∧ event.key = key ∧ event.source = source ∧ event.result = result := by
  obtain ⟨event, member, partition, same, result⟩ := history.origin stored
  exact ⟨event, member, partition, same, data.same member address same, result⟩

theorem selected (history : BetaCacheHistory β state) {source : KExpr .anon}
    (data : history.KeyData source) {partition : WhnfCachePartition} {key : Address × Address}
    {result : KExpr .anon} (address : key.1 = source.addr)
    (stored : (partition.cache state)[key]? = some result) :
    Nonempty (BetaCacheEventOrigin (β := β) partition key source result) := by
  obtain ⟨event, _, part, same, sourceEq, resultEq⟩ := history.selected_origin data address stored
  rw [← part, ← same, ← sourceEq, ← resultEq]
  exact ⟨event.origin⟩

end BetaCacheHistory

/-- Exhausting the outer loop retains exactly the completed prefix's
publications, including whole successful head callbacks. The same history
also covers successful execution when the loop budget is sufficient. -/
def BetaWhnfTrace.boundedCacheHistory {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel steps : Nat} {flags : WhnfFlags}
    {before after : TcState .anon} {source result : KExpr .anon} {term target : AExpr β}
    (trace : BetaWhnfTrace resolve locals fuel flags steps before source term after result target)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) (history : BetaCacheHistory β before) (loopFuel : Nat) :
    match (RecM.runBounded (fun current => RecM.whnfCoreWithFlagsStep current flags) loopFuel source).run
        (methodsN fuel) before with
    | .ok _ final | .error _ final => BetaCacheHistory β final := by
  cases loopFuel with
  | zero => exact history
  | succ remaining =>
      match trace with
      | .done finished =>
          rw [RecM.runBounded, ReaderT.run_bind]
          change match EStateM.bind (β := KExpr .anon) ((RecM.whnfCoreWithFlagsStep source flags).run _) _ before with
            | .ok _ final | .error _ final => BetaCacheHistory β final
          rw [EStateM.bind, finished]
          exact history
      | .next plan rest =>
          have next := plan.reading coherent
          rw [RecM.runBounded, ReaderT.run_bind]
          change match EStateM.bind (β := KExpr .anon) ((RecM.whnfCoreWithFlagsStep source flags).run _) _ before with
            | .ok _ final | .error _ final => BetaCacheHistory β final
          rw [EStateM.bind, plan.run _ flags]
          exact rest.boundedCacheHistory next.1 next.2 (history.intern _) remaining
      | .zeta plan rest =>
          have next := plan.reading reading coherent
          rw [RecM.runBounded, ReaderT.run_bind]
          change match EStateM.bind (β := KExpr .anon) ((RecM.whnfCoreWithFlagsStep source flags).run _) _ before with
            | .ok _ final | .error _ final => BetaCacheHistory β final
          rw [EStateM.bind, plan.run _ flags]
          exact rest.boundedCacheHistory next.1 next.2 (history.intern _) remaining
      | .head plan call rest =>
          have next := plan.reading (call.reading plan.sourceHeadReads coherent).2
          rw [RecM.runBounded, ReaderT.run_bind]
          change match EStateM.bind (β := KExpr .anon) ((RecM.whnfCoreWithFlagsStep source flags).run _) _ before with
            | .ok _ final | .error _ final => BetaCacheHistory β final
          rw [EStateM.bind, plan.run call.run]
          exact rest.boundedCacheHistory next.1 next.2
            ((history.afterHead call plan.sourceHeadReads coherent (.lam _ _ _ _ _)).intern _) remaining
termination_by structural trace

end Ix.Kernel.Consistency
