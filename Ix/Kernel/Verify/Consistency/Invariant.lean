/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.IngressState
import Ix.Kernel.Verify.Consistency.RunAssumptions
import Ix.Kernel.Verify.Consistency.SourceCache
import Ix.Kernel.Verify.Consistency.SynthesisCacheHistory
import Ix.Kernel.Verify.Consistency.BetaCacheHistory
import Ix.Kernel.Verify.Consistency.LocalStateReading
import Ix.Kernel.Verify.Consistency.SortCache

/-!
# The checker state invariant

One record bundles the state facts that the refinement currently threads
separately: source ownership, the installed verified loader, block
registration, intern coherence, standalone source agreement, catalog cache
agreement, both inference-cache histories with their retained synthesis
checks, the complete WHNF history, the structural local state, the local
context reading, and the synthesis origin of the current context. Five new
`Prop` fields state semantic agreement of the WHNF partitions, the two DefEq
caches, the equivalence manager, the unfold cache, and the is-prop cache in
terms of `ConversionClaim`/`TypingClaim`; empty maps satisfy them trivially.
The invariant holds at the driver's initial state under `RunAssumptions` and
is preserved by lookup on both outcomes, key computation, binder and let
opening, scope exit, cache clearing, per-item reset, and policy changes.
Sort and free-variable inference are restated as invariant preservation.
Not recorded: let-value substitution agreement and a reading of every loaded
declaration into the interface, which have no definition yet, and policy-flag
consistency. Per-lookup conversion data, cache key collision data, and binder
walker data remain explicit premises, each an instance of `RunAssumptions`.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-! ### Semantic agreement of the reduction caches -/

/-- Every stored WHNF result is convertible to, and retains every type of, a
source expression with the key's address, read in some local context. -/
def WhnfCacheSemantics {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (state : TcState .anon) : Prop :=
  ∀ (partition : WhnfCachePartition) (key : Address × Address) (result : KExpr .anon),
    (partition.cache state)[key]? = some result →
    ∃ (locals : List FVarId) (context : Model.Context β) (source : KExpr .anon)
      (term target : AExpr β),
      source.addr = key.1 ∧
      readScopedExpr? resolve locals source = some term.erase ∧
      readScopedExpr? resolve locals result = some target.erase ∧
      ConversionClaim.{u,v} entries context term target ∧
      ∀ type, TypingClaim.{u,v} entries context term type →
        TypingClaim.{u,v} entries context target type

theorem WhnfCacheSemantics.ofMaps {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {before after : TcState .anon}
    (valid : WhnfCacheSemantics.{u,v} resolve entries before)
    (preserved : ∀ partition : WhnfCachePartition, partition.cache after = partition.cache before) :
    WhnfCacheSemantics.{u,v} resolve entries after := by
  intro partition key result stored
  rw [preserved partition] at stored
  exact valid partition key result stored

theorem WhnfCacheSemantics.ofEmpty {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) {state : TcState .anon}
    (empty : ∀ partition : WhnfCachePartition, partition.cache state = ∅) :
    WhnfCacheSemantics.{u,v} resolve entries state := by
  intro partition key result stored
  rw [empty partition] at stored
  simp at stored

/-- The two definitional-equality caches. -/
inductive DefEqCachePartition where
  | full | cheap
  deriving DecidableEq

def DefEqCachePartition.cache : DefEqCachePartition → TcState .anon →
    Std.HashMap (Address × Address × Address) Bool
  | .full, state => state.env.defEqCache
  | .cheap, state => state.env.defEqCheapCache

/-- Every positive DefEq entry records two expressions with the key's
addresses whose readings are convertible in some local context. Negative
entries carry no claim. -/
def DefEqCacheSemantics {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (state : TcState .anon) : Prop :=
  ∀ (partition : DefEqCachePartition) (key : Address × Address × Address),
    (partition.cache state)[key]? = some true →
    ∃ (locals : List FVarId) (context : Model.Context β) (left right : KExpr .anon)
      (a b : AExpr β),
      left.addr = key.1 ∧ right.addr = key.2.1 ∧
      readScopedExpr? resolve locals left = some a.erase ∧
      readScopedExpr? resolve locals right = some b.erase ∧
      ConversionClaim.{u,v} entries context a b

theorem DefEqCacheSemantics.ofMaps {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {before after : TcState .anon}
    (valid : DefEqCacheSemantics.{u,v} resolve entries before)
    (preserved : ∀ partition : DefEqCachePartition, partition.cache after = partition.cache before) :
    DefEqCacheSemantics.{u,v} resolve entries after := by
  intro partition key stored
  rw [preserved partition] at stored
  exact valid partition key stored

theorem DefEqCacheSemantics.ofEmpty {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) {state : TcState .anon}
    (empty : ∀ partition : DefEqCachePartition, partition.cache state = ∅) :
    DefEqCacheSemantics.{u,v} resolve entries state := by
  intro partition key stored
  rw [empty partition] at stored
  simp at stored

/-- A justified union-find edge joins two keys of the same context scope whose
expressions read to convertible terms in some local context. -/
def EqKeyConversion {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (left right : EqKey) : Prop :=
  left.ctxAddr = right.ctxAddr ∧ left.lbr = right.lbr ∧
  ∃ (locals : List FVarId) (context : Model.Context β) (a b : KExpr .anon) (ta tb : AExpr β),
    a.addr = left.exprAddr ∧ b.addr = right.exprAddr ∧
    a.lbr = left.exprLbr ∧ b.lbr = right.exprLbr ∧
    readScopedExpr? resolve locals a = some ta.erase ∧
    readScopedExpr? resolve locals b = some tb.erase ∧
    ConversionClaim.{u,v} entries context ta tb

/-- Every parent link of the production union-find forest is a justified edge.
This is the `edge` field of the named track's `EquivManager.WF`, restated here
so the library does not import that module. -/
def EquivManagerSemantics {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (manager : EquivManager) : Prop :=
  ∀ node, node < manager.parent.size →
    EqKeyConversion.{u,v} resolve entries manager.nodeToKey[node]! manager.nodeToKey[manager.parent[node]!]!

theorem EquivManagerSemantics.empty {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} : EquivManagerSemantics.{u,v} resolve entries {} :=
  fun _ bound => (Nat.not_lt_zero _ bound).elim

/-- Every unfold entry is the universe instantiation of an admitted body at
the head constant whose address keys it. -/
def UnfoldCacheSemantics {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (state : TcState .anon) : Prop :=
  ∀ (addr : Address) (value : KExpr .anon), state.env.unfoldCache[addr]? = some value →
    ∃ (id : KId .anon) (arguments : Array (KUniv .anon)) (info : ExprInfo .anon)
      (ref : ConstRef β) (entry : ConstantEntry β) (body : AExpr β),
      (KExpr.const id arguments info).addr = addr ∧
      resolve id.addr = some ref ∧ entries ref = some entry ∧ entry.body = some body ∧
      entry.universes = arguments.size ∧
      readExpr? resolve value = some (body.instL (arguments.toList.map readLevel)).erase

theorem UnfoldCacheSemantics.ofMap {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {before after : TcState .anon}
    (valid : UnfoldCacheSemantics resolve entries before)
    (preserved : after.env.unfoldCache = before.env.unfoldCache) :
    UnfoldCacheSemantics resolve entries after := by
  intro addr value stored
  rw [preserved] at stored
  exact valid addr value stored

theorem UnfoldCacheSemantics.ofEmpty {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) {state : TcState .anon} (empty : state.env.unfoldCache = ∅) :
    UnfoldCacheSemantics resolve entries state := by
  intro addr value stored
  rw [empty] at stored
  simp at stored

/-- Every positive is-prop entry records a type with the key's address that
is a proposition in some local context. Negative entries carry no claim. -/
def IsPropCacheSemantics {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (state : TcState .anon) : Prop :=
  ∀ key : Address × Address, state.env.isPropCache[key]? = some true →
    ∃ (locals : List FVarId) (context : Model.Context β) (source : KExpr .anon) (term : AExpr β),
      source.addr = key.1 ∧ readScopedExpr? resolve locals source = some term.erase ∧
      TypingClaim.{u,v} entries context term (.sort .zero)

theorem IsPropCacheSemantics.ofMap {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {before after : TcState .anon}
    (valid : IsPropCacheSemantics.{u,v} resolve entries before)
    (preserved : after.env.isPropCache = before.env.isPropCache) :
    IsPropCacheSemantics.{u,v} resolve entries after := by
  intro key stored
  rw [preserved] at stored
  exact valid key stored

theorem IsPropCacheSemantics.ofEmpty {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) {state : TcState .anon} (empty : state.env.isPropCache = ∅) :
    IsPropCacheSemantics.{u,v} resolve entries state := by
  intro key stored
  rw [empty] at stored
  simp at stored

/-- Semantic agreement of every reduction memo not covered by an execution history. -/
structure ReductionCacheSemantics {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (state : TcState .anon) : Prop where
  whnf : WhnfCacheSemantics.{u,v} resolve entries state
  defEq : DefEqCacheSemantics.{u,v} resolve entries state
  equivalence : EquivManagerSemantics.{u,v} resolve entries state.equivManager
  unfold : UnfoldCacheSemantics resolve entries state
  isProp : IsPropCacheSemantics.{u,v} resolve entries state

namespace ReductionCacheSemantics

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}

theorem ofMapsManager {before after : TcState .anon}
    (valid : ReductionCacheSemantics.{u,v} resolve entries before)
    (whnf : ∀ partition : WhnfCachePartition, partition.cache after = partition.cache before)
    (defEq : ∀ partition : DefEqCachePartition, partition.cache after = partition.cache before)
    (manager : EquivManagerSemantics.{u,v} resolve entries after.equivManager)
    (unfold : after.env.unfoldCache = before.env.unfoldCache)
    (isProp : after.env.isPropCache = before.env.isPropCache) :
    ReductionCacheSemantics.{u,v} resolve entries after :=
  ⟨valid.whnf.ofMaps whnf, valid.defEq.ofMaps defEq, manager, valid.unfold.ofMap unfold,
    valid.isProp.ofMap isProp⟩

theorem ofMaps {before after : TcState .anon}
    (valid : ReductionCacheSemantics.{u,v} resolve entries before)
    (whnf : ∀ partition : WhnfCachePartition, partition.cache after = partition.cache before)
    (defEq : ∀ partition : DefEqCachePartition, partition.cache after = partition.cache before)
    (manager : after.equivManager = before.equivManager)
    (unfold : after.env.unfoldCache = before.env.unfoldCache)
    (isProp : after.env.isPropCache = before.env.isPropCache) :
    ReductionCacheSemantics.{u,v} resolve entries after :=
  valid.ofMapsManager whnf defEq (by rw [manager]; exact valid.equivalence) unfold isProp

/-- Empty memos and any well-formed manager satisfy the agreement. -/
theorem ofEmpty {state : TcState .anon}
    (whnf : ∀ partition : WhnfCachePartition, partition.cache state = ∅)
    (defEq : ∀ partition : DefEqCachePartition, partition.cache state = ∅)
    (manager : EquivManagerSemantics.{u,v} resolve entries state.equivManager)
    (unfold : state.env.unfoldCache = ∅) (isProp : state.env.isPropCache = ∅) :
    ReductionCacheSemantics.{u,v} resolve entries state :=
  ⟨.ofEmpty resolve entries whnf, .ofEmpty resolve entries defEq, manager,
    .ofEmpty resolve entries unfold, .ofEmpty resolve entries isProp⟩

theorem initial (source : Ixon.Env) :
    ReductionCacheSemantics.{u,v} resolve entries (TcState.newLazyAnon source) :=
  ofEmpty (fun partition => by cases partition <;> rfl) (fun partition => by cases partition <;> rfl)
    EquivManagerSemantics.empty rfl rfl

/-- Clearing empties every memo and retains the equivalence manager. -/
theorem clear {state : TcState .anon} (valid : ReductionCacheSemantics.{u,v} resolve entries state) :
    ReductionCacheSemantics.{u,v} resolve entries {state with env := state.env.clearReductionCaches} :=
  ofEmpty (fun partition => by cases partition <;> rfl) (fun partition => by cases partition <;> rfl)
    valid.equivalence rfl rfl

end ReductionCacheSemantics

/-! ### Operational state equations -/

/-- Context-digest computation changes only its memo table. -/
theorem ctxAddrForLbr_state {lbr : UInt64} {before after : TcState .anon} {addr : Address}
    (run : TcM.ctxAddrForLbr lbr before = .ok addr after) :
    after = {before with ctxAddrCache := after.ctxAddrCache} := by
  unfold TcM.ctxAddrForLbr at run
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ before = _ at run
  rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) before = .ok before before from rfl] at run
  dsimp only at run
  by_cases fast : (lbr == 0 || before.ctx.isEmpty) = true
  · rw [if_pos fast] at run
    cases run
    rfl
  · rw [if_neg fast] at run
    cases cached : before.ctxAddrCache[(before.ctxId, lbr)]? <;>
      rw [cached] at run <;> cases run <;> rfl

theorem inferKey_state {term : KExpr .anon} {before after : TcState .anon} {key : Address × Address}
    (run : TcM.inferKey term before = .ok key after) :
    after = {before with ctxAddrCache := after.ctxAddrCache} := by
  unfold TcM.inferKey at run
  change EStateM.bind (TcM.ctxAddrForLbr term.lbr) _ before = _ at run
  rw [EStateM.bind] at run
  cases digest : TcM.ctxAddrForLbr term.lbr before with
  | error err failed => rw [digest] at run; contradiction
  | ok addr keyed =>
      rw [digest] at run
      cases run
      exact ctxAddrForLbr_state digest

theorem whnfKey_state {term : KExpr .anon} {before after : TcState .anon} {key : Address × Address}
    (run : TcM.whnfKey term before = .ok key after) :
    after = {before with ctxAddrCache := after.ctxAddrCache} := by
  unfold TcM.whnfKey at run
  change EStateM.bind (TcM.ctxAddrForLbr term.lbr) _ before = _ at run
  rw [EStateM.bind] at run
  cases digest : TcM.ctxAddrForLbr term.lbr before with
  | error err failed => rw [digest] at run; contradiction
  | ok addr keyed =>
      rw [digest] at run
      cases run
      exact ctxAddrForLbr_state digest

theorem defEqCtxKey_state {left right : KExpr .anon} {before after : TcState .anon} {addr : Address}
    (run : TcM.defEqCtxKey left right before = .ok addr after) :
    after = {before with ctxAddrCache := after.ctxAddrCache} :=
  ctxAddrForLbr_state run

/-- The exact per-item reset. -/
theorem reset_eq (before : TcState .anon) :
    TcM.reset before = .ok () {before with
      ctx := #[], letVals := #[], numLetBindings := 0, ctxId := emptyCtxAddr, ctxIdStack := #[],
      equivManager := {}, inferOnly := false, inNativeReduce := false, cheapRecursionDepth := 0,
      eagerReduce := false, defEqDepth := 0, defEqPeak := 0, dispatchDepth := 0,
      recFuel := before.fuelBudget, ctxAddrCache := {}, lctx := {}} := rfl

private theorem lazyIngressAddr_ingressFrame {before : TcState .anon} {addr : Address}
    (source : Ixon.Env) (verify : Bool)
    (installed : before.lazyFault = some (fun address => ingressAnonAddrShallow source address verify)) :
    match TcM.lazyIngressAddr addr before with
    | .ok _ after | .error _ after => KEnv.IngressFrame before.env after.env := by
  unfold TcM.lazyIngressAddr
  rw [installed]
  dsimp only
  by_cases faulted : before.faultedAddrs.contains addr = true
  · rw [if_pos faulted]
    exact .refl _
  · rw [if_neg faulted]
    have frame := IngressM.FramesState.ingressAnonAddrShallow source addr verify before.env
    cases run : ingressAnonAddrShallow source addr verify before.env <;>
      rw [run] at frame <;> exact frame

private theorem tryGetConst_ingressFrame {before : TcState .anon} {id : KId .anon}
    (source : Ixon.Env) (verify : Bool)
    (installed : before.lazyFault = some (fun address => ingressAnonAddrShallow source address verify)) :
    match TcM.tryGetConst id before with
    | .ok _ after | .error _ after => KEnv.IngressFrame before.env after.env := by
  unfold TcM.tryGetConst
  change (match (EStateM.bind (get : TcM .anon (TcState .anon)) _ :
    TcM .anon (Option (KConst .anon))) before with
    | .ok _ after | .error _ after => KEnv.IngressFrame before.env after.env)
  rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) before = .ok before before from rfl]
  dsimp only
  cases before.env.get? id with
  | some concrete => exact .refl _
  | none =>
      change (match (EStateM.bind (TcM.lazyIngressAddr id.addr) _ :
        TcM .anon (Option (KConst .anon))) before with
        | .ok _ after | .error _ after => KEnv.IngressFrame before.env after.env)
      have preserved := lazyIngressAddr_ingressFrame (addr := id.addr) source verify installed
      cases fault : TcM.lazyIngressAddr id.addr before with
      | error err after =>
          rw [EStateM.bind, fault]
          simpa only [fault] using preserved
      | ok value after =>
          rw [fault] at preserved
          rw [EStateM.bind, fault]
          change (match (EStateM.bind (get : TcM .anon (TcState .anon)) _ :
            TcM .anon (Option (KConst .anon))) after with
            | .ok _ state | .error _ state => KEnv.IngressFrame before.env state.env)
          rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) after = .ok after after from rfl]
          dsimp only
          cases after.env.get? id with
          | some concrete => exact preserved
          | none => cases before.lazyFault.isSome <;> exact preserved

/-- Lookup through the installed production loader changes only the
ingress-owned environment fields on both outcomes. -/
theorem getConst_ingressFrame {before : TcState .anon} {id : KId .anon}
    (source : Ixon.Env) (verify : Bool)
    (installed : before.lazyFault = some (fun address => ingressAnonAddrShallow source address verify)) :
    match TcM.getConst id before with
    | .ok _ after | .error _ after => KEnv.IngressFrame before.env after.env := by
  unfold TcM.getConst
  change (match (EStateM.bind (TcM.tryGetConst id) _ : TcM .anon (KConst .anon)) before with
    | .ok _ after | .error _ after => KEnv.IngressFrame before.env after.env)
  have preserved := tryGetConst_ingressFrame (id := id) source verify installed
  cases tried : TcM.tryGetConst id before with
  | error err after =>
      rw [EStateM.bind, tried]
      simpa only [tried] using preserved
  | ok optional after =>
      rw [tried] at preserved
      rw [EStateM.bind, tried]
      cases optional <;> exact preserved

/-- Let opening retains ownership, block registration, and coherence exactly
as binder opening does; the value is stored, not walked. -/
theorem InferenceStateInvariant.openLet {source : Ixon.Env} {before after : TcState .anon}
    {name : Mode.anon.F Name} {domain value body opened : KExpr .anon} {fresh : FVarId}
    (valid : InferenceStateInvariant source before) (data : BinderOpeningData before body)
    (run : TcM.openLet name domain value body before = .ok (opened, fresh) after) :
    InferenceStateInvariant source after := by
  have nameUnit : name = () := Subsingleton.elim _ _
  subst name
  have interned : (before.env.intern.internExpr
      (KExpr.mkFVar ⟨before.env.nextFVarId⟩ ())).1 =
        KExpr.mkFVar ⟨before.env.nextFVarId⟩ () := by
    have faithful := KExpr.keyCollisionFree_anon.mpr
      (data.faithful.mono (fun _ h => h.elim Or.inl (fun equal => .inr (.inl equal))) :
        KExpr.CollisionFree fun term => before.env.intern.ExprSupport term ∨
          term = KExpr.mkFVar ⟨before.env.nextFVarId⟩ ())
    simpa only [KExpr.eraseMeta_anon] using
      before.env.intern.internExpr_eraseMeta valid.coherent faithful
  have walk := instantiateRev_spec (fvars := #[KExpr.mkFVar ⟨before.env.nextFVarId⟩ ()])
    data.faithful data.constructed (by simpa using data.bound)
    (fun _ reached => .inr (.inr reached))
    (valid.coherent.internExpr (KExpr.mkFVar ⟨before.env.nextFVarId⟩ ()))
    (fun _ member => (InternTable.ExprSupport.of_internExpr member).elim
      Or.inl (fun equal => .inr (.inl equal)))
  rw [openLet_eq] at run
  split at run
  · simp only [interned] at run
    cases run
    exact valid.ofMaps rfl rfl rfl walk.2.1
  · contradiction

/-! ### The invariant -/

/-- The bundled checker state invariant. The parameters fix the run: the
resolver, the anchor and current interfaces, the verified source, the source
cache catalog, and the current local context with its model reading and
synthesis bounds. -/
structure CheckerInvariant {β : Type u} (resolve : Address → Option (ConstRef β))
    (anchor entries : Model.Environment β) (source : Ixon.Env)
    (catalog : List (SourceCacheRequest source)) (locals : List FVarId)
    (context : Model.Context β) (bounds : List VLevel) (state : TcState .anon) : Prop where
  /-- Ownership, installed loader, block registration, intern coherence,
  standalone source agreement, and catalog cache agreement. -/
  sourceCache : SourceCacheInvariant catalog state
  /-- Both inference-cache maps with the retained synthesis checks of every full publication. -/
  synthesis : Nonempty (SynthesisCacheHistory resolve anchor entries state)
  /-- The five WHNF maps with their producing executions. -/
  whnf : Nonempty (BetaCacheHistory β state)
  /-- Coherent local lookup, fresh-id bound, and monotone loader counter. -/
  structural : LocalStateInvariant state
  /-- The active locals read to the model context. -/
  reading : LocalContextReading resolve locals state.lctx context
  /-- The current context was formed from the empty context by checked domains. -/
  origin : Nonempty (SynthesisContext resolve anchor [] [] entries context bounds)
  /-- Semantic agreement of the remaining reduction memos. -/
  semantics : ReductionCacheSemantics.{u,v} resolve entries state

namespace CheckerInvariant

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {locals : List FVarId}
  {context : Model.Context β} {bounds : List VLevel}

section Projections

variable {state : TcState .anon}
  (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state)
include valid

theorem sourceState : SourceStateInvariant source state := valid.sourceCache.state

theorem inference : InferenceStateInvariant source state := valid.sourceCache.state.state

theorem coherent : state.env.intern.WF := valid.inference.coherent

theorem installed :
    state.lazyFault = some (fun addr => ingressAnonAddrShallow source addr true) :=
  valid.inference.installed

theorem blocks : LoadedBlockInvariant source state.env := valid.inference.blocks

theorem ownership : SourceOwnership source := valid.inference.ownership

def owned : OwnedLazySupport state := valid.inference.owned

theorem agreement : StandaloneSourceAgreement source state.env := valid.sourceCache.state.agreement

theorem cache : SourceCacheAgreement catalog state := valid.sourceCache.cache

theorem inferenceHistory : Nonempty (InferenceCacheHistory state) :=
  valid.synthesis.elim fun history => ⟨history.execution⟩

end Projections

/-- The driver's initial checker satisfies the invariant under the run assumptions. -/
theorem initial {cfg : CheckCfg} {domain : RunDomain} (assumptions : RunAssumptions source cfg domain)
    (resolve : Address → Option (ConstRef β)) (anchor entries : Model.Environment β)
    (catalog : List (SourceCacheRequest source)) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog [] [] []
      (TcState.newLazyAnon source cfg.verifyHashes) := by
  rw [assumptions.verify]
  exact {
    sourceCache := .ofCheckedSource source catalog assumptions.checked
    synthesis := ⟨.initial source⟩
    whnf := ⟨.initial source⟩
    structural := LocalStateInvariant.newLazyAnon source true
    reading := .empty resolve _
    origin := ⟨.empty entries⟩
    semantics := .initial source }

theorem initialLoopState {cfg : CheckCfg} {domain : RunDomain}
    (assumptions : RunAssumptions source cfg domain)
    (resolve : Address → Option (ConstRef β)) (anchor entries : Model.Environment β)
    (catalog : List (SourceCacheRequest source)) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog [] [] []
      (initialAnonCheckLoopState source cfg).checker :=
  initial assumptions resolve anchor entries catalog

/-- Operations that retain every map, the loaded declarations, coherence, and
the local context up to lookup equivalence preserve the invariant. -/
theorem ofMaps {before after : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (frame : LocalStateFrame before after)
    (constants : after.env.consts = before.env.consts)
    (blocks : after.env.blocks = before.env.blocks)
    (coherent : after.env.intern.WF)
    (full : after.env.inferCache = before.env.inferCache)
    (only : after.env.inferOnlyCache = before.env.inferOnlyCache)
    (whnf : ∀ partition : WhnfCachePartition, partition.cache after = partition.cache before)
    (defEq : ∀ partition : DefEqCachePartition, partition.cache after = partition.cache before)
    (manager : after.equivManager = before.equivManager)
    (unfold : after.env.unfoldCache = before.env.unfoldCache)
    (isProp : after.env.isPropCache = before.env.isPropCache) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after where
  sourceCache := ⟨valid.sourceState.ofMaps frame.loader constants blocks coherent,
    valid.cache.ofMaps full only constants⟩
  synthesis := valid.synthesis.elim fun history => ⟨history.ofMaps full only⟩
  whnf := valid.whnf.elim fun history => ⟨history.ofMaps whnf⟩
  structural := frame.invariant valid.structural
  reading := valid.reading.congr frame.context.symm
  origin := valid.origin
  semantics := valid.semantics.ofMaps whnf defEq manager unfold isProp

theorem ofCtxAddrCache {before : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (memo : Std.HashMap (Address × UInt64) Address) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      {before with ctxAddrCache := memo} :=
  valid.ofMaps ⟨Nat.le_refl _, .refl _, rfl⟩ rfl rfl valid.coherent rfl rfl
    (fun partition => by cases partition <;> rfl) (fun partition => by cases partition <;> rfl)
    rfl rfl rfl

theorem inferKey {before after : TcState .anon} {term : KExpr .anon} {key : Address × Address}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (run : TcM.inferKey term before = .ok key after) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after := by
  rw [inferKey_state run]
  exact valid.ofCtxAddrCache _

theorem whnfKey {before after : TcState .anon} {term : KExpr .anon} {key : Address × Address}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (run : TcM.whnfKey term before = .ok key after) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after := by
  rw [whnfKey_state run]
  exact valid.ofCtxAddrCache _

theorem defEqCtxKey {before after : TcState .anon} {left right : KExpr .anon} {addr : Address}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (run : TcM.defEqCtxKey left right before = .ok addr after) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after := by
  rw [defEqCtxKey_state run]
  exact valid.ofCtxAddrCache _

theorem policy {before : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (policy : Bool) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      {before with inferOnly := policy} :=
  valid.ofMaps ⟨Nat.le_refl _, .refl _, rfl⟩ rfl rfl valid.coherent rfl rfl
    (fun partition => by cases partition <;> rfl) (fun partition => by cases partition <;> rfl)
    rfl rfl rfl

/-- The driver's periodic clearing begins empty histories and memos. -/
theorem clearReductionCaches {before : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      {before with env := before.env.clearReductionCaches} where
  sourceCache := valid.sourceCache.clearReductionCaches
  synthesis := valid.synthesis.elim fun history => ⟨history.clear⟩
  whnf := valid.whnf.elim fun history => ⟨history.clear⟩
  structural := ⟨valid.structural.coherent, valid.structural.allocated, valid.structural.loader⟩
  reading := valid.reading
  origin := valid.origin
  semantics := valid.semantics.clear

/-- Per-item reset empties the local context and the equivalence manager and
retains every environment map. -/
theorem reset {before after : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (run : TcM.reset before = .ok () after) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog [] [] [] after := by
  rw [reset_eq] at run
  cases run
  exact {
    sourceCache := ⟨valid.sourceState.ofMaps rfl rfl rfl valid.coherent, valid.cache.ofMaps rfl rfl rfl⟩
    synthesis := valid.synthesis.elim fun history => ⟨history.ofMaps rfl rfl⟩
    whnf := valid.whnf.elim fun history => ⟨history.ofMaps fun partition => by cases partition <;> rfl⟩
    structural := ⟨LocalContext.WF.empty, LocalContext.IdsBelow.empty _, valid.structural.loader⟩
    reading := .empty resolve _
    origin := ⟨.empty entries⟩
    semantics := valid.semantics.ofMapsManager (fun partition => by cases partition <;> rfl)
      (fun partition => by cases partition <;> rfl) EquivManagerSemantics.empty rfl rfl }

private theorem afterLookup {before after : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (sourceCache : SourceCacheInvariant catalog after)
    (synthesis : Nonempty (SynthesisCacheHistory resolve anchor entries after))
    (frame : LazyLookupFrame before after) (ingress : KEnv.IngressFrame before.env after.env)
    (structural : LocalStateFrame before after) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after := by
  obtain ⟨consts, blocks, intern, envEq⟩ := ingress
  have checker := frame.checker
  exact {
    sourceCache, synthesis
    whnf := valid.whnf.elim fun history => ⟨history.ofMaps fun partition => by
      cases partition <;> simp only [WhnfCachePartition.cache, envEq]⟩
    structural := structural.invariant valid.structural
    reading := valid.reading.congr structural.context.symm
    origin := valid.origin
    semantics := valid.semantics.ofMaps
      (fun partition => by cases partition <;> simp only [WhnfCachePartition.cache, envEq])
      (fun partition => by cases partition <;> simp only [DefEqCachePartition.cache, envEq])
      (by rw [checker]) (by rw [envEq]) (by rw [envEq]) }

/-- Lookup retains the invariant on both outcomes, including partially
completed conversion and publication before an unknown-root error. -/
theorem getConst {before : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (id : KId .anon) (data : StandaloneConversionData source id.addr before.env) :
    match TcM.getConst id before with
    | .ok _ after | .error _ after =>
        CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after := by
  have sourceCache := valid.sourceCache.getConst data
  have synthesis : match TcM.getConst id before with
      | .ok _ after | .error _ after => Nonempty (SynthesisCacheHistory resolve anchor entries after) := by
    refine valid.synthesis.elim fun history => ?_
    have preserved := history.getConst (valid.owned.toVerified id.addr)
    cases run : TcM.getConst id before <;> rw [run] at preserved <;> exact ⟨preserved⟩
  have frame := getConst_owned (id := id) valid.owned
  have ingress := getConst_ingressFrame (id := id) source true valid.installed
  have structural := FramesLocalState.getConst id before valid.structural
  cases run : TcM.getConst id before <;>
    rw [run] at sourceCache synthesis frame ingress structural <;>
    exact valid.afterLookup sourceCache synthesis frame.1 ingress structural

/-- Binder opening pushes the checked domain onto the model context; the
caller supplies the extended context's synthesis origin. -/
theorem openBinder {before after : TcState .anon} {name : Mode.anon.F Name}
    {bi : Mode.anon.F Lean.BinderInfo} {domain body opened : KExpr .anon} {fresh : FVarId}
    {A : AExpr β} {level : VLevel}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (data : BinderOpeningData before body)
    (typeReads : readScopedExpr? resolve locals domain = some A.erase)
    (pushed : Nonempty (SynthesisContext resolve anchor [] [] entries (context.push A) (level :: bounds)))
    (run : TcM.openBinder name bi domain body before = .ok (opened, fresh) after) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog (fresh :: locals) (context.push A)
      (level :: bounds) after := by
  have sourceCache := valid.sourceCache.openBinder data run
  have synthesis : Nonempty (SynthesisCacheHistory resolve anchor entries after) :=
    valid.synthesis.elim fun history => ⟨history.openBinder run⟩
  have whnf : Nonempty (BetaCacheHistory β after) :=
    valid.whnf.elim fun history => ⟨history.openBinder run⟩
  have effect := PreservesLocalState.openBinder name bi domain body before valid.structural
  rw [run] at effect
  have absent := valid.structural.freshReading valid.reading
  rw [openBinder_eq] at run
  split at run
  · cases run
    exact {
      sourceCache, synthesis, whnf
      structural := effect.valid
      reading := valid.reading.push absent typeReads
      origin := pushed
      semantics := valid.semantics.ofMaps (fun partition => by cases partition <;> rfl)
        (fun partition => by cases partition <;> rfl) rfl rfl rfl }
  · contradiction

/-- Let opening pushes the declared type; the value is retained in the local
declaration and its substitution agreement remains a separate obligation. -/
theorem openLet {before after : TcState .anon} {name : Mode.anon.F Name}
    {domain value body opened : KExpr .anon} {fresh : FVarId} {A : AExpr β} {level : VLevel}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (data : BinderOpeningData before body)
    (typeReads : readScopedExpr? resolve locals domain = some A.erase)
    (pushed : Nonempty (SynthesisContext resolve anchor [] [] entries (context.push A) (level :: bounds)))
    (run : TcM.openLet name domain value body before = .ok (opened, fresh) after) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog (fresh :: locals) (context.push A)
      (level :: bounds) after := by
  have maps := openLet_inference_state run
  have sourceCache : SourceCacheInvariant catalog after :=
    ⟨⟨valid.inference.openLet data run, valid.agreement.ofMap maps.2.2.1⟩,
      valid.cache.ofMaps maps.1 maps.2.1 maps.2.2.1⟩
  have synthesis := valid.synthesis.elim fun history =>
    (⟨⟨history.execution.openLet run, history.checks⟩⟩ :
      Nonempty (SynthesisCacheHistory resolve anchor entries after))
  have whnf : Nonempty (BetaCacheHistory β after) :=
    valid.whnf.elim fun history => ⟨history.openLet run⟩
  have effect := PreservesLocalState.openLet name domain value body before valid.structural
  rw [run] at effect
  have absent := valid.structural.freshReading valid.reading
  rw [openLet_eq] at run
  split at run
  · cases run
    exact {
      sourceCache, synthesis, whnf
      structural := effect.valid
      reading := valid.reading.push absent typeReads
      origin := pushed
      semantics := valid.semantics.ofMaps (fun partition => by cases partition <;> rfl)
        (fun partition => by cases partition <;> rfl) rfl rfl rfl }
  · contradiction

/-- Scope exit restores the caller's locals from any body state that only
extended the local context, retaining the body's other state updates. -/
theorem exitScope {before state : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    {locals' : List FVarId} {context' : Model.Context β} {bounds' : List VLevel}
    (extended : CheckerInvariant.{u,v} resolve anchor entries source catalog locals' context' bounds' state)
    (extension : before.lctx.Extension state.lctx)
    (counter : before.env.nextFVarId.toNat ≤ state.env.nextFVarId.toNat)
    (loader : state.lazyFault = before.lazyFault) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      {state with lctx := state.lctx.truncate before.lctx.size} :=
  let frame : LocalStateFrame before {state with lctx := state.lctx.truncate before.lctx.size} :=
    (LocalStateExtension.mk extended.structural counter extension loader).restore
  { sourceCache := extended.sourceCache.truncate _
    synthesis := extended.synthesis.elim fun history => ⟨history.truncate _⟩
    whnf := extended.whnf.elim fun history => ⟨history.truncate _⟩
    structural := frame.invariant valid.structural
    reading := valid.reading.congr frame.context.symm
    origin := valid.origin
    semantics := extended.semantics.ofMaps (fun partition => by cases partition <;> rfl)
      (fun partition => by cases partition <;> rfl) rfl rfl rfl }

/-- A scoped body that establishes the invariant for its extended context on
both outcomes yields the caller's invariant after the actual scope cleanup. -/
theorem withLctxScope {α : Type} {action : RecM .anon α} {methods : Methods .anon}
    {before : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (body : match action.run methods before with
      | .ok _ state | .error _ state =>
        (∃ (locals' : List FVarId) (context' : Model.Context β) (bounds' : List VLevel),
          CheckerInvariant.{u,v} resolve anchor entries source catalog locals' context' bounds' state) ∧
        before.lctx.Extension state.lctx ∧
        before.env.nextFVarId.toNat ≤ state.env.nextFVarId.toNat ∧
        state.lazyFault = before.lazyFault) :
    match (RecM.withLctxScope action).run methods before with
    | .ok _ after | .error _ after =>
        CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after := by
  rw [withLctxScope_eq]
  cases run : action.run methods before <;> rw [run] at body <;>
    obtain ⟨⟨locals', context', bounds', extended⟩, extension, counter, loader⟩ := body <;>
    exact valid.exitScope extended extension counter loader

/-! ### Demonstrations: sort and free-variable inference -/

/-- A successful closed-sort inference changes only the intern table and the
two inference maps. -/
private theorem infer_sort_state {level : KUniv .anon} {fuel : Nat} {result : KExpr .anon}
    {before after : TcState .anon}
    (accepted : RecM.infer (KExpr.mkSort level) (methodsN fuel) before = .ok result after) :
    ∃ table full only, after = {before with env := {before.env with
      intern := table, inferCache := full, inferOnlyCache := only}} := by
  have keyRun := inferKey_closed (term := KExpr.mkSort level) rfl before
  rcases observeInferenceCache keyRun with ⟨hit, _, stateEq⟩ | ⟨miss, _, stateEq⟩
  · rw [hit.run (methodsN fuel)] at accepted
    cases accepted
    rw [stateEq]
    exact ⟨before.env.intern, before.env.inferCache, before.env.inferOnlyCache, rfl⟩
  · obtain ⟨state, run, written⟩ := infer_uncached_success_state miss accepted
    rw [stateEq] at run
    change EStateM.Result.ok
      (before.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).1
      {before with env := {before.env with intern :=
        (before.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).2}} =
      .ok result state at run
    cases run
    rw [written]
    cases policy : before.inferOnly
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨_, _, before.env.inferOnlyCache, rfl⟩
    · simp only [↓reduceIte]
      exact ⟨_, before.env.inferCache, _, rfl⟩

/-- Sort inference preserves the invariant and returns the canonical
successor sort, whose typing is derived from the maintained catalog agreement
on a hit and from the actual intern step on a miss. -/
theorem inferSort {level : KUniv .anon} {fuel : Nat} {result : KExpr .anon}
    {before after : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (member : SourceCacheRequest.sort level ∈ catalog)
    (keyData : SourceCacheKeyData catalog (KExpr.mkSort level))
    (faithful : KExpr.KeyCollisionFree fun term => before.env.intern.ExprSupport term ∨
      term = KExpr.mkSort (KUniv.mkSucc level))
    (accepted : RecM.infer (KExpr.mkSort level) (methodsN fuel) before = .ok result after) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after ∧
      result = KExpr.mkSort (KUniv.mkSucc level) ∧
      ScopedModelTyping.{u,v} resolve entries locals context (KExpr.mkSort level) result := by
  have keyRun := inferKey_closed (term := KExpr.mkSort level) rfl before
  obtain ⟨canonical, _⟩ := infer_sort_cache_agreement keyRun
    (valid.cache (.sort level) member).correct valid.coherent faithful accepted
  refine ⟨?_, canonical, ⟨.sort (readLevel level), .sort (.succ (readLevel level)), rfl,
    by rw [canonical]; simp [AExpr.erase], TypingClaim.sort _⟩⟩
  have sourceCache : SourceCacheInvariant catalog after := by
    rcases observeInferenceCache keyRun with ⟨hit, _, _⟩ | ⟨miss, _, stateEq⟩
    · exact (OwnedInferenceTrace.hit (fuel := fuel) hit).preservesSourceCache valid.sourceCache
        trivial trivial accepted
    · exact (OwnedInferenceTrace.sort (fuel := fuel) miss).preservesSourceCache valid.sourceCache
        trivial (And.intro keyData (by rw [stateEq]; exact faithful)) accepted
  have synthesis : Nonempty (SynthesisCacheHistory resolve anchor entries after) := by
    rcases observeInferenceCache keyRun with ⟨hit, _, _⟩ | ⟨miss, _, stateEq⟩
    · exact valid.synthesis.elim fun history =>
        ⟨history.afterInference (InferenceCacheTrace.hit hit : InferenceCacheTrace.{0} fuel before _)
          accepted .nil⟩
    · refine valid.synthesis.elim fun history => valid.origin.elim fun origin => ?_
      have tree : SynthesisInference resolve entries locals context bounds fuel before
          (KExpr.mkSort level) (.sort (readLevel level)) (.sort (.succ (readLevel level)))
          (.succ (.succ (readLevel level))) :=
        .known (.sort miss (by rw [stateEq]; exact valid.coherent) (by rw [stateEq]; exact faithful))
          (.sort _)
      exact ⟨history.afterInference
        (InferenceCacheTrace.sort miss : InferenceCacheTrace.{0} fuel before _) accepted
        (.singleton (SynthesisEventCheck.ofSource tree origin valid.reading rfl miss accepted))⟩
  obtain ⟨table, full, only, stateEq⟩ := infer_sort_state accepted
  subst stateEq
  exact {
    sourceCache, synthesis
    whnf := valid.whnf.elim fun history => ⟨history.ofMaps fun partition => by cases partition <;> rfl⟩
    structural := ⟨valid.structural.coherent, valid.structural.allocated, valid.structural.loader⟩
    reading := valid.reading
    origin := valid.origin
    semantics := valid.semantics.ofMaps (fun partition => by cases partition <;> rfl)
      (fun partition => by cases partition <;> rfl) rfl rfl rfl }

/-- A successful free-variable inference changes only the context-digest memo
and the two inference maps. -/
private theorem infer_fvar_state {id : FVarId} {name : Mode.anon.F Name} {info : ExprInfo .anon}
    {fuel : Nat} {result : KExpr .anon} {before after : TcState .anon}
    (support : FVarInferenceSupport before id name info)
    (accepted : RecM.infer (.fvar id name info) (methodsN fuel) before = .ok result after) :
    ∃ memo full only, after = {before with ctxAddrCache := memo, env := {before.env with
      inferCache := full, inferOnlyCache := only}} := by
  have keyed := inferKey_state support.keyRun
  rcases observeInferenceCache support.keyRun with ⟨hit, _, stateEq⟩ | ⟨miss, _, stateEq⟩
  · rw [hit.run (methodsN fuel)] at accepted
    cases accepted
    rw [stateEq, keyed]
    exact ⟨_, before.env.inferCache, before.env.inferOnlyCache, rfl⟩
  · obtain ⟨state, run, written⟩ := infer_uncached_success_state miss accepted
    change (RecM.inferUncached RecM.inferCall before.inferOnly (.fvar id name info)).run
      (methodsN fuel) miss.keyed = _ at run
    unfold RecM.inferUncached at run
    simp only [ReaderT.run_bind] at run
    change EStateM.bind (get : TcM .anon (TcState .anon)) _ miss.keyed = _ at run
    rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) miss.keyed =
      .ok miss.keyed miss.keyed from rfl] at run
    dsimp only at run
    split at run
    · cases run
      rw [written, stateEq, keyed]
      cases policy : before.inferOnly
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨_, _, before.env.inferOnlyCache, rfl⟩
      · simp only [↓reduceIte]
        exact ⟨_, before.env.inferCache, _, rfl⟩
    · contradiction

/-- Free-variable inference preserves the invariant and returns the actual
declaration type, read at the registered model index. -/
theorem inferFVar {id : FVarId} {name : Mode.anon.F Name} {info : ExprInfo .anon} {index : Nat}
    {A : AExpr β} {level : VLevel} {fuel : Nat} {result : KExpr .anon} {before after : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (support : FVarInferenceSupport before id name info)
    (registered : localIndex? locals id = some index)
    (atIndex : context[index]? = some A) (boundAtIndex : bounds[index]? = some level)
    (keyData : SourceCacheKeyData catalog (.fvar id name info))
    (accepted : RecM.infer (.fvar id name info) (methodsN fuel) before = .ok result after) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after ∧
      readScopedExpr? resolve locals result = some A.erase ∧
      TypingClaim.{u,v} entries context (.bvar index) A := by
  obtain ⟨reading, typed⟩ := support.sound (entries := entries) valid.reading registered atIndex accepted
  refine ⟨?_, reading, typed⟩
  have sourceCache : SourceCacheInvariant catalog after := by
    rcases observeInferenceCache support.keyRun with ⟨hit, _, _⟩ | ⟨miss, _, _⟩
    · exact (OwnedInferenceTrace.hit (fuel := fuel) hit).preservesSourceCache valid.sourceCache
        trivial trivial accepted
    · exact (OwnedInferenceTrace.fvar (fuel := fuel) miss).preservesSourceCache valid.sourceCache
        trivial keyData accepted
  have synthesis : Nonempty (SynthesisCacheHistory resolve anchor entries after) := by
    rcases observeInferenceCache support.keyRun with ⟨hit, _, _⟩ | ⟨miss, _, _⟩
    · exact valid.synthesis.elim fun history =>
        ⟨history.afterInference (InferenceCacheTrace.hit hit : InferenceCacheTrace.{0} fuel before _)
          accepted .nil⟩
    · refine valid.synthesis.elim fun history => valid.origin.elim fun origin => ?_
      have tree : SynthesisInference resolve entries locals context bounds fuel before
          (.fvar id name info) (.bvar index) A level :=
        .fvar (.fvar support registered atIndex) atIndex boundAtIndex
      exact ⟨history.afterInference
        (InferenceCacheTrace.fvar miss : InferenceCacheTrace.{0} fuel before _) accepted
        (.singleton (SynthesisEventCheck.ofSource tree origin valid.reading
          (by simp [readScopedExpr?, registered, AExpr.erase]) miss accepted))⟩
  obtain ⟨memo, full, only, stateEq⟩ := infer_fvar_state support accepted
  subst stateEq
  exact {
    sourceCache, synthesis
    whnf := valid.whnf.elim fun history => ⟨history.ofMaps fun partition => by cases partition <;> rfl⟩
    structural := ⟨valid.structural.coherent, valid.structural.allocated, valid.structural.loader⟩
    reading := valid.reading
    origin := valid.origin
    semantics := valid.semantics.ofMaps (fun partition => by cases partition <;> rfl)
      (fun partition => by cases partition <;> rfl) rfl rfl rfl }

/-! ### Demonstration: natural-number literal inference -/

/-- A successful closed-literal inference changes only the intern table and
the two inference maps. -/
private theorem infer_nat_state {value : Nat} {fuel : Nat} {result : KExpr .anon}
    {before after : TcState .anon}
    (accepted : RecM.infer (KExpr.mkNatLit value) (methodsN fuel) before = .ok result after) :
    ∃ table full only, after = {before with env := {before.env with
      intern := table, inferCache := full, inferOnlyCache := only}} := by
  have keyRun := inferKey_closed (term := KExpr.mkNatLit value) rfl before
  rcases observeInferenceCache keyRun with ⟨hit, _, stateEq⟩ | ⟨miss, _, stateEq⟩
  · rw [hit.run (methodsN fuel)] at accepted
    cases accepted
    rw [stateEq]
    exact ⟨before.env.intern, before.env.inferCache, before.env.inferOnlyCache, rfl⟩
  · obtain ⟨state, run, written⟩ := infer_uncached_success_state miss accepted
    rw [stateEq] at run
    obtain ⟨rfl, rfl⟩ := inferUncached_nat_run run
    rw [written]
    cases policy : before.inferOnly
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨_, _, before.env.inferOnlyCache, rfl⟩
    · simp only [↓reduceIte]
      exact ⟨_, before.env.inferCache, _, rfl⟩

/-- Literal inference preserves the invariant and returns the primitive `Nat`
constant, whose typing comes from the static binding of that address; the
returned tree is derived from the maintained catalog agreement on a hit and
from the actual intern step on a miss. Every catalog request for this literal
names the run's primitive. -/
theorem inferNat {value : Nat} {fuel : Nat} {result : KExpr .anon} {before after : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (binding : PrimitiveNatBinding resolve entries before.prims)
    (member : SourceCacheRequest.nat value before.prims.nat ∈ catalog)
    (unique : ∀ prim, SourceCacheRequest.nat value prim ∈ catalog → prim = before.prims.nat)
    (keyData : SourceCacheKeyData catalog (KExpr.mkNatLit value))
    (faithful : KExpr.KeyCollisionFree fun term => before.env.intern.ExprSupport term ∨
      term = KExpr.mkConst before.prims.nat #[])
    (accepted : RecM.infer (KExpr.mkNatLit value) (methodsN fuel) before = .ok result after) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after ∧
      result = KExpr.mkConst before.prims.nat #[] ∧
      ScopedModelTyping.{u,v} resolve entries locals context (KExpr.mkNatLit value) result := by
  have keyRun := inferKey_closed (term := KExpr.mkNatLit value) rfl before
  obtain ⟨canonical, _⟩ := infer_nat_cache_agreement keyRun
    (valid.cache (.nat value before.prims.nat) member).correct valid.coherent faithful accepted
  refine ⟨?_, canonical, ⟨.natLit value, .const binding.ref [], rfl,
    by rw [canonical]; exact binding.typeReading locals, binding.typing context value⟩⟩
  have sourceCache : SourceCacheInvariant catalog after := by
    rcases observeInferenceCache keyRun with ⟨hit, _, _⟩ | ⟨miss, _, stateEq⟩
    · exact (OwnedInferenceTrace.hit (fuel := fuel) hit).preservesSourceCache valid.sourceCache
        trivial trivial accepted
    · exact (OwnedInferenceTrace.nat (fuel := fuel) miss).preservesSourceCache valid.sourceCache
        trivial ⟨keyData, by rw [stateEq]; exact unique, by rw [stateEq]; exact faithful⟩ accepted
  have synthesis : Nonempty (SynthesisCacheHistory resolve anchor entries after) := by
    rcases observeInferenceCache keyRun with ⟨hit, _, _⟩ | ⟨miss, _, stateEq⟩
    · exact valid.synthesis.elim fun history =>
        ⟨history.afterInference (InferenceCacheTrace.hit hit : InferenceCacheTrace.{0} fuel before _)
          accepted .nil⟩
    · refine valid.synthesis.elim fun history => valid.origin.elim fun origin => ?_
      have tree : SynthesisInference resolve entries locals context bounds fuel before
          (KExpr.mkNatLit value) (.natLit value) (.const binding.ref []) binding.level :=
        .natLit binding (.natLit miss binding (by rw [stateEq]; exact valid.coherent)
          (by rw [stateEq]; exact faithful))
      exact ⟨history.afterInference
        (InferenceCacheTrace.nat miss : InferenceCacheTrace.{0} fuel before _) accepted
        (.singleton (SynthesisEventCheck.ofSource tree origin valid.reading rfl miss accepted))⟩
  obtain ⟨table, full, only, stateEq⟩ := infer_nat_state accepted
  subst stateEq
  exact {
    sourceCache, synthesis
    whnf := valid.whnf.elim fun history => ⟨history.ofMaps fun partition => by cases partition <;> rfl⟩
    structural := ⟨valid.structural.coherent, valid.structural.allocated, valid.structural.loader⟩
    reading := valid.reading
    origin := valid.origin
    semantics := valid.semantics.ofMaps (fun partition => by cases partition <;> rfl)
      (fun partition => by cases partition <;> rfl) rfl rfl rfl }

end CheckerInvariant

end Ix.Kernel.Consistency
