/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.ConstantCache
import Ix.Kernel.Ingress

/-!
# Inference caches across verified standalone lazy loading

Conversion accesses only intern tables. Registration inserts one fresh
declaration, so existing declarations and inference caches survive both
successful loading and errors with partial conversion progress.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

private instance : LawfulBEq (KId .anon) where
  eq_of_beq {a b} equal := by
    cases a with | mk left leftName =>
    cases b with | mk right rightName =>
    have same : left = right := eq_of_beq (Bool.and_eq_true_iff.mp equal).1
    cases leftName
    cases rightName
    cases same
    rfl
  rfl {a} := by
    change (a.addr == a.addr && Mode.F.beq a.name a.name) = true
    exact Bool.and_eq_true_iff.mpr ⟨beq_self_eq_true _, rfl⟩

private instance : LawfulHashable (KId .anon) where
  hash_eq _ _ equal := by rw [eq_of_beq equal]

/-- Data protected while a lazy load grows the declaration map. -/
structure IngressCacheExtension (before after : AnonEnv) : Prop where
  full : after.inferCache = before.inferCache
  only : after.inferOnlyCache = before.inferOnlyCache
  constants : ∀ id concrete, before.get? id = some concrete → after.get? id = some concrete
  freshIds : after.nextFVarId = before.nextFVarId

theorem IngressCacheExtension.refl (env : AnonEnv) : IngressCacheExtension env env :=
  ⟨rfl, rfl, fun _ _ found => found, rfl⟩

theorem IngressCacheExtension.intern (env : AnonEnv) (it : InternTable .anon) :
    IngressCacheExtension env {env with intern := it} :=
  ⟨rfl, rfl, fun _ _ found => found, rfl⟩

theorem IngressCacheExtension.trans {before middle after : AnonEnv}
    (first : IngressCacheExtension before middle) (second : IngressCacheExtension middle after) :
    IngressCacheExtension before after :=
  ⟨second.full.trans first.full, second.only.trans first.only,
    fun id concrete found => second.constants id concrete (first.constants id concrete found),
    second.freshIds.trans first.freshIds⟩

/-- A fresh single-entry registration retains every old declaration. -/
theorem IngressCacheExtension.insert {env : AnonEnv} {id : KId .anon}
    (fresh : env.get? id = none) (concrete : KConst .anon) :
    IngressCacheExtension env ((env.insert id concrete).insertBlock id #[id]) := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  intro old value loaded
  have different : id ≠ old := by
    intro equal
    subst old
    rw [fresh] at loaded
    contradiction
  simpa only [KEnv.get?, KEnv.insert, KEnv.insertBlock, Std.HashMap.getElem?_insert,
    beq_iff_eq, different, ↓reduceIte] using loaded

/-- The public converter preserves protected state on success and error. -/
theorem ingress_runIntern_cache (action : InternIngressM α) (before : AnonEnv) :
    match IngressM.runIntern action before with
    | .ok _ after | .error _ after => IngressCacheExtension before after := by
  unfold IngressM.runIntern
  cases action before.intern <;> exact .intern _ _

theorem insertStandaloneEntries_singleton (id : KId .anon) (concrete : KConst .anon)
    (before : AnonEnv) :
    insertStandaloneEntries #[(id, concrete)] before =
      match reservedMarkerName id.addr with
      | some marker => .error
          s!"attempted to insert constant at reserved kernel marker address {marker} ({id.addr})" before
      | none => .ok () ((before.insert id concrete).insertBlock id #[id]) := by
  simp [insertStandaloneEntries, guardReserved]
  cases reservedMarkerName id.addr <;> rfl

/-- Fresh standalone ingress preserves old declarations and both caches,
including conversion errors and rejection by the reserved-address guard. -/
theorem ingressAnonStandalone_cache (source : Ixon.Env) (addr : Address)
    (constant : Ixon.Constant) (before : AnonEnv)
    (fresh : before.get? ⟨addr, ()⟩ = none) :
    match ingressAnonStandalone source addr constant before with
    | .ok _ after | .error _ after => IngressCacheExtension before after := by
  unfold ingressAnonStandalone
  change (match (EStateM.bind (IngressM.runIntern (convertAnonStandalone source addr constant))
    _ : IngressM (KId .anon)) before with
    | .ok _ after | .error _ after => IngressCacheExtension before after)
  unfold EStateM.bind IngressM.runIntern
  cases converted : convertAnonStandalone source addr constant before.intern with
  | error err it => exact .intern _ _
  | ok concrete it =>
      change (match (EStateM.bind (insertStandaloneEntries #[(⟨addr, ()⟩, concrete)])
        _ : IngressM (KId .anon)) {before with intern := it} with
        | .ok _ after | .error _ after => IngressCacheExtension before after)
      rw [EStateM.bind, insertStandaloneEntries_singleton]
      cases reservedMarkerName addr with
      | some marker => exact .intern _ _
      | none =>
          exact (IngressCacheExtension.intern before it).trans
            (.insert (env := {before with intern := it}) fresh concrete)

/-- The verified lookup either fails, misses, or materializes a standalone.
Mutual blocks and their projections require a separate publication proof. -/
def StandaloneMaterialization (source : Ixon.Env) (addr : Address) : Prop :=
  match getConstVerified source addr true with
  | .error _ | .ok none => True
  | .ok (some constant) => match constant.info with
    | .defn _ | .recr _ | .axio _ | .quot _ => True
    | _ => False

/-- The actual verified shallow loader derives the extension from fresh
standalone registration, with no assumed callback-preservation premise. -/
theorem ingressAnonAddrShallow_cache (source : Ixon.Env) (addr : Address)
    (standalone : StandaloneMaterialization source addr) (before : AnonEnv)
    (fresh : before.get? ⟨addr, ()⟩ = none) :
    match ingressAnonAddrShallow source addr true before with
    | .ok _ after | .error _ after => IngressCacheExtension before after := by
  unfold ingressAnonAddrShallow
  change (match (EStateM.bind (IngressM.liftExcept (getConstVerified source addr true))
    _ : IngressM Bool) before with
    | .ok _ after | .error _ after => IngressCacheExtension before after)
  unfold StandaloneMaterialization at standalone
  cases verified : getConstVerified source addr true with
  | error err => exact .refl _
  | ok optional =>
      cases optional with
      | none => exact .refl _
      | some constant =>
          rw [verified] at standalone
          cases info : constant.info <;> simp only [info] at standalone
          all_goals try contradiction
          all_goals
            dsimp only [IngressM.liftExcept, Bind.bind, Pure.pure, EStateM.pure, EStateM.bind]
            rw [info]
            dsimp only [Bind.bind, EStateM.bind]
            have frame := ingressAnonStandalone_cache source addr constant before fresh
            cases run : ingressAnonStandalone source addr constant before <;>
              rw [run] at frame <;> exact frame

/-- A lookup may grow the environment and record a fault attempt. Every
other checker field, including policy and both local contexts, is retained. -/
structure LazyLookupFrame (before after : TcState .anon) : Prop where
  environment : IngressCacheExtension before.env after.env
  checker : after = {before with env := after.env, faultedAddrs := after.faultedAddrs}

theorem LazyLookupFrame.refl (state : TcState .anon) : LazyLookupFrame state state :=
  ⟨.refl _, rfl⟩

theorem LazyLookupFrame.cache {before after : TcState .anon}
    (frame : LazyLookupFrame before after) (key : Address × Address) :
    InferenceCacheFrame key before after := by
  refine ⟨?_, ?_, frame.environment.constants⟩
  · rw [frame.environment.full]
  · rw [frame.environment.only]

theorem LazyLookupFrame.policy {before after : TcState .anon}
    (frame : LazyLookupFrame before after) : after.inferOnly = before.inferOnly := by
  rw [frame.checker]

/-- The installed callback is the production loader with verification on.
The source condition concerns materialization shape, not cache preservation. -/
structure StandaloneLazySupport (before : TcState .anon) (addr : Address) where
  source : Ixon.Env
  installed : before.lazyFault = some (fun address => ingressAnonAddrShallow source address true)
  standalone : StandaloneMaterialization source addr

/-- Direct fresh faults retain existing cache witnesses on every outcome,
including an address already recorded in the fault-deduplication set. -/
theorem lazyIngressAddr_cache {before : TcState .anon} {addr : Address}
    (support : StandaloneLazySupport before addr)
    (fresh : before.env.get? ⟨addr, ()⟩ = none) :
    match TcM.lazyIngressAddr addr before with
    | .ok _ after | .error _ after => LazyLookupFrame before after := by
  unfold TcM.lazyIngressAddr
  rw [support.installed]
  dsimp only
  by_cases faulted : before.faultedAddrs.contains addr = true
  · rw [if_pos faulted]
    exact .refl _
  · rw [if_neg faulted]
    have frame := ingressAnonAddrShallow_cache support.source addr support.standalone before.env fresh
    cases run : ingressAnonAddrShallow support.source addr true before.env <;>
      rw [run] at frame <;> refine ⟨frame, ?_⟩ <;> simp only [support.installed]

/-- Try-lookup derives freshness from its own initial miss. Loaded hits,
verified source misses, conversion failures, and deduplicated faults all
retain the original cache entries and loaded declarations. -/
theorem tryGetConst_standalone_cache {before : TcState .anon} {id : KId .anon}
    (support : StandaloneLazySupport before id.addr) :
    match TcM.tryGetConst id before with
    | .ok _ after | .error _ after => LazyLookupFrame before after := by
  unfold TcM.tryGetConst
  change (match (EStateM.bind (get : TcM .anon (TcState .anon)) _ :
    TcM .anon (Option (KConst .anon))) before with
    | .ok _ after | .error _ after => LazyLookupFrame before after)
  rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) before = .ok before before from rfl]
  dsimp only
  cases loaded : before.env.get? id with
  | some concrete => exact .refl _
  | none =>
      have fresh : before.env.get? ⟨id.addr, ()⟩ = none := by
        cases id with | mk addr name => cases name; exact loaded
      change (match (EStateM.bind (TcM.lazyIngressAddr id.addr) _ :
        TcM .anon (Option (KConst .anon))) before with
        | .ok _ after | .error _ after => LazyLookupFrame before after)
      have frame := lazyIngressAddr_cache support fresh
      cases fault : TcM.lazyIngressAddr id.addr before with
      | error err after =>
          rw [EStateM.bind, fault]
          simpa only [fault] using frame
      | ok value after =>
          rw [fault] at frame
          rw [EStateM.bind, fault]
          change (match (EStateM.bind (get : TcM .anon (TcState .anon)) _ :
            TcM .anon (Option (KConst .anon))) after with
            | .ok _ state | .error _ state => LazyLookupFrame before state)
          rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) after = .ok after after from rfl]
          dsimp only
          cases after.env.get? id with
          | some concrete => exact frame
          | none => cases before.lazyFault.isSome <;> exact frame

/-- Hard lookup has the same frame, including the error for an absent source. -/
theorem getConst_standalone_cache {before : TcState .anon} {id : KId .anon}
    (support : StandaloneLazySupport before id.addr) :
    match TcM.getConst id before with
    | .ok _ after | .error _ after => LazyLookupFrame before after := by
  unfold TcM.getConst
  change (match (EStateM.bind (TcM.tryGetConst id) _ : TcM .anon (KConst .anon)) before with
    | .ok _ after | .error _ after => LazyLookupFrame before after)
  have frame := tryGetConst_standalone_cache support
  cases tried : TcM.tryGetConst id before with
  | error err after =>
      rw [EStateM.bind, tried]
      simpa only [tried] using frame
  | ok optional after =>
      rw [tried] at frame
      rw [EStateM.bind, tried]
      cases optional <;> exact frame

/-- An earlier cached constant witness survives a successful lazy lookup of
another declaration. No new cache observation or typing premise is supplied. -/
def CachedConstantInferenceSupport.afterGetConst {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {before after : TcState .anon} {id requested : KId .anon}
    {arguments : Array (KUniv .anon)} {info : ExprInfo .anon}
    {ref : ConstRef β} {entry : ConstantEntry β} {type : AExpr β} {concrete : KConst .anon}
    (support : CachedConstantInferenceSupport resolve entries before id arguments info ref entry type)
    (closed : (KExpr.const id arguments info).lbr = 0)
    (loader : StandaloneLazySupport before requested.addr)
    (run : TcM.getConst requested before = .ok concrete after) :
    CachedConstantInferenceSupport resolve entries after id arguments info ref entry type := by
  have frame := getConst_standalone_cache loader
  rw [run] at frame
  exact support.transport closed (frame.cache _) frame.policy

/-- Failed loading retains the earlier witness even when conversion has
already changed the intern tables and the fault attempt remains recorded. -/
def CachedConstantInferenceSupport.afterFailedGetConst {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {before after : TcState .anon} {id requested : KId .anon}
    {arguments : Array (KUniv .anon)} {info : ExprInfo .anon}
    {ref : ConstRef β} {entry : ConstantEntry β} {type : AExpr β} {err : TcError .anon}
    (support : CachedConstantInferenceSupport resolve entries before id arguments info ref entry type)
    (closed : (KExpr.const id arguments info).lbr = 0)
    (loader : StandaloneLazySupport before requested.addr)
    (run : TcM.getConst requested before = .error err after) :
    CachedConstantInferenceSupport resolve entries after id arguments info ref entry type := by
  have frame := getConst_standalone_cache loader
  rw [run] at frame
  exact support.transport closed (frame.cache _) frame.policy

end Ix.Kernel.Consistency
