/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.LazyCache

/-!
# Cache preservation through verified mutual-block loading

Preparation can change only intern tables. Publication uses the production
left-to-right insertion fold and retains old declarations when every entry
agrees with any declaration already loaded at its key. Duplicate fresh keys
do not require an injectivity assumption to preserve the original environment.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- Each proposed declaration agrees with any previously loaded declaration
at its key. Fresh entries satisfy this condition without a comparison. -/
def EntriesCompatible (before : AnonEnv) (entries : Array Entry) : Prop :=
  ∀ entry ∈ entries, ∀ old, before.get? entry.1 = some old → entry.2 = old

theorem EntriesCompatible.ofFresh {before : AnonEnv} {entries : Array Entry}
    (fresh : ∀ entry ∈ entries, before.get? entry.1 = none) :
    EntriesCompatible before entries := by
  intro entry member old loaded
  rw [fresh entry member] at loaded
  contradiction

/-- A finite check may mix fresh entries with exact repeats of old entries. -/
theorem EntriesCompatible.ofLookups {before : AnonEnv} {entries : Array Entry}
    (lookups : ∀ entry ∈ entries, before.get? entry.1 = none ∨
      before.get? entry.1 = some entry.2) : EntriesCompatible before entries := by
  intro entry member old loaded
  rcases lookups entry member with fresh | same
  · rw [fresh] at loaded
    contradiction
  · exact Option.some.inj (same.symm.trans loaded)

private theorem insert_retains_original {before current : AnonEnv}
    (frame : IngressCacheExtension before current) (entry : Entry)
    (compatible : ∀ old, before.get? entry.1 = some old → entry.2 = old) :
    IngressCacheExtension before (current.insert entry.1 entry.2) := by
  refine ⟨frame.full, frame.only, ?_, frame.freshIds⟩
  intro id concrete loaded
  by_cases same : entry.1 = id
  · rw [← same] at loaded ⊢
    simp [KEnv.get?, KEnv.insert, compatible concrete loaded]
  · simpa [KEnv.get?, KEnv.insert, Std.HashMap.getElem?_insert, same] using
      frame.constants id concrete loaded

private theorem foldl_insert_retains_original (before : AnonEnv) (entries : List Entry)
    (compatible : ∀ entry ∈ entries, ∀ old, before.get? entry.1 = some old → entry.2 = old)
    (current : AnonEnv) (frame : IngressCacheExtension before current) :
    IngressCacheExtension before
      (entries.foldl (fun env entry => env.insert entry.1 entry.2) current) := by
  induction entries generalizing current with
  | nil => exact frame
  | cons entry rest ih =>
      apply ih (fun member found => compatible member (List.mem_cons_of_mem _ found))
      exact insert_retains_original frame entry (compatible entry (List.mem_cons_self))

/-- Last-write-wins publication preserves the original declarations without
requiring uniqueness among fresh entries. The block map may also grow. -/
theorem insertMutsEntriesState_cache {before : AnonEnv} {entries : Array Entry}
    (compatible : EntriesCompatible before entries) :
    IngressCacheExtension before (insertMutsEntriesState before entries) := by
  unfold insertMutsEntriesState insertEntriesState
  apply foldl_insert_retains_original before entries.toList
  · intro entry member old loaded
    exact compatible entry (by simpa using member) old loaded
  · split <;> exact ⟨rfl, rfl, fun _ _ found => found, rfl⟩

/-- Reserved-address validation retains the exact environment on both outcomes. -/
theorem guardReserved_state (entries : Array Entry) (before : AnonEnv) :
    guardReserved entries before = match checkReserved entries with
      | .ok _ => .ok () before
      | .error err => .error err before := by
  unfold guardReserved IngressM.liftExcept
  cases checkReserved entries with
  | error err => rfl
  | ok value => cases value; rfl

theorem insertMutsEntries_cache {before : AnonEnv} {entries : Array Entry}
    (compatible : EntriesCompatible before entries) :
    match insertMutsEntries entries before with
    | .ok _ after | .error _ after => IngressCacheExtension before after := by
  unfold insertMutsEntries
  change (match (EStateM.bind (guardReserved entries) _ : IngressM Unit) before with
    | .ok _ after | .error _ after => IngressCacheExtension before after)
  rw [EStateM.bind, guardReserved_state]
  cases checkReserved entries with
  | error err => exact .refl _
  | ok value => exact insertMutsEntriesState_cache compatible

/-- This resource describes the actual converted entries before publication;
it supplies no assertion about cache state or the final environment. -/
def BlockEntriesCompatible (source : Ixon.Env) (constant : Ixon.Constant)
    (addr : Address) (before : AnonEnv) : Prop :=
  ∀ trace converted, prepareAnonBlock source constant addr before = .ok trace converted →
    EntriesCompatible before trace.allEntries

theorem BlockEntriesCompatible.ofFresh {source : Ixon.Env} {constant : Ixon.Constant}
    {addr : Address} {before : AnonEnv}
    (fresh : ∀ trace converted, prepareAnonBlock source constant addr before = .ok trace converted →
      ∀ entry ∈ trace.allEntries, before.get? entry.1 = none) :
    BlockEntriesCompatible source constant addr before :=
  fun trace converted run => EntriesCompatible.ofFresh (fresh trace converted run)

theorem BlockEntriesCompatible.ofLookups {source : Ixon.Env} {constant : Ixon.Constant}
    {addr : Address} {before : AnonEnv}
    (lookups : ∀ trace converted, prepareAnonBlock source constant addr before = .ok trace converted →
      ∀ entry ∈ trace.allEntries, before.get? entry.1 = none ∨
        before.get? entry.1 = some entry.2) : BlockEntriesCompatible source constant addr before :=
  fun trace converted run => EntriesCompatible.ofLookups (lookups trace converted run)

/-- All preparation effects, including failures after earlier members were
converted, are confined to intern tables. No entry is published here. -/
theorem prepareAnonBlock_cache (source : Ixon.Env) (constant : Ixon.Constant)
    (addr : Address) (before : AnonEnv) :
    match prepareAnonBlock source constant addr before with
    | .ok _ after | .error _ after => IngressCacheExtension before after := by
  unfold prepareAnonBlock IngressM.runIntern
  cases convertAnonBlock source constant addr before.intern <;> exact .intern _ _

theorem ingressAnonBlockWithTrace_cache (source : Ixon.Env) (constant : Ixon.Constant)
    (addr : Address) (before : AnonEnv)
    (compatible : BlockEntriesCompatible source constant addr before) :
    match ingressAnonBlockWithTrace source constant addr before with
    | .ok _ after | .error _ after => IngressCacheExtension before after := by
  unfold ingressAnonBlockWithTrace
  change (match (EStateM.bind (prepareAnonBlock source constant addr) _ :
    IngressM AnonBlockIngressTrace) before with
    | .ok _ after | .error _ after => IngressCacheExtension before after)
  unfold prepareAnonBlock IngressM.runIntern EStateM.bind
  dsimp only
  cases converted : convertAnonBlock source constant addr before.intern with
  | error err it => exact .intern _ _
  | ok trace it =>
      have prepared : prepareAnonBlock source constant addr before =
          .ok trace {before with intern := it} := by
        unfold prepareAnonBlock IngressM.runIntern
        rw [converted]
      have entries := compatible trace _ prepared
      have published := insertMutsEntries_cache
        (before := {before with intern := it}) entries
      change (match EStateM.bind (insertMutsEntries trace.allEntries)
        (fun _ => EStateM.pure trace) {before with intern := it} with
        | .ok _ after | .error _ after => IngressCacheExtension before after)
      rw [EStateM.bind]
      cases run : insertMutsEntries trace.allEntries {before with intern := it} <;>
        rw [run] at published <;> exact (IngressCacheExtension.intern before it).trans published

theorem ingressAnonBlock_cache (source : Ixon.Env) (constant : Ixon.Constant)
    (addr : Address) (before : AnonEnv)
    (compatible : BlockEntriesCompatible source constant addr before) :
    match ingressAnonBlock source constant addr before with
    | .ok _ after | .error _ after => IngressCacheExtension before after := by
  unfold ingressAnonBlock
  change (match (EStateM.bind (ingressAnonBlockWithTrace source constant addr) _ :
    IngressM (Array (KId .anon))) before with
    | .ok _ after | .error _ after => IngressCacheExtension before after)
  have frame := ingressAnonBlockWithTrace_cache source constant addr before compatible
  rw [EStateM.bind]
  cases run : ingressAnonBlockWithTrace source constant addr before <;> rw [run] at frame <;> exact frame

/-- Only an actual block publication needs overlap agreement. Failed source
lookups and already recorded blocks require no declaration resource. -/
def LazyMaterializationSupport (source : Ixon.Env) (addr : Address) (before : AnonEnv) : Prop :=
  match getConstVerified source addr true with
  | .error _ | .ok none => True
  | .ok (some constant) => match ingressBlockAddr? addr constant.info with
    | none => True
    | some blockAddr => if before.blocks.contains ⟨blockAddr, ()⟩ then True else
      match getConstVerified source blockAddr true with
      | .error _ | .ok none => True
      | .ok (some blockConstant) => BlockEntriesCompatible source blockConstant blockAddr before

/-- The real verified loader preserves old declarations and both caches on
every outcome, including failed preparation and successful whole-block publication. -/
theorem ingressAnonAddrShallow_verified_cache (source : Ixon.Env) (addr : Address)
    (before : AnonEnv) (materialization : LazyMaterializationSupport source addr before)
    (fresh : before.get? ⟨addr, ()⟩ = none) :
    match ingressAnonAddrShallow source addr true before with
    | .ok _ after | .error _ after => IngressCacheExtension before after := by
  unfold ingressAnonAddrShallow
  change (match (EStateM.bind (IngressM.liftExcept (getConstVerified source addr true))
    _ : IngressM Bool) before with
    | .ok _ after | .error _ after => IngressCacheExtension before after)
  unfold LazyMaterializationSupport at materialization
  cases verified : getConstVerified source addr true with
  | error err => exact .refl _
  | ok optional =>
      cases optional with
      | none => exact .refl _
      | some constant =>
          rw [verified] at materialization
          dsimp only at materialization
          dsimp only [IngressM.liftExcept, Bind.bind, Pure.pure, EStateM.pure, EStateM.bind]
          cases block : ingressBlockAddr? addr constant.info with
          | none =>
              dsimp only [Bind.bind, EStateM.bind]
              have frame := ingressAnonStandalone_cache source addr constant before fresh
              cases run : ingressAnonStandalone source addr constant before <;>
                rw [run] at frame <;> exact frame
          | some blockAddr =>
              rw [block] at materialization
              dsimp only [Bind.bind, EStateM.bind]
              rw [show (get : IngressM AnonEnv) before = .ok before before from rfl]
              dsimp only
              by_cases recorded : before.blocks.contains ⟨blockAddr, ()⟩ = true
              · simp only [recorded, ↓reduceIte]
                exact .refl _
              · simp only [recorded, Bool.false_eq_true, ↓reduceIte] at materialization ⊢
                cases parent : getConstVerified source blockAddr true with
                | error err => exact .refl _
                | ok optional =>
                    cases optional with
                    | none => exact .refl _
                    | some blockConstant =>
                        rw [parent] at materialization
                        have frame := ingressAnonBlock_cache source blockConstant blockAddr before
                          materialization
                        dsimp only [IngressM.liftExcept, Bind.bind, Pure.pure, EStateM.pure, EStateM.bind]
                        cases run : ingressAnonBlock source blockConstant blockAddr before <;>
                          rw [run] at frame <;> exact frame

/-- The callback is the production loader with integrity verification on.
An initial loaded hit needs no publication resource; an actual miss requires
agreement only for entries of the block that would be prepared. -/
structure VerifiedLazySupport (before : TcState .anon) (addr : Address) where
  source : Ixon.Env
  installed : before.lazyFault = some (fun address => ingressAnonAddrShallow source address true)
  materialization : before.env.get? ⟨addr, ()⟩ = none →
    LazyMaterializationSupport source addr before.env

def StandaloneLazySupport.toVerified {before : TcState .anon} {addr : Address}
    (support : StandaloneLazySupport before addr) : VerifiedLazySupport before addr := by
  refine ⟨support.source, support.installed, fun _ => ?_⟩
  have standalone := support.standalone
  unfold StandaloneMaterialization at standalone
  unfold LazyMaterializationSupport
  cases verified : getConstVerified support.source addr true with
  | error err => trivial
  | ok optional =>
      cases optional with
      | none => trivial
      | some constant =>
          rw [verified] at standalone
          cases info : constant.info <;> simp only [info] at standalone
          all_goals try contradiction
          all_goals simp only [info, ingressBlockAddr?]

/-- Direct fresh faults retain existing cache witnesses on every outcome,
including an address already recorded in the fault-deduplication set. -/
theorem lazyIngressAddr_verified_cache {before : TcState .anon} {addr : Address}
    (support : VerifiedLazySupport before addr)
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
    have frame := ingressAnonAddrShallow_verified_cache support.source addr before.env
      (support.materialization fresh) fresh
    cases run : ingressAnonAddrShallow support.source addr true before.env <;>
      rw [run] at frame <;> refine ⟨frame, ?_⟩ <;> simp only [support.installed]

/-- Try-lookup derives freshness from its own initial miss. Loaded hits,
verified source misses, conversion failures, and deduplicated faults all
retain the original cache entries and loaded declarations. -/
theorem tryGetConst_verified_cache {before : TcState .anon} {id : KId .anon}
    (support : VerifiedLazySupport before id.addr) :
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
      have frame := lazyIngressAddr_verified_cache support fresh
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
theorem getConst_verified_cache {before : TcState .anon} {id : KId .anon}
    (support : VerifiedLazySupport before id.addr) :
    match TcM.getConst id before with
    | .ok _ after | .error _ after => LazyLookupFrame before after := by
  unfold TcM.getConst
  change (match (EStateM.bind (TcM.tryGetConst id) _ : TcM .anon (KConst .anon)) before with
    | .ok _ after | .error _ after => LazyLookupFrame before after)
  have frame := tryGetConst_verified_cache support
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
def CachedConstantInferenceSupport.afterVerifiedGetConst {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {before after : TcState .anon} {id requested : KId .anon}
    {arguments : Array (KUniv .anon)} {info : ExprInfo .anon}
    {ref : ConstRef β} {entry : ConstantEntry β} {type : AExpr β} {concrete : KConst .anon}
    (support : CachedConstantInferenceSupport resolve entries before id arguments info ref entry type)
    (closed : (KExpr.const id arguments info).lbr = 0)
    (loader : VerifiedLazySupport before requested.addr)
    (run : TcM.getConst requested before = .ok concrete after) :
    CachedConstantInferenceSupport resolve entries after id arguments info ref entry type := by
  have frame := getConst_verified_cache loader
  rw [run] at frame
  exact support.transport closed (frame.cache _) frame.policy

/-- Failed loading retains the earlier witness even when conversion has
already changed the intern tables and the fault attempt remains recorded. -/
def CachedConstantInferenceSupport.afterFailedVerifiedGetConst {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {before after : TcState .anon} {id requested : KId .anon}
    {arguments : Array (KUniv .anon)} {info : ExprInfo .anon}
    {ref : ConstRef β} {entry : ConstantEntry β} {type : AExpr β} {err : TcError .anon}
    (support : CachedConstantInferenceSupport resolve entries before id arguments info ref entry type)
    (closed : (KExpr.const id arguments info).lbr = 0)
    (loader : VerifiedLazySupport before requested.addr)
    (run : TcM.getConst requested before = .error err after) :
    CachedConstantInferenceSupport resolve entries after id arguments info ref entry type := by
  have frame := getConst_verified_cache loader
  rw [run] at frame
  exact support.transport closed (frame.cache _) frame.policy

end Ix.Kernel.Consistency
