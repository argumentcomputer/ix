/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.WhnfGeneric

/-!
# The three WHNF cache layers under the generic contracts

`whnfCoreWithFlagsNonLeaf`, `whnfNoDeltaImplNonLeaf`, and
`whnfWithNatSuccModeNonLeaf` wrap their bounded loops with key computation,
the transient natural-literal check, a memo lookup, and a guarded
publication. Each layer is a generically sound reduction whenever its
uncached body is: a hit is served by the memo semantics, a miss runs the
body and publishes its generic result, and every failure inherits the
body's or the lookup's invariant. The transient check consults the
environment through the lazy loader, so it needs the per-lookup conversion
data that `RunAssumptions` supplies; hits need the identification of the
query with the recorded source, the collision resource of this library.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

section Data

variable {β : Type u} (resolve : Address → Option (ConstRef β))
  (anchor entries : Model.Environment β) (source : Ixon.Env)
  (catalog : List (SourceCacheRequest source))

/-- Conversion data for every lookup from an invariant state: the standalone
conversion resource of `RunAssumptions`, quantified over the run's states. -/
def LookupData : Prop :=
  ∀ (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (state : TcState .anon),
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
    ∀ addr, StandaloneConversionData source addr state.env

/-- Every WHNF memo entry consulted at a query with its key's address was
produced from that query. This is the key collision resource of the memo,
stated as the identification of the recorded source with the query. -/
def WhnfHitData : Prop :=
  ∀ (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (state : TcState .anon),
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
    ∀ (partition : WhnfCachePartition) (key : Address × Address) (result query : KExpr .anon),
      (partition.cache state)[key]? = some result → key.1 = query.addr →
      ∀ recorded : KExpr .anon, recorded.addr = query.addr →
        GenericReduction.{u,v} resolve entries recorded result → recorded = query

/-- Invariant preservation on both outcomes of a checker action. -/
def PreservesInvariant {α : Type} (action : TcM .anon α) : Prop :=
  ∀ (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (before : TcState .anon),
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before →
    match action before with
    | .ok _ after | .error _ after =>
        ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds after

end Data

section Combinators

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)}

namespace PreservesInvariant

theorem pure {α : Type} (value : α) :
    PreservesInvariant.{u,v} resolve anchor entries source catalog (Pure.pure value : TcM .anon α) :=
  fun _ _ _ _ valid => valid

theorem throw {α : Type} (error : TcError .anon) :
    PreservesInvariant.{u,v} resolve anchor entries source catalog (throw error : TcM .anon α) :=
  fun _ _ _ _ valid => valid

theorem bind {α γ : Type} {action : TcM .anon α} {next : α → TcM .anon γ}
    (first : PreservesInvariant.{u,v} resolve anchor entries source catalog action)
    (rest : ∀ value, PreservesInvariant.{u,v} resolve anchor entries source catalog (next value)) :
    PreservesInvariant.{u,v} resolve anchor entries source catalog (action >>= next) := by
  intro locals context bounds before valid
  have intermediate := first locals context bounds before valid
  change match EStateM.bind action next before with
    | .ok _ after | .error _ after =>
        ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds after
  cases run : action before with
  | error error after =>
      rw [EStateM.bind, run]
      simpa only [run] using intermediate
  | ok value after =>
      rw [run] at intermediate
      rw [EStateM.bind, run]
      exact rest value locals context bounds after intermediate

theorem get :
    PreservesInvariant.{u,v} resolve anchor entries source catalog (get : TcM .anon (TcState .anon)) :=
  fun _ _ _ _ valid => valid

theorem tryGetConst (lookups : LookupData.{u,v} resolve anchor entries source catalog) (id : KId .anon) :
    PreservesInvariant.{u,v} resolve anchor entries source catalog (TcM.tryGetConst id) := by
  intro locals context bounds before valid
  have post := valid.tryGetConst id (lookups locals context bounds before valid id.addr)
  cases run : TcM.tryGetConst id before <;> rw [run] at post <;> exact post

theorem getConst (lookups : LookupData.{u,v} resolve anchor entries source catalog) (id : KId .anon) :
    PreservesInvariant.{u,v} resolve anchor entries source catalog (TcM.getConst id) := by
  intro locals context bounds before valid
  have post := valid.getConst id (lookups locals context bounds before valid id.addr)
  cases run : TcM.getConst id before <;> rw [run] at post <;> exact post

/-- Any action whose two outcomes are given by cases can be closed by
inspecting the run. -/
theorem of_run {α : Type} {action : TcM .anon α}
    (run : ∀ (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
      (before : TcState .anon),
      ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before →
      ∀ after, (∃ value, action before = .ok value after) ∨ (∃ error, action before = .error error after) →
        ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds after) :
    PreservesInvariant.{u,v} resolve anchor entries source catalog action := by
  intro locals context bounds before valid
  cases outcome : action before with
  | ok value after => exact run locals context bounds before valid after (.inl ⟨value, outcome⟩)
  | error error after => exact run locals context bounds before valid after (.inr ⟨error, outcome⟩)

end PreservesInvariant

end Combinators

/-! ### The transient natural-literal check -/

section Transient

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {methods : Methods .anon}

theorem PreservesInvariant.prims :
    PreservesInvariant.{u,v} resolve anchor entries source catalog
      (ReaderT.run (RecM.prims : RecM .anon (Primitives .anon)) methods) :=
  fun _ _ _ _ valid => valid

theorem PreservesInvariant.runPure {α : Type} (value : α) :
    PreservesInvariant.{u,v} resolve anchor entries source catalog
      (ReaderT.run (Pure.pure value : RecM .anon α) methods) :=
  fun _ _ _ _ valid => valid

theorem isNatLiteralRecursorApp_preserves
    (lookups : LookupData.{u,v} resolve anchor entries source catalog) (term : KExpr .anon) :
    PreservesInvariant.{u,v} resolve anchor entries source catalog
      ((RecM.isNatLiteralRecursorApp term).run methods) := by
  unfold RecM.isNatLiteralRecursorApp
  cases spine : term.collectSpine with
  | mk head arguments =>
      cases head with
      | const id levels info =>
          dsimp only
          rw [ReaderT.run_bind]
          apply PreservesInvariant.bind PreservesInvariant.prims
          intro primitives
          split
          · exact PreservesInvariant.runPure _
          · rw [ReaderT.run_bind, ReaderT.run_monadLift]
            apply PreservesInvariant.bind (PreservesInvariant.tryGetConst lookups id)
            intro found
            split
            · split <;> exact PreservesInvariant.runPure _
            · exact PreservesInvariant.runPure _
      | _ => exact PreservesInvariant.runPure _

theorem isTransientNatLiteralWork_preserves
    (lookups : LookupData.{u,v} resolve anchor entries source catalog) (term : KExpr .anon) :
    PreservesInvariant.{u,v} resolve anchor entries source catalog
      ((RecM.isTransientNatLiteralWork term).run methods) := by
  unfold RecM.isTransientNatLiteralWork
  rw [ReaderT.run_bind]
  apply PreservesInvariant.bind (isNatLiteralRecursorApp_preserves lookups term)
  intro literal
  split
  · exact PreservesInvariant.runPure _
  · cases spine : term.collectSpine with
    | mk head arguments =>
        cases head with
        | const id levels info =>
            dsimp only
            rw [ReaderT.run_bind]
            apply PreservesInvariant.bind PreservesInvariant.prims
            intro primitives
            split
            · exact isNatLiteralRecursorApp_preserves lookups _
            · exact PreservesInvariant.runPure _
        | _ => exact PreservesInvariant.runPure _

end Transient

/-! ### Sequencing a body with its publication -/

section Sequencing

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {locals : List FVarId}
  {context : Model.Context β} {bounds : List VLevel}

/-- A body outcome followed by a continuation that, from the body's invariant
state and generic result, yields an outcome for the same input. -/
theorem ReductionOutcome.bind {input : KExpr .anon} {action : TcM .anon (KExpr .anon)}
    {next : KExpr .anon → TcM .anon (KExpr .anon)} {before : TcState .anon}
    (first : ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds input
      (action before))
    (rest : ∀ result middle,
      ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds middle →
      GenericReduction.{u,v} resolve entries input result →
      ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds input
        (next result middle)) :
    ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds input
      (EStateM.bind action next before) := by
  cases run : action before with
  | error error after =>
      rw [EStateM.bind, run]
      simpa only [run] using first
  | ok result after =>
      rw [run] at first
      rw [EStateM.bind, run]
      exact rest result after first.1 first.2

/-- A pure return of a generic result. -/
theorem ReductionOutcome.pure {input result : KExpr .anon} {state : TcState .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds state)
    (reduction : GenericReduction.{u,v} resolve entries input result) :
    ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds input
      (.ok result state) :=
  ⟨valid, reduction⟩

end Sequencing

/-! ### The structural layer -/

section Core

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {methods : Methods .anon}

private theorem get_run (state : TcState .anon) :
    (get : TcM .anon (TcState .anon)) state = .ok state state := rfl

/-- The key/transient/lookup/publication layer of structural WHNF is
generically sound whenever its bounded loop is. -/
theorem whnfCoreWithFlagsNonLeaf_sound
    (lookups : LookupData.{u,v} resolve anchor entries source catalog)
    (hits : WhnfHitData.{u,v} resolve anchor entries source catalog)
    (body : ∀ term flags, GenericSoundReduction.{u,v} resolve anchor entries source catalog term
      ((RecM.whnfCoreWithFlagsUncached term flags).run methods))
    (term : KExpr .anon) (flags : WhnfFlags) :
    GenericSoundReduction.{u,v} resolve anchor entries source catalog term
      ((RecM.whnfCoreWithFlagsNonLeaf term flags).run methods) := by
  intro locals context bounds before reading valid reads typed
  unfold RecM.whnfCoreWithFlagsNonLeaf
  rw [ReaderT.run_bind]
  change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
    (EStateM.bind (TcM.whnfKey term) _ before)
  rw [EStateM.bind, betaWhnfKey_run]
  have keyed := valid.whnfKey term
  have address : (betaWhnfKey term before).1.1 = term.addr := betaWhnfKey_address term before
  generalize (betaWhnfKey term before).1 = key at address ⊢
  generalize (betaWhnfKey term before).2 = keyedState at keyed ⊢
  dsimp only
  rw [ReaderT.run_bind]
  change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
    (EStateM.bind ((RecM.isTransientNatLiteralWork term).run methods) _ keyedState)
  have transient := isTransientNatLiteralWork_preserves (methods := methods) lookups term
    locals context bounds keyedState keyed
  cases transientRun : (RecM.isTransientNatLiteralWork term).run methods keyedState with
  | error error failed =>
      rw [EStateM.bind, transientRun]
      simp only [transientRun] at transient
      exact transient
  | ok transientWork checked =>
      rw [transientRun] at transient
      simp only [] at transient
      rw [EStateM.bind, transientRun]
      dsimp only
      cases full : flags.isFull <;> cases transientWork <;>
        simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      · -- cheap partition, lookup then publication
        rw [ReaderT.run_bind]
        change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
          (EStateM.bind (get : TcM .anon (TcState .anon)) _ checked)
        rw [EStateM.bind, get_run]
        dsimp only
        cases lookup : checked.env.whnfCoreCheapCache[key]? with
        | some cached =>
            exact ReductionOutcome.pure transient (transient.semantics.whnf.hit (partition := .coreCheap)
              lookup address (hits locals context bounds checked transient .coreCheap key cached term lookup address))
        | none =>
            rw [ReaderT.run_bind]
            change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
              (EStateM.bind ((RecM.whnfCoreWithFlagsUncached term flags).run methods) _ checked)
            apply ReductionOutcome.bind (body term flags locals context bounds checked reading transient reads typed)
            intro result reduced valid' reduction
            exact ReductionOutcome.pure (valid'.publishCoreCheap address.symm reduction) reduction
      · -- cheap partition, transient work: no lookup, no publication
        rw [ReaderT.run_bind]
        change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
          (EStateM.bind ((RecM.whnfCoreWithFlagsUncached term flags).run methods) _ checked)
        apply ReductionOutcome.bind (body term flags locals context bounds checked reading transient reads typed)
        intro result reduced valid' reduction
        exact ReductionOutcome.pure valid' reduction
      · -- full partition, lookup then publication
        rw [ReaderT.run_bind]
        change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
          (EStateM.bind (get : TcM .anon (TcState .anon)) _ checked)
        rw [EStateM.bind, get_run]
        dsimp only
        cases lookup : checked.env.whnfCoreCache[key]? with
        | some cached =>
            exact ReductionOutcome.pure transient (transient.semantics.whnf.hit (partition := .core)
              lookup address (hits locals context bounds checked transient .core key cached term lookup address))
        | none =>
            rw [ReaderT.run_bind]
            change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
              (EStateM.bind ((RecM.whnfCoreWithFlagsUncached term flags).run methods) _ checked)
            apply ReductionOutcome.bind (body term flags locals context bounds checked reading transient reads typed)
            intro result reduced valid' reduction
            exact ReductionOutcome.pure (valid'.publishCore address.symm reduction) reduction
      · -- full partition, transient work
        rw [ReaderT.run_bind]
        change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
          (EStateM.bind ((RecM.whnfCoreWithFlagsUncached term flags).run methods) _ checked)
        apply ReductionOutcome.bind (body term flags locals context bounds checked reading transient reads typed)
        intro result reduced valid' reduction
        exact ReductionOutcome.pure valid' reduction

end Core

/-! ### The no-delta layer -/

section NoDelta

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {methods : Methods .anon}

private theorem get_run' (state : TcState .anon) :
    (get : TcM .anon (TcState .anon)) state = .ok state state := rfl

private theorem collapse_beq : (NatSuccMode.collapse == NatSuccMode.collapse) = true := rfl
private theorem stuck_beq : (NatSuccMode.stuck == NatSuccMode.collapse) = false := rfl

/-- The key/transient/lookup/publication layer of no-delta WHNF is
generically sound whenever its bounded loop is. Only the collapsing mode
consults or publishes the memo, and publication is suppressed inside native
reduction and for transient natural-literal work. -/
theorem whnfNoDeltaImplNonLeaf_sound
    (lookups : LookupData.{u,v} resolve anchor entries source catalog)
    (hits : WhnfHitData.{u,v} resolve anchor entries source catalog)
    (body : ∀ term flags mode, GenericSoundReduction.{u,v} resolve anchor entries source catalog term
      ((RecM.whnfNoDeltaImplUncached term flags mode).run methods))
    (term : KExpr .anon) (flags : WhnfFlags) (mode : NatSuccMode) :
    GenericSoundReduction.{u,v} resolve anchor entries source catalog term
      ((RecM.whnfNoDeltaImplNonLeaf term flags mode).run methods) := by
  intro locals context bounds before reading valid reads typed
  unfold RecM.whnfNoDeltaImplNonLeaf
  rw [ReaderT.run_bind]
  change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
    (EStateM.bind (TcM.whnfKey term) _ before)
  rw [EStateM.bind, betaWhnfKey_run]
  have keyed := valid.whnfKey term
  have address : (betaWhnfKey term before).1.1 = term.addr := betaWhnfKey_address term before
  generalize (betaWhnfKey term before).1 = key at address ⊢
  generalize (betaWhnfKey term before).2 = keyedState at keyed ⊢
  dsimp only
  rw [ReaderT.run_bind]
  change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
    (EStateM.bind ((RecM.isTransientNatLiteralWork term).run methods) _ keyedState)
  have transient := isTransientNatLiteralWork_preserves (methods := methods) lookups term
    locals context bounds keyedState keyed
  cases transientRun : (RecM.isTransientNatLiteralWork term).run methods keyedState with
  | error error failed =>
      rw [EStateM.bind, transientRun]
      simp only [transientRun] at transient
      exact transient
  | ok transientWork checked =>
      rw [transientRun] at transient
      simp only [] at transient
      rw [EStateM.bind, transientRun]
      dsimp only
      cases mode <;> cases transientWork <;>
        simp only [collapse_beq, stuck_beq, Bool.not_false, Bool.not_true, Bool.and_false,
          Bool.and_true, Bool.false_eq_true, ↓reduceIte]
      · -- collapse, non-transient: lookup and guarded publication
        split <;> rename_i full
        · rw [ReaderT.run_bind]
          change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
            (EStateM.bind (get : TcM .anon (TcState .anon)) _ checked)
          rw [EStateM.bind, get_run']
          dsimp only
          cases lookup : checked.env.whnfNoDeltaCache[key]? with
          | some cached =>
              exact ReductionOutcome.pure transient (transient.semantics.whnf.hit (partition := .noDelta)
                lookup address (hits locals context bounds checked transient .noDelta key cached term
                  lookup address))
          | none =>
              rw [ReaderT.run_bind]
              change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds
                term (EStateM.bind ((RecM.whnfNoDeltaImplUncached term flags .collapse).run methods) _ checked)
              apply ReductionOutcome.bind
                (body term flags .collapse locals context bounds checked reading transient reads typed)
              intro result reduced valid' reduction
              rw [ReaderT.run_bind]
              change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds
                term (EStateM.bind (get : TcM .anon (TcState .anon)) _ reduced)
              rw [EStateM.bind, get_run']
              dsimp only
              split
              · exact ReductionOutcome.pure (valid'.publishNoDelta address.symm reduction) reduction
              · exact ReductionOutcome.pure valid' reduction
        · rw [ReaderT.run_bind]
          change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
            (EStateM.bind (get : TcM .anon (TcState .anon)) _ checked)
          rw [EStateM.bind, get_run']
          dsimp only
          cases lookup : checked.env.whnfNoDeltaCheapCache[key]? with
          | some cached =>
              exact ReductionOutcome.pure transient (transient.semantics.whnf.hit (partition := .noDeltaCheap)
                lookup address (hits locals context bounds checked transient .noDeltaCheap key cached term
                  lookup address))
          | none =>
              rw [ReaderT.run_bind]
              change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds
                term (EStateM.bind ((RecM.whnfNoDeltaImplUncached term flags .collapse).run methods) _ checked)
              apply ReductionOutcome.bind
                (body term flags .collapse locals context bounds checked reading transient reads typed)
              intro result reduced valid' reduction
              rw [ReaderT.run_bind]
              change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds
                term (EStateM.bind (get : TcM .anon (TcState .anon)) _ reduced)
              rw [EStateM.bind, get_run']
              dsimp only
              split
              · exact ReductionOutcome.pure (valid'.publishNoDeltaCheap address.symm reduction) reduction
              · exact ReductionOutcome.pure valid' reduction
      all_goals
        rw [ReaderT.run_bind]
        change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
          (EStateM.bind ((RecM.whnfNoDeltaImplUncached term flags _).run methods) _ checked)
        apply ReductionOutcome.bind
          (body term flags _ locals context bounds checked reading transient reads typed)
        intro result reduced valid' reduction
        rw [ReaderT.run_bind]
        change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
          (EStateM.bind (get : TcM .anon (TcState .anon)) _ reduced)
        rw [EStateM.bind, get_run']
        exact ReductionOutcome.pure valid' reduction

end NoDelta

/-! ### The full layer -/

section Full

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {locals : List FVarId}
  {context : Model.Context β} {bounds : List VLevel} {methods : Methods .anon}

/-- The optional miss counter bump. -/
def betaWhnfBump (before : TcState .anon) : TcState .anon :=
  if before.stats then { before with whnfMisses := before.whnfMisses + 1 } else before

theorem betaWhnfBump_run (before : TcState .anon) :
    TcM.bumpStats (fun state => { state with whnfMisses := state.whnfMisses + 1 }) before =
      .ok () (betaWhnfBump before) := by
  unfold TcM.bumpStats betaWhnfBump
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ before = _
  simp only [EStateM.bind, show (get : TcM .anon (TcState .anon)) before = .ok before before from rfl]
  split <;> rfl

theorem tick_run (before : TcState .anon) :
    TcM.tick before = if (before.recFuel == 0) = true then .error .maxRecFuel before
      else .ok () { before with recFuel := before.recFuel - 1 } := by
  unfold TcM.tick
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ before = _
  simp only [EStateM.bind, show (get : TcM .anon (TcState .anon)) before = .ok before before from rfl]
  split <;> rfl

theorem ReductionInvariant.bump {before : TcState .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before) :
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      (betaWhnfBump before) := by
  unfold betaWhnfBump
  split
  · exact valid.ofMaps ⟨Nat.le_refl _, .refl _, rfl⟩ rfl rfl valid.coherent rfl rfl
      (fun partition => by cases partition <;> rfl) (fun partition => by cases partition <;> rfl)
      rfl rfl rfl rfl
  · exact valid

theorem ReductionInvariant.tick {before : TcState .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before) :
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      { before with recFuel := before.recFuel - 1 } :=
  valid.ofMaps ⟨Nat.le_refl _, .refl _, rfl⟩ rfl rfl valid.coherent rfl rfl
    (fun partition => by cases partition <;> rfl) (fun partition => by cases partition <;> rfl)
    rfl rfl rfl rfl

/-- The miss charge bumps the optional counter, then ticks. -/
theorem whnfWithNatSuccModeMissCharge_run (before : TcState .anon) :
    (RecM.whnfWithNatSuccModeMissCharge : RecM .anon Unit).run methods before =
      if ((betaWhnfBump before).recFuel == 0) = true then .error .maxRecFuel (betaWhnfBump before)
      else .ok () { betaWhnfBump before with recFuel := (betaWhnfBump before).recFuel - 1 } := by
  unfold RecM.whnfWithNatSuccModeMissCharge
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.bumpStats (fun state => { state with whnfMisses := state.whnfMisses + 1 }))
    (fun _ => TcM.tick) before = _
  rw [EStateM.bind, betaWhnfBump_run]
  exact tick_run _

/-- The miss charge preserves the invariant on both outcomes: exhausted fuel
fails after the optional counter bump. -/
theorem whnfWithNatSuccModeMissCharge_preserves :
    PreservesInvariant.{u,v} resolve anchor entries source catalog
      ((RecM.whnfWithNatSuccModeMissCharge : RecM .anon Unit).run methods) := by
  intro locals context bounds before valid
  rw [whnfWithNatSuccModeMissCharge_run]
  by_cases exhausted : ((betaWhnfBump before).recFuel == 0) = true
  · rw [if_pos exhausted]
    exact valid.bump
  · rw [if_neg exhausted]
    exact valid.bump.tick

private theorem get_run'' (state : TcState .anon) :
    (get : TcM .anon (TcState .anon)) state = .ok state state := rfl

private theorem collapse_beq' : (NatSuccMode.collapse == NatSuccMode.collapse) = true := rfl
private theorem stuck_beq' : (NatSuccMode.stuck == NatSuccMode.collapse) = false := rfl

/-- The instrumented full-WHNF layer is generically sound whenever its
bounded loop is. The memo is consulted and published only in the collapsing
mode, outside native reduction, and for non-transient work. -/
theorem whnfWithNatSuccModeNonLeaf_sound
    (lookups : LookupData.{u,v} resolve anchor entries source catalog)
    (hits : WhnfHitData.{u,v} resolve anchor entries source catalog)
    (body : ∀ term mode, GenericSoundReduction.{u,v} resolve anchor entries source catalog term
      ((RecM.whnfWithNatSuccModeUncached term mode).run methods))
    (term : KExpr .anon) (mode : NatSuccMode) :
    GenericSoundReduction.{u,v} resolve anchor entries source catalog term
      ((RecM.whnfWithNatSuccModeNonLeaf term mode).run methods) := by
  intro locals context bounds before reading valid reads typed
  unfold RecM.whnfWithNatSuccModeNonLeaf
  rw [ReaderT.run_bind]
  change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
    (EStateM.bind ((RecM.whnfWithNatSuccModePrefix term).run methods) _ before)
  rw [EStateM.bind, betaWhnfPrefix_run]
  have instrumented := valid.instrument
  generalize betaWhnfPrefix before = traced at instrumented ⊢
  dsimp only
  rw [ReaderT.run_bind]
  change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
    (EStateM.bind (TcM.whnfKey term) _ traced)
  rw [EStateM.bind, betaWhnfKey_run]
  have keyed := instrumented.whnfKey term
  have address : (betaWhnfKey term traced).1.1 = term.addr := betaWhnfKey_address term traced
  generalize (betaWhnfKey term traced).1 = key at address ⊢
  generalize (betaWhnfKey term traced).2 = keyedState at keyed ⊢
  dsimp only
  rw [ReaderT.run_bind]
  change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
    (EStateM.bind ((RecM.isTransientNatLiteralWork term).run methods) _ keyedState)
  have transient := isTransientNatLiteralWork_preserves (methods := methods) lookups term
    locals context bounds keyedState keyed
  cases transientRun : (RecM.isTransientNatLiteralWork term).run methods keyedState with
  | error error failed =>
      rw [EStateM.bind, transientRun]
      simp only [transientRun] at transient
      exact transient
  | ok transientWork checked =>
      rw [transientRun] at transient
      simp only [] at transient
      rw [EStateM.bind, transientRun]
      dsimp only
      have miss : ∀ (guard : TcState .anon → Bool) (state : TcState .anon),
          ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
          ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
            (EStateM.bind ((RecM.whnfWithNatSuccModeMissCharge : RecM .anon Unit).run methods)
              (fun _ => ReaderT.run (do
                let cur ← RecM.whnfWithNatSuccModeUncached term mode
                let current ← get
                if guard current then
                  modify fun s => { s with env := { s.env with
                    whnfCache := s.env.whnfCache.insert key cur } }
                pure cur) methods) state) := by
        intro guard state valid
        have charged := whnfWithNatSuccModeMissCharge_preserves (methods := methods)
          locals context bounds state valid
        cases chargeRun : (RecM.whnfWithNatSuccModeMissCharge : RecM .anon Unit).run methods state with
        | error error failed =>
            rw [EStateM.bind, chargeRun]
            simp only [chargeRun] at charged
            exact charged
        | ok _ charging =>
            rw [chargeRun] at charged
            simp only [] at charged
            rw [EStateM.bind, chargeRun]
            rw [ReaderT.run_bind]
            change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
              (EStateM.bind ((RecM.whnfWithNatSuccModeUncached term mode).run methods) _ charging)
            apply ReductionOutcome.bind
              (body term mode locals context bounds charging reading charged reads typed)
            intro result reduced valid' reduction
            rw [ReaderT.run_bind]
            change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
              (EStateM.bind (get : TcM .anon (TcState .anon)) _ reduced)
            rw [EStateM.bind, get_run'']
            dsimp only
            split
            · exact ReductionOutcome.pure (valid'.publishFull address.symm reduction) reduction
            · exact ReductionOutcome.pure valid' reduction
      cases mode <;> cases transientWork <;>
        simp only [collapse_beq', stuck_beq', Bool.not_false, Bool.not_true, Bool.and_false,
          Bool.and_true, Bool.false_eq_true, ↓reduceIte]
      · -- collapse, non-transient: lookup, then charge and guarded publication
        rw [ReaderT.run_bind]
        change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
          (EStateM.bind (get : TcM .anon (TcState .anon)) _ checked)
        rw [EStateM.bind, get_run'']
        dsimp only
        cases lookup : checked.env.whnfCache[key]? with
        | some cached =>
            exact ReductionOutcome.pure transient (transient.semantics.whnf.hit (partition := .full)
              lookup address (hits locals context bounds checked transient .full key cached term
                lookup address))
        | none =>
            rw [ReaderT.run_bind]
            exact miss (fun current => !current.inNativeReduce) checked transient
      all_goals
        rw [ReaderT.run_bind]
        change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
          (EStateM.bind ((RecM.whnfWithNatSuccModeMissCharge : RecM .anon Unit).run methods) _ checked)
        have charged := whnfWithNatSuccModeMissCharge_preserves (methods := methods)
          locals context bounds checked transient
        cases chargeRun : (RecM.whnfWithNatSuccModeMissCharge : RecM .anon Unit).run methods checked with
        | error error failed =>
            rw [EStateM.bind, chargeRun]
            simp only [chargeRun] at charged
            exact charged
        | ok _ charging =>
            rw [chargeRun] at charged
            simp only [] at charged
            rw [EStateM.bind, chargeRun]
            rw [ReaderT.run_bind]
            change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
              (EStateM.bind ((RecM.whnfWithNatSuccModeUncached term _).run methods) _ charging)
            apply ReductionOutcome.bind
              (body term _ locals context bounds charging reading charged reads typed)
            intro result reduced valid' reduction
            rw [ReaderT.run_bind]
            change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds term
              (EStateM.bind (get : TcM .anon (TcState .anon)) _ reduced)
            rw [EStateM.bind, get_run'']
            exact ReductionOutcome.pure valid' reduction

end Full

end Ix.Kernel.Consistency
