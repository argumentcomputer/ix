/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Contracts
import Ix.Kernel.Verify.Consistency.BetaWhnfState

/-!
# Scope-generic reduction contracts and the reduction invariant

The reduction contracts of `Contracts.lean` state a memo hit at the scope of
the caller, but every WHNF memo is keyed by address alone once binders are
opened through free variables, so a hit may be served in a scope other than
the one that produced it. Semantic conversion at one scope does not transport
to another (a scope may hypothesize an empty type), so a per-entry memo
invariant must be stated for every scope at once. `GenericReduction`
(in `Invariant.lean`) is that statement, and `GenericSoundReduction` is the
contract whose successful outcomes are generic; it implies the scoped
`ReductionPost` conversion clause at any scope.

Two further departures from `CheckerInvariant` are forced by the production
code. Its WHNF history field admits only beta, let, and head-call
publications, so a delta result cannot be published under it;
`ReductionInvariant` keeps every other field and replaces the history by the
semantic memo agreement. Its acceleration flag is a run configuration, so the
invariant records `noAccel = true` and every operation preserves it. The
bounded loop driver is treated once, over any loop state with a term view,
covering the structural loop and the `(term, seen)` state of the full loop.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-! ### The reduction invariant -/

/-- `CheckerInvariant` without its beta-only WHNF history, plus the
acceleration configuration. -/
structure ReductionInvariant {β : Type u} (resolve : Address → Option (ConstRef β))
    (anchor entries : Model.Environment β) (source : Ixon.Env)
    (catalog : List (SourceCacheRequest source)) (locals : List FVarId)
    (context : Model.Context β) (bounds : List VLevel) (state : TcState .anon) : Prop where
  sourceCache : SourceCacheInvariant catalog state
  synthesis : Nonempty (SynthesisCacheHistory resolve anchor entries state)
  structural : LocalStateInvariant state
  reading : LocalContextReading resolve locals state.lctx context
  origin : Nonempty (SynthesisContext resolve anchor [] [] entries context bounds)
  semantics : ReductionCacheSemantics.{u,v} resolve entries state
  accelerationsOff : state.noAccel = true

namespace ReductionInvariant

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {locals : List FVarId}
  {context : Model.Context β} {bounds : List VLevel}

theorem ofChecker {state : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state)
    (off : state.noAccel = true) :
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds state :=
  ⟨valid.sourceCache, valid.synthesis, valid.structural, valid.reading, valid.origin,
    valid.semantics, off⟩

section Projections

variable {state : TcState .anon}
  (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds state)
include valid

theorem sourceState : SourceStateInvariant source state := valid.sourceCache.state

theorem inference : InferenceStateInvariant source state := valid.sourceCache.state.state

theorem coherent : state.env.intern.WF := valid.inference.coherent

theorem installed :
    state.lazyFault = some (fun addr => ingressAnonAddrShallow source addr true) :=
  valid.inference.installed

def owned : OwnedLazySupport state := valid.inference.owned

theorem cache : SourceCacheAgreement catalog state := valid.sourceCache.cache

end Projections

/-- Operations that retain every map, the loaded declarations, coherence,
the acceleration flag, and the local context up to lookup equivalence. -/
theorem ofMaps {before after : TcState .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
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
    (isProp : after.env.isPropCache = before.env.isPropCache)
    (off : after.noAccel = before.noAccel) :
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds after where
  sourceCache := ⟨valid.sourceState.ofMaps frame.loader constants blocks coherent,
    valid.cache.ofMaps full only constants⟩
  synthesis := valid.synthesis.elim fun history => ⟨history.ofMaps full only⟩
  structural := frame.invariant valid.structural
  reading := valid.reading.congr frame.context.symm
  origin := valid.origin
  semantics := valid.semantics.ofMaps whnf defEq manager unfold isProp
  accelerationsOff := off.trans valid.accelerationsOff

/-- A new intern table is the only change of an intern-only operation. -/
theorem ofIntern {before : TcState .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    {table : InternTable .anon} (coherent : table.WF) :
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      {before with env := {before.env with intern := table}} :=
  valid.ofMaps ⟨Nat.le_refl _, .refl _, rfl⟩ rfl rfl coherent rfl rfl
    (fun partition => by cases partition <;> rfl) (fun partition => by cases partition <;> rfl)
    rfl rfl rfl rfl

theorem ofCtxAddrCache {before : TcState .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (memo : Std.HashMap (Address × UInt64) Address) :
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      {before with ctxAddrCache := memo} :=
  valid.ofMaps ⟨Nat.le_refl _, .refl _, rfl⟩ rfl rfl valid.coherent rfl rfl
    (fun partition => by cases partition <;> rfl) (fun partition => by cases partition <;> rfl)
    rfl rfl rfl rfl

theorem whnfKey {before : TcState .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (term : KExpr .anon) :
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      (betaWhnfKey term before).2 := by
  have keyed := whnfKey_state (betaWhnfKey_run term before)
  rw [keyed]
  exact valid.ofCtxAddrCache _

/-- The full-WHNF instrumentation prefix and miss charge touch only counters
and the shared fuel. -/
theorem instrument {before : TcState .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before) :
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      (betaWhnfPrefix before) := by
  unfold betaWhnfPrefix
  split
  · exact valid.ofMaps ⟨Nat.le_refl _, .refl _, rfl⟩ rfl rfl valid.coherent rfl rfl
      (fun partition => by cases partition <;> rfl) (fun partition => by cases partition <;> rfl)
      rfl rfl rfl rfl
  · exact valid

theorem charge {before : TcState .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before) :
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      (betaWhnfCharge before) := by
  unfold betaWhnfCharge
  split <;> exact valid.ofMaps ⟨Nat.le_refl _, .refl _, rfl⟩ rfl rfl valid.coherent rfl rfl
    (fun partition => by cases partition <;> rfl) (fun partition => by cases partition <;> rfl)
    rfl rfl rfl rfl

private theorem afterLookup {before after : TcState .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (sourceCache : SourceCacheInvariant catalog after)
    (synthesis : Nonempty (SynthesisCacheHistory resolve anchor entries after))
    (frame : LazyLookupFrame before after) (ingress : KEnv.IngressFrame before.env after.env)
    (structural : LocalStateFrame before after) :
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds after := by
  obtain ⟨consts, blocks, intern, envEq⟩ := ingress
  have checker := frame.checker
  exact {
    sourceCache, synthesis
    structural := structural.invariant valid.structural
    reading := valid.reading.congr structural.context.symm
    origin := valid.origin
    semantics := valid.semantics.ofMaps
      (fun partition => by cases partition <;> simp only [WhnfCachePartition.cache, envEq])
      (fun partition => by cases partition <;> simp only [DefEqCachePartition.cache, envEq])
      (by rw [checker]) (by rw [envEq]) (by rw [envEq])
    accelerationsOff := by rw [checker]; exact valid.accelerationsOff }

/-- Lookup retains the invariant on both outcomes. -/
theorem getConst {before : TcState .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (id : KId .anon) (data : StandaloneConversionData source id.addr before.env) :
    match TcM.getConst id before with
    | .ok _ after | .error _ after =>
        ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds after := by
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

/-- `getConst` is `tryGetConst` followed by a pure match, so the invariant
after a `tryGetConst` outcome is the invariant after the matching `getConst`
outcome. -/
theorem tryGetConst {before : TcState .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (id : KId .anon) (data : StandaloneConversionData source id.addr before.env) :
    match TcM.tryGetConst id before with
    | .ok _ after | .error _ after =>
        ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds after := by
  have post := valid.getConst id data
  unfold TcM.getConst at post
  change (match (EStateM.bind (TcM.tryGetConst id) _ : TcM .anon (KConst .anon)) before with
    | .ok _ after | .error _ after =>
        ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds after) at post
  cases tried : TcM.tryGetConst id before with
  | error err after =>
      rw [EStateM.bind, tried] at post
      exact post
  | ok optional after =>
      rw [EStateM.bind, tried] at post
      cases optional <;> exact post

end ReductionInvariant

/-! ### The generic contracts -/

section Contracts

variable {β : Type u} (resolve : Address → Option (ConstRef β))
  (anchor entries : Model.Environment β) (source : Ixon.Env)
  (catalog : List (SourceCacheRequest source))

/-- One reduction outcome from an invariant state: the invariant holds
afterwards, and a successful result is a scope-generic reduction of the input. -/
def ReductionOutcome (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (input : KExpr .anon) :
    EStateM.Result (TcError .anon) (TcState .anon) (KExpr .anon) → Prop
  | .ok result after =>
      ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds after ∧
      GenericReduction.{u,v} resolve entries input result
  | .error _ after =>
      ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds after

/-- The scope-generic reduction contract of one call. -/
def GenericSoundReduction (input : KExpr .anon) (action : TcM .anon (KExpr .anon)) : Prop :=
  ∀ (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (before : TcState .anon) (term : AExpr β),
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before →
    readScopedExpr? resolve locals input = some term.erase →
    (∃ type, CheckedTyping.{u,v} entries context term type) →
    ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds input
      (action before)

/-- One iteration outcome of a bounded loop whose state has a term view. -/
def StepOutcome {σ : Type} (view : σ → KExpr .anon) (locals : List FVarId)
    (context : Model.Context β) (bounds : List VLevel) (current : σ) :
    EStateM.Result (TcError .anon) (TcState .anon) (RecM.BoundedStep σ (KExpr .anon)) → Prop
  | .ok (.next next) after =>
      ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds after ∧
      GenericReduction.{u,v} resolve entries (view current) (view next)
  | .ok (.done result) after =>
      ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds after ∧
      GenericReduction.{u,v} resolve entries (view current) result
  | .error _ after =>
      ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds after

/-- A loop step is sound when, from an invariant state whose current term
reads to a checked annotated term, it continues or finishes with a generic
reduction of the current term, or fails with the invariant. -/
def SoundStep {σ : Type} (view : σ → KExpr .anon)
    (step : σ → TcM .anon (RecM.BoundedStep σ (KExpr .anon))) : Prop :=
  ∀ (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (before : TcState .anon) (term : AExpr β) (current : σ),
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before →
    readScopedExpr? resolve locals (view current) = some term.erase →
    (∃ type, CheckedTyping.{u,v} entries context term type) →
    StepOutcome.{u,v} resolve anchor entries source catalog view locals context bounds current
      (step current before)

/-- One probe outcome: absence and errors preserve the invariant, and a
produced expression is a generic reduction of the input. -/
def ReducerOutcome (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (input : KExpr .anon) :
    EStateM.Result (TcError .anon) (TcState .anon) (Option (KExpr .anon)) → Prop
  | .ok none after =>
      ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds after
  | .ok (some reduced) after =>
      ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds after ∧
      GenericReduction.{u,v} resolve entries input reduced
  | .error _ after =>
      ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds after

/-- A reducer probe is sound when every outcome from an invariant state on a
readable checked input satisfies `ReducerOutcome`. -/
def SoundReducer (probe : KExpr .anon → TcM .anon (Option (KExpr .anon))) : Prop :=
  ∀ (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (before : TcState .anon) (term : AExpr β) (input : KExpr .anon),
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before →
    readScopedExpr? resolve locals input = some term.erase →
    (∃ type, CheckedTyping.{u,v} entries context term type) →
    ReducerOutcome.{u,v} resolve anchor entries source catalog locals context bounds input
      (probe input before)

/-- The four reduction fields of a method table, generically sound. -/
structure GenericWhnfContract (methods : Methods .anon) : Prop where
  whnf : ∀ term, GenericSoundReduction.{u,v} resolve anchor entries source catalog term
    (methods.whnf term)
  whnfCore : ∀ term, GenericSoundReduction.{u,v} resolve anchor entries source catalog term
    (methods.whnfCore term)
  whnfMode : ∀ term mode, GenericSoundReduction.{u,v} resolve anchor entries source catalog term
    (methods.whnfMode term mode)
  whnfCoreFlags : ∀ term flags, GenericSoundReduction.{u,v} resolve anchor entries source catalog term
    (methods.whnfCoreFlags term flags)

end Contracts

/-! ### Composition of generic reductions -/

section Generic

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}

theorem GenericReduction.refl (source : KExpr .anon) :
    GenericReduction.{u,v} resolve entries source source :=
  fun _ _ term reads _ => ⟨term, reads, .refl _, fun _ checked => checked⟩

theorem GenericReduction.trans {a b c : KExpr .anon}
    (first : GenericReduction.{u,v} resolve entries a b)
    (second : GenericReduction.{u,v} resolve entries b c) :
    GenericReduction.{u,v} resolve entries a c := by
  intro locals context term reads typed
  obtain ⟨middle, readsMiddle, converted, preserved⟩ := first locals context term reads typed
  obtain ⟨type, checked⟩ := typed
  obtain ⟨target, readsTarget, converted', preserved'⟩ :=
    second locals context middle readsMiddle ⟨type, preserved type checked⟩
  exact ⟨target, readsTarget, converted.trans converted',
    fun type checked => preserved' type (preserved type checked)⟩

/-- A generic reduction of a readable checked source, at any scope, retains
every semantic type of the source: the reduct is denoted, since it is
checked, and interprets equally. -/
theorem GenericReduction.typing {source result : KExpr .anon}
    (reduction : GenericReduction.{u,v} resolve entries source result)
    {locals : List FVarId} {context : Model.Context β} {term : AExpr β}
    (reads : readScopedExpr? resolve locals source = some term.erase)
    (typed : ∃ type, CheckedTyping.{u,v} entries context term type) :
    ∃ target : AExpr β, readScopedExpr? resolve locals result = some target.erase ∧
      ConversionClaim.{u,v} entries context term target ∧
      ∀ type, TypingClaim.{u,v} entries context term type →
        TypingClaim.{u,v} entries context target type := by
  obtain ⟨target, readsTarget, converted, preserved⟩ := reduction locals context term reads typed
  refine ⟨target, readsTarget, converted, ?_⟩
  obtain ⟨checkedType, checked⟩ := typed
  have targetTyped := (preserved checkedType checked).typing
  intro type sourceTyped V _ constants realizes levels env valid
  obtain ⟨_, typeValid, member⟩ := sourceTyped V constants realizes levels env valid
  exact ⟨(targetTyped V constants realizes levels env valid).1, typeValid,
    converted V constants realizes levels env valid ▸ member⟩

end Generic

/-! ### Contract combinators -/

section Combinators

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)}

theorem GenericSoundReduction.throw {input : KExpr .anon} {error : TcError .anon} :
    GenericSoundReduction.{u,v} resolve anchor entries source catalog input (throw error) :=
  fun _ _ _ _ _ valid _ _ => valid

theorem GenericSoundReduction.pure {input : KExpr .anon} :
    GenericSoundReduction.{u,v} resolve anchor entries source catalog input (pure input) :=
  fun _ _ _ _ _ valid _ _ => ⟨valid, .refl _⟩

/-- The exhausted table fails every reduction call without touching the state. -/
theorem GenericWhnfContract.zero :
    GenericWhnfContract.{u,v} resolve anchor entries source catalog (methodsN 0) where
  whnf := fun _ => GenericSoundReduction.throw
  whnfCore := fun _ => GenericSoundReduction.throw
  whnfMode := fun _ _ => GenericSoundReduction.throw
  whnfCoreFlags := fun _ _ => GenericSoundReduction.throw

/-- The scoped conversion clause of `ReductionPost` follows from a generic
outcome at any scope whose reading is checked. -/
theorem ReductionOutcome.scoped {locals : List FVarId} {context : Model.Context β}
    {bounds : List VLevel} {input result : KExpr .anon} {after : TcState .anon} {term : AExpr β}
    (outcome : ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds input
      (.ok result after))
    (reads : readScopedExpr? resolve locals input = some term.erase)
    (typed : ∃ type, CheckedTyping.{u,v} entries context term type) :
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds after ∧
      ∃ target : AExpr β, readScopedExpr? resolve locals result = some target.erase ∧
        ConversionClaim.{u,v} entries context term target ∧
        ∀ type, TypingClaim.{u,v} entries context term type →
          TypingClaim.{u,v} entries context target type :=
  ⟨outcome.1, outcome.2.typing reads typed⟩

end Combinators

/-! ### Memo hits and publications -/

section Memo

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {locals : List FVarId}
  {context : Model.Context β} {bounds : List VLevel}

/-- A stored WHNF result serves any query with the key's address, once the
query is identified with the recorded source. The identification premise is
the collision resource of this hit; a run inventory of memo sources would
discharge it from `RunAssumptions`. -/
theorem WhnfCacheSemantics.hit {state : TcState .anon}
    (valid : WhnfCacheSemantics.{u,v} resolve entries state) {partition : WhnfCachePartition}
    {key : Address × Address} {result query : KExpr .anon}
    (found : (partition.cache state)[key]? = some result) (address : key.1 = query.addr)
    (faithful : ∀ source : KExpr .anon, source.addr = query.addr →
      GenericReduction.{u,v} resolve entries source result → source = query) :
    GenericReduction.{u,v} resolve entries query result := by
  obtain ⟨recorded, recordedAddress, reduction⟩ := valid partition key result found
  rw [faithful recorded (recordedAddress.trans address) reduction] at reduction
  exact reduction

/-- Publishing a generic reduction at its source's key retains the semantics. -/
theorem WhnfCacheSemantics.insert {before after : TcState .anon}
    (valid : WhnfCacheSemantics.{u,v} resolve entries before) (partition : WhnfCachePartition)
    {key : Address × Address} {input result : KExpr .anon} (address : input.addr = key.1)
    (reduction : GenericReduction.{u,v} resolve entries input result)
    (written : ∀ other : WhnfCachePartition, other.cache after =
      if other = partition then (partition.cache before).insert key result else other.cache before) :
    WhnfCacheSemantics.{u,v} resolve entries after := by
  intro other stored value found
  rw [written other] at found
  by_cases same : other = partition
  · rw [if_pos same] at found
    by_cases sameKey : key = stored
    · subst sameKey
      rw [Std.HashMap.getElem?_insert_self] at found
      cases found
      exact ⟨input, address, reduction⟩
    · rw [Std.HashMap.getElem?_insert, if_neg (fun equal => sameKey (eq_of_beq equal))] at found
      subst same
      exact valid other stored value found
  · rw [if_neg same] at found
    exact valid other stored value found

/-- A stored unfold entry at the head's address is the recorded instantiation
of the recorded head, once the head is identified with it. -/
theorem UnfoldCacheSemantics.hit {state : TcState .anon}
    (valid : UnfoldCacheSemantics resolve entries state)
    {id : KId .anon} {arguments : Array (KUniv .anon)} {info : ExprInfo .anon} {value : KExpr .anon}
    (found : state.env.unfoldCache[(KExpr.const id arguments info).addr]? = some value)
    (faithful : ∀ (id' : KId .anon) (arguments' : Array (KUniv .anon)) (info' : ExprInfo .anon),
      (KExpr.const id' arguments' info').addr = (KExpr.const id arguments info).addr →
      KExpr.const id' arguments' info' = KExpr.const id arguments info) :
    ∃ (ref : ConstRef β) (entry : ConstantEntry β) (body output : AExpr β),
      resolve id.addr = some ref ∧ entries ref = some entry ∧ entry.body = some body ∧
      entry.universes = arguments.size ∧
      readScopedExpr? resolve [] value = some output.erase ∧
      AExpr.LevelEquivalent (body.instL (arguments.toList.map readLevel)) output := by
  obtain ⟨id', arguments', info', ref, entry, body, output, address, resolved, entryFound, bodyFound,
    universes, reads, same⟩ := valid _ value found
  cases faithful id' arguments' info' address
  exact ⟨ref, entry, body, output, resolved, entryFound, bodyFound, universes, reads, same⟩

theorem UnfoldCacheSemantics.insert {before : TcState .anon}
    (valid : UnfoldCacheSemantics resolve entries before)
    {id : KId .anon} {arguments : Array (KUniv .anon)} {info : ExprInfo .anon} {value : KExpr .anon}
    {ref : ConstRef β} {entry : ConstantEntry β} {body output : AExpr β}
    (resolved : resolve id.addr = some ref) (entryFound : entries ref = some entry)
    (bodyFound : entry.body = some body) (universes : entry.universes = arguments.size)
    (reads : readScopedExpr? resolve [] value = some output.erase)
    (same : AExpr.LevelEquivalent (body.instL (arguments.toList.map readLevel)) output) :
    UnfoldCacheSemantics resolve entries {before with env := {before.env with
      unfoldCache := before.env.unfoldCache.insert (KExpr.const id arguments info).addr value}} := by
  intro addr stored found
  change (before.env.unfoldCache.insert (KExpr.const id arguments info).addr value)[addr]? =
    some stored at found
  by_cases sameKey : (KExpr.const id arguments info).addr = addr
  · subst sameKey
    rw [Std.HashMap.getElem?_insert_self] at found
    cases found
    exact ⟨id, arguments, info, ref, entry, body, output, rfl, resolved, entryFound, bodyFound,
      universes, reads, same⟩
  · rw [Std.HashMap.getElem?_insert, if_neg (fun equal => sameKey (eq_of_beq equal))] at found
    exact valid addr stored found

/-- Publishing into one WHNF partition: the invariant's other components are
untouched and the memo agreement absorbs the new entry. -/
theorem ReductionInvariant.publishWhnf {before after : TcState .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (partition : WhnfCachePartition) {key : Address × Address} {input result : KExpr .anon}
    (address : input.addr = key.1)
    (reduction : GenericReduction.{u,v} resolve entries input result)
    (written : ∀ other : WhnfCachePartition, other.cache after =
      if other = partition then (partition.cache before).insert key result else other.cache before)
    (frame : LocalStateFrame before after)
    (constants : after.env.consts = before.env.consts)
    (blocks : after.env.blocks = before.env.blocks)
    (intern : after.env.intern = before.env.intern)
    (full : after.env.inferCache = before.env.inferCache)
    (only : after.env.inferOnlyCache = before.env.inferOnlyCache)
    (defEq : ∀ partition : DefEqCachePartition, partition.cache after = partition.cache before)
    (manager : after.equivManager = before.equivManager)
    (unfold : after.env.unfoldCache = before.env.unfoldCache)
    (isProp : after.env.isPropCache = before.env.isPropCache)
    (off : after.noAccel = before.noAccel) :
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds after where
  sourceCache := ⟨valid.sourceState.ofMaps frame.loader constants blocks
    (intern ▸ valid.coherent), valid.cache.ofMaps full only constants⟩
  synthesis := valid.synthesis.elim fun history => ⟨history.ofMaps full only⟩
  structural := frame.invariant valid.structural
  reading := valid.reading.congr frame.context.symm
  origin := valid.origin
  semantics := ⟨valid.semantics.whnf.insert partition address reduction written,
    valid.semantics.defEq.ofMaps defEq, by rw [manager]; exact valid.semantics.equivalence,
    valid.semantics.unfold.ofMap unfold, valid.semantics.isProp.ofMap isProp⟩
  accelerationsOff := off.trans valid.accelerationsOff

theorem ReductionInvariant.publishCore {before : TcState .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    {key : Address × Address} {input result : KExpr .anon} (address : input.addr = key.1)
    (reduction : GenericReduction.{u,v} resolve entries input result) :
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      {before with env := {before.env with
        whnfCoreCache := before.env.whnfCoreCache.insert key result}} :=
  valid.publishWhnf .core address reduction (fun other => by cases other <;> rfl)
    ⟨Nat.le_refl _, .refl _, rfl⟩ rfl rfl rfl rfl rfl (fun partition => by cases partition <;> rfl)
    rfl rfl rfl rfl

theorem ReductionInvariant.publishCoreCheap {before : TcState .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    {key : Address × Address} {input result : KExpr .anon} (address : input.addr = key.1)
    (reduction : GenericReduction.{u,v} resolve entries input result) :
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      {before with env := {before.env with
        whnfCoreCheapCache := before.env.whnfCoreCheapCache.insert key result}} :=
  valid.publishWhnf .coreCheap address reduction (fun other => by cases other <;> rfl)
    ⟨Nat.le_refl _, .refl _, rfl⟩ rfl rfl rfl rfl rfl (fun partition => by cases partition <;> rfl)
    rfl rfl rfl rfl

theorem ReductionInvariant.publishNoDelta {before : TcState .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    {key : Address × Address} {input result : KExpr .anon} (address : input.addr = key.1)
    (reduction : GenericReduction.{u,v} resolve entries input result) :
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      {before with env := {before.env with
        whnfNoDeltaCache := before.env.whnfNoDeltaCache.insert key result}} :=
  valid.publishWhnf .noDelta address reduction (fun other => by cases other <;> rfl)
    ⟨Nat.le_refl _, .refl _, rfl⟩ rfl rfl rfl rfl rfl (fun partition => by cases partition <;> rfl)
    rfl rfl rfl rfl

theorem ReductionInvariant.publishNoDeltaCheap {before : TcState .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    {key : Address × Address} {input result : KExpr .anon} (address : input.addr = key.1)
    (reduction : GenericReduction.{u,v} resolve entries input result) :
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      {before with env := {before.env with
        whnfNoDeltaCheapCache := before.env.whnfNoDeltaCheapCache.insert key result}} :=
  valid.publishWhnf .noDeltaCheap address reduction (fun other => by cases other <;> rfl)
    ⟨Nat.le_refl _, .refl _, rfl⟩ rfl rfl rfl rfl rfl (fun partition => by cases partition <;> rfl)
    rfl rfl rfl rfl

theorem ReductionInvariant.publishFull {before : TcState .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    {key : Address × Address} {input result : KExpr .anon} (address : input.addr = key.1)
    (reduction : GenericReduction.{u,v} resolve entries input result) :
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      {before with env := {before.env with whnfCache := before.env.whnfCache.insert key result}} :=
  valid.publishWhnf .full address reduction (fun other => by cases other <;> rfl)
    ⟨Nat.le_refl _, .refl _, rfl⟩ rfl rfl rfl rfl rfl (fun partition => by cases partition <;> rfl)
    rfl rfl rfl rfl

/-- Publishing an unfold entry at the head constant's address. -/
theorem ReductionInvariant.publishUnfold {before : TcState .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    {id : KId .anon} {arguments : Array (KUniv .anon)} {info : ExprInfo .anon} {value : KExpr .anon}
    {ref : ConstRef β} {entry : ConstantEntry β} {body output : AExpr β}
    (resolved : resolve id.addr = some ref) (entryFound : entries ref = some entry)
    (bodyFound : entry.body = some body) (universes : entry.universes = arguments.size)
    (reads : readScopedExpr? resolve [] value = some output.erase)
    (same : AExpr.LevelEquivalent (body.instL (arguments.toList.map readLevel)) output) :
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      {before with env := {before.env with
        unfoldCache := before.env.unfoldCache.insert (KExpr.const id arguments info).addr value}} where
  sourceCache := ⟨valid.sourceState.ofMaps rfl rfl rfl valid.coherent, valid.cache.ofMaps rfl rfl rfl⟩
  synthesis := valid.synthesis.elim fun history => ⟨history.ofMaps rfl rfl⟩
  structural := ⟨valid.structural.coherent, valid.structural.allocated, valid.structural.loader⟩
  reading := valid.reading
  origin := valid.origin
  semantics := ⟨valid.semantics.whnf.ofMaps (fun partition => by cases partition <;> rfl),
    valid.semantics.defEq.ofMaps (fun partition => by cases partition <;> rfl),
    valid.semantics.equivalence,
    valid.semantics.unfold.insert resolved entryFound bodyFound universes reads same,
    valid.semantics.isProp.ofMap rfl⟩
  accelerationsOff := valid.accelerationsOff

end Memo

/-! ### The bounded loop -/

section Loop

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)}

/-- A bounded loop of sound steps is a generically sound reduction of its
start term: successful iterations compose by transitivity, and exhaustion
fails without touching the state. -/
theorem runBounded_sound {σ : Type} {view : σ → KExpr .anon}
    {step : σ → RecM .anon (RecM.BoundedStep σ (KExpr .anon))} {methods : Methods .anon}
    (sound : SoundStep.{u,v} resolve anchor entries source catalog view
      (fun current => (step current).run methods)) :
    ∀ (fuel : Nat) (start : σ), GenericSoundReduction.{u,v} resolve anchor entries source catalog
      (view start) ((RecM.runBounded step fuel start).run methods)
  | 0, start => fun _ _ _ _ _ valid _ _ => valid
  | fuel + 1, start => by
      intro locals context bounds before term valid reads typed
      have outcome := sound locals context bounds before term start valid reads typed
      change StepOutcome.{u,v} resolve anchor entries source catalog view locals context bounds start
        ((step start).run methods before) at outcome
      rw [RecM.runBounded, ReaderT.run_bind]
      change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds
        (view start) (EStateM.bind ((step start).run methods) _ before)
      cases run : (step start).run methods before with
      | error error after =>
          rw [run] at outcome
          rw [EStateM.bind, run]
          exact outcome
      | ok outcomeValue after =>
          rw [run] at outcome
          rw [EStateM.bind, run]
          cases outcomeValue with
          | next next =>
              obtain ⟨valid', reduction⟩ := outcome
              obtain ⟨middle, readsMiddle, _, preserved⟩ :=
                reduction locals context term reads typed
              obtain ⟨type, checked⟩ := typed
              have rest := runBounded_sound sound fuel next locals context bounds after middle
                valid' readsMiddle ⟨type, preserved type checked⟩
              change ReductionOutcome.{u,v} resolve anchor entries source catalog locals context
                bounds (view start) ((RecM.runBounded step fuel next).run methods after)
              cases final : (RecM.runBounded step fuel next).run methods after with
              | error error last => rw [final] at rest; exact rest
              | ok result last =>
                  rw [final] at rest
                  exact ⟨rest.1, reduction.trans rest.2⟩
          | done result => exact outcome

end Loop

/-! ### Accelerations under `noAccel` -/

section Accelerations

variable {methods : Methods .anon} {state : TcState .anon}

private theorem get_run (state : TcState .anon) :
    (get : TcM .anon (TcState .anon)) state = .ok state state := rfl

theorem tryReduceNative_noAccel (off : state.noAccel = true) (term : KExpr .anon) :
    (RecM.tryReduceNative term).run methods state = .ok none state := by
  unfold RecM.tryReduceNative
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ state = _
  rw [EStateM.bind, get_run]
  simp only [off, ↓reduceIte]
  rfl

theorem tryReduceBitvec_noAccel (off : state.noAccel = true) (term : KExpr .anon) :
    (RecM.tryReduceBitvec term).run methods state = .ok none state := by
  unfold RecM.tryReduceBitvec
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ state = _
  rw [EStateM.bind, get_run]
  simp only [off, ↓reduceIte]
  rfl

theorem tryReduceDecidable_noAccel (off : state.noAccel = true) (term : KExpr .anon) :
    (RecM.tryReduceDecidable term).run methods state = .ok none state := by
  unfold RecM.tryReduceDecidable
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ state = _
  rw [EStateM.bind, get_run]
  simp only [off, ↓reduceIte]
  rfl

end Accelerations

end Ix.Kernel.Consistency
