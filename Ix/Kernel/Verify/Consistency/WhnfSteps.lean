/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.WhnfLayers
import Ix.Kernel.Verify.Consistency.ScopedInstUniv
import Ix.Kernel.Verify.Consistency.LetWhnfPlan
import Ix.Kernel.Verify.Consistency.AppSpineSource
import Ix.Kernel.Verify.Consistency.BetaPrefixPlan

/-!
# WHNF step cases under the generic contracts

The step bodies of the three bounded WHNF loops are proved sound one branch
at a time. Leaves finish reflexively; a loose bound variable never reads;
an explicit let substitutes its value, which the reader already did; a
let-bound free variable needs the local let-value agreement the invariant
does not record; delta unfolding of a definition is `ConversionClaim.delta`
through the unfold memo and the universe instantiation walker, with checked
typing of the unfolded body a model-side obligation; the accelerated
reducers return nothing under `noAccel`; an application runs its head through
the recursive method table, then either beta-reduces a returned lambda by the
simultaneous substitution of the beta track or rebuilds the spine. Projection,
iota, and the literal and quotient reducers remain seams, collected with the
walker and memo resources in `WhnfSeamAssumptions` so that later work
discharges them field by field.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-! ### Static bindings and seams -/

section Seams

variable {β : Type u} (resolve : Address → Option (ConstRef β))
  (anchor entries : Model.Environment β) (source : Ixon.Env)
  (catalog : List (SourceCacheRequest source))

/-- A loaded definition's binding to its admitted model entry: the resolved
reference, the entry with its body, and the closed reading of the loaded
value as that body. -/
structure DefinitionBinding (id : KId .anon) (value : KExpr .anon) (ref : ConstRef β)
    (entry : ConstantEntry β) (body : AExpr β) : Prop where
  resolved : resolve id.addr = some ref
  found : entries ref = some entry
  bodyFound : entry.body = some body
  reading : readScopedExpr? resolve [] value = some body.erase

/-- Walker resources of one multi-argument beta step: the simultaneous
substitution bounds and collision freedom, and collision freedom of the
interned argument suffix chain. -/
structure BetaWalkerResources (state : TcState .anon) (rawBody : KExpr .anon)
    (consumed rawArguments : Array (KExpr .anon)) : Prop where
  bounds : SimulSubstBounds rawBody consumed.reverse 0
  faithful : KExpr.CollisionFree fun term => state.env.intern.ExprSupport term ∨
    KExpr.SimulSubstReach consumed.reverse rawBody 0 term
  suffix : KExpr.CollisionFree fun term =>
    (simulSubst rawBody consumed.reverse 0 state.env.intern).2.ExprSupport term ∨
      term ∈ cheapBetaChainList (simulSubst rawBody consumed.reverse 0 state.env.intern).1
        (rawArguments.extract consumed.size rawArguments.size).toList

/-- The remaining obligations of the WHNF bodies, per method table. Each is
either a run resource (lookup data, walker resources, memo identification),
a model-side fact (checked bodies), or a reducer seam left to later work. -/
structure WhnfSeamAssumptions (methods : Methods .anon) : Prop where
  /-- Standalone conversion data for every lookup from an invariant state. -/
  lookups : LookupData.{u,v} resolve anchor entries source catalog
  /-- Every consulted WHNF memo entry was produced from the query. -/
  hits : WhnfHitData.{u,v} resolve anchor entries source catalog
  /-- Syntactic closure of the admitted interface. -/
  wellFormed : entries.WF
  /-- Every admitted body, instantiated and read through the walker's
  universe simplifications, is checked at the declared instantiated type in
  every context. This is the model-side obligation of delta. -/
  bodies : ∀ (context : Model.Context β) (ref : ConstRef β) (entry : ConstantEntry β)
    (body output : AExpr β) (levels : List VLevel),
    entries ref = some entry → entry.body = some body → levels.length = entry.universes →
    AExpr.LevelEquivalent (body.instL levels) output →
    CheckedTyping.{u,v} entries context output (entry.type.instL levels)
  /-- Every loaded reducible definition has a static binding. -/
  definitions : ∀ (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (state : TcState .anon) (id : KId .anon) (name : Mode.anon.F Name)
    (levelParams : Mode.anon.F (Array Name)) (kind : Ix.DefKind) (safety : Ix.DefinitionSafety)
    (hints : Lean.ReducibilityHints) (lvls : UInt64) (ty val : KExpr .anon)
    (leanAll : Mode.anon.F (Array (KId .anon))) (block : KId .anon),
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
    state.env.get? id = some (.defn name levelParams kind safety hints lvls ty val leanAll block) →
    kind ≠ .opaq → ∃ ref entry body, DefinitionBinding resolve entries id val ref entry body
  /-- Every consulted unfold entry was produced from the head that keys it. -/
  unfoldFaithful : ∀ (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (state : TcState .anon) (id : KId .anon) (arguments : Array (KUniv .anon)) (info : ExprInfo .anon)
    (value : KExpr .anon),
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
    state.env.unfoldCache[(KExpr.const id arguments info).addr]? = some value →
    ∀ (id' : KId .anon) (arguments' : Array (KUniv .anon)) (info' : ExprInfo .anon),
      (KExpr.const id' arguments' info').addr = (KExpr.const id arguments info).addr →
      KExpr.const id' arguments' info' = KExpr.const id arguments info
  /-- Walker resources of universe instantiation at every invariant state. -/
  instantiation : ∀ (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (state : TcState .anon) (term : KExpr .anon) (arguments : Array (KUniv .anon)),
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
    UniverseInstantiationSupport state term arguments
  /-- Collision freedom of the interned application chains. -/
  chains : ∀ (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (state : TcState .anon) (head : KExpr .anon) (arguments : List (KExpr .anon)),
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
    KExpr.CollisionFree fun term => state.env.intern.ExprSupport term ∨
      term ∈ cheapBetaChainList head arguments
  /-- Let-value agreement of the local context: a let-bound free variable is
  a generic reduction to its stored value. -/
  letValue : ∀ (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (state : TcState .anon) (id : FVarId) (name declName : Mode.anon.F Name) (info : ExprInfo .anon)
    (type value : KExpr .anon),
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
    state.lctx.find? id = some (.ldecl declName type value) →
    GenericReduction.{u,v} resolve entries (.fvar id name info) value
  /-- Walker resources of explicit-let substitution. -/
  letResources : ∀ (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (state : TcState .anon) (term : KExpr .anon),
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
    LetStepSource.selected term = true → LetStepSource.Resources term state
  /-- The projection branch of the structural step. -/
  projection : ∀ (flags : WhnfFlags) (locals : List FVarId) (context : Model.Context β)
    (bounds : List VLevel) (before : TcState .anon) (term : AExpr β) (id : KId .anon)
    (field : UInt64) (value : KExpr .anon) (info : ExprInfo .anon),
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before →
    readScopedExpr? resolve locals (.prj id field value info) = some term.erase →
    (∃ type, CheckedTyping.{u,v} entries context term type) →
    StepOutcome.{u,v} resolve anchor entries source catalog (fun current : KExpr .anon => current) locals context bounds
      (.prj id field value info) ((RecM.whnfCoreWithFlagsStep (.prj id field value info) flags).run methods before)
  /-- Walker resources of every multi-argument beta step at an invariant state. -/
  betaResources : ∀ (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (state : TcState .anon) (rawBody : KExpr .anon) (consumed rawArguments : Array (KExpr .anon)),
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds state →
    BetaWalkerResources state rawBody consumed rawArguments
  /-- Iota reduction with the structural flags. -/
  iota : ∀ flags, SoundReducer.{u,v} resolve anchor entries source catalog
    (fun term => (RecM.tryIotaWithFlags term flags).run methods)
  /-- The reducer probes of the no-delta and full loops. -/
  projApp : ∀ flags, SoundReducer.{u,v} resolve anchor entries source catalog
    (fun term => (RecM.tryProjAppReduceFinished term flags).run methods)
  nat : ∀ mode, SoundReducer.{u,v} resolve anchor entries source catalog
    (fun term => (RecM.tryReduceNatWithSuccMode term mode).run methods)
  string : SoundReducer.{u,v} resolve anchor entries source catalog
    (fun term => (RecM.tryReduceString term).run methods)
  projectionDefinition : SoundReducer.{u,v} resolve anchor entries source catalog
    (fun term => (RecM.tryReduceProjectionDefinition term).run methods)
  quot : SoundReducer.{u,v} resolve anchor entries source catalog
    (fun term => (RecM.tryQuotReduce term).run methods)
  natOffsetStuck : SoundReducer.{u,v} resolve anchor entries source catalog
    (fun term => (RecM.tryNatOffsetStuck term).run methods)

end Seams

/-! ### Probe combinators -/

section Probes

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {locals : List FVarId}
  {context : Model.Context β} {bounds : List VLevel}

theorem ReducerOutcome.absent {input : KExpr .anon} {state : TcState .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds state) :
    ReducerOutcome.{u,v} resolve anchor entries source catalog locals context bounds input
      (.ok none state) := valid

theorem ReducerOutcome.found {input reduced : KExpr .anon} {state : TcState .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds state)
    (reduction : GenericReduction.{u,v} resolve entries input reduced) :
    ReducerOutcome.{u,v} resolve anchor entries source catalog locals context bounds input
      (.ok (some reduced) state) := ⟨valid, reduction⟩

/-- An invariant-preserving prefix followed by a continuation that knows the
prefix's run equation. -/
theorem ReducerOutcome.bindPreserving {α : Type} {input : KExpr .anon} {action : TcM .anon α}
    {next : α → TcM .anon (Option (KExpr .anon))} {before : TcState .anon}
    (first : PreservesInvariant.{u,v} resolve anchor entries source catalog action)
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (rest : ∀ value middle, action before = .ok value middle →
      ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds middle →
      ReducerOutcome.{u,v} resolve anchor entries source catalog locals context bounds input
        (next value middle)) :
    ReducerOutcome.{u,v} resolve anchor entries source catalog locals context bounds input
      (EStateM.bind action next before) := by
  have intermediate := first locals context bounds before valid
  cases run : action before with
  | error error after =>
      rw [EStateM.bind, run]
      simp only [run] at intermediate
      exact intermediate
  | ok value after =>
      simp only [run] at intermediate
      rw [EStateM.bind, run]
      exact rest value after run intermediate

/-- A probe outcome followed by a continuation on its absence. -/
theorem ReducerOutcome.bindProbe {input : KExpr .anon} {probe : TcM .anon (Option (KExpr .anon))}
    {next : Option (KExpr .anon) → TcM .anon (Option (KExpr .anon))} {before : TcState .anon}
    (first : ReducerOutcome.{u,v} resolve anchor entries source catalog locals context bounds input
      (probe before))
    (found : ∀ reduced middle,
      ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds middle →
      GenericReduction.{u,v} resolve entries input reduced →
      ReducerOutcome.{u,v} resolve anchor entries source catalog locals context bounds input
        (next (Option.some reduced) middle))
    (absent : ∀ middle,
      ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds middle →
      ReducerOutcome.{u,v} resolve anchor entries source catalog locals context bounds input
        (next Option.none middle)) :
    ReducerOutcome.{u,v} resolve anchor entries source catalog locals context bounds input
      (EStateM.bind probe next before) := by
  cases run : probe before with
  | error error after =>
      rw [EStateM.bind, run]
      simp only [run] at first
      exact first
  | ok value after =>
      rw [run] at first
      rw [EStateM.bind, run]
      cases value with
      | none => exact absent after first
      | some reduced => exact found reduced after first.1 first.2

end Probes

/-! ### Delta -/

section Delta

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {methods : Methods .anon}
  {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel}

private theorem get_run (state : TcState .anon) :
    (get : TcM .anon (TcState .anon)) state = .ok state state := rfl

theorem levelEquivalent_conversion {left right : AExpr β}
    (same : AExpr.LevelEquivalent left right) (context : Model.Context β) :
    ConversionClaim.{u,v} entries context left right :=
  fun _ _ constants _ levels env _ => same.interp constants levels env

/-- A successful `tryGetConst` leaves the declaration loaded. -/
theorem tryGetConst_loaded {id : KId .anon} {concrete : KConst .anon} {before after : TcState .anon}
    (run : TcM.tryGetConst id before = .ok (some concrete) after) :
    after.env.get? id = some concrete := by
  apply getConst_result_loaded (id := id) (before := before)
  unfold TcM.getConst
  change EStateM.bind (TcM.tryGetConst id) _ before = _
  rw [EStateM.bind, run]
  rfl

/-- The interning loop of delta unfolding is a monadic fold. -/
theorem internLoop_eq_foldlM (base : KExpr .anon) (arguments : Array (KExpr .anon)) :
    (forIn (m := RecM .anon) arguments base fun arg acc => do
        let result ← liftM (TcM.intern (KExpr.mkApp acc arg))
        pure (ForInStep.yield result)) =
      arguments.foldlM (fun acc arg => liftM (TcM.intern (KExpr.mkApp acc arg))) base := by
  simp [Array.forIn_yield_eq_foldlM]

/-- The interning loop of delta unfolding is the interned application chain. -/
theorem internLoop_run (base : KExpr .anon) (arguments : Array (KExpr .anon)) :
    (forIn (m := RecM .anon) arguments base fun arg acc => do
        let result ← liftM (TcM.intern (KExpr.mkApp acc arg))
        pure (ForInStep.yield result)).run methods =
      TcM.runIntern (internAppChain base arguments.toList) := by
  funext before
  rw [internLoop_eq_foldlM, ← Array.foldlM_toList]
  generalize arguments.toList = remaining
  induction remaining generalizing base before with
  | nil => rfl
  | cons argument remaining ih =>
      rw [List.foldlM_cons, ReaderT.run_bind, ReaderT.run_monadLift]
      change EStateM.bind (TcM.intern (KExpr.mkApp base argument)) _ before = _
      unfold EStateM.bind TcM.intern TcM.runIntern
      exact ih _ _

/-- The unfold memo: a hit is the recorded instantiation of the head, a miss
runs the universe instantiation walker and publishes its result. -/
theorem unfoldConstValue_ok (seams : WhnfSeamAssumptions.{u,v} resolve anchor entries source catalog methods)
    {state after : TcState .anon} {id : KId .anon} {arguments : Array (KUniv .anon)}
    {info : ExprInfo .anon} {value result : KExpr .anon} {ref : ConstRef β} {entry : ConstantEntry β}
    {body : AExpr β}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds state)
    (binding : DefinitionBinding resolve entries id value ref entry body)
    (arity : arguments.size = entry.universes)
    (run : (RecM.unfoldConstValue (.const id arguments info) value arguments).run methods state =
      .ok result after) :
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds after ∧
      ∃ output : AExpr β, readScopedExpr? resolve [] result = some output.erase ∧
        AExpr.LevelEquivalent (body.instL (arguments.toList.map readLevel)) output := by
  unfold RecM.unfoldConstValue at run
  rw [ReaderT.run_bind] at run
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ state = _ at run
  rw [EStateM.bind, get_run] at run
  dsimp only at run
  cases lookup : state.env.unfoldCache[(KExpr.const id arguments info).addr]? with
  | some cached =>
      rw [lookup] at run
      change EStateM.Result.ok cached state = _ at run
      cases run
      obtain ⟨ref', entry', body', output, resolved', found', bodyFound', _, reads, same⟩ :=
        valid.semantics.unfold.hit lookup
          (seams.unfoldFaithful _ _ _ _ _ _ _ _ valid lookup)
      cases Option.some.inj (resolved'.symm.trans binding.resolved)
      cases Option.some.inj (found'.symm.trans binding.found)
      cases Option.some.inj (bodyFound'.symm.trans binding.bodyFound)
      exact ⟨valid, output, reads, same⟩
  | none =>
      rw [lookup] at run
      dsimp only at run
      rw [ReaderT.run_bind, ReaderT.run_monadLift] at run
      change EStateM.bind (TcM.instantiateUnivParams value arguments) _ state = _ at run
      have support := seams.instantiation locals context bounds state value arguments valid
      have post := TcM.instantiateUnivParams_wf support.faithful (fun _ reach => Or.inr reach)
        ⟨support.coherent, fun _ member => Or.inl member⟩
      cases instantiated : TcM.instantiateUnivParams value arguments state with
      | error error failed =>
          rw [EStateM.bind, instantiated] at run
          cases run
      | ok unfolded walked =>
          rw [instantiated] at post
          rw [EStateM.bind, instantiated] at run
          change EStateM.Result.ok unfolded {walked with env := {walked.env with
            unfoldCache := walked.env.unfoldCache.insert (KExpr.const id arguments info).addr unfolded}} =
            _ at run
          cases run
          obtain ⟨⟨coherent, _⟩, _, stateEq, _⟩ := post
          have levelScope := (seams.wellFormed.bodyScope ref entry binding.found body binding.bodyFound).erase.1
          rw [← arity] at levelScope
          obtain ⟨output, reads, same⟩ := instantiateUnivParams_readScopedAnnotated (locals := [])
            support levelScope binding.reading instantiated
          have valid' := valid.ofIntern (table := walked.env.intern) coherent
          rw [← stateEq] at valid'
          exact ⟨valid'.publishUnfold binding.resolved binding.found binding.bodyFound arity.symm reads same,
            output, reads, same⟩

theorem unfoldConstValue_error (seams : WhnfSeamAssumptions.{u,v} resolve anchor entries source catalog methods)
    {state after : TcState .anon} {id : KId .anon} {arguments : Array (KUniv .anon)}
    {info : ExprInfo .anon} {value : KExpr .anon} {error : TcError .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds state)
    (run : (RecM.unfoldConstValue (.const id arguments info) value arguments).run methods state =
      .error error after) :
    ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds after := by
  unfold RecM.unfoldConstValue at run
  rw [ReaderT.run_bind] at run
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ state = _ at run
  rw [EStateM.bind, get_run] at run
  dsimp only at run
  cases lookup : state.env.unfoldCache[(KExpr.const id arguments info).addr]? with
  | some cached =>
      rw [lookup] at run
      change EStateM.Result.ok cached state = _ at run
      cases run
  | none =>
      rw [lookup] at run
      dsimp only at run
      rw [ReaderT.run_bind, ReaderT.run_monadLift] at run
      change EStateM.bind (TcM.instantiateUnivParams value arguments) _ state = _ at run
      have support := seams.instantiation locals context bounds state value arguments valid
      have post := TcM.instantiateUnivParams_wf support.faithful (fun _ reach => Or.inr reach)
        ⟨support.coherent, fun _ member => Or.inl member⟩
      cases instantiated : TcM.instantiateUnivParams value arguments state with
      | error failure failed =>
          rw [instantiated] at post
          rw [EStateM.bind, instantiated] at run
          cases run
          obtain ⟨⟨coherent, _⟩, stateEq, _⟩ := post
          have valid' := valid.ofIntern (table := _) coherent
          rw [← stateEq] at valid'
          exact valid'
      | ok unfolded walked =>
          rw [EStateM.bind, instantiated] at run
          change EStateM.Result.ok unfolded {walked with env := {walked.env with
            unfoldCache := walked.env.unfoldCache.insert (KExpr.const id arguments info).addr unfolded}} =
            _ at run
          cases run

/-- Invariant preservation of the unfold memo on both outcomes. -/
theorem unfoldConstValue_preserves
    (seams : WhnfSeamAssumptions.{u,v} resolve anchor entries source catalog methods)
    {id : KId .anon} {arguments : Array (KUniv .anon)} {info : ExprInfo .anon} {value : KExpr .anon}
    {ref : ConstRef β} {entry : ConstantEntry β} {body : AExpr β}
    (binding : DefinitionBinding resolve entries id value ref entry body)
    (arity : arguments.size = entry.universes) :
    PreservesInvariant.{u,v} resolve anchor entries source catalog
      ((RecM.unfoldConstValue (.const id arguments info) value arguments).run methods) := by
  intro locals context bounds state valid
  cases run : (RecM.unfoldConstValue (.const id arguments info) value arguments).run methods state with
  | ok result after => exact (unfoldConstValue_ok seams valid binding arity run).1
  | error error after => exact unfoldConstValue_error seams valid run

/-- A constant whose reading is a constant instance reads to that instance. -/
theorem constant_reading {id : KId .anon} {levels : Array (KUniv .anon)} {info : ExprInfo .anon}
    {head : AExpr β} {ref : ConstRef β} (resolved : resolve id.addr = some ref)
    (reads : readScopedExpr? resolve locals (KExpr.const id levels info) = some head.erase) :
    head = .const ref (levels.toList.map readLevel) := by
  simp [readScopedExpr?, resolved] at reads
  cases head <;> simp_all [AExpr.erase]

/-- The head of a checked constant spine has the arity of its entry. -/
theorem constant_spine_arity {term : AExpr β} {ref : ConstRef β} {levels : List VLevel}
    {arguments : List (AExpr β)} {entry : ConstantEntry β}
    (same : term = (AExpr.const ref levels).appN arguments)
    (typed : ∃ type, CheckedTyping.{u,v} entries context term type)
    (found : entries ref = some entry) : levels.length = entry.universes := by
  obtain ⟨type, checked⟩ := typed
  rw [same] at checked
  obtain ⟨headType, headChecked⟩ := checked.headTyped
  obtain ⟨entry', found', arity⟩ := headChecked.constArity rfl
  cases Option.some.inj (found'.symm.trans found)
  exact arity

/-- Unfolding a definition instance under an application spine is a generic
reduction: delta, universe level equivalence, and application congruence,
with checked typing of the unfolded body supplied by the interface. -/
theorem unfolded_spine_reduction
    (seams : WhnfSeamAssumptions.{u,v} resolve anchor entries source catalog methods)
    {state : TcState .anon} {input : KExpr .anon} {id : KId .anon} {levels : Array (KUniv .anon)}
    {info : ExprInfo .anon} {arguments : Array (KExpr .anon)} {unfolded : KExpr .anon}
    {value : KExpr .anon} {ref : ConstRef β} {entry : ConstantEntry β} {body output : AExpr β}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds state)
    (spine : input.collectSpine = (KExpr.const id levels info, arguments))
    (binding : DefinitionBinding resolve entries id value ref entry body)
    (readsOutput : readScopedExpr? resolve [] unfolded = some output.erase)
    (same : AExpr.LevelEquivalent (body.instL (levels.toList.map readLevel)) output) :
    GenericReduction.{u,v} resolve entries input
      (internAppChain unfolded arguments.toList state.env.intern).1 := by
  intro locals' context' term' reads' typed'
  obtain ⟨termEq, headReads, argumentReads⟩ := AppSpineSource.reading reads'
  rw [spine] at headReads argumentReads
  generalize AppSpineSource.parts input term' = parts at termEq headReads argumentReads
  obtain ⟨head', arguments'⟩ := parts
  have headEq := constant_reading binding.resolved headReads
  subst headEq
  subst termEq
  have arity := constant_spine_arity rfl typed' binding.found
  obtain ⟨reads, _⟩ := internAppChain_readScopedExpr? valid.coherent
    (seams.chains locals context bounds state unfolded arguments.toList valid)
    (readScopedExpr?_weaken_closed readsOutput locals') argumentReads
  refine ⟨output.appN arguments', reads, ?_, ?_⟩
  · exact ConversionClaim.appN ((ConversionClaim.delta binding.found binding.bodyFound arity).trans
      (levelEquivalent_conversion same context')) _
  · intro type checked
    exact CheckedTyping.rewriteHead (fun _ headChecked => headChecked.unfoldConst rfl binding.found
      (seams.bodies context' ref entry body output _ binding.found binding.bodyFound arity same)) checked

/-- Unfolding a bare definition instance is a generic reduction. -/
theorem unfolded_constant_reduction
    (seams : WhnfSeamAssumptions.{u,v} resolve anchor entries source catalog methods)
    {id : KId .anon} {levels : Array (KUniv .anon)} {info : ExprInfo .anon} {unfolded : KExpr .anon}
    {value : KExpr .anon} {ref : ConstRef β} {entry : ConstantEntry β} {body output : AExpr β}
    (binding : DefinitionBinding resolve entries id value ref entry body)
    (readsOutput : readScopedExpr? resolve [] unfolded = some output.erase)
    (same : AExpr.LevelEquivalent (body.instL (levels.toList.map readLevel)) output) :
    GenericReduction.{u,v} resolve entries (KExpr.const id levels info) unfolded := by
  intro locals' context' term' reads' typed'
  have headEq := constant_reading binding.resolved reads'
  have arity := constant_spine_arity (arguments := []) headEq typed' binding.found
  refine ⟨output, readScopedExpr?_weaken_closed readsOutput locals', ?_, ?_⟩
  · rw [headEq]
    exact (ConversionClaim.delta binding.found binding.bodyFound arity).trans (levelEquivalent_conversion same context')
  · intro type checked
    rw [headEq] at checked
    exact checked.unfoldConst rfl binding.found
      (seams.bodies context' ref entry body output _ binding.found binding.bodyFound arity same)

/-- The arity of a constant-headed spine, from the current scope's reading and typing. -/
theorem spine_arity_of_reading {input : KExpr .anon} {term : AExpr β} {id : KId .anon}
    {levels : Array (KUniv .anon)} {info : ExprInfo .anon} {arguments : Array (KExpr .anon)}
    {ref : ConstRef β} {entry : ConstantEntry β}
    (reads : readScopedExpr? resolve locals input = some term.erase)
    (typed : ∃ type, CheckedTyping.{u,v} entries context term type)
    (spine : input.collectSpine = (KExpr.const id levels info, arguments))
    (resolved : resolve id.addr = some ref) (found : entries ref = some entry) :
    levels.size = entry.universes := by
  obtain ⟨termEq, headReads, _⟩ := AppSpineSource.reading reads
  rw [spine] at headReads
  have headEq := constant_reading resolved headReads
  rw [headEq] at termEq
  have arity := constant_spine_arity termEq typed found
  simpa only [List.length_map, Array.length_toList] using arity

/-- Delta unfolding of a head-applied or bare definition instance. -/
theorem tryDeltaUnfold_sound
    (seams : WhnfSeamAssumptions.{u,v} resolve anchor entries source catalog methods) :
    SoundReducer.{u,v} resolve anchor entries source catalog
      (fun input => (RecM.tryDeltaUnfold input).run methods) := by
  intro locals context bounds before term input valid reads typed
  dsimp only
  unfold RecM.tryDeltaUnfold
  cases spine : input.collectSpine with
  | mk head arguments =>
      cases head with
      | const id levels info =>
          dsimp only
          rw [ReaderT.run_bind, ReaderT.run_monadLift]
          change ReducerOutcome.{u,v} resolve anchor entries source catalog locals context bounds input
            (EStateM.bind (TcM.tryGetConst id) _ before)
          apply ReducerOutcome.bindPreserving (PreservesInvariant.tryGetConst seams.lookups id) valid
          intro found middle lookup valid₁
          cases found with
          | none => exact ReducerOutcome.absent valid₁
          | some constant =>
              cases constant with
              | defn name levelParams kind safety hints lvls ty val leanAll block =>
                  have loaded := tryGetConst_loaded lookup
                  have unfold : ∀ (proceed : kind ≠ .opaq),
                      ReducerOutcome.{u,v} resolve anchor entries source catalog locals context bounds
                        input (ReaderT.run (do
                          let val ← pure val
                          let val ← RecM.unfoldConstValue (KExpr.const id levels info) val levels
                          let acc ← forIn arguments val fun arg acc => do
                            let result ← liftM (TcM.intern (KExpr.mkApp acc arg))
                            pure (ForInStep.yield result)
                          pure (some acc)) methods middle) := by
                    intro proceed
                    obtain ⟨ref, entry, body, binding⟩ := seams.definitions locals context bounds middle
                      id name levelParams kind safety hints lvls ty val leanAll block valid₁ loaded proceed
                    have arity := spine_arity_of_reading reads typed spine binding.resolved binding.found
                    rw [pure_bind, ReaderT.run_bind]
                    change ReducerOutcome.{u,v} resolve anchor entries source catalog locals context
                      bounds input (EStateM.bind
                        ((RecM.unfoldConstValue (KExpr.const id levels info) val levels).run methods) _ middle)
                    apply ReducerOutcome.bindPreserving
                      (unfoldConstValue_preserves (info := info) seams binding arity) valid₁
                    intro unfolded reduced run valid₂
                    obtain ⟨_, output, readsOutput, same⟩ := unfoldConstValue_ok seams valid₁ binding arity run
                    rw [ReaderT.run_bind, internLoop_run]
                    obtain ⟨_, coherent⟩ := internAppChain_readScopedExpr? valid₂.coherent
                      (seams.chains locals context bounds reduced unfolded arguments.toList valid₂)
                      (readScopedExpr?_weaken_closed readsOutput locals)
                      (by
                        obtain ⟨_, _, argumentReads⟩ := AppSpineSource.reading reads
                        rw [spine] at argumentReads
                        exact argumentReads)
                    exact ReducerOutcome.found (valid₂.ofIntern coherent)
                      (unfolded_spine_reduction seams valid₂ spine binding readsOutput same)
                  dsimp only
                  cases kind with
                  | opaq => exact ReducerOutcome.absent valid₁
                  | defn => exact unfold (by intro same; cases same)
                  | thm => exact unfold (by intro same; cases same)
              | _ => exact ReducerOutcome.absent valid₁
      | _ => exact ReducerOutcome.absent valid

/-- One delta step: the spine unfolding, then the bare-constant retry. -/
theorem deltaUnfoldOne_sound
    (seams : WhnfSeamAssumptions.{u,v} resolve anchor entries source catalog methods) :
    SoundReducer.{u,v} resolve anchor entries source catalog
      (fun input => (RecM.deltaUnfoldOne input).run methods) := by
  intro locals context bounds before term input valid reads typed
  dsimp only
  unfold RecM.deltaUnfoldOne
  rw [ReaderT.run_bind]
  change ReducerOutcome.{u,v} resolve anchor entries source catalog locals context bounds input
    (EStateM.bind ((RecM.tryDeltaUnfold input).run methods) _ before)
  apply ReducerOutcome.bindProbe (tryDeltaUnfold_sound seams locals context bounds before term input valid
    reads typed)
  · intro reduced middle valid₁ reduction
    exact ReducerOutcome.found valid₁ reduction
  · intro middle valid₁
    cases input with
    | const id levels info =>
        dsimp only
        rw [ReaderT.run_bind, ReaderT.run_monadLift]
        change ReducerOutcome.{u,v} resolve anchor entries source catalog locals context bounds
          (KExpr.const id levels info) (EStateM.bind (TcM.tryGetConst id) _ middle)
        apply ReducerOutcome.bindPreserving (PreservesInvariant.tryGetConst seams.lookups id) valid₁
        intro found looked lookup valid₂
        cases found with
        | none => exact ReducerOutcome.absent valid₂
        | some constant =>
            cases constant with
            | defn name levelParams kind safety hints lvls ty val leanAll block =>
                have loaded := tryGetConst_loaded lookup
                have unfold : ∀ (proceed : kind ≠ .opaq),
                    ReducerOutcome.{u,v} resolve anchor entries source catalog locals context bounds
                      (KExpr.const id levels info) (ReaderT.run (do
                        let unfolded ← RecM.unfoldConstValue (KExpr.const id levels info) val levels
                        pure (some unfolded)) methods looked) := by
                  intro proceed
                  obtain ⟨ref, entry, body, binding⟩ := seams.definitions locals context bounds looked
                    id name levelParams kind safety hints lvls ty val leanAll block valid₂ loaded proceed
                  have arity := spine_arity_of_reading (id := id) (levels := levels) (info := info)
                    (arguments := #[]) reads typed (by simp [KExpr.collectSpine, KExpr.collectSpine.go])
                    binding.resolved binding.found
                  rw [ReaderT.run_bind]
                  change ReducerOutcome.{u,v} resolve anchor entries source catalog locals context
                    bounds (KExpr.const id levels info) (EStateM.bind
                      ((RecM.unfoldConstValue (KExpr.const id levels info) val levels).run methods) _ looked)
                  apply ReducerOutcome.bindPreserving
                    (unfoldConstValue_preserves (info := info) seams binding arity) valid₂
                  intro unfolded reduced run valid₃
                  obtain ⟨_, output, readsOutput, same⟩ :=
                    unfoldConstValue_ok seams valid₂ binding arity run
                  exact ReducerOutcome.found valid₃
                    (unfolded_constant_reduction seams binding readsOutput same)
                dsimp only
                cases kind with
                | opaq => exact ReducerOutcome.absent valid₂
                | defn => exact unfold (by intro same; cases same)
                | thm => exact unfold (by intro same; cases same)
            | _ => exact ReducerOutcome.absent valid₂
    | _ => exact ReducerOutcome.absent valid₁

end Delta

/-! ### Step combinators -/

section StepCombinators

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {locals : List FVarId}
  {context : Model.Context β} {bounds : List VLevel}

/-- A probe outcome followed by a step continuation on each answer. -/
theorem StepOutcome.bindProbe {σ : Type} {view : σ → KExpr .anon} {current : σ} {input : KExpr .anon}
    {probe : TcM .anon (Option (KExpr .anon))}
    {next : Option (KExpr .anon) → TcM .anon (RecM.BoundedStep σ (KExpr .anon))} {before : TcState .anon}
    (first : ReducerOutcome.{u,v} resolve anchor entries source catalog locals context bounds input
      (probe before))
    (found : ∀ reduced middle,
      ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds middle →
      GenericReduction.{u,v} resolve entries input reduced →
      StepOutcome.{u,v} resolve anchor entries source catalog view locals context bounds current
        (next (Option.some reduced) middle))
    (absent : ∀ middle,
      ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds middle →
      StepOutcome.{u,v} resolve anchor entries source catalog view locals context bounds current
        (next Option.none middle)) :
    StepOutcome.{u,v} resolve anchor entries source catalog view locals context bounds current
      (EStateM.bind probe next before) := by
  cases run : probe before with
  | error error after =>
      rw [EStateM.bind, run]
      simp only [run] at first
      exact first
  | ok value after =>
      rw [run] at first
      rw [EStateM.bind, run]
      cases value with
      | none => exact absent after first
      | some reduced => exact found reduced after first.1 first.2

/-- A reduction outcome followed by a step continuation on its result. -/
theorem StepOutcome.bindReduction {σ : Type} {view : σ → KExpr .anon} {current : σ}
    {action : TcM .anon (KExpr .anon)}
    {next : KExpr .anon → TcM .anon (RecM.BoundedStep σ (KExpr .anon))} {before : TcState .anon}
    (first : ReductionOutcome.{u,v} resolve anchor entries source catalog locals context bounds
      (view current) (action before))
    (rest : ∀ result middle,
      ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds middle →
      GenericReduction.{u,v} resolve entries (view current) result →
      StepOutcome.{u,v} resolve anchor entries source catalog view locals context bounds current
        (next result middle)) :
    StepOutcome.{u,v} resolve anchor entries source catalog view locals context bounds current
      (EStateM.bind action next before) := by
  cases run : action before with
  | error error after =>
      rw [EStateM.bind, run]
      simp only [run] at first
      exact first
  | ok result after =>
      rw [run] at first
      rw [EStateM.bind, run]
      exact rest result after first.1 first.2

/-- A step outcome at an intermediate term transports along a generic
reduction from the current term. -/
theorem StepOutcome.transport {current reduced : KExpr .anon}
    {outcome : EStateM.Result (TcError .anon) (TcState .anon) (RecM.BoundedStep (KExpr .anon) (KExpr .anon))}
    (later : StepOutcome.{u,v} resolve anchor entries source catalog (fun term : KExpr .anon => term)
      locals context bounds reduced outcome)
    (reduction : GenericReduction.{u,v} resolve entries current reduced) :
    StepOutcome.{u,v} resolve anchor entries source catalog (fun term : KExpr .anon => term)
      locals context bounds current outcome := by
  cases outcome with
  | error error after => exact later
  | ok value after =>
      cases value with
      | next next => exact ⟨later.1, reduction.trans later.2⟩
      | done result => exact ⟨later.1, reduction.trans later.2⟩

end StepCombinators

/-! ### The application branch -/

section ApplicationStep

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {methods : Methods .anon}
  {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel}

theorem consumeBetaLamsFuel_size :
    ∀ (fuel : Nat) (body : KExpr .anon) (args consumed : Array (KExpr .anon)),
      consumed.size ≤ (RecM.consumeBetaLamsFuel fuel body args consumed).2.size
  | 0, _, _, _ => Nat.le_refl _
  | fuel + 1, body, args, consumed => by
      unfold RecM.consumeBetaLamsFuel
      split
      · exact Nat.le_refl _
      · cases body with
        | lam _ _ _ inner _ =>
            exact Nat.le_trans (by simp) (consumeBetaLamsFuel_size fuel inner args (consumed.push _))
        | _ => exact Nat.le_refl _

/-- Peeling a lambda against a nonempty spine consumes at least one argument. -/
theorem consumeBetaLams_lam_nonempty {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body rawBody : KExpr .anon} {info : ExprInfo .anon} {args consumed : Array (KExpr .anon)}
    (nonempty : 0 < args.size)
    (peeling : RecM.consumeBetaLams (.lam name bi domain body info) args = (rawBody, consumed)) :
    (!consumed.isEmpty) = true := by
  unfold RecM.consumeBetaLams at peeling
  obtain ⟨size, sizeEq⟩ : ∃ size, args.size = size + 1 := ⟨args.size - 1, by omega⟩
  rw [sizeEq] at peeling
  have zero : (Array.mkEmpty (size + 1) : Array (KExpr .anon)).size = 0 := rfl
  have first : RecM.consumeBetaLamsFuel (size + 1) (.lam name bi domain body info) args
      (Array.mkEmpty (size + 1) : Array (KExpr .anon)) = RecM.consumeBetaLamsFuel size body args
        ((Array.mkEmpty (size + 1) : Array (KExpr .anon)).push
          args[(Array.mkEmpty (size + 1) : Array (KExpr .anon)).size]!) := by
    rw [RecM.consumeBetaLamsFuel.eq_2, if_neg (by rw [zero, sizeEq]; omega)]
  rw [first] at peeling
  have bound := consumeBetaLamsFuel_size size body args
    ((Array.mkEmpty (size + 1) : Array (KExpr .anon)).push
      args[(Array.mkEmpty (size + 1) : Array (KExpr .anon)).size]!)
  rw [peeling, Array.size_push, zero] at bound
  cases empty : consumed.isEmpty with
  | false => rfl
  | true =>
      rw [Array.isEmpty_iff] at empty
      subst empty
      simp at bound

/-- The annotated reading of a lambda is a lambda. -/
theorem lambda_reading {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body : KExpr .anon} {info : ExprInfo .anon} {target : AExpr β}
    (reads : readScopedExpr? resolve locals (.lam name bi domain body info) = some target.erase) :
    ∃ (condition : Certified.PropWhen) (A b : AExpr β), target = .lam condition A b := by
  cases target with
  | lam condition A b => exact ⟨condition, A, b, rfl⟩
  | _ =>
      cases hd : readScopedExpr? resolve locals domain <;>
        cases hb : readScopedExpr? resolve locals body 1 <;>
        simp [readScopedExpr?, hd, hb, AExpr.erase] at reads

/-- The argument suffix loop, point-free. -/
theorem finishAppResult_run (result : KExpr .anon) (args : Array (KExpr .anon)) (consumed : Nat) :
    (RecM.finishAppResult result args consumed).run methods =
      TcM.runIntern (internAppChain result (args.extract consumed args.size).toList) := by
  funext before
  exact RecM.finishAppResult_eq_internAppChain result args consumed methods before

/-- Binding an intern-table action is its result at the updated table. -/
theorem runIntern_bind {α γ : Type} (action : InternM .anon α) (next : α → TcM .anon γ)
    (state : TcState .anon) :
    (TcM.runIntern action >>= next) state =
      next (action state.env.intern).1
        {state with env := {state.env with intern := (action state.env.intern).2}} := rfl

/-- Multi-argument beta after the head callback returned a lambda: the
production output reads as the model beta prefix at every scope, is
convertible to the source by head conversion and beta, and is checked at
every type of the source. -/
theorem beta_prefix_reduction
    (seams : WhnfSeamAssumptions.{u,v} resolve anchor entries source catalog methods)
    {middle : TcState .anon} {fn arg head rawBody : KExpr .anon} {info : ExprInfo .anon}
    {args consumed : Array (KExpr .anon)} {name : Mode.anon.F Name}
    {bi : Mode.anon.F Lean.BinderInfo} {domain body : KExpr .anon} {lamInfo : ExprInfo .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds middle)
    (spine : (KExpr.app fn arg info).collectSpine = (head, args))
    (peeling : RecM.consumeBetaLams (.lam name bi domain body lamInfo) args = (rawBody, consumed))
    (nonempty : (!consumed.isEmpty) = true)
    (headReduction : GenericReduction.{u,v} resolve entries head (.lam name bi domain body lamInfo)) :
    GenericReduction.{u,v} resolve entries (.app fn arg info)
      (internAppChain (simulSubst rawBody consumed.reverse 0 middle.env.intern).1
        (args.extract consumed.size args.size).toList
        (simulSubst rawBody consumed.reverse 0 middle.env.intern).2).1 := by
  intro locals' context' term' reads' typed'
  obtain ⟨termEq, headReads, argumentReads⟩ := AppSpineSource.reading reads'
  rw [spine] at headReads argumentReads
  generalize AppSpineSource.parts (KExpr.app fn arg info) term' = parts at termEq headReads argumentReads
  obtain ⟨headTerm, arguments⟩ := parts
  subst termEq
  obtain ⟨T, checked⟩ := typed'
  obtain ⟨headType, headChecked⟩ := checked.headTyped
  obtain ⟨lambda, lambdaReads, headConverted, headPreserved⟩ :=
    headReduction locals' context' headTerm headReads ⟨headType, headChecked⟩
  obtain ⟨condition, A, b, rfl⟩ := lambda_reading lambdaReads
  have resources := seams.betaResources locals context bounds middle rawBody consumed args valid
  let plan : BetaPrefixPlan resolve locals' middle := {
    name, bi, rawDomain := domain, rawInner := body, lambdaInfo := lamInfo, rawArguments := args,
    rawBody, consumed, condition, domain := A, inner := b, arguments
    headReads := lambdaReads, argumentReads, peeling, nonempty
    walkerBounds := resources.bounds, walkerFaithful := resources.faithful
    suffixFaithful := resources.suffix }
  obtain ⟨reads, _⟩ := plan.reading valid.coherent
  have spineChecked : CheckedTyping.{u,v} entries context' ((AExpr.lam condition A b).appN arguments) T :=
    CheckedTyping.rewriteHead (fun _ headChecked' => headPreserved _ headChecked') checked
  obtain ⟨converted, _⟩ := LambdaSpineTyping.betaPrefix (count := consumed.size)
    spineChecked.lambdaSpine plan.counts.1
  refine ⟨plan.modelResult, reads, ?_, ?_⟩
  · exact (ConversionClaim.appN headConverted arguments).trans converted
  · intro type checked'
    exact CheckedTyping.betaPrefix seams.wellFormed consumed.size (.lam condition A b) arguments
      (CheckedTyping.rewriteHead (fun _ headChecked' => headPreserved _ headChecked') checked')

/-- Rebuilding the spine on a reduced head is a generic reduction by head
conversion and application congruence. -/
theorem rebuilt_spine_reduction
    (seams : WhnfSeamAssumptions.{u,v} resolve anchor entries source catalog methods)
    {middle : TcState .anon} {fn arg head reduced : KExpr .anon} {info : ExprInfo .anon}
    {args : Array (KExpr .anon)}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds middle)
    (spine : (KExpr.app fn arg info).collectSpine = (head, args))
    (headReduction : GenericReduction.{u,v} resolve entries head reduced) :
    GenericReduction.{u,v} resolve entries (.app fn arg info)
      (internAppChain reduced (args.extract 0 args.size).toList middle.env.intern).1 := by
  intro locals' context' term' reads' typed'
  obtain ⟨termEq, headReads, argumentReads⟩ := AppSpineSource.reading reads'
  rw [spine] at headReads argumentReads
  generalize AppSpineSource.parts (KExpr.app fn arg info) term' = parts at termEq headReads argumentReads
  obtain ⟨headTerm, arguments⟩ := parts
  subst termEq
  obtain ⟨T, checked⟩ := typed'
  obtain ⟨headType, headChecked⟩ := checked.headTyped
  obtain ⟨target, targetReads, headConverted, headPreserved⟩ :=
    headReduction locals' context' headTerm headReads ⟨headType, headChecked⟩
  obtain ⟨reads, _⟩ := internAppChain_readScopedExpr? valid.coherent
    (seams.chains locals context bounds middle reduced (args.extract 0 args.size).toList valid)
    targetReads (by simpa only [Array.extract_size] using argumentReads)
  exact ⟨target.appN arguments, reads, ConversionClaim.appN headConverted arguments,
    fun _ checked' => CheckedTyping.rewriteHead (fun _ headChecked' => headPreserved _ headChecked') checked'⟩

/-- The application branch of the structural step: the recursive head call
through the method table, then multi-argument beta on a lambda, head
rebuilding with one iota attempt, or iota on the original spine. -/
theorem whnfCoreWithFlagsStep_app_sound
    (seams : WhnfSeamAssumptions.{u,v} resolve anchor entries source catalog methods)
    (callbacks : GenericWhnfContract.{u,v} resolve anchor entries source catalog methods)
    (flags : WhnfFlags) {before : TcState .anon} {term : AExpr β} {fn arg : KExpr .anon}
    {info : ExprInfo .anon}
    (valid : ReductionInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (reads : readScopedExpr? resolve locals (.app fn arg info) = some term.erase)
    (typed : ∃ type, CheckedTyping.{u,v} entries context term type) :
    StepOutcome.{u,v} resolve anchor entries source catalog (fun current : KExpr .anon => current)
      locals context bounds (.app fn arg info)
      ((RecM.whnfCoreWithFlagsStep (.app fn arg info) flags).run methods before) := by
  obtain ⟨termEq, headReads, argumentReads⟩ := AppSpineSource.reading reads
  have nonempty := AppSpineSource.nonempty fn arg info
  generalize spine : (KExpr.app fn arg info).collectSpine = pair at headReads argumentReads nonempty
  obtain ⟨head, args⟩ := pair
  generalize AppSpineSource.parts (KExpr.app fn arg info) term = parts at termEq headReads argumentReads
  obtain ⟨headTerm, arguments⟩ := parts
  have headTyped : ∃ headType, CheckedTyping.{u,v} entries context headTerm headType := by
    obtain ⟨T, checked⟩ := typed
    rw [termEq] at checked
    exact checked.headTyped
  have outcome := callbacks.whnfCoreFlags head flags locals context bounds before headTerm valid
    headReads headTyped
  cases headRun : methods.whnfCoreFlags head flags before with
  | error error failed =>
      rw [headRun] at outcome
      unfold RecM.whnfCoreWithFlagsStep
      rw [ReaderT.run_bind, spine]
      change StepOutcome.{u,v} resolve anchor entries source catalog (fun current : KExpr .anon => current)
        locals context bounds (.app fn arg info) (EStateM.bind (methods.whnfCoreFlags head flags) _ before)
      rw [EStateM.bind, headRun]
      exact outcome
  | ok reduced middle =>
      rw [headRun] at outcome
      obtain ⟨valid', headReduction⟩ := outcome
      have rebuiltReduction := rebuilt_spine_reduction seams valid' spine headReduction
      obtain ⟨target, targetReads, _, _⟩ := headReduction locals context headTerm headReads headTyped
      obtain ⟨_, coherence⟩ := internAppChain_readScopedExpr? valid'.coherent
        (seams.chains locals context bounds middle reduced (args.extract 0 args.size).toList valid')
        targetReads (by simpa only [Array.extract_size] using argumentReads)
      obtain ⟨rebuiltTerm, rebuiltReads, _, rebuiltPreserved⟩ :=
        rebuiltReduction locals context term reads typed
      have rebuiltTyped : ∃ type, CheckedTyping.{u,v} entries context rebuiltTerm type := by
        obtain ⟨T, checked⟩ := typed
        exact ⟨T, rebuiltPreserved T checked⟩
      cases reduced with
      | lam name bi domain body lamInfo =>
          cases peeling : RecM.consumeBetaLams (.lam name bi domain body lamInfo) args with
          | mk rawBody consumed =>
              have nonemptyConsumed := consumeBetaLams_lam_nonempty nonempty peeling
              obtain ⟨condition, A, b, rfl⟩ := lambda_reading targetReads
              have resources := seams.betaResources locals context bounds middle rawBody consumed args valid'
              let plan : BetaPrefixPlan resolve locals middle := {
                name, bi, rawDomain := domain, rawInner := body, lambdaInfo := lamInfo, rawArguments := args,
                rawBody, consumed, condition, domain := A, inner := b, arguments
                headReads := targetReads, argumentReads, peeling, nonempty := nonemptyConsumed
                walkerBounds := resources.bounds, walkerFaithful := resources.faithful
                suffixFaithful := resources.suffix }
              rw [plan.run spine headRun]
              exact ⟨valid'.ofIntern (plan.reading valid'.coherent).2,
                beta_prefix_reduction seams valid' spine peeling nonemptyConsumed headReduction⟩
      | _ =>
          unfold RecM.whnfCoreWithFlagsStep
          rw [ReaderT.run_bind, spine]
          change StepOutcome.{u,v} resolve anchor entries source catalog (fun current : KExpr .anon => current)
            locals context bounds (.app fn arg info)
            (EStateM.bind (methods.whnfCoreFlags head flags) _ before)
          rw [EStateM.bind, headRun]
          dsimp only
          split
          · rw [ReaderT.run_bind, finishAppResult_run, runIntern_bind]
            dsimp only
            rw [ReaderT.run_bind]
            change StepOutcome.{u,v} resolve anchor entries source catalog (fun current : KExpr .anon => current)
              locals context bounds (.app fn arg info)
              (EStateM.bind ((RecM.tryIotaWithFlags _ flags).run methods) _ _)
            apply StepOutcome.bindProbe (seams.iota flags locals context bounds _ rebuiltTerm _
              (valid'.ofIntern coherence) rebuiltReads rebuiltTyped)
            · intro next state valid₃ stepped
              exact ⟨valid₃, rebuiltReduction.trans stepped⟩
            · intro state valid₃
              exact ⟨valid₃, rebuiltReduction⟩
          · rw [ReaderT.run_bind]
            change StepOutcome.{u,v} resolve anchor entries source catalog (fun current : KExpr .anon => current)
              locals context bounds (.app fn arg info)
              (EStateM.bind ((RecM.tryIotaWithFlags (.app fn arg info) flags).run methods) _ middle)
            apply StepOutcome.bindProbe
              (seams.iota flags locals context bounds middle term (.app fn arg info) valid' reads typed)
            · intro next state valid₃ stepped
              exact ⟨valid₃, stepped⟩
            · intro state valid₃
              exact ⟨valid₃, .refl _⟩

end ApplicationStep

/-! ### The structural step -/

section CoreStep

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {methods : Methods .anon}

private theorem get_run' (state : TcState .anon) :
    (get : TcM .anon (TcState .anon)) state = .ok state state := rfl

/-- The structural step: leaves finish, a loose bound variable does not read,
a let-bound free variable is its value, an explicit let substitutes, and the
projection and application branches are seams. -/
theorem whnfCoreWithFlagsStep_sound
    (seams : WhnfSeamAssumptions.{u,v} resolve anchor entries source catalog methods)
    (callbacks : GenericWhnfContract.{u,v} resolve anchor entries source catalog methods) (flags : WhnfFlags) :
    SoundStep.{u,v} resolve anchor entries source catalog (fun term : KExpr .anon => term)
      (fun current => (RecM.whnfCoreWithFlagsStep current flags).run methods) := by
  intro locals context bounds before term current valid reads typed
  dsimp only at reads ⊢
  cases current with
  | var index name info => simp [readScopedExpr?] at reads
  | fvar id name info =>
      unfold RecM.whnfCoreWithFlagsStep
      dsimp only
      rw [ReaderT.run_bind]
      change StepOutcome.{u,v} resolve anchor entries source catalog (fun term : KExpr .anon => term)
        locals context bounds (KExpr.fvar id name info) (EStateM.bind (get : TcM .anon (TcState .anon)) _ before)
      rw [EStateM.bind, get_run']
      dsimp only
      cases found : before.lctx.find? id with
      | none => exact ⟨valid, .refl _⟩
      | some decl =>
          cases decl with
          | cdecl _ _ _ => exact ⟨valid, .refl _⟩
          | ldecl declName type value =>
              exact ⟨valid, seams.letValue locals context bounds before id name declName info type value
                valid found⟩
  | sort _ _ | all _ _ _ _ _ | lam _ _ _ _ _ | nat _ _ _ | str _ _ _ | const _ _ _ =>
      exact ⟨valid, .refl _⟩
  | prj id field value info =>
      exact seams.projection flags locals context bounds before term id field value info valid reads typed
  | letE name domain value body nonDep info =>
      have resources := seams.letResources locals context bounds before
        (.letE name domain value body nonDep info) valid rfl
      obtain ⟨plan, _⟩ := LetStepSource.construct rfl resources
      rw [plan.run methods flags]
      obtain ⟨_, coherent⟩ := plan.reading reads valid.coherent
      refine ⟨valid.ofIntern coherent, ?_⟩
      intro locals' context' term' reads' _
      exact ⟨term', (plan.reading reads' valid.coherent).1, .refl _, fun _ checked => checked⟩
  | app fn arg info =>
      exact whnfCoreWithFlagsStep_app_sound seams callbacks flags valid reads typed

end CoreStep

/-! ### The no-delta step -/

section NoDeltaStep

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {methods : Methods .anon}

/-- The reducer tail of a no-delta iteration, in production order; the
accelerated probes are absent under `noAccel`. -/
theorem whnfNoDeltaReducersStep_sound
    (seams : WhnfSeamAssumptions.{u,v} resolve anchor entries source catalog methods)
    (flags : WhnfFlags) (mode : NatSuccMode) :
    SoundStep.{u,v} resolve anchor entries source catalog (fun term : KExpr .anon => term)
      (fun current => (RecM.whnfNoDeltaReducersStep flags mode current).run methods) := by
  intro locals context bounds before term current valid reads typed
  dsimp only at reads ⊢
  unfold RecM.whnfNoDeltaReducersStep
  rw [ReaderT.run_bind]
  change StepOutcome.{u,v} resolve anchor entries source catalog (fun term : KExpr .anon => term)
    locals context bounds current
    (EStateM.bind ((RecM.tryProjAppReduceFinished current flags).run methods) _ before)
  apply StepOutcome.bindProbe (seams.projApp flags locals context bounds before term current valid reads typed)
  · intro reduced middle valid' reduction
    exact ⟨valid', reduction⟩
  intro middle valid'
  rw [ReaderT.run_bind]
  change StepOutcome.{u,v} resolve anchor entries source catalog (fun term : KExpr .anon => term)
    locals context bounds current
    (EStateM.bind ((RecM.tryReduceBitvec current).run methods) _ middle)
  rw [EStateM.bind, tryReduceBitvec_noAccel valid'.accelerationsOff]
  dsimp only
  rw [ReaderT.run_bind]
  change StepOutcome.{u,v} resolve anchor entries source catalog (fun term : KExpr .anon => term)
    locals context bounds current
    (EStateM.bind ((RecM.tryReduceNatWithSuccMode current mode).run methods) _ middle)
  apply StepOutcome.bindProbe (seams.nat mode locals context bounds middle term current valid' reads typed)
  · intro reduced middle' valid'' reduction
    exact ⟨valid'', reduction⟩
  intro middle' valid''
  rw [ReaderT.run_bind]
  change StepOutcome.{u,v} resolve anchor entries source catalog (fun term : KExpr .anon => term)
    locals context bounds current
    (EStateM.bind ((RecM.tryReduceNative current).run methods) _ middle')
  rw [EStateM.bind, tryReduceNative_noAccel valid''.accelerationsOff]
  dsimp only
  rw [ReaderT.run_bind]
  change StepOutcome.{u,v} resolve anchor entries source catalog (fun term : KExpr .anon => term)
    locals context bounds current
    (EStateM.bind ((RecM.tryReduceString current).run methods) _ middle')
  apply StepOutcome.bindProbe (seams.string locals context bounds middle' term current valid'' reads typed)
  · intro reduced state valid₃ reduction
    exact ⟨valid₃, reduction⟩
  intro state valid₃
  by_cases full : flags.isFull = true
  · rw [if_pos full, ReaderT.run_bind]
    change StepOutcome.{u,v} resolve anchor entries source catalog (fun term : KExpr .anon => term)
      locals context bounds current
      (EStateM.bind ((RecM.tryReduceProjectionDefinition current).run methods) _ state)
    apply StepOutcome.bindProbe
      (seams.projectionDefinition locals context bounds state term current valid₃ reads typed)
    · intro reduced final valid₄ reduction
      exact ⟨valid₄, reduction⟩
    · intro final valid₄
      dsimp only
      rw [ReaderT.run_bind]
      change StepOutcome.{u,v} resolve anchor entries source catalog (fun term : KExpr .anon => term)
        locals context bounds current
        (EStateM.bind ((RecM.tryQuotReduce current).run methods) _ final)
      apply StepOutcome.bindProbe (seams.quot locals context bounds final term current valid₄ reads typed)
      · intro reduced last valid₅ reduction
        exact ⟨valid₅, reduction⟩
      · intro last valid₅
        exact ⟨valid₅, .refl _⟩
  · rw [if_neg full]
    dsimp only
    rw [ReaderT.run_bind]
    change StepOutcome.{u,v} resolve anchor entries source catalog (fun term : KExpr .anon => term)
      locals context bounds current
      (EStateM.bind ((RecM.tryQuotReduce current).run methods) _ state)
    apply StepOutcome.bindProbe (seams.quot locals context bounds state term current valid₃ reads typed)
    · intro reduced last valid₅ reduction
      exact ⟨valid₅, reduction⟩
    · intro last valid₅
      exact ⟨valid₅, .refl _⟩

/-- One no-delta iteration: the same-layer structural call, then the reducers. -/
theorem whnfNoDeltaImplStep_sound
    (seams : WhnfSeamAssumptions.{u,v} resolve anchor entries source catalog methods)
    (core : ∀ term flags, GenericSoundReduction.{u,v} resolve anchor entries source catalog term
      ((RecM.whnfCoreWithFlags term flags).run methods))
    (flags : WhnfFlags) (mode : NatSuccMode) :
    SoundStep.{u,v} resolve anchor entries source catalog (fun term : KExpr .anon => term)
      (fun current => (RecM.whnfNoDeltaImplStep flags mode current).run methods) := by
  intro locals context bounds before term current valid reads typed
  dsimp only at reads ⊢
  unfold RecM.whnfNoDeltaImplStep
  rw [ReaderT.run_bind]
  change StepOutcome.{u,v} resolve anchor entries source catalog (fun term : KExpr .anon => term)
    locals context bounds current
    (EStateM.bind ((RecM.whnfCoreWithFlags current flags).run methods) _ before)
  apply StepOutcome.bindReduction (core current flags locals context bounds before term valid reads typed)
  intro reduced middle valid' reduction
  obtain ⟨target, readsTarget, _, preserved⟩ := reduction locals context term reads typed
  obtain ⟨type, checked⟩ := typed
  exact (whnfNoDeltaReducersStep_sound seams flags mode locals context bounds middle target reduced valid'
    readsTarget ⟨type, preserved type checked⟩).transport reduction

end NoDeltaStep

/-! ### The full step -/

section FullStep

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {methods : Methods .anon}

/-- One full-WHNF iteration: the same-layer no-delta call, the cycle check,
the literal reducers, the stuck offset, and one delta step. -/
theorem whnfWithNatSuccModeStep_sound
    (seams : WhnfSeamAssumptions.{u,v} resolve anchor entries source catalog methods)
    (noDelta : ∀ term flags mode, GenericSoundReduction.{u,v} resolve anchor entries source catalog term
      ((RecM.whnfNoDeltaImpl term flags mode).run methods))
    (mode : NatSuccMode) :
    SoundStep.{u,v} resolve anchor entries source catalog Prod.fst
      (fun state => (RecM.whnfWithNatSuccModeStep mode state).run methods) := by
  intro locals context bounds before term state valid reads typed
  obtain ⟨current, seen⟩ := state
  dsimp only at reads ⊢
  unfold RecM.whnfWithNatSuccModeStep
  dsimp only
  rw [ReaderT.run_bind]
  change StepOutcome.{u,v} resolve anchor entries source catalog Prod.fst locals context bounds
    (current, seen) (EStateM.bind ((RecM.whnfNoDeltaImpl current .FULL mode).run methods) _ before)
  apply StepOutcome.bindReduction
    (noDelta current .FULL mode locals context bounds before term valid reads typed)
  intro reduced middle valid' reduction
  obtain ⟨target, readsTarget, _, preserved⟩ := reduction locals context term reads typed
  obtain ⟨type, checked⟩ := typed
  have typed' : ∃ type, CheckedTyping.{u,v} entries context target type := ⟨type, preserved type checked⟩
  by_cases repeated : seen.contains reduced.addr = true
  · rw [if_pos repeated]
    exact ⟨valid', reduction⟩
  rw [if_neg repeated, ReaderT.run_bind]
  change StepOutcome.{u,v} resolve anchor entries source catalog Prod.fst locals context bounds
    (current, seen) (EStateM.bind ((RecM.tryReduceNative reduced).run methods) _ middle)
  rw [EStateM.bind, tryReduceNative_noAccel valid'.accelerationsOff]
  dsimp only
  rw [ReaderT.run_bind]
  change StepOutcome.{u,v} resolve anchor entries source catalog Prod.fst locals context bounds
    (current, seen) (EStateM.bind ((RecM.tryReduceBitvec reduced).run methods) _ middle)
  rw [EStateM.bind, tryReduceBitvec_noAccel valid'.accelerationsOff]
  dsimp only
  rw [ReaderT.run_bind]
  change StepOutcome.{u,v} resolve anchor entries source catalog Prod.fst locals context bounds
    (current, seen) (EStateM.bind ((RecM.tryReduceNatWithSuccMode reduced mode).run methods) _ middle)
  apply StepOutcome.bindProbe
    (seams.nat mode locals context bounds middle target reduced valid' readsTarget typed')
  · intro next state valid'' stepped
    exact ⟨valid'', reduction.trans stepped⟩
  intro state valid''
  rw [ReaderT.run_bind]
  change StepOutcome.{u,v} resolve anchor entries source catalog Prod.fst locals context bounds
    (current, seen) (EStateM.bind ((RecM.tryReduceDecidable reduced).run methods) _ state)
  rw [EStateM.bind, tryReduceDecidable_noAccel valid''.accelerationsOff]
  dsimp only
  rw [ReaderT.run_bind]
  change StepOutcome.{u,v} resolve anchor entries source catalog Prod.fst locals context bounds
    (current, seen) (EStateM.bind ((RecM.tryReduceString reduced).run methods) _ state)
  apply StepOutcome.bindProbe
    (seams.string locals context bounds state target reduced valid'' readsTarget typed')
  · intro next state' valid₃ stepped
    exact ⟨valid₃, reduction.trans stepped⟩
  intro state' valid₃
  rw [ReaderT.run_bind]
  change StepOutcome.{u,v} resolve anchor entries source catalog Prod.fst locals context bounds
    (current, seen) (EStateM.bind ((RecM.tryNatOffsetStuck reduced).run methods) _ state')
  apply StepOutcome.bindProbe
    (seams.natOffsetStuck locals context bounds state' target reduced valid₃ readsTarget typed')
  · intro stuck state'' valid₄ stepped
    exact ⟨valid₄, reduction.trans stepped⟩
  intro state'' valid₄
  rw [ReaderT.run_bind]
  change StepOutcome.{u,v} resolve anchor entries source catalog Prod.fst locals context bounds
    (current, seen) (EStateM.bind ((RecM.deltaUnfoldOne reduced).run methods) _ state'')
  apply StepOutcome.bindProbe
    (deltaUnfoldOne_sound seams locals context bounds state'' target reduced valid₄ readsTarget typed')
  · intro unfolded final valid₅ stepped
    exact ⟨valid₅, reduction.trans stepped⟩
  · intro final valid₅
    exact ⟨valid₅, reduction⟩

end FullStep

/-! ### Assembly -/

section Assembly

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {methods : Methods .anon}

/-- Structural WHNF with flags: leaves return, a loose variable does not
read, and every other form runs the cache layer over the sound loop. -/
theorem whnfCoreWithFlags_sound
    (seams : WhnfSeamAssumptions.{u,v} resolve anchor entries source catalog methods)
    (callbacks : GenericWhnfContract.{u,v} resolve anchor entries source catalog methods) (flags : WhnfFlags)
    (term : KExpr .anon) :
    GenericSoundReduction.{u,v} resolve anchor entries source catalog term
      ((RecM.whnfCoreWithFlags term flags).run methods) := by
  have layer := whnfCoreWithFlagsNonLeaf_sound (methods := methods) seams.lookups seams.hits
    (fun term flags => runBounded_sound (whnfCoreWithFlagsStep_sound seams callbacks flags) _ term)
  intro locals context bounds before reading valid reads typed
  cases term with
  | var index name info => simp [readScopedExpr?] at reads
  | sort _ _ | all _ _ _ _ _ | lam _ _ _ _ _ | nat _ _ _ | str _ _ _ | const _ _ _ =>
      exact ⟨valid, .refl _⟩
  | fvar id name info => exact layer _ flags locals context bounds before reading valid reads typed
  | prj id field value info => exact layer _ flags locals context bounds before reading valid reads typed
  | letE name domain value body nonDep info =>
      exact layer _ flags locals context bounds before reading valid reads typed
  | app fn arg info => exact layer _ flags locals context bounds before reading valid reads typed

theorem whnfCore_sound
    (seams : WhnfSeamAssumptions.{u,v} resolve anchor entries source catalog methods)
    (callbacks : GenericWhnfContract.{u,v} resolve anchor entries source catalog methods) (term : KExpr .anon) :
    GenericSoundReduction.{u,v} resolve anchor entries source catalog term
      ((RecM.whnfCore term).run methods) :=
  whnfCoreWithFlags_sound seams callbacks .FULL term

/-- No-delta WHNF: the cache layer over the loop of sound iterations. -/
theorem whnfNoDeltaImpl_sound
    (seams : WhnfSeamAssumptions.{u,v} resolve anchor entries source catalog methods)
    (callbacks : GenericWhnfContract.{u,v} resolve anchor entries source catalog methods)
    (flags : WhnfFlags) (mode : NatSuccMode) (term : KExpr .anon) :
    GenericSoundReduction.{u,v} resolve anchor entries source catalog term
      ((RecM.whnfNoDeltaImpl term flags mode).run methods) := by
  have layer := whnfNoDeltaImplNonLeaf_sound (methods := methods) seams.lookups seams.hits
    (fun term flags mode => runBounded_sound
      (whnfNoDeltaImplStep_sound seams (fun term flags => whnfCoreWithFlags_sound seams callbacks flags term) flags mode) _ term)
  intro locals context bounds before reading valid reads typed
  cases term with
  | var index name info => simp [readScopedExpr?] at reads
  | sort _ _ | all _ _ _ _ _ | lam _ _ _ _ _ | nat _ _ _ | str _ _ _ => exact ⟨valid, .refl _⟩
  | const _ _ _ | fvar _ _ _ | prj _ _ _ _ | letE _ _ _ _ _ _ | app _ _ _ =>
      exact layer _ flags mode locals context bounds before reading valid reads typed

/-- Full WHNF in either successor mode: the instrumented cache layer over
the loop of sound iterations started with an empty cycle set. -/
theorem whnfWithNatSuccMode_sound
    (seams : WhnfSeamAssumptions.{u,v} resolve anchor entries source catalog methods)
    (callbacks : GenericWhnfContract.{u,v} resolve anchor entries source catalog methods)
    (mode : NatSuccMode) (term : KExpr .anon) :
    GenericSoundReduction.{u,v} resolve anchor entries source catalog term
      ((RecM.whnfWithNatSuccMode term mode).run methods) := by
  have layer := whnfWithNatSuccModeNonLeaf_sound (methods := methods) seams.lookups seams.hits
    (fun term mode => runBounded_sound
      (whnfWithNatSuccModeStep_sound seams (fun term flags mode => whnfNoDeltaImpl_sound seams callbacks flags mode term) mode) _ (term, {}))
  intro locals context bounds before reading valid reads typed
  cases term with
  | var index name info => simp [readScopedExpr?] at reads
  | sort _ _ | all _ _ _ _ _ | lam _ _ _ _ _ | nat _ _ _ | str _ _ _ => exact ⟨valid, .refl _⟩
  | const _ _ _ | fvar _ _ _ | prj _ _ _ _ | letE _ _ _ _ _ _ | app _ _ _ =>
      exact layer _ mode locals context bounds before reading valid reads typed

theorem whnf_sound
    (seams : WhnfSeamAssumptions.{u,v} resolve anchor entries source catalog methods)
    (callbacks : GenericWhnfContract.{u,v} resolve anchor entries source catalog methods) (term : KExpr .anon) :
    GenericSoundReduction.{u,v} resolve anchor entries source catalog term ((RecM.whnf term).run methods) :=
  whnfWithNatSuccMode_sound seams callbacks .collapse term

/-- One induction step of the reduction contracts: the bodies that
`methodsN (depth + 1)` installs are sound under the seams at `methodsN depth`. -/
theorem GenericWhnfContract.succ {depth : Nat}
    (recursive : GenericWhnfContract.{u,v} resolve anchor entries source catalog (methodsN depth))
    (seams : WhnfSeamAssumptions.{u,v} resolve anchor entries source catalog (methodsN depth)) :
    GenericWhnfContract.{u,v} resolve anchor entries source catalog (methodsN (depth + 1)) where
  whnf := fun term => whnf_sound seams recursive term
  whnfCore := fun term => whnfCore_sound seams recursive term
  whnfMode := fun term mode => whnfWithNatSuccMode_sound seams recursive mode term
  whnfCoreFlags := fun term flags => whnfCoreWithFlags_sound seams recursive flags term

/-- Every finite production table satisfies the reduction contracts under
the seams at every depth. -/
theorem GenericWhnfContract.methodsN
    (seams : ∀ depth, WhnfSeamAssumptions.{u,v} resolve anchor entries source catalog (methodsN depth)) :
    ∀ depth, GenericWhnfContract.{u,v} resolve anchor entries source catalog (methodsN depth)
  | 0 => GenericWhnfContract.zero
  | depth + 1 => GenericWhnfContract.succ (GenericWhnfContract.methodsN seams depth) (seams depth)

end Assembly

end Ix.Kernel.Consistency
