/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.RecursiveCache

/-!
# Reusable state invariants through recursive inference

One checked source and initial intern table supply ownership and coherence
throughout a finite operational tree. Nodes carry finite walker data, without
assuming the invariants at recursive boundaries or after lazy loading.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- The fixed verified source, block registration, and intern coherence needed
by the next inference call. No cache typing or source interpretation is asserted. -/
structure InferenceStateInvariant (source : Ixon.Env) (state : TcState .anon) : Prop where
  ownership : SourceOwnership source
  installed : state.lazyFault = some (fun addr => ingressAnonAddrShallow source addr true)
  blocks : LoadedBlockInvariant source state.env
  coherent : state.env.intern.WF

def InferenceStateInvariant.owned {source : Ixon.Env} {state : TcState .anon}
    (valid : InferenceStateInvariant source state) : OwnedLazySupport state :=
  ⟨source, valid.ownership, valid.installed, valid.blocks⟩

theorem InferenceStateInvariant.ofOwned {state : TcState .anon}
    (owned : OwnedLazySupport state) (coherent : state.env.intern.WF) :
    InferenceStateInvariant owned.source state :=
  ⟨owned.ownership, owned.installed, owned.blocks, coherent⟩

/-- One finite source check initializes the reusable invariant. -/
theorem InferenceStateInvariant.ofCheckedSource (source : Ixon.Env)
    (checked : sourceOwnershipCheck source = true) :
    InferenceStateInvariant source (TcState.newLazyAnon source) :=
  ⟨.ofCheck checked, rfl, .empty source, newLazyAnon_intern_coherent source⟩

/-- Cache writes, local scope cleanup, and statistics updates use this frame;
the new intern table's coherence is supplied by the operation that changed it. -/
theorem InferenceStateInvariant.ofMaps {source : Ixon.Env} {before after : TcState .anon}
    (valid : InferenceStateInvariant source before)
    (installed : after.lazyFault = before.lazyFault)
    (constants : after.env.consts = before.env.consts)
    (blocks : after.env.blocks = before.env.blocks)
    (coherent : after.env.intern.WF) : InferenceStateInvariant source after :=
  ⟨valid.ownership, installed.trans valid.installed,
    valid.blocks.ofMaps constants blocks, coherent⟩

theorem InferenceStateInvariant.afterInferKey {source : Ixon.Env}
    {term : KExpr .anon} {before after : TcState .anon} {key : Address × Address}
    (valid : InferenceStateInvariant source before)
    (run : TcM.inferKey term before = .ok key after) :
    InferenceStateInvariant source after :=
  .ofOwned (valid.owned.afterInferKey run) (by rw [inferKey_environment run]; exact valid.coherent)

/-- Lookup retains both resources on success and failure, including partially
completed conversion and publication before an unknown-root error. -/
theorem InferenceStateInvariant.getConst {source : Ixon.Env} {before : TcState .anon}
    (valid : InferenceStateInvariant source before) (id : KId .anon) :
    match TcM.getConst id before with
    | .ok _ after | .error _ after => InferenceStateInvariant source after := by
  have ownership := getConst_owned (id := id) valid.owned
  have coherence := getConst_coherent (id := id) source true valid.installed valid.coherent
  cases run : TcM.getConst id before <;> rw [run] at ownership coherence <;>
    exact ⟨valid.ownership, by rw [ownership.1.checker]; exact valid.installed,
      ownership.2, coherence⟩

/-- Binder data omits coherence, which comes from the preceding recursive call. -/
structure BinderOpeningData (before : TcState .anon) (body : KExpr .anon) : Prop where
  constructed : body.Constructed
  bound : body.size + 1 < UInt64.size
  faithful : KExpr.CollisionFree fun term =>
    before.env.intern.ExprSupport term ∨
      term = KExpr.mkFVar ⟨before.env.nextFVarId⟩ () ∨
      KExpr.InstRevReach #[KExpr.mkFVar ⟨before.env.nextFVarId⟩ ()] body 0 term

theorem InferenceStateInvariant.openBinder {source : Ixon.Env}
    {before after : TcState .anon} {name : Mode.anon.F Name}
    {bi : Mode.anon.F Lean.BinderInfo} {domain body opened : KExpr .anon} {fresh : FVarId}
    (valid : InferenceStateInvariant source before) (data : BinderOpeningData before body)
    (run : TcM.openBinder name bi domain body before = .ok (opened, fresh) after) :
    InferenceStateInvariant source after := by
  have nameUnit : name = () := Subsingleton.elim _ _
  have biUnit : bi = () := Subsingleton.elim _ _
  subst name bi
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
  rw [openBinder_eq] at run
  split at run
  · simp only [interned] at run
    cases run
    exact valid.ofMaps rfl rfl rfl walk.2.1
  · contradiction

/-- Finite codomain-substitution resources at the actual comparison state. -/
structure ApplicationSubstitutionData (table : InternTable .anon)
    (body arg : KExpr .anon) : Prop where
  bodyConstructed : body.Constructed
  argConstructed : arg.Constructed
  bodyBound : body.size < UInt64.size
  argBound : arg.size < UInt64.size
  faithful : KExpr.CollisionFree fun term => table.ExprSupport term ∨ KExpr.SubstReach arg body 0 term

theorem ApplicationSubstitutionData.coherent {table : InternTable .anon}
    {body arg : KExpr .anon} (data : ApplicationSubstitutionData table body arg)
    (coherent : table.WF) : (subst body arg 0 table).2.WF :=
  (subst_spec data.faithful data.bodyConstructed data.argConstructed
    (by simpa using data.bodyBound) data.argBound (fun _ => Or.inr) coherent (fun _ => Or.inl)).2.1

/-- Finite abstraction resources at the actual returned body type. -/
structure LambdaClosingData (table : InternTable .anon) (body : KExpr .anon)
    (fresh : FVarId) : Prop where
  constructed : body.Constructed
  bound : body.size < UInt64.size
  faithful : KExpr.CollisionFree fun term => table.ExprSupport term ∨
    KExpr.AbstractReach ((∅ : Std.HashMap FVarId UInt64).insert fresh 0) 1 body 0 term

theorem LambdaClosingData.coherent {table : InternTable .anon} {body : KExpr .anon}
    {fresh : FVarId} (data : LambdaClosingData table body fresh) (coherent : table.WF) :
    (abstractFVars body #[fresh] table).2.WF :=
  (abstractFVars_singleton_spec data.constructed data.bound data.faithful coherent
    (fun _ => Or.inl) (fun _ => Or.inr)).2

private theorem invariant_hash {source : Ixon.Env} {before after : TcState .anon}
    {left right : KExpr .anon} {methods : Methods .anon}
    (valid : InferenceStateInvariant source before) (equal : (left.addr == right.addr) = true)
    (run : RecM.isDefEq left right methods before = .ok true after) :
    InferenceStateInvariant source after := by
  rw [isDefEq_hash_state equal] at run
  split at run <;> cases run <;> exact valid.ofMaps rfl rfl rfl valid.coherent

private theorem invariant_miss {source : Ixon.Env} {term result : KExpr .anon}
    {methods : Methods .anon} {before after : TcState .anon}
    (valid : InferenceStateInvariant source before) (miss : UncachedInference before term)
    (accepted : RecM.infer term methods before = .ok result after)
    (uncached : ∀ middle,
      RecM.inferUncached RecM.inferCall before.inferOnly term methods miss.keyed = .ok result middle →
      InferenceStateInvariant source miss.keyed → InferenceStateInvariant source middle) :
    InferenceStateInvariant source after := by
  obtain ⟨middle, run, written⟩ := infer_uncached_success_state miss accepted
  have post := uncached middle run (valid.afterInferKey miss.keyRun)
  rw [written]
  cases before.inferOnly <;> exact post.ofMaps rfl rfl rfl post.coherent

/-- Constant data concerns only the finite walk after an actual successful
lookup. Its coherence and block compatibility are derived from the tree root. -/
structure ConstantInstantiationData (before : TcState .anon) (id : KId .anon)
    (arguments : Array (KUniv .anon)) : Prop where
  faithful : ∀ concrete loaded, TcM.getConst id before = .ok concrete loaded →
    KExpr.CollisionFree fun term => loaded.env.intern.ExprSupport term ∨
      KExpr.InstUnivReach arguments concrete.ty term
  levels : ∀ concrete loaded, TcM.getConst id before = .ok concrete loaded →
    UniverseSubstitutionSupport arguments concrete.ty

/-- Operational trees with finite walker data. Ownership and coherence occur
only in the initial state resource, not in any constructor or child resource.
The supported production paths match `InferenceCacheTrace`. -/
inductive OwnedInferenceTrace : Nat → TcState .anon → KExpr .anon → Type
  | hit {fuel before term} (hit : InferenceCacheHit before term) :
      OwnedInferenceTrace fuel before term
  | sort {fuel before level info} (miss : UncachedInference before (.sort level info)) :
      OwnedInferenceTrace fuel before (.sort level info)
  | fvar {fuel before id name info} (miss : UncachedInference before (.fvar id name info)) :
      OwnedInferenceTrace fuel before (.fvar id name info)
  | nat {fuel before value blob info} (miss : UncachedInference before (.nat value blob info)) :
      OwnedInferenceTrace fuel before (.nat value blob info)
  | const {fuel before id arguments info}
      (miss : UncachedInference before (.const id arguments info))
      (data : ConstantInstantiationData miss.keyed id arguments) :
      OwnedInferenceTrace fuel before (.const id arguments info)
  | app {fuel before fn arg info} (full : before.inferOnly = false)
      (miss : UncachedInference before (.app fn arg info))
      (trace : ApplicationInferenceTrace fuel miss.keyed fn arg)
      (hashPath : (trace.argumentType.addr == trace.domain.addr) = true)
      (data : ApplicationSubstitutionData trace.comparedState.env.intern trace.codomain arg)
      (functionTree : OwnedInferenceTrace fuel miss.keyed fn)
      (argumentTree : OwnedInferenceTrace fuel trace.functionState arg) :
      OwnedInferenceTrace (fuel + 1) before (.app fn arg info)
  | forallE {fuel before name bi domain body info}
      (miss : UncachedInference before (.all name bi domain body info))
      (trace : ForallInferenceTrace fuel miss.keyed name bi domain body)
      (opening : BinderOpeningData trace.domainState body)
      (domainTree : OwnedInferenceTrace fuel miss.keyed domain)
      (bodyTree : OwnedInferenceTrace fuel trace.openedState trace.opened) :
      OwnedInferenceTrace (fuel + 1) before (.all name bi domain body info)
  | lam {fuel before name bi domain body info} (full : before.inferOnly = false)
      (miss : UncachedInference before (.lam name bi domain body info))
      (trace : LambdaInferenceTrace fuel miss.keyed name bi domain body)
      (opening : BinderOpeningData trace.domainState body)
      (closing : LambdaClosingData trace.bodyState.env.intern trace.bodyType trace.fresh)
      (domainTree : OwnedInferenceTrace fuel miss.keyed domain)
      (bodyTree : OwnedInferenceTrace fuel trace.openedState trace.opened) :
      OwnedInferenceTrace (fuel + 1) before (.lam name bi domain body info)

def OwnedInferenceTrace.writes {fuel : Nat} {before : TcState .anon} {term : KExpr .anon} :
    OwnedInferenceTrace fuel before term → List (Address × Address)
  | .hit _ => []
  | .sort miss | .fvar miss | .nat miss | .const miss _ => [miss.key]
  | .app _ miss _ _ _ first second | .forallE miss _ _ first second |
      .lam _ miss _ _ _ first second => miss.key :: (first.writes ++ second.writes)

/-- A successful whole call returns the invariant needed by its successor.
The proof follows each actual recursive call, binder walk, and final cache write. -/
theorem OwnedInferenceTrace.preserves {source : Ixon.Env} {fuel : Nat}
    {before after : TcState .anon} {term result : KExpr .anon}
    (tree : OwnedInferenceTrace fuel before term) (valid : InferenceStateInvariant source before)
    (accepted : RecM.infer term (methodsN fuel) before = .ok result after) :
    InferenceStateInvariant source after := by
  induction tree generalizing result after with
  | hit hit =>
      rw [hit.run] at accepted
      cases accepted
      exact valid.afterInferKey hit.keyRun
  | @sort fuel before level info miss =>
      apply invariant_miss valid miss accepted
      intro middle run keyed
      change EStateM.Result.ok
        (miss.keyed.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).1
        {miss.keyed with env := {miss.keyed.env with intern :=
          (miss.keyed.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).2}} =
        .ok result middle at run
      cases run
      exact keyed.ofMaps rfl rfl rfl (keyed.coherent.internExpr _)
  | @fvar fuel before id name info miss =>
      apply invariant_miss valid miss accepted
      intro middle run keyed
      change (RecM.inferUncached RecM.inferCall before.inferOnly (.fvar id name info)).run
        (methodsN fuel) miss.keyed = _ at run
      unfold RecM.inferUncached at run
      simp only [ReaderT.run_bind] at run
      change EStateM.bind (get : TcM .anon (TcState .anon)) _ miss.keyed = _ at run
      rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) miss.keyed =
        .ok miss.keyed miss.keyed from rfl] at run
      dsimp only at run
      split at run
      · cases run; exact keyed
      · contradiction
  | @nat fuel before value blob info miss =>
      apply invariant_miss valid miss accepted
      intro middle run keyed
      obtain ⟨_, rfl⟩ := inferUncached_nat_run run
      exact keyed.ofMaps rfl rfl rfl (keyed.coherent.internExpr _)
  | @const fuel before id arguments info miss data =>
      apply invariant_miss valid miss accepted
      intro middle run keyed
      obtain ⟨concrete, loaded, got, _, instantiated⟩ := inferUncached_const_instantiation run
      have lookup := keyed.getConst id
      rw [got] at lookup
      have post := TcM.instantiateUnivParams_wf (data.faithful concrete loaded got)
        (fun _ h => Or.inr h) ⟨lookup.coherent, fun _ h => Or.inl h⟩
      rw [instantiated] at post
      rw [post.2.2.1]
      exact lookup.ofMaps rfl rfl rfl post.1.1
  | app full miss trace hashPath data functionTree argumentTree functionIH argumentIH =>
      apply invariant_miss valid miss accepted
      intro middle run keyed
      rw [full] at run
      have function := functionIH keyed trace.functionRun
      have argument := argumentIH function trace.argumentRun
      have compared := invariant_hash argument hashPath trace.compareRun
      rw [(trace.output_state run).2]
      exact compared.ofMaps rfl rfl rfl (data.coherent compared.coherent)
  | forallE miss trace opening domainTree bodyTree domainIH bodyIH =>
      apply invariant_miss valid miss accepted
      intro middle run keyed
      have domain := domainIH keyed trace.domainRun
      have opened := domain.openBinder opening trace.openRun
      have body := bodyIH opened trace.bodyRun
      rw [(trace.output_state run).2]
      exact body.ofMaps rfl rfl rfl (body.coherent.internExpr _)
  | lam full miss trace opening closing domainTree bodyTree domainIH bodyIH =>
      apply invariant_miss valid miss accepted
      intro middle run keyed
      rw [full] at run
      have domain := domainIH keyed trace.domainRun
      have opened := domain.openBinder opening trace.openRun
      have body := bodyIH opened trace.bodyRun
      rw [(trace.output_state run).2]
      exact body.ofMaps rfl rfl rfl ((closing.coherent body.coherent).internExpr _)

/-- Recover the existing cache-frame tree by deriving every constant leaf's
loader and post-lookup coherence from the single initial state invariant. -/
def OwnedInferenceTrace.toCacheTrace {source : Ixon.Env} {fuel : Nat}
    {before : TcState .anon} {term : KExpr .anon} (tree : OwnedInferenceTrace fuel before term)
    (valid : InferenceStateInvariant source before) : InferenceCacheTrace.{0} fuel before term :=
  match tree with
  | .hit cached => .hit cached
  | .sort miss => .sort miss
  | .fvar miss => .fvar miss
  | .nat miss => .nat miss
  | @OwnedInferenceTrace.const _ _ id _ _ miss data =>
      let keyed := valid.afterInferKey miss.keyRun
      let loader := keyed.owned.toVerified id.addr
      .lazyConst miss loader fun concrete loaded got =>
        .afterVerifiedGetConst loader keyed.coherent got
          (data.faithful concrete loaded got) (data.levels concrete loaded got)
  | .app full miss trace hashPath _ functionTree argumentTree =>
      let keyed := valid.afterInferKey miss.keyRun
      .app full miss trace hashPath (functionTree.toCacheTrace keyed)
        (argumentTree.toCacheTrace (functionTree.preserves keyed trace.functionRun))
  | .forallE miss trace opening domainTree bodyTree =>
      let keyed := valid.afterInferKey miss.keyRun
      let domain := domainTree.preserves keyed trace.domainRun
      .forallE miss trace (domainTree.toCacheTrace keyed)
        (bodyTree.toCacheTrace (domain.openBinder opening trace.openRun))
  | .lam full miss trace opening _ domainTree bodyTree =>
      let keyed := valid.afterInferKey miss.keyRun
      let domain := domainTree.preserves keyed trace.domainRun
      .lam full miss trace (domainTree.toCacheTrace keyed)
        (bodyTree.toCacheTrace (domain.openBinder opening trace.openRun))

theorem OwnedInferenceTrace.toCacheTrace_writes {source : Ixon.Env} {fuel : Nat}
    {before : TcState .anon} {term : KExpr .anon} (tree : OwnedInferenceTrace fuel before term)
    (valid : InferenceStateInvariant source before) :
    (tree.toCacheTrace valid).writes = tree.writes := by
  induction tree <;> simp only [toCacheTrace, writes, InferenceCacheTrace.writes, *]

/-- The whole call retains the earlier cache frame and returns both state
invariants. Only entries outside the computed write footprint are protected. -/
theorem OwnedInferenceTrace.frame {source : Ixon.Env} {fuel : Nat}
    {before after : TcState .anon} {term result : KExpr .anon}
    (tree : OwnedInferenceTrace fuel before term) (valid : InferenceStateInvariant source before)
    {key : Address × Address} (outside : key ∉ tree.writes)
    (accepted : RecM.infer term (methodsN fuel) before = .ok result after) :
    InferenceCacheFrame key before after ∧ after.inferOnly = before.inferOnly ∧
      InferenceStateInvariant source after :=
  let frame := (tree.toCacheTrace valid).frame (by rwa [tree.toCacheTrace_writes valid]) accepted
  ⟨frame.1, frame.2, tree.preserves valid accepted⟩

/-- Atomic constructors observe the actual cache selection. -/
def OwnedInferenceTrace.sortOfKey {fuel : Nat} {before keyed : TcState .anon}
    {level : KUniv .anon} {info : ExprInfo .anon} {key : Address × Address}
    (keyRun : TcM.inferKey (.sort level info) before = .ok key keyed) :
    OwnedInferenceTrace fuel before (.sort level info) := by
  rcases observeInferenceCache keyRun with ⟨hit, _, _⟩ | ⟨miss, _, _⟩
  · exact .hit hit
  · exact .sort miss

def OwnedInferenceTrace.fvarOfKey {fuel : Nat} {before keyed : TcState .anon}
    {id : FVarId} {name : Mode.anon.F Name} {info : ExprInfo .anon} {key : Address × Address}
    (keyRun : TcM.inferKey (.fvar id name info) before = .ok key keyed) :
    OwnedInferenceTrace fuel before (.fvar id name info) := by
  rcases observeInferenceCache keyRun with ⟨hit, _, _⟩ | ⟨miss, _, _⟩
  · exact .hit hit
  · exact .fvar miss

def OwnedInferenceTrace.natOfKey {fuel : Nat} {before keyed : TcState .anon}
    {value : Nat} {blob : Address} {info : ExprInfo .anon} {key : Address × Address}
    (keyRun : TcM.inferKey (.nat value blob info) before = .ok key keyed) :
    OwnedInferenceTrace fuel before (.nat value blob info) := by
  rcases observeInferenceCache keyRun with ⟨hit, _, _⟩ | ⟨miss, _, _⟩
  · exact .hit hit
  · exact .nat miss

def OwnedInferenceTrace.constOfKey {fuel : Nat} {before keyed : TcState .anon}
    {id : KId .anon} {arguments : Array (KUniv .anon)} {info : ExprInfo .anon}
    {key : Address × Address}
    (keyRun : TcM.inferKey (.const id arguments info) before = .ok key keyed)
    (data : ConstantInstantiationData keyed id arguments) :
    OwnedInferenceTrace fuel before (.const id arguments info) := by
  rcases observeInferenceCache keyRun with ⟨hit, _, _⟩ | ⟨miss, _, stateEq⟩
  · exact .hit hit
  · exact .const miss (by simpa only [stateEq] using data)

/-- A later constant inference reuses the invariant returned by any supported
recursive call, including when it must load another block. -/
theorem InferenceStateInvariant.afterConstInference {source : Ixon.Env} {fuel : Nat}
    {before keyed after : TcState .anon} {id : KId .anon}
    {arguments : Array (KUniv .anon)} {info : ExprInfo .anon} {key : Address × Address}
    {result : KExpr .anon} (valid : InferenceStateInvariant source before)
    (keyRun : TcM.inferKey (.const id arguments info) before = .ok key keyed)
    (data : ConstantInstantiationData keyed id arguments)
    (accepted : RecM.infer (.const id arguments info) (methodsN fuel) before = .ok result after) :
    InferenceStateInvariant source after :=
  (OwnedInferenceTrace.constOfKey keyRun data).preserves valid accepted

def CachedConstantInferenceSupport.afterOwnedRecursiveInference {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {source : Ixon.Env} {fuel : Nat} {before after : TcState .anon}
    {term result : KExpr .anon} {id : KId .anon} {arguments : Array (KUniv .anon)}
    {info : ExprInfo .anon} {ref : ConstRef β} {entry : ConstantEntry β} {type : AExpr β}
    (support : CachedConstantInferenceSupport resolve entries before id arguments info ref entry type)
    (closed : (KExpr.const id arguments info).lbr = 0)
    (tree : OwnedInferenceTrace fuel before term) (valid : InferenceStateInvariant source before)
    (outside : ((KExpr.const id arguments info).addr, emptyCtxAddr) ∉ tree.writes)
    (accepted : RecM.infer term (methodsN fuel) before = .ok result after) :
    CachedConstantInferenceSupport resolve entries after id arguments info ref entry type :=
  support.afterInference closed (tree.toCacheTrace valid)
    (by rwa [tree.toCacheTrace_writes valid]) accepted

/-- The later sort leaf no longer needs a separate post-inference coherence
premise. Its collision data and earlier cache agreement remain explicit. -/
def BinderInference.sortAfterOwnedInference {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {source : Ixon.Env} {fuel nextFuel : Nat}
    {before after : TcState .anon} {term result : KExpr .anon}
    {level : KUniv .anon} {info : ExprInfo .anon}
    (closed : (KExpr.sort level info).lbr = 0)
    (agreement : InferenceCacheAgreement before ((KExpr.sort level info).addr, emptyCtxAddr)
      (KExpr.mkSort (KUniv.mkSucc level)))
    (tree : OwnedInferenceTrace fuel before term) (valid : InferenceStateInvariant source before)
    (outside : ((KExpr.sort level info).addr, emptyCtxAddr) ∉ tree.writes)
    (accepted : RecM.infer term (methodsN fuel) before = .ok result after)
    (faithful : KExpr.KeyCollisionFree fun candidate => after.env.intern.ExprSupport candidate ∨
      candidate = KExpr.mkSort (KUniv.mkSucc level)) :
    BinderInference resolve entries locals context nextFuel after (.sort level info)
      (.sort (readLevel level)) (.sort (.succ (readLevel level))) :=
  .sortAfterInference closed agreement (tree.toCacheTrace valid)
    (by rwa [tree.toCacheTrace_writes valid]) accepted (tree.preserves valid accepted).coherent faithful

end Ix.Kernel.Consistency
