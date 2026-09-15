/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.SourceAgreement

/-!
# Inference cache agreement established from source

A finite catalog selects closed sort and standalone-constant instances. Its
expected types come from source prediction and pure universe substitution.
Both inference partitions start empty and retain this agreement through actual
recursive calls, including writes at catalog keys. Later hits need no separate
observation asserting their type or the presence of a loaded declaration.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- A source request records syntax, arity, and a pure conversion result.
It contains no inference run, cache observation, or semantic typing premise. -/
inductive SourceCacheRequest (source : Ixon.Env) where
  | sort (level : KUniv .anon)
  | const (id : KId .anon) (arguments : Array (KUniv .anon))
      (declaration : KConst .anon) (result : KExpr .anon)
      (predicted : predictStandalone? source id.addr = .ok (some declaration))
      (arity : declaration.lvls.toNat = arguments.size)
      (substitution : KExpr.instantiateUnivParamsSpec declaration.ty arguments = .ok result)
  /-- A closed natural-number literal, typed by the named primitive `Nat` constant. -/
  | nat (value : Nat) (prim : KId .anon)

def SourceCacheRequest.term {source : Ixon.Env} : SourceCacheRequest source → KExpr .anon
  | .sort level => .mkSort level
  | .const id arguments .. => .mkConst id arguments
  | .nat value _ => .mkNatLit value

def SourceCacheRequest.result {source : Ixon.Env} : SourceCacheRequest source → KExpr .anon
  | .sort level => .mkSort (.mkSucc level)
  | .const _ _ _ result .. => result
  | .nat _ prim => .mkConst prim #[]

def SourceCacheRequest.key {source : Ixon.Env} (request : SourceCacheRequest source) :
    Address × Address := (request.term.addr, emptyCtxAddr)

theorem SourceCacheRequest.closed {source : Ixon.Env} (request : SourceCacheRequest source) :
    request.term.lbr = 0 := by cases request <;> rfl

/-- Constant cache entries retain the source declaration that produced them. -/
def SourceCacheRequest.Loaded {source : Ixon.Env} (request : SourceCacheRequest source)
    (before : TcState .anon) : Prop :=
  match request with
  | .sort _ => True
  | .const id _ declaration .. => before.env.get? id = some declaration
  | .nat .. => True

theorem SourceCacheRequest.Loaded.frame {source : Ixon.Env} {request : SourceCacheRequest source}
    {before after : TcState .anon} (loaded : request.Loaded before)
    (constants : ∀ id declaration, before.env.get? id = some declaration →
      after.env.get? id = some declaration) : request.Loaded after := by
  cases request with
  | sort => trivial
  | const => exact constants _ _ loaded
  | nat => trivial

theorem SourceCacheRequest.Loaded.ofMap {source : Ixon.Env} {request : SourceCacheRequest source}
    {before after : TcState .anon} (loaded : request.Loaded before)
    (constants : after.env.consts = before.env.consts) : request.Loaded after :=
  loaded.frame (fun _ _ found => by simpa only [KEnv.get?, constants] using found)

structure SourceCacheEntry {source : Ixon.Env} (request : SourceCacheRequest source)
    (before : TcState .anon) : Prop where
  correct : InferenceCacheAgreement before request.key request.result
  loaded : ∀ cached, before.env.inferCache[request.key]? = some cached ∨
    before.env.inferOnlyCache[request.key]? = some cached → request.Loaded before

theorem SourceCacheEntry.frame {source : Ixon.Env} {request : SourceCacheRequest source}
    {before after : TcState .anon} (entry : SourceCacheEntry request before)
    (frame : InferenceCacheFrame request.key before after) : SourceCacheEntry request after := by
  refine ⟨entry.correct.frame frame, ?_⟩
  intro cached present
  have old : before.env.inferCache[request.key]? = some cached ∨
      before.env.inferOnlyCache[request.key]? = some cached := by
    simpa only [frame.full, frame.only] using present
  exact (entry.loaded cached old).frame frame.constants

/-- Agreement includes both partitions, even when only one is currently eligible. -/
def SourceCacheAgreement {source : Ixon.Env} (catalog : List (SourceCacheRequest source))
    (before : TcState .anon) : Prop :=
  ∀ request ∈ catalog, SourceCacheEntry request before

theorem SourceCacheAgreement.empty (source : Ixon.Env) (catalog : List (SourceCacheRequest source)) :
    SourceCacheAgreement catalog (TcState.newLazyAnon source) := by
  intro request member
  constructor
  · constructor <;> intro cached found <;> simp [TcState.newLazyAnon] at found
  · intro cached found
    simp [TcState.newLazyAnon] at found

theorem SourceCacheAgreement.ofMaps {source : Ixon.Env} {catalog : List (SourceCacheRequest source)}
    {before after : TcState .anon} (agreement : SourceCacheAgreement catalog before)
    (full : after.env.inferCache = before.env.inferCache)
    (only : after.env.inferOnlyCache = before.env.inferOnlyCache)
    (constants : after.env.consts = before.env.consts) :
    SourceCacheAgreement catalog after := by
  intro request member
  exact (agreement request member).frame
    (.of_eq (by rw [full]) (by rw [only]) constants)

theorem SourceCacheAgreement.afterInferKey {source : Ixon.Env}
    {catalog : List (SourceCacheRequest source)} {before after : TcState .anon}
    {term : KExpr .anon} {key : Address × Address}
    (agreement : SourceCacheAgreement catalog before)
    (run : TcM.inferKey term before = .ok key after) : SourceCacheAgreement catalog after :=
  agreement.ofMaps (congrArg KEnv.inferCache (inferKey_environment run))
    (congrArg KEnv.inferOnlyCache (inferKey_environment run))
    (congrArg KEnv.consts (inferKey_environment run))

theorem SourceCacheAgreement.openBinder {source : Ixon.Env}
    {catalog : List (SourceCacheRequest source)} {before after : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body opened : KExpr .anon} {fresh : FVarId}
    (agreement : SourceCacheAgreement catalog before)
    (run : TcM.openBinder name bi domain body before = .ok (opened, fresh) after) :
    SourceCacheAgreement catalog after := by
  intro request member
  apply (agreement request member).frame
  have frame := PreservesInferenceCache.openBinder request.key name bi domain body before
  simpa only [run] using frame

theorem SourceCacheAgreement.getConst {source : Ixon.Env}
    {catalog : List (SourceCacheRequest source)} {before : TcState .anon} {id : KId .anon}
    (agreement : SourceCacheAgreement catalog before) (valid : SourceStateInvariant source before) :
    match TcM.getConst id before with
    | .ok _ after | .error _ after => SourceCacheAgreement catalog after := by
  have frame := getConst_owned (id := id) valid.state.owned
  cases run : TcM.getConst id before <;> rw [run] at frame <;>
    exact fun request member => (agreement request member).frame (frame.1.cache request.key)

/-- A write at a catalog key must contain its predicted type. Other writes
retain agreement without constraining their values. -/
theorem SourceCacheAgreement.write {source : Ixon.Env}
    {catalog : List (SourceCacheRequest source)} {before after : TcState .anon}
    {key : Address × Address} {result : KExpr .anon} {policy : Bool} {methods : Methods .anon}
    (agreement : SourceCacheAgreement catalog before)
    (correct : ∀ request ∈ catalog, key = request.key →
      result = request.result ∧ request.Loaded before)
    (run : RecM.cacheInferResult policy key result methods before = .ok () after) :
    SourceCacheAgreement catalog after := by
  intro request member
  by_cases same : key = request.key
  · obtain ⟨resultEq, loaded⟩ := correct request member same
    subst key result
    refine ⟨(agreement request member).correct.write run, ?_⟩
    intro cached present
    apply loaded.ofMap
    rw [cacheInferResult_eq] at run
    cases policy <;> cases run <;> rfl
  · apply (agreement request member).frame
    have frame := PreservesInferenceCache.write_other same policy result methods before
    simpa only [run] using frame

/-- The key always stores the actual input address, even when its context
component required memoization. -/
theorem inferKey_address {term : KExpr .anon} {before after : TcState .anon}
    {key : Address × Address} (run : TcM.inferKey term before = .ok key after) :
    key.1 = term.addr := by
  unfold TcM.inferKey at run
  change EStateM.bind (TcM.ctxAddrForLbr term.lbr) _ before = _ at run
  rw [EStateM.bind] at run
  cases computed : TcM.ctxAddrForLbr term.lbr before <;> rw [computed] at run
  · cases run; rfl
  · contradiction

/-- A finite collision domain consists only of one executed input and the
catalog's inputs. It prevents another syntax form from writing a catalog key. -/
def SourceCacheKeyData {source : Ixon.Env} (catalog : List (SourceCacheRequest source))
    (term : KExpr .anon) : Prop :=
  KExpr.CollisionFree fun candidate => candidate = term ∨
    ∃ request ∈ catalog, candidate = request.term

theorem SourceCacheKeyData.same {source : Ixon.Env}
    {catalog : List (SourceCacheRequest source)} {term : KExpr .anon}
    {before after : TcState .anon} {key : Address × Address}
    (data : SourceCacheKeyData catalog term) {request : SourceCacheRequest source}
    (member : request ∈ catalog) (run : TcM.inferKey term before = .ok key after)
    (same : key = request.key) : term = request.term := by
  have addr : term.addr = request.term.addr :=
    (inferKey_address run).symm.trans (congrArg Prod.fst same)
  simpa only [KExpr.eraseMeta_anon] using data (Or.inl rfl) (Or.inr ⟨request, member, rfl⟩) addr

private theorem request_sort {source : Ixon.Env} {request : SourceCacheRequest source}
    {level : KUniv .anon} {info : ExprInfo .anon} (before : TcState .anon)
    (equal : KExpr.sort level info = request.term) :
    request.result = KExpr.mkSort (KUniv.mkSucc level) ∧ request.Loaded before := by
  cases request with
  | sort other =>
      change KExpr.sort level info = KExpr.sort other _ at equal
      have levels := (KExpr.sort.inj equal).1
      subst other
      exact ⟨rfl, trivial⟩
  | const id arguments declaration result predicted arity substitution =>
      change KExpr.sort level info = KExpr.const id arguments _ at equal
      cases equal
  | nat value prim =>
      change KExpr.sort level info = KExpr.nat value _ _ at equal
      cases equal

private theorem request_const {source : Ixon.Env} {request : SourceCacheRequest source}
    {id : KId .anon} {arguments : Array (KUniv .anon)} {info : ExprInfo .anon}
    (equal : KExpr.const id arguments info = request.term) :
    ∃ declaration, predictStandalone? source id.addr = .ok (some declaration) ∧
      declaration.lvls.toNat = arguments.size ∧
      KExpr.instantiateUnivParamsSpec declaration.ty arguments = .ok request.result ∧
      (∀ before : TcState .anon, before.env.get? id = some declaration → request.Loaded before) := by
  cases request with
  | sort level =>
      change KExpr.const id arguments info = KExpr.sort level _ at equal
      cases equal
  | const other levels declaration result predicted arity substitution =>
      change KExpr.const id arguments info = KExpr.const other levels _ at equal
      obtain ⟨rfl, rfl, _⟩ := KExpr.const.inj equal
      exact ⟨declaration, predicted, arity, substitution, fun _ loaded => loaded⟩
  | nat value prim =>
      change KExpr.const id arguments info = KExpr.nat value _ _ at equal
      cases equal

/-- A literal request at a literal's key names the same value; its expected
type is the constant at the request's primitive. -/
private theorem request_nat {source : Ixon.Env} {request : SourceCacheRequest source}
    {value : Nat} {blob : Address} {info : ExprInfo .anon} (before : TcState .anon)
    (equal : KExpr.nat value blob info = request.term) :
    ∃ prim, request = .nat value prim ∧ request.result = KExpr.mkConst prim #[] ∧
      request.Loaded before := by
  cases request with
  | sort level =>
      change KExpr.nat value blob info = KExpr.sort level _ at equal
      cases equal
  | const id arguments declaration result predicted arity substitution =>
      change KExpr.nat value blob info = KExpr.const id arguments _ at equal
      cases equal
  | nat other prim =>
      change KExpr.nat value blob info = KExpr.nat other _ _ at equal
      obtain ⟨rfl, _, _⟩ := KExpr.nat.inj equal
      exact ⟨prim, rfl, rfl, trivial⟩

/-- Recursive nodes contain only finite key-collision data and the proposed
sort result's intern domain. Constant walkers already supply their finite
substitution data in `OwnedInferenceTrace`, and source conversion data is
carried by `SourceData`. -/
def OwnedInferenceTrace.CacheData {source : Ixon.Env} (catalog : List (SourceCacheRequest source))
    {fuel : Nat} {before : TcState .anon} {term : KExpr .anon}
    (tree : OwnedInferenceTrace fuel before term) : Prop :=
  match tree with
  | .hit _ => True
  | @OwnedInferenceTrace.sort _ _ level _ miss =>
      SourceCacheKeyData catalog term ∧ KExpr.KeyCollisionFree fun candidate =>
        miss.keyed.env.intern.ExprSupport candidate ∨ candidate = KExpr.mkSort (KUniv.mkSucc level)
  | .fvar _ | .const _ _ => SourceCacheKeyData catalog term
  | @OwnedInferenceTrace.nat _ _ value _ _ miss =>
      SourceCacheKeyData catalog term ∧
        (∀ prim, SourceCacheRequest.nat value prim ∈ catalog → prim = miss.keyed.prims.nat) ∧
        KExpr.KeyCollisionFree fun candidate => miss.keyed.env.intern.ExprSupport candidate ∨
          candidate = KExpr.mkConst miss.keyed.prims.nat #[]
  | .app _ _ _ _ _ first second | .forallE _ _ _ first second |
      .lam _ _ _ _ _ first second =>
      SourceCacheKeyData catalog term ∧ first.CacheData catalog ∧ second.CacheData catalog

private theorem source_cache_hash {source : Ixon.Env} {catalog : List (SourceCacheRequest source)}
    {before after : TcState .anon} {left right : KExpr .anon} {methods : Methods .anon}
    (agreement : SourceCacheAgreement catalog before) (equal : (left.addr == right.addr) = true)
    (run : RecM.isDefEq left right methods before = .ok true after) :
    SourceCacheAgreement catalog after := by
  intro request member
  exact (agreement request member).frame (isDefEq_hash_frame equal run request.key).1

private theorem source_cache_miss {source : Ixon.Env} {catalog : List (SourceCacheRequest source)}
    {term result : KExpr .anon} {methods : Methods .anon} {before after : TcState .anon}
    (valid : SourceStateInvariant source before) (agreement : SourceCacheAgreement catalog before)
    (miss : UncachedInference before term)
    (accepted : RecM.infer term methods before = .ok result after)
    (uncached : ∀ middle,
      RecM.inferUncached RecM.inferCall before.inferOnly term methods miss.keyed = .ok result middle →
      SourceStateInvariant source miss.keyed → SourceCacheAgreement catalog miss.keyed →
      SourceCacheAgreement catalog middle ∧
        (∀ request ∈ catalog, miss.key = request.key →
          result = request.result ∧ request.Loaded middle)) : SourceCacheAgreement catalog after := by
  obtain ⟨middle, run, written⟩ := infer_uncached_success_state miss accepted
  obtain ⟨post, correct⟩ := uncached middle run (valid.afterInferKey miss.keyRun)
    (agreement.afterInferKey miss.keyRun)
  apply post.write (policy := before.inferOnly) (methods := methods) correct
  rw [cacheInferResult_eq, written]

/-- The complete recursive call preserves both partitions at every catalog
key, including keys written by its constant and sort leaves. Key collision
data rules out writes from a different syntax form at those same addresses. -/
theorem OwnedInferenceTrace.preservesCache {source : Ixon.Env}
    {catalog : List (SourceCacheRequest source)} {fuel : Nat}
    {before after : TcState .anon} {term result : KExpr .anon}
    (tree : OwnedInferenceTrace fuel before term) (valid : SourceStateInvariant source before)
    (agreement : SourceCacheAgreement catalog before) (sourceData : tree.SourceData source)
    (cacheData : tree.CacheData catalog)
    (accepted : RecM.infer term (methodsN fuel) before = .ok result after) :
    SourceCacheAgreement catalog after := by
  induction tree generalizing result after with
  | hit hit =>
      rw [hit.run] at accepted
      cases accepted
      exact agreement.afterInferKey hit.keyRun
  | @sort fuel before level info miss =>
      apply source_cache_miss valid agreement miss accepted
      intro middle run keyed cache
      change EStateM.Result.ok
        (miss.keyed.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).1
        {miss.keyed with env := {miss.keyed.env with intern :=
          (miss.keyed.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).2}} =
        .ok result middle at run
      cases run
      refine ⟨cache.ofMaps rfl rfl rfl, ?_⟩
      intro request member same
      have equal := cacheData.1.same member miss.keyRun same
      obtain ⟨typeEq, loaded⟩ := request_sort _ equal
      refine ⟨?_, loaded⟩
      rw [typeEq]
      simpa only [KExpr.eraseMeta_anon] using
        miss.keyed.env.intern.internExpr_eraseMeta keyed.state.coherent cacheData.2
  | @fvar fuel before id name info miss =>
      apply source_cache_miss valid agreement miss accepted
      intro middle run keyed cache
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
        refine ⟨cache, ?_⟩
        intro request member same
        have equal := cacheData.same member miss.keyRun same
        cases request <;> cases equal
      · contradiction
  | @nat fuel before value blob info miss =>
      apply source_cache_miss valid agreement miss accepted
      intro middle run keyed cache
      obtain ⟨rfl, rfl⟩ := inferUncached_nat_run run
      refine ⟨cache.ofMaps rfl rfl rfl, ?_⟩
      intro request member same
      have equal := cacheData.1.same member miss.keyRun same
      obtain ⟨prim, rfl, typeEq, loaded⟩ := request_nat _ equal
      refine ⟨?_, loaded⟩
      rw [typeEq, cacheData.2.1 prim member]
      simpa only [KExpr.eraseMeta_anon] using
        miss.keyed.env.intern.internExpr_eraseMeta keyed.state.coherent cacheData.2.2
  | @const fuel before id arguments info miss data =>
      apply source_cache_miss valid agreement miss accepted
      intro middle run keyed cache
      obtain ⟨concrete, loaded, got, _, instantiated⟩ := inferUncached_const_instantiation run
      have post := keyed.getConst sourceData
      have retained := cache.getConst (id := id) keyed
      rw [got] at post retained
      have walked := TcM.instantiateUnivParams_wf (data.faithful concrete loaded got)
        (fun _ h => Or.inr h) ⟨post.state.coherent, fun _ h => Or.inl h⟩
      rw [instantiated] at walked
      refine ⟨?_, ?_⟩
      · rw [walked.2.2.1]
        exact retained.ofMaps rfl rfl rfl
      · intro request member same
        obtain ⟨declaration, predicted, _, substitution, load⟩ :=
          request_const (cacheData.same member miss.keyRun same)
        have equal := post.agreement id concrete (getConst_result_loaded got) declaration predicted
        have prediction := walked.2.1
        rw [equal] at prediction
        refine ⟨Except.ok.inj (prediction.symm.trans substitution), ?_⟩
        rw [walked.2.2.1]
        apply (load loaded (by rw [← equal]; exact getConst_result_loaded got)).ofMap rfl
  | @app fuel before fn arg info full miss trace hashPath data functionTree argumentTree functionIH argumentIH =>
      apply source_cache_miss valid agreement miss accepted
      intro middle run keyed cache
      rw [full] at run
      have functionState := functionTree.preservesSource keyed sourceData.1 trace.functionRun
      have function := functionIH keyed cache sourceData.1 cacheData.2.1 trace.functionRun
      have argument := argumentIH functionState function sourceData.2 cacheData.2.2 trace.argumentRun
      have compared := source_cache_hash argument hashPath trace.compareRun
      refine ⟨?_, ?_⟩
      · rw [(trace.output_state run).2]
        exact compared.ofMaps rfl rfl rfl
      · intro request member same
        have equal := cacheData.1.same member miss.keyRun same
        cases request <;> cases equal
  | @forallE fuel before name bi domain body info miss trace opening domainTree bodyTree domainIH bodyIH =>
      apply source_cache_miss valid agreement miss accepted
      intro middle run keyed cache
      have domainState := domainTree.preservesSource keyed sourceData.1 trace.domainRun
      have domainCache := domainIH keyed cache sourceData.1 cacheData.2.1 trace.domainRun
      have bodyCache := bodyIH (domainState.openBinder opening trace.openRun)
        (domainCache.openBinder trace.openRun) sourceData.2 cacheData.2.2 trace.bodyRun
      refine ⟨?_, ?_⟩
      · rw [(trace.output_state run).2]
        exact bodyCache.ofMaps rfl rfl rfl
      · intro request member same
        have equal := cacheData.1.same member miss.keyRun same
        cases request <;> cases equal
  | @lam fuel before name bi domain body info full miss trace opening closing domainTree bodyTree domainIH bodyIH =>
      apply source_cache_miss valid agreement miss accepted
      intro middle run keyed cache
      rw [full] at run
      have domainState := domainTree.preservesSource keyed sourceData.1 trace.domainRun
      have domainCache := domainIH keyed cache sourceData.1 cacheData.2.1 trace.domainRun
      have bodyCache := bodyIH (domainState.openBinder opening trace.openRun)
        (domainCache.openBinder trace.openRun) sourceData.2 cacheData.2.2 trace.bodyRun
      refine ⟨?_, ?_⟩
      · rw [(trace.output_state run).2]
        exact bodyCache.ofMaps rfl rfl rfl
      · intro request member same
        have equal := cacheData.1.same member miss.keyRun same
        cases request <;> cases equal

/-- Source, intern, and cache agreement form the resource returned to the
next call. The catalog is fixed independently of mutable cache contents. -/
structure SourceCacheInvariant {source : Ixon.Env} (catalog : List (SourceCacheRequest source))
    (before : TcState .anon) : Prop where
  state : SourceStateInvariant source before
  cache : SourceCacheAgreement catalog before

theorem SourceCacheInvariant.ofCheckedSource (source : Ixon.Env)
    (catalog : List (SourceCacheRequest source)) (checked : sourceOwnershipCheck source = true) :
    SourceCacheInvariant catalog (TcState.newLazyAnon source) :=
  ⟨.ofCheckedSource source checked, .empty source catalog⟩

theorem OwnedInferenceTrace.preservesSourceCache {source : Ixon.Env}
    {catalog : List (SourceCacheRequest source)} {fuel : Nat}
    {before after : TcState .anon} {term result : KExpr .anon}
    (tree : OwnedInferenceTrace fuel before term) (valid : SourceCacheInvariant catalog before)
    (sourceData : tree.SourceData source) (cacheData : tree.CacheData catalog)
    (accepted : RecM.infer term (methodsN fuel) before = .ok result after) :
    SourceCacheInvariant catalog after :=
  ⟨tree.preservesSource valid.state sourceData accepted,
    tree.preservesCache valid.state valid.cache sourceData cacheData accepted⟩

theorem SourceCacheInvariant.getConst {source : Ixon.Env}
    {catalog : List (SourceCacheRequest source)} {before : TcState .anon} {id : KId .anon}
    (valid : SourceCacheInvariant catalog before)
    (data : StandaloneConversionData source id.addr before.env) :
    match TcM.getConst id before with
    | .ok _ after | .error _ after => SourceCacheInvariant catalog after := by
  have state := valid.state.getConst data
  have cache := valid.cache.getConst (id := id) valid.state
  cases run : TcM.getConst id before <;> rw [run] at state cache <;> exact ⟨state, cache⟩

theorem SourceCacheInvariant.policy {source : Ixon.Env}
    {catalog : List (SourceCacheRequest source)} {before : TcState .anon}
    (valid : SourceCacheInvariant catalog before) (policy : Bool) :
    SourceCacheInvariant catalog {before with inferOnly := policy} :=
  ⟨valid.state.ofMaps rfl rfl rfl valid.state.state.coherent, valid.cache.ofMaps rfl rfl rfl⟩

theorem SourceCacheInvariant.truncate {source : Ixon.Env}
    {catalog : List (SourceCacheRequest source)} {before : TcState .anon}
    (valid : SourceCacheInvariant catalog before) (size : Nat) :
    SourceCacheInvariant catalog {before with lctx := before.lctx.truncate size} :=
  ⟨valid.state.ofMaps rfl rfl rfl valid.state.state.coherent, valid.cache.ofMaps rfl rfl rfl⟩

theorem SourceCacheInvariant.openBinder {source : Ixon.Env}
    {catalog : List (SourceCacheRequest source)} {before after : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body opened : KExpr .anon} {fresh : FVarId}
    (valid : SourceCacheInvariant catalog before) (data : BinderOpeningData before body)
    (run : TcM.openBinder name bi domain body before = .ok (opened, fresh) after) :
    SourceCacheInvariant catalog after :=
  ⟨valid.state.openBinder data run, valid.cache.openBinder run⟩

theorem SourceCacheInvariant.clearReductionCaches {source : Ixon.Env}
    {catalog : List (SourceCacheRequest source)} {before : TcState .anon}
    (valid : SourceCacheInvariant catalog before) :
    SourceCacheInvariant catalog {before with env := before.env.clearReductionCaches} := by
  refine ⟨valid.state.ofMaps rfl rfl rfl valid.state.state.coherent, ?_⟩
  intro request member
  refine ⟨.clearReductionCaches before request.key request.result, ?_⟩
  intro cached present
  simp [KEnv.clearReductionCaches] at present

/-- An execution history starts at the actual empty lazy state and records
operations and finite data, never a cache-correctness or typing assumption. -/
inductive SourceCacheHistory {source : Ixon.Env} (catalog : List (SourceCacheRequest source)) :
    TcState .anon → Prop
  | initial (checked : sourceOwnershipCheck source = true) :
      SourceCacheHistory catalog (TcState.newLazyAnon source)
  | infer {fuel before after term result}
      (previous : SourceCacheHistory catalog before) (tree : OwnedInferenceTrace fuel before term)
      (sourceData : tree.SourceData source) (cacheData : tree.CacheData catalog)
      (accepted : RecM.infer term (methodsN fuel) before = .ok result after) :
      SourceCacheHistory catalog after
  | getConst {before after id declaration} (previous : SourceCacheHistory catalog before)
      (data : StandaloneConversionData source id.addr before.env)
      (run : TcM.getConst id before = .ok declaration after) : SourceCacheHistory catalog after
  | failedGetConst {before after id error} (previous : SourceCacheHistory catalog before)
      (data : StandaloneConversionData source id.addr before.env)
      (run : TcM.getConst id before = .error error after) : SourceCacheHistory catalog after
  | policy {before} (previous : SourceCacheHistory catalog before) (policy : Bool) :
      SourceCacheHistory catalog {before with inferOnly := policy}
  | openBinder {before after name bi domain body opened fresh}
      (previous : SourceCacheHistory catalog before) (data : BinderOpeningData before body)
      (run : TcM.openBinder name bi domain body before = .ok (opened, fresh) after) :
      SourceCacheHistory catalog after
  | truncate {before} (previous : SourceCacheHistory catalog before) (size : Nat) :
      SourceCacheHistory catalog {before with lctx := before.lctx.truncate size}
  | clear {before} (previous : SourceCacheHistory catalog before) :
      SourceCacheHistory catalog {before with env := before.env.clearReductionCaches}

theorem SourceCacheHistory.invariant {source : Ixon.Env} {catalog : List (SourceCacheRequest source)}
    {before : TcState .anon} (history : SourceCacheHistory catalog before) :
    SourceCacheInvariant catalog before := by
  induction history with
  | initial checked => exact .ofCheckedSource source catalog checked
  | infer previous tree sourceData cacheData accepted ih =>
      exact tree.preservesSourceCache ih sourceData cacheData accepted
  | getConst previous data run ih | failedGetConst previous data run ih =>
      have post := ih.getConst data
      simpa only [run] using post
  | policy previous policy ih => exact ih.policy policy
  | openBinder previous data run ih => exact ih.openBinder data run
  | truncate previous size ih => exact ih.truncate size
  | clear previous ih => exact ih.clearReductionCaches

/-- Static source/model bindings supply catalog requests independently of
the checker's mutable state or its cache selection. -/
def StandaloneModelBinding.cacheRequest {β : Type u} {source : Ixon.Env}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {id : KId .anon} {ref : ConstRef β} {entry : ConstantEntry β}
    (binding : StandaloneModelBinding source resolve entries id ref entry)
    (arguments : Array (KUniv .anon)) (result : KExpr .anon)
    (arity : entry.universes = arguments.size)
    (substitution : KExpr.instantiateUnivParamsSpec binding.constant.ty arguments = .ok result) :
    SourceCacheRequest source :=
  .const id arguments binding.constant result binding.predicted (binding.universes.trans arity) substitution

/-- A real selected hit obtains its complete earlier inference interface from
maintained catalog agreement. The loaded declaration and cached substitution
are derived here, including for the inference-only partition. -/
def CachedConstantInferenceSupport.ofSourceCache {β : Type u} {source : Ixon.Env}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {id : KId .anon} {ref : ConstRef β} {entry : ConstantEntry β}
    {arguments : Array (KUniv .anon)} {result : KExpr .anon} {type : AExpr β}
    {catalog : List (SourceCacheRequest source)} {before : TcState .anon}
    (binding : StandaloneModelBinding source resolve entries id ref entry)
    (arity : entry.universes = arguments.size)
    (substitution : KExpr.instantiateUnivParamsSpec binding.constant.ty arguments = .ok result)
    (member : binding.cacheRequest arguments result arity substitution ∈ catalog)
    (valid : SourceCacheInvariant catalog before) (wellFormed : entries.WF)
    (instantiation : ConstantInstantiationData before id arguments)
    (prediction : readInstantiatedType? resolve binding.constant.ty arguments = some type.erase)
    (conditions : (entry.type.instL (arguments.toList.map readLevel)).annotations = type.annotations)
    (hit : InferenceCacheHit before (.mkConst id arguments)) :
    CachedConstantInferenceSupport resolve entries before id arguments
      (KExpr.mkConst id arguments).info ref entry type := by
  let request := binding.cacheRequest arguments result arity substitution
  have requestKey : request.key = ((KExpr.mkConst id arguments).addr, emptyCtxAddr) := rfl
  have requestResult : request.result = result := rfl
  have cached := valid.cache request member
  obtain ⟨keyEq, stateEq⟩ := hit.key_closed (by rfl)
  have selected : before.env.inferCache[request.key]? = some hit.cached ∨
      before.env.inferOnlyCache[request.key]? = some hit.cached := by
    rcases hit.selected with full | ⟨_, _, only⟩
    · exact .inl (by simpa only [stateEq, keyEq, requestKey] using full)
    · exact .inr (by simpa only [stateEq, keyEq, requestKey] using only)
  have loaded : before.env.get? id = some binding.constant := cached.loaded _ selected
  have equal : hit.cached = result := InferenceCacheAgreement.selected hit
    (by simpa only [stateEq, keyEq, requestKey, requestResult] using cached.correct)
  exact {
    hit
    concrete := binding.constant
    loaded := by rwa [stateEq]
    resolved := binding.resolved
    found := binding.found
    count := binding.universes
    arity := binding.universes.trans arity
    scope := wellFormed.typeScope ref entry binding.found
    reading := binding.reading
    levels := instantiation.levels binding.constant before (getConst_loaded loaded)
    substitution := by rw [equal]; exact substitution
    prediction, conditions
  }

/-- Construct a constant inference leaf by observing production's actual
selection. Source bindings and the history-derived invariant supply both
miss and hit interfaces; no lookup reading or cache agreement is an input. -/
def BinderInference.constFromSourceCache {β : Type u} {source : Ixon.Env}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {fuel : Nat}
    {id : KId .anon} {ref : ConstRef β} {entry : ConstantEntry β}
    {arguments : Array (KUniv .anon)} {result : KExpr .anon} {type : AExpr β}
    {catalog : List (SourceCacheRequest source)} {before : TcState .anon}
    (binding : StandaloneModelBinding source resolve entries id ref entry)
    (arity : entry.universes = arguments.size)
    (substitution : KExpr.instantiateUnivParamsSpec binding.constant.ty arguments = .ok result)
    (member : binding.cacheRequest arguments result arity substitution ∈ catalog)
    (valid : SourceCacheInvariant catalog before) (wellFormed : entries.WF)
    (conversion : StandaloneConversionData source id.addr before.env)
    (instantiation : ConstantInstantiationData before id arguments)
    (prediction : readInstantiatedType? resolve binding.constant.ty arguments = some type.erase)
    (conditions : (entry.type.instL (arguments.toList.map readLevel)).annotations = type.annotations) :
    BinderInference resolve entries locals context fuel before (.mkConst id arguments)
      (.const ref (arguments.toList.map readLevel)) type := by
  rcases observeInferenceCache (inferKey_closed (term := KExpr.mkConst id arguments) rfl before) with
    ⟨hit, _, _⟩ | ⟨miss, _, stateEq⟩
  · exact .cachedConst (.ofSourceCache binding arity substitution member valid wellFormed
      instantiation prediction conditions hit)
  · have keyed := valid.state.afterInferKey miss.keyRun
    have convert : StandaloneConversionData source id.addr miss.keyed.env := by rwa [stateEq]
    refine .polymorphic miss (.ofSource binding keyed wellFormed convert
      (by rwa [stateEq])) ?_ conditions
    intro concrete loaded got
    have post := keyed.getConst convert
    rw [got] at post
    have equal := post.agreement id concrete (getConst_result_loaded got) binding.constant binding.predicted
    rw [equal]
    exact prediction

def BinderInference.sortFromSourceCache {β : Type u} {source : Ixon.Env}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {fuel : Nat}
    {catalog : List (SourceCacheRequest source)} {before : TcState .anon} {level : KUniv .anon}
    (valid : SourceCacheInvariant catalog before) (member : SourceCacheRequest.sort level ∈ catalog)
    (faithful : KExpr.KeyCollisionFree fun term => before.env.intern.ExprSupport term ∨
      term = KExpr.mkSort (KUniv.mkSucc level)) :
    BinderInference resolve entries locals context fuel before (.mkSort level)
      (.sort (readLevel level)) (.sort (.succ (readLevel level))) :=
  .sortOfAgreement rfl (valid.cache (.sort level) member).correct valid.state.state.coherent faithful

/-- A literal leaf from catalog agreement at the literal's key. The catalog
request names the run's primitive `Nat` constant; the binding supplies the
model entry behind it. -/
def BinderInference.natFromSourceCache {β : Type u} {source : Ixon.Env}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {fuel : Nat}
    {catalog : List (SourceCacheRequest source)} {before : TcState .anon} {value : Nat}
    (valid : SourceCacheInvariant catalog before)
    (binding : PrimitiveNatBinding resolve entries before.prims)
    (member : SourceCacheRequest.nat value before.prims.nat ∈ catalog)
    (faithful : KExpr.KeyCollisionFree fun term => before.env.intern.ExprSupport term ∨
      term = KExpr.mkConst before.prims.nat #[]) :
    BinderInference resolve entries locals context fuel before (.mkNatLit value)
      (.natLit value) (.const binding.ref []) :=
  .natOfAgreement rfl binding (valid.cache (.nat value before.prims.nat) member).correct
    valid.state.state.coherent faithful

/-- Actual constant inference is model-typed after a history beginning with
empty caches. Both cache partitions and the miss path are handled by actual
selection; no initial cache agreement or post-lookup reading is assumed. -/
theorem infer_const_history_sound {β : Type u} {source : Ixon.Env}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {context : Model.Context β} {id : KId .anon} {ref : ConstRef β} {entry : ConstantEntry β}
    {arguments : Array (KUniv .anon)} {expected result : KExpr .anon} {type : AExpr β}
    {catalog : List (SourceCacheRequest source)} {before after : TcState .anon}
    {methods : Methods .anon}
    (binding : StandaloneModelBinding source resolve entries id ref entry)
    (arity : entry.universes = arguments.size)
    (substitution : KExpr.instantiateUnivParamsSpec binding.constant.ty arguments = .ok expected)
    (member : binding.cacheRequest arguments expected arity substitution ∈ catalog)
    (history : SourceCacheHistory catalog before) (wellFormed : entries.WF)
    (conversion : StandaloneConversionData source id.addr before.env)
    (instantiation : ConstantInstantiationData before id arguments)
    (prediction : readInstantiatedType? resolve binding.constant.ty arguments = some type.erase)
    (conditions : (entry.type.instL (arguments.toList.map readLevel)).annotations = type.annotations)
    (accepted : RecM.infer (.mkConst id arguments) methods before = .ok result after) :
    ModelTyping.{u,v} resolve entries context (.mkConst id arguments) result := by
  have valid := history.invariant
  rcases observeInferenceCache (inferKey_closed (term := KExpr.mkConst id arguments) rfl before) with
    ⟨hit, _, _⟩ | ⟨miss, _, stateEq⟩
  · have support := CachedConstantInferenceSupport.ofSourceCache binding arity substitution member
      valid wellFormed instantiation prediction conditions hit
    obtain ⟨reading, typed⟩ := support.sound (locals := []) accepted
    exact ⟨.const ref (arguments.toList.map readLevel), type,
      by
        change readExpr? resolve (.const id arguments (KExpr.mkConst id arguments).info) = _
        simp [readExpr?, binding.resolved, AExpr.erase],
      readScopedExpr?_closed reading, typed⟩
  · exact infer_const_source_sound binding valid.state wellFormed miss conversion
      (by rwa [stateEq]) accepted

end Ix.Kernel.Consistency
