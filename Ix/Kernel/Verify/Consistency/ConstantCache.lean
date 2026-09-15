/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.ScopedConstant
import Ix.Kernel.Verify.Consistency.InferenceCache

/-!
# Constant inference cache hits

Production cache selection gives full checking priority and consults the
inference-only partition only under that policy. A selected constant result
must equal pure universe substitution of its current loaded declaration.
The admitted entry then supplies typing; no semantic cache invariant is an
input. Structural frames transport these witnesses through operations that
retain the watched entries and loaded declarations. Inference of an already
loaded constant preserves concrete agreement at its key and frames other keys.
`LazyCache` and `RecursiveCache` extend preservation to standalone lazy loading
and finite recursive inference trees.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- Looking up an already loaded declaration does not invoke lazy loading
or change any checker state. -/
theorem getConst_loaded {before : TcState .anon} {id : KId .anon} {concrete : KConst .anon}
    (loaded : before.env.get? id = some concrete) :
    TcM.getConst id before = .ok concrete before := by
  have found : TcM.tryGetConst id before = .ok (some concrete) before := by
    unfold TcM.tryGetConst
    change EStateM.bind (get : TcM .anon (TcState .anon)) _ before = _
    rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) before =
      .ok before before from rfl]
    simp only [loaded]
    rfl
  unfold TcM.getConst
  change EStateM.bind (TcM.tryGetConst id) _ before = _
  rw [EStateM.bind, found]
  rfl

/-- The verified universe walker changes only its intern table, preserving
both inference partitions and the loaded declarations at every key. -/
theorem instantiateUnivParams_cache_frame {before after : TcState .anon}
    {term result : KExpr .anon} {arguments : Array (KUniv .anon)}
    (support : UniverseInstantiationSupport before term arguments)
    (run : TcM.instantiateUnivParams term arguments before = .ok result after)
    (key : Address × Address) : InferenceCacheFrame key before after := by
  have post := TcM.instantiateUnivParams_wf support.faithful
    (fun _ h => Or.inr h) ⟨support.coherent, fun _ h => Or.inl h⟩
  rw [run] at post
  rw [post.2.2.1]
  exact .of_eq rfl rfl rfl

/-- Inference of an already loaded constant frames all other cache keys,
including on a miss that runs universe substitution and writes a result.
Lazy loading needs its own preservation proof when the declaration is absent. -/
theorem infer_const_cache_frame {before keyed after : TcState .anon}
    {id : KId .anon} {arguments : Array (KUniv .anon)} {info : ExprInfo .anon}
    {key other : Address × Address} {concrete : KConst .anon}
    {methods : Methods .anon} {result : KExpr .anon}
    (keyRun : TcM.inferKey (.const id arguments info) before = .ok key keyed)
    (different : key ≠ other)
    (loaded : keyed.env.get? id = some concrete)
    (resources : UniverseInstantiationSupport keyed concrete.ty arguments)
    (accepted : RecM.infer (.const id arguments info) methods before = .ok result after) :
    InferenceCacheFrame other before after := by
  have keyFrame := PreservesInferenceCache.inferKey other (.const id arguments info) before
  rw [keyRun] at keyFrame
  rcases observeInferenceCache keyRun with ⟨hit, _, stateEq⟩ | ⟨miss, keyEq, stateEq⟩
  · rw [hit.run methods] at accepted
    cases accepted
    simpa only [stateEq] using keyFrame
  · obtain ⟨state, run, written⟩ := infer_uncached_success_state miss accepted
    rw [stateEq] at run
    obtain ⟨actual, foundState, got, _, instantiated⟩ := inferUncached_const_instantiation run
    rw [getConst_loaded loaded] at got
    cases got
    have substitution := instantiateUnivParams_cache_frame resources instantiated other
    have wrote : RecM.cacheInferResult before.inferOnly key result methods state = .ok () after := by
      rw [cacheInferResult_eq]
      rw [keyEq] at written
      rw [written]
    have tail := PreservesInferenceCache.write_other different before.inferOnly result methods state
    rw [wrote] at tail
    exact keyFrame.trans (substitution.trans tail)

/-- A maintained agreement at a loaded constant's key survives its actual
inference. The pure substituted tree determines both cache writes and hits;
the two partition witnesses no longer need to be re-established afterward. -/
theorem infer_const_cache_agreement {before keyed after : TcState .anon}
    {id : KId .anon} {arguments : Array (KUniv .anon)} {info : ExprInfo .anon}
    {key : Address × Address} {concrete : KConst .anon} {expected result : KExpr .anon}
    {methods : Methods .anon}
    (keyRun : TcM.inferKey (.const id arguments info) before = .ok key keyed)
    (agreement : InferenceCacheAgreement keyed key expected)
    (loaded : keyed.env.get? id = some concrete)
    (resources : UniverseInstantiationSupport keyed concrete.ty arguments)
    (prediction : KExpr.instantiateUnivParamsSpec concrete.ty arguments = .ok expected)
    (accepted : RecM.infer (.const id arguments info) methods before = .ok result after) :
    result = expected ∧ InferenceCacheAgreement after key expected := by
  rcases observeInferenceCache keyRun with ⟨hit, keyEq, stateEq⟩ | ⟨miss, keyEq, stateEq⟩
  · rw [hit.run methods] at accepted
    cases accepted
    refine ⟨InferenceCacheAgreement.selected hit ?_, ?_⟩
    · simpa only [keyEq, stateEq] using agreement
    · simpa only [stateEq] using agreement
  · obtain ⟨state, run, written⟩ := infer_uncached_success_state miss accepted
    rw [stateEq] at run
    obtain ⟨actual, foundState, got, _, instantiated⟩ := inferUncached_const_instantiation run
    rw [getConst_loaded loaded] at got
    cases got
    have post := TcM.instantiateUnivParams_wf resources.faithful
      (fun _ h => Or.inr h) ⟨resources.coherent, fun _ h => Or.inl h⟩
    rw [instantiated] at post
    have equal := Except.ok.inj (post.2.1.symm.trans prediction)
    refine ⟨equal, ?_⟩
    have unchanged := agreement.frame (instantiateUnivParams_cache_frame resources instantiated key)
    apply unchanged.write (policy := before.inferOnly) (methods := methods)
    rw [cacheInferResult_eq]
    rw [keyEq, equal] at written
    rw [written]

/-- A successful constant miss inserts the exact pure substituted type in
the selected partition. This establishes the concrete substitution agreement
used by later hits; preserving it across other operations remains explicit. -/
theorem infer_const_cache_write {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {before after : TcState .anon} {id : KId .anon} {arguments : Array (KUniv .anon)}
    {info : ExprInfo .anon} {ref : ConstRef β} {entry : ConstantEntry β}
    {methods : Methods .anon} {result : KExpr .anon}
    (miss : UncachedInference before (.const id arguments info))
    (support : ScopedConstantInferenceSupport resolve entries miss.keyed id arguments ref entry)
    (accepted : RecM.infer (.const id arguments info) methods before = .ok result after) :
    ∃ concrete loaded, TcM.getConst id miss.keyed = .ok concrete loaded ∧
      concrete.lvls.toNat = arguments.size ∧
      KExpr.instantiateUnivParamsSpec concrete.ty arguments = .ok result ∧
      (if before.inferOnly then after.env.inferOnlyCache[miss.key]?
        else after.env.inferCache[miss.key]?) = some result := by
  obtain ⟨state, run, written⟩ := infer_uncached_success_state miss accepted
  obtain ⟨concrete, loaded, got, arity, instantiated⟩ := inferUncached_const_instantiation run
  obtain ⟨_, _, resources⟩ := support.lookup concrete loaded got
  have post := TcM.instantiateUnivParams_wf resources.faithful
    (fun _ h => Or.inr h) ⟨resources.coherent, fun _ h => Or.inl h⟩
  rw [instantiated] at post
  refine ⟨concrete, loaded, got, arity, post.2.1, ?_⟩
  cases policy : before.inferOnly <;> simp [policy, written]

/-- Concrete coherence for one selected constant cache entry. Both arity
equalities are explicit because a hit skips the runtime arity guard. The
cached syntax equals pure substitution of a loaded declaration whose type
reads as the admitted entry. Prediction and annotations select the result
of a finite inference tree; they do not assert typing or validity. -/
structure CachedConstantInferenceSupport {β : Type u}
    (resolve : Address → Option (ConstRef β)) (entries : Model.Environment β)
    (before : TcState .anon) (id : KId .anon) (arguments : Array (KUniv .anon))
    (info : ExprInfo .anon) (ref : ConstRef β) (entry : ConstantEntry β) (type : AExpr β) where
  hit : InferenceCacheHit before (.const id arguments info)
  concrete : KConst .anon
  loaded : hit.keyed.env.get? id = some concrete
  resolved : resolve id.addr = some ref
  found : entries ref = some entry
  count : concrete.lvls.toNat = entry.universes
  arity : concrete.lvls.toNat = arguments.size
  scope : entry.type.Scope entry.universes 0
  reading : readScopedExpr? resolve [] concrete.ty = some entry.type.erase
  levels : UniverseSubstitutionSupport arguments concrete.ty
  substitution : KExpr.instantiateUnivParamsSpec concrete.ty arguments = .ok hit.cached
  prediction : readInstantiatedType? resolve concrete.ty arguments = some type.erase
  conditions : (entry.type.instL (arguments.toList.map readLevel)).annotations = type.annotations

/-- A preserved closed cache entry and retained loaded declarations carry
the complete constant witness into a later checker state. Only checking
policy matters for the eligibility of an inference-only hit. -/
def CachedConstantInferenceSupport.transport {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {before after : TcState .anon} {id : KId .anon} {arguments : Array (KUniv .anon)}
    {info : ExprInfo .anon} {ref : ConstRef β} {entry : ConstantEntry β} {type : AExpr β}
    (support : CachedConstantInferenceSupport resolve entries before id arguments info ref entry type)
    (closed : (KExpr.const id arguments info).lbr = 0)
    (frame : InferenceCacheFrame ((KExpr.const id arguments info).addr, emptyCtxAddr) before after)
    (policy : after.inferOnly = before.inferOnly) :
    CachedConstantInferenceSupport resolve entries after id arguments info ref entry type := {
  hit := support.hit.transport closed frame policy
  concrete := support.concrete
  loaded := by
    change after.env.get? id = some support.concrete
    have loaded := support.loaded
    rw [(support.hit.key_closed closed).2] at loaded
    exact frame.constants id support.concrete loaded
  resolved := support.resolved, found := support.found
  count := support.count, arity := support.arity, scope := support.scope
  reading := support.reading, levels := support.levels
  substitution := support.substitution, prediction := support.prediction
  conditions := support.conditions
}

/-- Actual binder opening supplies the cache frame and policy equality. No
new lookup, substitution prediction, or cache-hit observation is supplied. -/
def CachedConstantInferenceSupport.openBinder {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {before after : TcState .anon} {id : KId .anon} {arguments : Array (KUniv .anon)}
    {info : ExprInfo .anon} {ref : ConstRef β} {entry : ConstantEntry β} {type : AExpr β}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body opened : KExpr .anon} {fresh : FVarId}
    (support : CachedConstantInferenceSupport resolve entries before id arguments info ref entry type)
    (closed : (KExpr.const id arguments info).lbr = 0)
    (run : TcM.openBinder name bi domain body before = .ok (opened, fresh) after) :
    CachedConstantInferenceSupport resolve entries after id arguments info ref entry type :=
  support.transport closed (by
    have frame := PreservesInferenceCache.openBinder
      ((KExpr.const id arguments info).addr, emptyCtxAddr) name bi domain body before
    rw [run] at frame
    exact frame) (by
      rw [openBinder_eq] at run
      split at run
      · cases run; rfl
      · contradiction)

/-- The pure prediction and concrete cache agreement derive the cached
type's reading in every active context and its congruence with the admitted
entry's instantiated type. Mutable interning resources are unnecessary. -/
theorem CachedConstantInferenceSupport.refinement {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {before : TcState .anon} {id : KId .anon} {arguments : Array (KUniv .anon)}
    {info : ExprInfo .anon} {ref : ConstRef β} {entry : ConstantEntry β} {type : AExpr β}
    (support : CachedConstantInferenceSupport resolve entries before id arguments info ref entry type)
    (locals : List FVarId) :
    readScopedExpr? resolve locals support.hit.cached = some type.erase ∧
      AExpr.LevelEquivalent (entry.type.instL (arguments.toList.map readLevel)) type ∧
      (arguments.toList.map readLevel).length = entry.universes := by
  have scope : entry.type.Scope arguments.size 0 := by
    rw [← support.arity, support.count]
    exact support.scope
  obtain ⟨output, outputReads, same⟩ := instantiateUnivParamsSpec_readScopedAnnotated
    (locals := locals) support.levels scope.erase.1 support.reading support.substitution
  have predicted := support.prediction
  rw [readInstantiatedType?, support.substitution] at predicted
  have typeReads := readScopedExpr?_weaken_closed predicted locals
  have equal := AExpr.eq_of_erase_annotations
    (Option.some.inj (outputReads.symm.trans typeReads))
    (same.annotations.symm.trans support.conditions)
  refine ⟨typeReads, equal ▸ same, ?_⟩
  simpa only [List.length_map, Array.length_toList] using support.arity.symm.trans support.count

/-- An actual cache hit has the admitted constant's full model typing. The
semantic conclusion is derived from concrete cache coherence, pure universe
substitution, and the dependency model, including simplifying levels. -/
theorem CachedConstantInferenceSupport.sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β}
    {before after : TcState .anon} {id : KId .anon} {arguments : Array (KUniv .anon)}
    {info : ExprInfo .anon} {ref : ConstRef β} {entry : ConstantEntry β} {type : AExpr β}
    {methods : Methods .anon} {result : KExpr .anon}
    (support : CachedConstantInferenceSupport resolve entries before id arguments info ref entry type)
    (accepted : RecM.infer (.const id arguments info) methods before = .ok result after) :
    readScopedExpr? resolve locals result = some type.erase ∧
      TypingClaim.{u,v} entries context (.const ref (arguments.toList.map readLevel)) type := by
  rw [support.hit.run methods] at accepted
  cases accepted
  obtain ⟨typeReads, same, arity⟩ := support.refinement locals
  exact ⟨typeReads, same.typing (TypingClaim.const support.found arity)⟩

/-- Reuse the proved constant type after a sequence of operations whose
cache frames compose. The later hit observation and declaration agreement
are transported from the earlier witness. -/
theorem CachedConstantInferenceSupport.sound_after_frame {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β}
    {before later after : TcState .anon} {id : KId .anon} {arguments : Array (KUniv .anon)}
    {info : ExprInfo .anon} {ref : ConstRef β} {entry : ConstantEntry β} {type : AExpr β}
    {methods : Methods .anon} {result : KExpr .anon}
    (support : CachedConstantInferenceSupport resolve entries before id arguments info ref entry type)
    (closed : (KExpr.const id arguments info).lbr = 0)
    (frame : InferenceCacheFrame ((KExpr.const id arguments info).addr, emptyCtxAddr) before later)
    (policy : later.inferOnly = before.inferOnly)
    (accepted : RecM.infer (.const id arguments info) methods later = .ok result after) :
    readScopedExpr? resolve locals result = some type.erase ∧
      TypingClaim.{u,v} entries context (.const ref (arguments.toList.map readLevel)) type :=
  (support.transport closed frame policy).sound accepted

end Ix.Kernel.Consistency
