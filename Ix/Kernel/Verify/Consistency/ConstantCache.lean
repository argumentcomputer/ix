/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.ScopedConstant

/-!
# Constant inference cache hits

Production cache selection gives full checking priority and consults the
inference-only partition only under that policy. A selected constant result
must equal pure universe substitution of its current loaded declaration.
The admitted entry then supplies typing; no semantic cache invariant is an
input. These witnesses check individual entries, not global cache maintenance.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- The exact cache entry eligible at production's computed inference key.
An inference-only result cannot witness a full-mode hit or override a full
result. No declaration lookup or recursive inference is performed on a hit. -/
structure InferenceCacheHit (before : TcState .anon) (term : KExpr .anon) where
  key : Address × Address
  keyed : TcState .anon
  cached : KExpr .anon
  keyRun : TcM.inferKey term before = .ok key keyed
  selected : keyed.env.inferCache[key]? = some cached ∨
    (keyed.env.inferCache[key]? = none ∧ before.inferOnly = true ∧
      keyed.env.inferOnlyCache[key]? = some cached)

/-- Cache selection determines both the returned type and state, without
executing the uncached branch or rewriting either cache partition. -/
theorem InferenceCacheHit.run {before : TcState .anon} {term : KExpr .anon}
    (hit : InferenceCacheHit before term) (methods : Methods .anon) :
    RecM.infer term methods before = .ok hit.cached hit.keyed := by
  change (RecM.infer term).run methods before = _
  unfold RecM.infer RecM.inferWith
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.inferKey term) _ before = _
  rw [EStateM.bind, hit.keyRun]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ hit.keyed = _
  rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) hit.keyed =
    .ok hit.keyed hit.keyed from rfl]
  rcases hit.selected with full | ⟨full, policy, only⟩
  · simp only [full]; rfl
  · simp only [full, policy, if_true, ReaderT.run_bind]
    change EStateM.bind (get : TcM .anon (TcState .anon)) _ hit.keyed = _
    rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) hit.keyed =
      .ok hit.keyed hit.keyed from rfl]
    simp only [only]
    rfl

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

end Ix.Kernel.Consistency
