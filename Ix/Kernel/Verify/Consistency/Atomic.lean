/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Infer

/-!
# Atomic production inference

The declaration fragment admits closed sorts and monomorphic references.
References use the type of an existing interface entry. Cache misses, lookup
agreement, and finite interning support connect each production result to its
model type.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- The two inference-cache partitions miss at the actual key computed by
production. Both misses are required, so this applies in either policy mode. -/
structure UncachedInference (before : TcState .anon) (term : KExpr .anon) where
  key : Address × Address
  keyed : TcState .anon
  keyRun : TcM.inferKey term before = .ok key keyed
  fullMiss : keyed.env.inferCache[key]? = none
  onlyMiss : keyed.env.inferOnlyCache[key]? = none

/-- Strip only key lookup and the final cache write from an actual successful
inference. The recursive method table and returned type are unchanged. -/
theorem infer_uncached_success {term type : KExpr .anon}
    {methods : Methods .anon} {before after : TcState .anon}
    (miss : UncachedInference before term)
    (accepted : RecM.infer term methods before = .ok type after) :
    ∃ inferredState, RecM.inferUncached RecM.inferCall before.inferOnly term
      methods miss.keyed = .ok type inferredState := by
  change (RecM.infer term).run methods before = .ok type after at accepted
  unfold RecM.infer RecM.inferWith at accepted
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at accepted
  change EStateM.bind (TcM.inferKey term) _ before = _ at accepted
  rw [EStateM.bind, miss.keyRun] at accepted
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ miss.keyed = _ at accepted
  rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) miss.keyed =
    .ok miss.keyed miss.keyed from rfl] at accepted
  simp only at accepted
  rw [miss.fullMiss] at accepted
  cases policy : before.inferOnly with
  | false =>
      simp only [policy, Bool.false_eq_true, if_false] at accepted
      change EStateM.bind (RecM.inferUncached RecM.inferCall false term methods)
        _ miss.keyed = _ at accepted
      cases run : RecM.inferUncached RecM.inferCall false term methods miss.keyed with
      | error err failed => rw [EStateM.bind, run] at accepted; contradiction
      | ok ty state =>
          rw [EStateM.bind, run] at accepted
          change EStateM.Result.ok ty { state with env := { state.env with
            inferCache := state.env.inferCache.insert miss.key ty } } = .ok type after at accepted
          cases accepted
          exact ⟨state, rfl⟩
  | true =>
      simp only [policy, if_true] at accepted
      simp only [ReaderT.run_bind] at accepted
      change EStateM.bind (get : TcM .anon (TcState .anon)) _ miss.keyed = _ at accepted
      rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) miss.keyed =
        .ok miss.keyed miss.keyed from rfl] at accepted
      simp only at accepted
      rw [miss.onlyMiss] at accepted
      change EStateM.bind (RecM.inferUncached RecM.inferCall true term methods)
        _ miss.keyed = _ at accepted
      cases run : RecM.inferUncached RecM.inferCall true term methods miss.keyed with
      | error err failed => rw [EStateM.bind, run] at accepted; contradiction
      | ok ty state =>
          rw [EStateM.bind, run] at accepted
          change EStateM.Result.ok ty { state with env := { state.env with
            inferOnlyCache := state.env.inferOnlyCache.insert miss.key ty } } = .ok type after at accepted
          cases accepted
          exact ⟨state, rfl⟩

/-- Supported syntax plus the concrete resources needed by its uncached
production branch. A constant's semantic type comes from an existing entry,
while `lookup` checks agreement with the actual lazy-loaded declaration.
The monomorphic type is explicitly stable under the empty level substitution. -/
inductive AtomicInferenceSupport {β : Type u}
    (resolve : Address → Option (ConstRef β)) (entries : Model.Environment β) :
    KExpr .anon → TcState .anon → AExpr β → AExpr β → Prop
  | sort {level : KUniv .anon} {info : ExprInfo .anon} {before : TcState .anon}
      (closed : (readLevel level).WF 0)
      (coherent : before.env.intern.WF)
      (faithful : KExpr.KeyCollisionFree fun e =>
        before.env.intern.ExprSupport e ∨ e = KExpr.mkSort (KUniv.mkSucc level)) :
      AtomicInferenceSupport resolve entries (.sort level info) before
        (.sort (readLevel level)) (.sort (.succ (readLevel level)))
  | const {id : KId .anon} {info : ExprInfo .anon} {before : TcState .anon}
      {ref : ConstRef β} {entry : ConstantEntry β}
      (resolved : resolve id.addr = some ref)
      (found : entries ref = some entry)
      (monomorphic : entry.universes = 0)
      (stable : entry.type.instL [] = entry.type)
      (lookup : ∀ concrete loaded,
        TcM.getConst id before = .ok concrete loaded →
        readExpr? resolve concrete.ty = some entry.type.erase) :
      AtomicInferenceSupport resolve entries (.const id #[] info) before
        (.const ref []) entry.type

namespace AtomicInferenceSupport

/-- The model's sort and constant rules type each supported syntax form. -/
theorem typing {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {term : KExpr .anon} {before : TcState .anon}
    {body type : AExpr β} (support : AtomicInferenceSupport resolve entries term before body type) :
    TypingClaim.{u,v} entries [] body type := by
  cases support with
  | sort => exact TypingClaim.sort _
  | const resolved found monomorphic stable lookup =>
      simpa only [stable] using
        (TypingClaim.const (ls := []) found (by simpa using monomorphic.symm))

theorem reads {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {term : KExpr .anon} {before : TcState .anon}
    {body type : AExpr β} (support : AtomicInferenceSupport resolve entries term before body type) :
    readExpr? resolve term = some body.erase := by
  cases support with
  | sort => rfl
  | const resolved found monomorphic stable lookup =>
      simp [readExpr?, resolved, AExpr.erase]

/-- Exact output refinement for the production syntax dispatcher. -/
theorem output {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {term inferred : KExpr .anon}
    {before after : TcState .anon} {body type : AExpr β}
    (support : AtomicInferenceSupport resolve entries term before body type)
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)}
    {inferOnly : Bool} {methods : Methods .anon}
    (accepted : RecM.inferUncached inferRec inferOnly term methods before =
      .ok inferred after) :
    readExpr? resolve inferred = some type.erase := by
  cases support with
  | sort closed coherent faithful =>
      change EStateM.Result.ok
          (before.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc _))).1
          _ = .ok inferred after at accepted
      cases accepted
      rw [internExpr_readExpr? coherent faithful]
      simp only [readExpr?_mkSort, readLevel_mkSucc, AExpr.erase]
  | @const id info before ref entry resolved found monomorphic stable lookup =>
      change (RecM.inferUncached inferRec inferOnly (.const id #[] info)).run
        methods before = .ok inferred after at accepted
      unfold RecM.inferUncached at accepted
      simp only [ReaderT.run_bind, ReaderT.run_monadLift] at accepted
      change EStateM.bind (TcM.getConst id) _ before = _ at accepted
      cases got : TcM.getConst id before with
      | error err failed => rw [EStateM.bind, got] at accepted; contradiction
      | ok concrete loaded =>
          rw [EStateM.bind, got] at accepted
          simp only at accepted
          split at accepted
          · contradiction
          · change EStateM.Result.ok concrete.ty loaded = .ok inferred after at accepted
            cases accepted
            exact lookup concrete _ got

theorem scopeAndReferences {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {term : KExpr .anon} {before : TcState .anon}
    {body type : AExpr β} (support : AtomicInferenceSupport resolve entries term before body type)
    (wellFormed : entries.WF) :
    body.Scope 0 0 ∧ type.Scope 0 0 ∧
      body.ReferencesIn entries ∧ type.ReferencesIn entries := by
  cases support with
  | sort closed coherent faithful =>
      exact ⟨closed, closed, by simp [AExpr.ReferencesIn, AExpr.references],
        by simp [AExpr.ReferencesIn, AExpr.references]⟩
  | const resolved found monomorphic stable lookup =>
      refine ⟨by simp [AExpr.Scope], ?_, ?_, wellFormed.typeReferences _ _ found⟩
      · simpa only [monomorphic] using wellFormed.typeScope _ _ found
      · intro ref href
        simp only [AExpr.references, List.mem_singleton] at href
        subst ref
        simp only [found, Option.isSome_some]

end AtomicInferenceSupport

/-- Resources at the actual inference entry and its computed cache key. -/
structure AtomicInference {β : Type u} (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (before : TcState .anon) (term : KExpr .anon)
    (body type : AExpr β) where
  misses : UncachedInference before term
  support : AtomicInferenceSupport resolve entries term misses.keyed body type

/-- Successful production inference returns the model type of the source tree. -/
theorem AtomicInference.sound {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {before after : TcState .anon}
    {term inferred : KExpr .anon} {body type : AExpr β} {methods : Methods .anon}
    (fragment : AtomicInference resolve entries before term body type)
    (accepted : RecM.infer term methods before = .ok inferred after) :
    readExpr? resolve term = some body.erase ∧
      readExpr? resolve inferred = some type.erase ∧
      TypingClaim.{u,v} entries [] body type := by
  obtain ⟨state, run⟩ := infer_uncached_success fragment.misses accepted
  exact ⟨fragment.support.reads, fragment.support.output run, fragment.support.typing⟩

end Ix.Kernel.Consistency
