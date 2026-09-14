/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.InferenceCache

/-!
# Invariants for every inference-cache entry

Both physical maps carry one invariant, with separate full-checking and
inference-only meanings. Every insertion establishes its own entry's meaning
and preserves all other entries. A caller never supplies an outside-write
condition or a new agreement witness for a hit.

The cache shell is independent of the eventual semantic interpretation of a
key. Its uncached-body premise is the induction obligation for inference,
reduction and conversion; these structural laws do not assume it is discharged.
-/

namespace Ix.Kernel.Consistency

/-- The boolean identifies the partition that originally produced a result,
not the current caller's policy. -/
abbrev InferenceCacheMeaning := Bool → (Address × Address) → KExpr .anon → Prop

/-- Every present entry has the meaning of its actual production partition.
This permits full checking and synthesis to have different contracts. -/
structure InferenceCacheInvariant (meaning : InferenceCacheMeaning)
    (state : TcState .anon) : Prop where
  full : ∀ key type, state.env.inferCache[key]? = some type → meaning false key type
  only : ∀ key type, state.env.inferOnlyCache[key]? = some type → meaning true key type

namespace InferenceCacheInvariant

theorem empty {meaning : InferenceCacheMeaning} {state : TcState .anon}
    (full : state.env.inferCache = {}) (only : state.env.inferOnlyCache = {}) :
    InferenceCacheInvariant meaning state := by
  constructor <;> intro key type found
  · simp [full] at found
  · simp [only] at found

theorem frame {meaning : InferenceCacheMeaning} {before after : TcState .anon}
    (valid : InferenceCacheInvariant meaning before)
    (full : after.env.inferCache = before.env.inferCache)
    (only : after.env.inferOnlyCache = before.env.inferOnlyCache) :
    InferenceCacheInvariant meaning after := by
  constructor
  · intro key type found; exact valid.full key type (full ▸ found)
  · intro key type found; exact valid.only key type (only ▸ found)

/-- Environment extension can transport all stored facts at once. -/
theorem mono {beforeMeaning afterMeaning : InferenceCacheMeaning}
    {state : TcState .anon} (valid : InferenceCacheInvariant beforeMeaning state)
    (transport : ∀ policy key type, beforeMeaning policy key type → afterMeaning policy key type) :
    InferenceCacheInvariant afterMeaning state :=
  ⟨fun key type found => transport false key type (valid.full key type found),
    fun key type found => transport true key type (valid.only key type found)⟩

/-- The old contents at the overwritten key need not equal the new result.
Only the result actually inserted must satisfy its partition's contract. -/
theorem write {meaning : InferenceCacheMeaning} {before after : TcState .anon}
    {policy : Bool} {key : Address × Address} {type : KExpr .anon}
    {methods : Methods .anon} (valid : InferenceCacheInvariant meaning before)
    (fact : meaning policy key type)
    (run : RecM.cacheInferResult policy key type methods before = .ok () after) :
    InferenceCacheInvariant meaning after := by
  rw [cacheInferResult_eq] at run
  cases policy <;> cases run
  · refine ⟨?_, valid.only⟩
    intro other cached found
    change (before.env.inferCache.insert key type)[other]? = some cached at found
    by_cases equal : key = other
    · subst other
      simp only [Std.HashMap.getElem?_insert_self, Option.some.injEq] at found
      exact found ▸ fact
    · simp only [Std.HashMap.getElem?_insert, beq_iff_eq, equal, if_false] at found
      exact valid.full other cached found
  · refine ⟨valid.full, ?_⟩
    intro other cached found
    change (before.env.inferOnlyCache.insert key type)[other]? = some cached at found
    by_cases equal : key = other
    · subst other
      simp only [Std.HashMap.getElem?_insert_self, Option.some.injEq] at found
      exact found ▸ fact
    · simp only [Std.HashMap.getElem?_insert, beq_iff_eq, equal, if_false] at found
      exact valid.only other cached found

theorem inferKey {meaning : InferenceCacheMeaning} {before after : TcState .anon}
    {term : KExpr .anon} {key : Address × Address}
    (valid : InferenceCacheInvariant meaning before)
    (run : TcM.inferKey term before = .ok key after) :
    InferenceCacheInvariant meaning after := by
  constructor
  · intro other type found
    have frame := PreservesInferenceCache.inferKey other term before
    rw [run] at frame
    exact valid.full other type (frame.full.symm.trans found)
  · intro other type found
    have frame := PreservesInferenceCache.inferKey other term before
    rw [run] at frame
    exact valid.only other type (frame.only.symm.trans found)

/-- A successful hit supplies the stored partition's fact. Full mode cannot
obtain a fact from the synthesis-only partition. -/
theorem selected {meaning : InferenceCacheMeaning} {before : TcState .anon}
    {term : KExpr .anon} (valid : InferenceCacheInvariant meaning before)
    (hit : InferenceCacheHit before term) :
    meaning false hit.key hit.cached ∨
      (before.inferOnly = true ∧ meaning true hit.key hit.cached) := by
  have keyed := valid.inferKey hit.keyRun
  rcases hit.selected with full | ⟨_, policy, only⟩
  · exact .inl (keyed.full _ _ full)
  · exact .inr ⟨policy, keyed.only _ _ only⟩

theorem runIntern {meaning : InferenceCacheMeaning} {before after : TcState .anon}
    {action : InternM .anon α} {value : α}
    (valid : InferenceCacheInvariant meaning before)
    (run : TcM.runIntern action before = .ok value after) :
    InferenceCacheInvariant meaning after := by
  cases run
  exact valid.frame rfl rfl

theorem openBinder {meaning : InferenceCacheMeaning} {before after : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body opened : KExpr .anon} {fresh : FVarId}
    (valid : InferenceCacheInvariant meaning before)
    (run : TcM.openBinder name bi domain body before = .ok (opened, fresh) after) :
    InferenceCacheInvariant meaning after := by
  constructor
  · intro key type found
    have frame := PreservesInferenceCache.openBinder key name bi domain body before
    rw [run] at frame
    exact valid.full key type (frame.full.symm.trans found)
  · intro key type found
    have frame := PreservesInferenceCache.openBinder key name bi domain body before
    rw [run] at frame
    exact valid.only key type (frame.only.symm.trans found)

theorem clearReductionCaches (meaning : InferenceCacheMeaning) (state : TcState .anon) :
    InferenceCacheInvariant meaning {state with env := state.env.clearReductionCaches} :=
  empty rfl rfl

theorem reset {meaning : InferenceCacheMeaning} {before after : TcState .anon}
    (valid : InferenceCacheInvariant meaning before)
    (run : TcM.reset before = .ok () after) : InferenceCacheInvariant meaning after := by
  cases run
  exact valid.frame rfl rfl

/-- Error isolation restores the complete trusted cache invariant, even if
the failed computation inserted results with no established meaning. -/
theorem restoreCheckCachesOnError {meaning : InferenceCacheMeaning}
    {before : TcState .anon} (valid : InferenceCacheInvariant meaning before)
    (failed : TcState .anon) :
    InferenceCacheInvariant meaning (before.restoreCheckCachesOnError failed) :=
  valid.frame rfl rfl

theorem isolateCheckErrors {meaning : InferenceCacheMeaning} {action : TcM .anon α}
    {before after : TcState .anon} {error : TcError .anon}
    (valid : InferenceCacheInvariant meaning before)
    (run : TcM.isolateCheckErrors action before = .error error after) :
    InferenceCacheInvariant meaning after := by
  unfold TcM.isolateCheckErrors at run
  cases result : action before with
  | ok value finished => rw [result] at run; contradiction
  | error error failed =>
      rw [result] at run
      cases run
      exact valid.restoreCheckCachesOnError failed

end InferenceCacheInvariant

/-- Preservation includes the state returned on failure, because a caller
may catch an error and continue using the same environment. -/
def PreservesInferenceInvariant (meaning : InferenceCacheMeaning) (action : TcM .anon α) : Prop :=
  ∀ before, InferenceCacheInvariant meaning before →
    match action before with
    | .ok _ after | .error _ after => InferenceCacheInvariant meaning after

namespace PreservesInferenceInvariant

theorem pure (meaning : InferenceCacheMeaning) (value : α) :
    PreservesInferenceInvariant meaning (Pure.pure value) := fun _ valid => valid

theorem bind {meaning : InferenceCacheMeaning} {action : TcM .anon α}
    {next : α → TcM .anon γ}
    (first : PreservesInferenceInvariant meaning action)
    (rest : ∀ value, PreservesInferenceInvariant meaning (next value)) :
    PreservesInferenceInvariant meaning (action >>= next) := by
  intro before valid
  have intermediate := first before valid
  change match EStateM.bind action next before with
    | .ok _ after | .error _ after => InferenceCacheInvariant meaning after
  cases run : action before with
  | error err after =>
      rw [EStateM.bind, run]
      simpa only [run] using intermediate
  | ok value after =>
      rw [run] at intermediate
      rw [EStateM.bind, run]
      exact rest value after intermediate

theorem runIntern (meaning : InferenceCacheMeaning) (action : InternM .anon α) :
    PreservesInferenceInvariant meaning (TcM.runIntern action) := by
  intro before valid
  exact valid.frame rfl rfl

theorem withLctxScope {meaning : InferenceCacheMeaning} {action : RecM .anon α}
    {methods : Methods .anon}
    (body : PreservesInferenceInvariant meaning (action.run methods)) :
    PreservesInferenceInvariant meaning ((RecM.withLctxScope action).run methods) := by
  intro before valid
  rw [withLctxScope_eq]
  have inner := body before valid
  cases run : action.run methods before <;> rw [run] at inner <;>
    exact inner.frame rfl rfl

theorem withInferOnly {meaning : InferenceCacheMeaning} {action : TcM .anon α}
    (body : PreservesInferenceInvariant meaning action) :
    PreservesInferenceInvariant meaning (TcM.withInferOnly action) := by
  intro before valid
  rw [withInferOnly_eq]
  have inner := body {before with inferOnly := true} (valid.frame rfl rfl)
  cases run : action {before with inferOnly := true} <;> rw [run] at inner <;>
    exact inner.frame rfl rfl

end PreservesInferenceInvariant

/-- The actual key computation has a successful result for every state;
observing a hit or miss never requires a caller-supplied key witness. -/
theorem inferKey_total (term : KExpr .anon) (before : TcState .anon) :
    ∃ key after, TcM.inferKey term before = .ok key after := by
  unfold TcM.inferKey TcM.ctxAddrForLbr
  change ∃ key after, EStateM.bind (fun state =>
    EStateM.bind (get : TcM .anon (TcState .anon)) _ state) _ before = .ok key after
  simp only [EStateM.bind, show (get : TcM .anon (TcState .anon)) before =
    .ok before before from rfl]
  by_cases fast : (term.lbr == 0 || before.ctx.isEmpty) = true
  · rw [if_pos fast]
    exact ⟨_, _, rfl⟩
  · rw [if_neg fast]
    cases cached : before.ctxAddrCache[(before.ctxId, term.lbr)]? <;> exact ⟨_, _, rfl⟩

/-- Close the real inference cache shell around a proof of its uncached
body. Recursive body writes are included in `bodyValid`; each outer write is
handled here for every key and both partitions. No fragment tree, hit
agreement or write-footprint exclusion is an input. -/
theorem InferenceCacheInvariant.infer {meaning : InferenceCacheMeaning}
    {before after : TcState .anon} {term result : KExpr .anon} {methods : Methods .anon}
    (valid : InferenceCacheInvariant meaning before)
    (uncached : ∀ key keyed type finished,
      TcM.inferKey term before = .ok key keyed →
      InferenceCacheInvariant meaning keyed →
      RecM.inferUncached RecM.inferCall before.inferOnly term methods keyed =
        .ok type finished →
      InferenceCacheInvariant meaning finished ∧ meaning before.inferOnly key type)
    (run : RecM.infer term methods before = .ok result after) :
    InferenceCacheInvariant meaning after ∧
      ∃ key keyed, TcM.inferKey term before = .ok key keyed ∧
        (meaning false key result ∨ (before.inferOnly = true ∧ meaning true key result)) := by
  obtain ⟨key, keyed, keyRun⟩ := inferKey_total term before
  rcases observeInferenceCache keyRun with ⟨hit, keyEq, stateEq⟩ | ⟨miss, keyEq, stateEq⟩
  · have hitRun := hit.run methods
    rw [hitRun] at run
    cases run
    exact ⟨valid.inferKey hit.keyRun, hit.key, hit.keyed, hit.keyRun, valid.selected hit⟩
  · obtain ⟨finished, bodyRun, written⟩ := infer_uncached_success_state miss run
    obtain ⟨bodyValid, fact⟩ := uncached miss.key miss.keyed result finished
      miss.keyRun (valid.inferKey miss.keyRun) bodyRun
    have writeRun : RecM.cacheInferResult before.inferOnly miss.key result methods finished =
        .ok () after := by
      rw [cacheInferResult_eq, written]
    refine ⟨bodyValid.write fact writeRun, miss.key, miss.keyed, miss.keyRun, ?_⟩
    cases policy : before.inferOnly with
    | false => exact .inl (by simpa only [policy] using fact)
    | true => exact .inr ⟨rfl, by simpa only [policy] using fact⟩

end Ix.Kernel.Consistency
