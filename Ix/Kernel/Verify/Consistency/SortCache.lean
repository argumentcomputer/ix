/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.InferenceCache

/-!
# Sort inference and cache preservation

The canonical type of `Sort u` is the production tree for `Sort (succ u)`.
Concrete cache agreement derives both typing and its own preservation through
the actual inference call. Other cache keys and loaded declarations are framed.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- Cached sorts synthesize their canonical type under any active locals.
No intern-table resources are needed when the selected result is cached. -/
theorem infer_sort_cached_sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β}
    {before after : TcState .anon} {level : KUniv .anon} {info : ExprInfo .anon}
    {methods : Methods .anon} {result : KExpr .anon}
    (hit : InferenceCacheHit before (.sort level info))
    (canonical : hit.cached = KExpr.mkSort (KUniv.mkSucc level))
    (accepted : RecM.infer (.sort level info) methods before = .ok result after) :
    readScopedExpr? resolve locals result = some (.sort (.succ (readLevel level))) ∧
      TypingClaim.{u,v} entries context (.sort (readLevel level)) (.sort (.succ (readLevel level))) := by
  rw [hit.run methods] at accepted
  cases accepted
  rw [canonical]
  exact ⟨by simp, TypingClaim.sort _⟩

/-- Both policies return the exact canonical sort tree and retain agreement
at its key. The miss branch establishes this through interning and the real
cache write; the hit branch reads it from the maintained invariant. -/
theorem infer_sort_cache_agreement {before keyed after : TcState .anon}
    {level : KUniv .anon} {info : ExprInfo .anon} {key : Address × Address}
    {methods : Methods .anon} {result : KExpr .anon}
    (keyRun : TcM.inferKey (.sort level info) before = .ok key keyed)
    (agreement : InferenceCacheAgreement keyed key (KExpr.mkSort (KUniv.mkSucc level)))
    (coherent : keyed.env.intern.WF)
    (faithful : KExpr.KeyCollisionFree fun term => keyed.env.intern.ExprSupport term ∨
      term = KExpr.mkSort (KUniv.mkSucc level))
    (accepted : RecM.infer (.sort level info) methods before = .ok result after) :
    result = KExpr.mkSort (KUniv.mkSucc level) ∧
      InferenceCacheAgreement after key (KExpr.mkSort (KUniv.mkSucc level)) := by
  rcases observeInferenceCache keyRun with ⟨hit, keyEq, stateEq⟩ | ⟨miss, keyEq, stateEq⟩
  · rw [hit.run methods] at accepted
    cases accepted
    refine ⟨InferenceCacheAgreement.selected hit ?_, ?_⟩
    · simpa only [keyEq, stateEq] using agreement
    · simpa only [stateEq] using agreement
  · obtain ⟨state, run, written⟩ := infer_uncached_success_state miss accepted
    rw [stateEq] at run
    change EStateM.Result.ok
      (keyed.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).1
      {keyed with env := {keyed.env with intern :=
        (keyed.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).2}} =
      .ok result state at run
    cases run
    have canonical := keyed.env.intern.internExpr_eraseMeta coherent faithful
    simp only [KExpr.eraseMeta_anon] at canonical
    refine ⟨canonical, ?_⟩
    have unchanged : InferenceCacheAgreement
        {keyed with env := {keyed.env with intern :=
          (keyed.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).2}}
        key (KExpr.mkSort (KUniv.mkSucc level)) := ⟨agreement.full, agreement.only⟩
    apply unchanged.write (policy := before.inferOnly) (methods := methods)
    rw [cacheInferResult_eq]
    rw [keyEq, canonical] at written
    rw [written]

/-- A successful sort call preserves every other cache key and all loaded
declarations. This frame is operational and needs no typing or cache
agreement premise, even when the call writes a new result at its own key. -/
theorem infer_sort_cache_frame {before keyed after : TcState .anon}
    {level : KUniv .anon} {info : ExprInfo .anon} {key other : Address × Address}
    {methods : Methods .anon} {result : KExpr .anon}
    (keyRun : TcM.inferKey (.sort level info) before = .ok key keyed)
    (different : key ≠ other)
    (accepted : RecM.infer (.sort level info) methods before = .ok result after) :
    InferenceCacheFrame other before after := by
  have keyFrame := PreservesInferenceCache.inferKey other (.sort level info) before
  rw [keyRun] at keyFrame
  rcases observeInferenceCache keyRun with ⟨hit, keyEq, stateEq⟩ | ⟨miss, keyEq, stateEq⟩
  · rw [hit.run methods] at accepted
    cases accepted
    simpa only [stateEq] using keyFrame
  · obtain ⟨state, run, written⟩ := infer_uncached_success_state miss accepted
    rw [stateEq] at run
    change EStateM.Result.ok
      (keyed.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).1
      {keyed with env := {keyed.env with intern :=
        (keyed.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).2}} =
      .ok result state at run
    cases run
    apply keyFrame.trans
    rw [keyEq] at written
    rw [written]
    cases policy : before.inferOnly <;>
      refine ⟨?_, ?_, rfl⟩ <;> simp [Std.HashMap.getElem?_insert, different]

end Ix.Kernel.Consistency
