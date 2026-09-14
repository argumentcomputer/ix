/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.LocalScope
import Ix.Kernel.Verify.Consistency.LetInference
import Ix.Kernel.Verify.Consistency.CacheInvariant

/-!
# Restoring model locals at production scope boundaries

Actual scope cleanup restores every caller lookup after a body that only
extends the local context, on both success and failure. Let inference uses
this fact to restore the modeled context present after value validation.
The recursive execution proof must establish the body extension invariant.
-/

namespace Ix.Kernel.Consistency
open Theory Theory.Model
universe u v

/-- Observable context restoration transports the semantic invariant. -/
theorem LocalContextValues.congr {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {values : LocalValues β} {context : Model.Context β}
    {left right : LocalContext .anon}
    (agreement : LocalContextValues.{u,v} resolve entries values left context)
    (same : LocalContext.Equiv left right) :
    LocalContextValues.{u,v} resolve entries values right context := by
  refine ⟨same.wf agreement.coherent, ?_, ?_⟩
  · intro id decl found
    exact agreement.complete id decl ((same.find? id).trans found)
  · intro id value found
    obtain ⟨decl, A, hit, typeRead, typed, valueRead⟩ := agreement.lookup id value found
    exact ⟨decl, A, (same.find? id).symm.trans hit, typeRead, typed, valueRead⟩

/-- Actual scope cleanup restores the incoming context after an arbitrary
successful body which only extended its local declarations. -/
theorem withLctxScope_restores {action : RecM .anon α} {methods : Methods .anon}
    {before after : TcState .anon} {result : α}
    (extended : ∀ state, action.run methods before = .ok result state →
      before.lctx.Extension state.lctx)
    (run : (RecM.withLctxScope action).run methods before = .ok result after) :
    after.lctx.Equiv before.lctx := by
  rw [withLctxScope_eq] at run
  cases bodyRun : action.run methods before with
  | error error state => rw [bodyRun] at run; contradiction
  | ok value state =>
      rw [bodyRun] at run
      cases run
      exact (extended state bodyRun).restore

/-- The same restoration applies to the partial state returned on failure. -/
theorem withLctxScope_error_restores {action : RecM .anon α} {methods : Methods .anon}
    {before after : TcState .anon} {error : TcError .anon}
    (extended : ∀ state, action.run methods before = .error error state →
      before.lctx.Extension state.lctx)
    (run : (RecM.withLctxScope action).run methods before = .error error after) :
    after.lctx.Equiv before.lctx := by
  rw [withLctxScope_eq] at run
  cases bodyRun : action.run methods before with
  | ok value state => rw [bodyRun] at run; contradiction
  | error failure state =>
      rw [bodyRun] at run
      cases run
      exact (extended state bodyRun).restore

theorem openLet_extends {name : Mode.anon.F Name} {type value body opened : KExpr .anon}
    {fresh : FVarId} {before after : TcState .anon}
    (absent : before.lctx.index[(⟨before.env.nextFVarId⟩ : FVarId)]? = none)
    (run : TcM.openLet name type value body before = .ok (opened, fresh) after) :
    before.lctx.Extension after.lctx := by
  rw [openLet_eq] at run
  split at run
  · cases run; exact .push _ (.refl _) absent
  · contradiction

theorem openBinder_extends {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {type body opened : KExpr .anon} {fresh : FVarId} {before after : TcState .anon}
    (absent : before.lctx.index[(⟨before.env.nextFVarId⟩ : FVarId)]? = none)
    (run : TcM.openBinder name bi type body before = .ok (opened, fresh) after) :
    before.lctx.Extension after.lctx := by
  rw [openBinder_eq] at run
  split at run
  · cases run; exact .push _ (.refl _) absent
  · contradiction

/-- Let inference restores the context present after value validation. The
body's local-extension premise is the recursive execution invariant. -/
theorem LetInferenceTrace.restores {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {values : LocalValues β} {context : Model.Context β}
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)} {methods : Methods .anon}
    {inferOnly : Bool} {name : Mode.anon.F Name} {type value body result : KExpr .anon}
    {before after : TcState .anon}
    (trace : LetInferenceTrace inferRec methods inferOnly name type value body before result after)
    (agreement : LocalContextValues.{u,v} resolve entries values trace.validated.lctx context)
    (below : values.Below trace.validated.env.nextFVarId)
    (extended : trace.openedState.lctx.Extension trace.bodyState.lctx) :
    after.lctx.Equiv trace.validated.lctx ∧
      LocalContextValues.{u,v} resolve entries values after.lctx context := by
  have opened := openLet_extends (agreement.index_none below.absent) trace.openRun
  have restored : after.lctx.Equiv trace.validated.lctx := by
    rw [show after.lctx = trace.bodyState.lctx.truncate trace.validated.lctx.size from
      congrArg TcState.lctx trace.stateEq]
    exact (opened.trans extended).restore
  exact ⟨restored, agreement.congr restored.symm⟩

/-- Neither successful nor failed execution removes or changes an incoming
local declaration. Extra fresh declarations are restored by enclosing scopes. -/
def PreservesLocalExtension (action : TcM .anon α) : Prop :=
  ∀ before, match action before with
    | .ok _ after | .error _ after => before.lctx.Extension after.lctx

namespace PreservesLocalExtension

theorem pure (value : α) : PreservesLocalExtension (Pure.pure value) := fun _ => .refl _

theorem throw (error : TcError .anon) :
    PreservesLocalExtension (throw error : TcM .anon α) := fun _ => .refl _

theorem bind {action : TcM .anon α} {next : α → TcM .anon γ}
    (first : PreservesLocalExtension action)
    (rest : ∀ value, PreservesLocalExtension (next value)) :
    PreservesLocalExtension (action >>= next) := by
  intro before
  have intermediate := first before
  change match EStateM.bind action next before with
    | .ok _ after | .error _ after => before.lctx.Extension after.lctx
  cases run : action before with
  | error error after =>
      rw [EStateM.bind, run]
      simpa only [run] using intermediate
  | ok value after =>
      rw [run] at intermediate
      rw [EStateM.bind, run]
      dsimp only
      have final := rest value after
      cases finished : next value after <;>
        rw [finished] at final <;> exact intermediate.trans final

theorem runIntern (action : InternM .anon α) :
    PreservesLocalExtension (TcM.runIntern action) := fun _ => .refl _

theorem inferKey (term : KExpr .anon) : PreservesLocalExtension (TcM.inferKey term) := by
  intro before
  obtain ⟨key, keyed, run⟩ := inferKey_total term before
  rw [run]
  change before.lctx.Extension keyed.lctx
  rw [inferKey_lctx run]
  exact .refl _

theorem withInferOnly {action : TcM .anon α} (body : PreservesLocalExtension action) :
    PreservesLocalExtension (TcM.withInferOnly action) := by
  intro before
  rw [withInferOnly_eq]
  have inner := body {before with inferOnly := true}
  cases run : action {before with inferOnly := true} <;>
    simpa only [run] using inner

theorem withLctxScope {action : RecM .anon α} {methods : Methods .anon}
    (body : PreservesLocalExtension (action.run methods)) :
    PreservesLocalExtension ((RecM.withLctxScope action).run methods) := by
  intro before
  rw [withLctxScope_eq]
  have inner := body before
  cases run : action.run methods before <;> rw [run] at inner <;>
    exact .equiv (.refl _) inner.restore.symm

end PreservesLocalExtension

/-- The actual inference cache shell preserves the caller's local context
whenever its uncached branch does. Both eligible partitions and the outer
write are handled directly from execution. -/
theorem infer_localContext
    {before after : TcState .anon} {term result : KExpr .anon} {methods : Methods .anon}
    (uncached : ∀ key keyed type finished,
      TcM.inferKey term before = .ok key keyed →
      RecM.inferUncached RecM.inferCall before.inferOnly term methods keyed =
        .ok type finished →
      finished.lctx.Equiv keyed.lctx)
    (run : RecM.infer term methods before = .ok result after) :
    after.lctx.Equiv before.lctx := by
  obtain ⟨key, keyed, keyRun⟩ := inferKey_total term before
  rcases observeInferenceCache keyRun with ⟨hit, _, _⟩ | ⟨miss, _, _⟩
  · rw [hit.run methods] at run
    cases run
    rw [inferKey_lctx hit.keyRun]
    exact .refl _
  · obtain ⟨finished, bodyRun, written⟩ := infer_uncached_success_state miss run
    have bodySame := uncached miss.key miss.keyed result finished miss.keyRun bodyRun
    have same : after.lctx = finished.lctx := by
      rw [written]
      cases before.inferOnly <;> rfl
    simpa only [same, miss.localContext] using bodySame

end Ix.Kernel.Consistency
