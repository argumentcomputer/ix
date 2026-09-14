/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.SpineReading

/-! Recover annotations for the raw application spine. A let at its head
may already read as an application, so the raw spine determines where to stop. -/

namespace Ix.Kernel.Consistency.AppSpineSource

open Theory Theory.Model

universe u

def parts {β : Type u} : KExpr .anon → AExpr β → AExpr β × List (AExpr β)
  | .app fn _ _, .app f a => let (head, arguments) := parts fn f; (head, arguments ++ [a])
  | _, term => (term, [])

private theorem app_shape {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fn arg : KExpr .anon} {info : ExprInfo .anon} {term : AExpr β}
    (reading : readScopedExpr? resolve locals (.app fn arg info) = some term.erase) :
    ∃ f a, term = .app f a ∧ readScopedExpr? resolve locals fn = some f.erase ∧
      readScopedExpr? resolve locals arg = some a.erase := by
  cases term with
  | app f a => exact ⟨f, a, rfl, readScopedExpr?_app_parts reading⟩
  | _ =>
      cases hf : readScopedExpr? resolve locals fn <;>
        cases ha : readScopedExpr? resolve locals arg <;>
        simp [readScopedExpr?, hf, ha, AExpr.erase] at reading

private theorem view {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {source : KExpr .anon} {term : AExpr β}
    (reading : readScopedExpr? resolve locals source = some term.erase) :
    term = (parts source term).1.appN (parts source term).2 ∧
      readScopedExpr? resolve locals (RecM.appSpineView source).1 = some (parts source term).1.erase ∧
      (RecM.appSpineView source).2.map (readScopedExpr? resolve locals ·) =
        (parts source term).2.map (some ·.erase) := by
  induction source generalizing term with
  | app fn arg info ihFn ihArg =>
      obtain ⟨f, a, rfl, fnReads, argReads⟩ := app_shape reading
      obtain ⟨rebuilt, headReads, argumentReads⟩ := ihFn fnReads
      refine ⟨?_, headReads, ?_⟩
      · simpa only [parts, AExpr.appN_append, AExpr.appN_cons, AExpr.appN_nil] using
          congrArg (AExpr.app · a) rebuilt
      · simp only [parts, RecM.appSpineView, List.map_append, List.map_cons, List.map_nil,
          argumentReads, argReads]
  | _ => exact ⟨rfl, reading, rfl⟩

theorem reading {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {source : KExpr .anon} {term : AExpr β}
    (reads : readScopedExpr? resolve locals source = some term.erase) :
    term = (parts source term).1.appN (parts source term).2 ∧
      readScopedExpr? resolve locals source.collectSpine.1 = some (parts source term).1.erase ∧
      source.collectSpine.2.toList.map (readScopedExpr? resolve locals ·) =
        (parts source term).2.map (some ·.erase) := by
  obtain ⟨rebuilt, headReads, argumentReads⟩ := view reads
  exact ⟨rebuilt, (RecM.appSpineView_collectSpine source).1.symm ▸ headReads,
    (RecM.appSpineView_collectSpine source).2.symm ▸ argumentReads⟩

theorem nonempty (fn arg : KExpr .anon) (info : ExprInfo .anon) :
    0 < (KExpr.app fn arg info).collectSpine.2.size := by
  have size := congrArg List.length (RecM.appSpineView_collectSpine (.app fn arg info)).2
  simp only [Array.length_toList, List.length_append, List.length_singleton] at size
  omega

end Ix.Kernel.Consistency.AppSpineSource
