/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.ScopedExpr
import Ix.Kernel.Verify.Check.ValidatorSoundness

/-!
# Production validation and model scope

Successful declaration validation supplies the universe bounds of its actual
syntax. The scoped reader supplies de Bruijn closure. Only the occurrence
annotations, which are absent from kernel syntax, need a separate bounds
check; no typing or model-realization premise is used here.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u
variable {β : Type u}

/-- Bounds for the auxiliary binder conditions, without any claim about
source syntax, typing, or the truth of those conditions. -/
def ConditionsScoped (universes : Nat) : AExpr β → Prop
  | .app fn arg => ConditionsScoped universes fn ∧ ConditionsScoped universes arg
  | .lam condition domain body | .forallE condition domain body =>
      condition.WF universes ∧ ConditionsScoped universes domain ∧
        ConditionsScoped universes body
  | .proj _ _ major => ConditionsScoped universes major
  | _ => True

private theorem option_bind_success {α γ : Type _} {action : Option α}
    {next : α → Option γ} {result : γ} (run : action.bind next = some result) :
    ∃ intermediate, action = some intermediate ∧ next intermediate = some result := by
  cases action with
  | none => contradiction
  | some value => exact ⟨value, rfl, run⟩

/-- The actual validator's universe bounds and the closed scoped reading
establish both parts of raw model scope. The reader counts binders with
unbounded naturals, so this theorem does not convert a wrapped kernel depth. -/
theorem readScopedExpr?_scope {resolve : Address → Option (ConstRef β)}
    {term : KExpr .anon} {source : VExpr β} {depth universes : Nat} {kernelDepth : UInt64}
    (reading : readScopedExpr? resolve [] term depth = some source)
    (validSyntax : term.Scoped kernelDepth universes) :
    source.LevelWF universes ∧ source.ClosedN depth := by
  induction term generalizing source depth kernelDepth with
  | var index name info =>
      simp only [readScopedExpr?] at reading
      split at reading
      next bound => cases reading; exact ⟨trivial, bound⟩
      next => contradiction
  | fvar _ _ _ | letE _ _ _ _ _ _ _ _ _ | str _ _ _ => contradiction
  | sort level info =>
      cases reading
      exact ⟨readLevel_eq level ▸ validSyntax.toVLevel_wf, trivial⟩
  | const id levels info =>
      rw [readScopedExpr?] at reading
      obtain ⟨ref, _, reading⟩ := option_bind_success reading
      cases reading
      refine ⟨?_, trivial⟩
      intro level member
      obtain ⟨value, present, rfl⟩ := List.mem_map.mp member
      simpa only [readLevel_eq] using (validSyntax value (by simpa using present)).toVLevel_wf
  | app fn arg info ihFn ihArg | lam _ _ fn arg info ihFn ihArg | all _ _ fn arg info ihFn ihArg =>
      rw [readScopedExpr?] at reading
      obtain ⟨f, fReads, reading⟩ := option_bind_success reading
      obtain ⟨a, aReads, reading⟩ := option_bind_success reading
      cases reading
      have fScope := ihFn fReads validSyntax.1
      have aScope := ihArg aReads validSyntax.2
      exact ⟨⟨fScope.1, aScope.1⟩, ⟨fScope.2, aScope.2⟩⟩
  | prj id index value info ih =>
      rw [readScopedExpr?] at reading
      obtain ⟨ref, _, reading⟩ := option_bind_success reading
      obtain ⟨value, valueReads, reading⟩ := option_bind_success reading
      cases reading
      have scope := ih valueReads validSyntax
      exact ⟨scope.1, scope.2⟩
  | nat value name info => cases reading; exact ⟨trivial, trivial⟩

/-- Add only the auxiliary condition bounds to the scope of the erased
syntax; every source universe and term index comes from that syntax. -/
theorem ConditionsScoped.scope {term : AExpr β} {universes depth : Nat}
    (conditions : ConditionsScoped universes term)
    (levels : term.erase.LevelWF universes) (closed : term.erase.ClosedN depth) :
    term.Scope universes depth := by
  induction term generalizing depth with
  | bvar => exact closed
  | sort | const => exact levels
  | app fn arg ihFn ihArg =>
      exact ⟨ihFn conditions.1 levels.1 closed.1, ihArg conditions.2 levels.2 closed.2⟩
  | lam p domain body ihDomain ihBody | forallE p domain body ihDomain ihBody =>
      exact ⟨conditions.1, ihDomain conditions.2.1 levels.1 closed.1,
        ihBody conditions.2.2 levels.2 closed.2⟩
  | proj ref field major ih => exact ih conditions levels closed
  | natLit => trivial

/-- Scope of an annotated reading follows from the production syntax
certificate and bounds on the auxiliary conditions. -/
theorem readScopedExpr?_annotated_scope {resolve : Address → Option (ConstRef β)}
    {term : KExpr .anon} {source : AExpr β} {depth universes : Nat} {kernelDepth : UInt64}
    (reading : readScopedExpr? resolve [] term depth = some source.erase)
    (validSyntax : term.Scoped kernelDepth universes)
    (conditions : ConditionsScoped universes source) : source.Scope universes depth := by
  have scope := readScopedExpr?_scope reading validSyntax
  exact conditions.scope scope.1 scope.2

end Ix.Kernel.Consistency
