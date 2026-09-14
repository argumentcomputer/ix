/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.LocalScope
import Ix.Kernel.Verify.UniverseInternOnly

/-!
# Maintained structural local state

Coherent lookups and the allocation-counter bound justify freshness at each
actual binder opening. The installed lazy loader must preserve that bound
by never rewinding the counter. Interning preserves the state; successful opening
extends it under the production overflow guard; scope cleanup restores the
caller context while retaining the larger allocation counter. The same
contracts cover partial failure states and compose through monadic binds.

This is the structural local component of the general semantic state
invariant. It does not establish inference, reduction or cache meaning.
-/

namespace Ix.Kernel.LocalContext

private local instance : LawfulBEq FVarId where
  eq_of_beq := by
    intro left right equal
    cases left
    cases right
    congr 1
    exact eq_of_beq equal
  rfl {a} := by
    cases a with
    | mk x => show (x == x) = true; exact beq_self_eq_true x

/-- Every indexed local was allocated before the actual next identifier. -/
def IdsBelow (context : LocalContext m) (next : UInt64) : Prop :=
  ∀ (id : FVarId) (position : Nat), context.index[id]? = some position →
    id.id.toNat < next.toNat

namespace IdsBelow

theorem empty (next : UInt64) : IdsBelow ({} : LocalContext m) next := by
  intro id position found
  simp at found

theorem mono {context : LocalContext m} {next later : UInt64}
    (bound : context.IdsBelow next) (order : next.toNat ≤ later.toNat) : context.IdsBelow later := by
  intro id position found
  exact Nat.lt_of_lt_of_le (bound id position found) order

theorem equiv {left right : LocalContext m} {next : UInt64}
    (bound : left.IdsBelow next) (same : left.Equiv right) : right.IdsBelow next := by
  intro id position found
  exact bound id position ((same.index id).trans found)

theorem fresh {context : LocalContext m} {next : UInt64} (bound : context.IdsBelow next) :
    context.index[(⟨next⟩ : FVarId)]? = none := by
  cases found : context.index[(⟨next⟩ : FVarId)]? with
  | none => rfl
  | some position => exact False.elim (Nat.lt_irrefl _ (bound _ _ found))

theorem push {context : LocalContext m} {next : UInt64}
    (bound : context.IdsBelow next) (decl : LocalDecl m)
    (room : next.toNat + 1 < UInt64.size) :
    (context.push ⟨next⟩ decl).IdsBelow (next + 1) := by
  have increment : (next + 1).toNat = next.toNat + 1 := by
    rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt room]
  intro id position found
  simp only [LocalContext.push, Std.HashMap.getElem?_insert] at found
  rw [increment]
  split at found
  next equal =>
    have equal : (⟨next⟩ : FVarId) = id := eq_of_beq equal
    subst id
    exact Nat.lt_succ_self _
  next different => exact Nat.lt_trans (bound _ _ found) (Nat.lt_succ_self _)

end IdsBelow
end Ix.Kernel.LocalContext

namespace Ix.Kernel.Consistency
open Theory Theory.Model
universe u v

/-- The installed lazy loader never rewinds the allocation counter. The
production ingress loader must establish this property on both outcomes. -/
def LoaderCounterMonotone (loader : Option (Address → EStateM String (KEnv .anon) Bool)) : Prop :=
  ∀ fault, loader = some fault → ∀ addr before,
    match fault addr before with
    | .ok _ after | .error _ after => before.nextFVarId.toNat ≤ after.nextFVarId.toNat

/-- Structural component of the general state invariant: local lookup is
coherent, every live identifier precedes the allocation counter, and lazy
loading never rewinds that counter. -/
structure LocalStateInvariant (state : TcState .anon) : Prop where
  coherent : state.lctx.WF
  allocated : state.lctx.IdsBelow state.env.nextFVarId
  loader : LoaderCounterMonotone state.lazyFault

/-- A scoped operation can allocate fresh identifiers but restores all
incoming local declarations and lookups. -/
structure LocalStateFrame (before after : TcState .anon) : Prop where
  counter : before.env.nextFVarId.toNat ≤ after.env.nextFVarId.toNat
  context : after.lctx.Equiv before.lctx
  loader : after.lazyFault = before.lazyFault

namespace LocalStateFrame

theorem refl (state : TcState .anon) : LocalStateFrame state state := ⟨Nat.le_refl _, .refl _, rfl⟩

theorem trans {before middle after : TcState .anon}
    (first : LocalStateFrame before middle) (second : LocalStateFrame middle after) :
    LocalStateFrame before after :=
  ⟨Nat.le_trans first.counter second.counter, second.context.trans first.context,
    second.loader.trans first.loader⟩

theorem invariant {before after : TcState .anon}
    (frame : LocalStateFrame before after) (valid : LocalStateInvariant before) :
    LocalStateInvariant after :=
  ⟨frame.context.symm.wf valid.coherent,
    (valid.allocated.equiv frame.context.symm).mono frame.counter,
    by rw [frame.loader]; exact valid.loader⟩

end LocalStateFrame

/-- A body may leave fresh local declarations for its enclosing scope to
remove. Both returned states, including failures, must satisfy this effect. -/
structure LocalStateExtension (before after : TcState .anon) : Prop where
  valid : LocalStateInvariant after
  counter : before.env.nextFVarId.toNat ≤ after.env.nextFVarId.toNat
  context : before.lctx.Extension after.lctx
  loader : after.lazyFault = before.lazyFault

namespace LocalStateExtension

theorem refl {state : TcState .anon} (valid : LocalStateInvariant state) :
    LocalStateExtension state state := ⟨valid, Nat.le_refl _, .refl _, rfl⟩

theorem trans {before middle after : TcState .anon}
    (first : LocalStateExtension before middle) (second : LocalStateExtension middle after) :
    LocalStateExtension before after :=
  ⟨second.valid, Nat.le_trans first.counter second.counter, first.context.trans second.context,
    second.loader.trans first.loader⟩

theorem of_frame {before after : TcState .anon} (valid : LocalStateInvariant before)
    (frame : LocalStateFrame before after) : LocalStateExtension before after :=
  ⟨frame.invariant valid, frame.counter, .equiv (.refl _) frame.context.symm, frame.loader⟩

theorem restore {before after : TcState .anon} (effect : LocalStateExtension before after) :
    LocalStateFrame before {after with lctx := after.lctx.truncate before.lctx.size} :=
  ⟨effect.counter, effect.context.restore, effect.loader⟩

end LocalStateExtension

theorem LocalStateInvariant.ofValues {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {values : LocalValues β} {context : Model.Context β}
    {state : TcState .anon}
    (agreement : LocalContextValues.{u,v} resolve entries values state.lctx context)
    (bound : values.Below state.env.nextFVarId)
    (loader : LoaderCounterMonotone state.lazyFault) : LocalStateInvariant state := by
  refine ⟨agreement.coherent, ?_, loader⟩
  intro id position found
  obtain ⟨decl, hit⟩ := agreement.coherent.sound found
  have lookup : state.lctx.find? id = some decl := by
    simp [LocalContext.find?, found, hit]
  obtain ⟨value, read⟩ := agreement.complete id decl lookup
  exact bound id value read

/-- Prefix preservation under the structural local-state invariant. -/
def PreservesLocalState (action : TcM .anon α) : Prop :=
  ∀ before, LocalStateInvariant before → match action before with
    | .ok _ after | .error _ after => LocalStateExtension before after

/-- Scoped preservation under the same invariant. The ending invariant is
derived from the restored context and monotone counter. -/
def FramesLocalState (action : TcM .anon α) : Prop :=
  ∀ before, LocalStateInvariant before → match action before with
    | .ok _ after | .error _ after => LocalStateFrame before after

namespace FramesLocalState

theorem preserves {action : TcM .anon α} (framed : FramesLocalState action) :
    PreservesLocalState action := by
  intro before valid
  have frame := framed before valid
  cases run : action before <;> rw [run] at frame <;> exact .of_frame valid frame

theorem pure (value : α) : FramesLocalState (Pure.pure value) := fun _ _ => .refl _

theorem throw (error : TcError .anon) : FramesLocalState (throw error : TcM .anon α) :=
  fun _ _ => .refl _

theorem runIntern (action : InternM .anon α) : FramesLocalState (TcM.runIntern action) :=
  fun _ _ => ⟨Nat.le_refl _, .refl _, rfl⟩

theorem of_internOnly {action : TcM .anon α} (only : action.InternOnly) :
    FramesLocalState action := by
  intro before _
  have changed := only before
  cases run : action before <;> rw [run] at changed <;>
    obtain ⟨table, exactState⟩ := changed <;> rw [exactState] <;>
    exact ⟨Nat.le_refl _, .refl _, rfl⟩

theorem instantiateUnivParams (type : KExpr .anon) (levels : Array (KUniv .anon)) :
    FramesLocalState (TcM.instantiateUnivParams type levels) :=
  of_internOnly (TcM.InternOnly.instantiateUnivParams type levels)

theorem bind {action : TcM .anon α} {next : α → TcM .anon γ}
    (first : FramesLocalState action) (rest : ∀ value, FramesLocalState (next value)) :
    FramesLocalState (action >>= next) := by
  intro before valid
  have intermediate := first before valid
  change match EStateM.bind action next before with
    | .ok _ after | .error _ after => LocalStateFrame before after
  cases run : action before with
  | error error after => rw [EStateM.bind, run]; simpa only [run] using intermediate
  | ok value after =>
      rw [run] at intermediate
      rw [EStateM.bind, run]
      dsimp only
      have final := rest value after (intermediate.invariant valid)
      cases finished : next value after <;> rw [finished] at final <;> exact intermediate.trans final

end FramesLocalState

namespace PreservesLocalState

theorem bind {action : TcM .anon α} {next : α → TcM .anon γ}
    (first : PreservesLocalState action) (rest : ∀ value, PreservesLocalState (next value)) :
    PreservesLocalState (action >>= next) := by
  intro before valid
  have intermediate := first before valid
  change match EStateM.bind action next before with
    | .ok _ after | .error _ after => LocalStateExtension before after
  cases run : action before with
  | error error after => rw [EStateM.bind, run]; simpa only [run] using intermediate
  | ok value after =>
      rw [run] at intermediate
      rw [EStateM.bind, run]
      dsimp only
      have final := rest value after intermediate.valid
      cases finished : next value after <;> rw [finished] at final <;> exact intermediate.trans final

/-- Scope cleanup turns a prefix-preserving body into a framed computation,
including the body's partially updated failure state. -/
theorem withLctxScope {action : RecM .anon α} {methods : Methods .anon}
    (body : PreservesLocalState (action.run methods)) :
    FramesLocalState ((RecM.withLctxScope action).run methods) := by
  intro before valid
  rw [withLctxScope_eq]
  have inner := body before valid
  cases run : action.run methods before <;> rw [run] at inner <;> exact inner.restore

theorem openLet (name : Mode.anon.F Name) (type value body : KExpr .anon) :
    PreservesLocalState (TcM.openLet name type value body) := by
  intro before valid
  rw [openLet_eq]
  by_cases room : before.env.nextFVarId.toNat + 1 < UInt64.size
  · rw [if_pos room]
    have increment : (before.env.nextFVarId + 1).toNat = before.env.nextFVarId.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt room]
    exact ⟨⟨valid.coherent.push valid.allocated.fresh, valid.allocated.push _ room, valid.loader⟩,
      by change before.env.nextFVarId.toNat ≤ (before.env.nextFVarId + 1).toNat
         rw [increment]; omega, .push _ (.refl _) valid.allocated.fresh, rfl⟩
  · rw [if_neg room]; exact .refl valid

theorem openBinder (name : Mode.anon.F Name) (bi : Mode.anon.F Lean.BinderInfo)
    (type body : KExpr .anon) : PreservesLocalState (TcM.openBinder name bi type body) := by
  intro before valid
  rw [openBinder_eq]
  by_cases room : before.env.nextFVarId.toNat + 1 < UInt64.size
  · rw [if_pos room]
    have increment : (before.env.nextFVarId + 1).toNat = before.env.nextFVarId.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt room]
    exact ⟨⟨valid.coherent.push valid.allocated.fresh, valid.allocated.push _ room, valid.loader⟩,
      by change before.env.nextFVarId.toNat ≤ (before.env.nextFVarId + 1).toNat
         rw [increment]; omega, .push _ (.refl _) valid.allocated.fresh, rfl⟩
  · rw [if_neg room]; exact .refl valid

end PreservesLocalState
end Ix.Kernel.Consistency
