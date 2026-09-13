/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Natural.Checked

namespace Ix.Theory.Certified.Natural

open Model Model.SetTheory

universe u v
variable {β : Type u} [DecidableEq β] {entries : Environment β} {store : Store β}
  {pin : ConstRef β} {source recursor : β} {mode : Inductive.ElimMode}

theorem family_lookup (h : Checked.{u,v} entries store pin source recursor mode) :
    shape.publishedEnvironment entries source recursor mode (.member source 0) = some (shape : Ordinary.Shape β).familyEntry := by
  apply Environment.insert_old h.block.recursorChecked.fresh
  simp [Ordinary.Shape.constructorEnvironment, Environment.overlay, Ordinary.Shape.constructorEntries,
    Ordinary.Shape.familyEnvironment]

theorem environment_wf (h : Checked.{u,v} entries store pin source recursor mode) (hE : entries.WF) :
    (environment entries source recursor mode).WF := by
  have hb := Ordinary.Shape.publishedEnvironment_wf h.block hE
  exact hb.insert (hb.typeScope _ (shape : Ordinary.Shape β).familyEntry (family_lookup h))
    (by simp [entry, Ordinary.Shape.familyEntry])
    (hb.typeReferences _ (shape : Ordinary.Shape β).familyEntry (family_lookup h))
    (by simp [entry, Ordinary.Shape.familyEntry])
    (by simp [entry, Ordinary.Shape.familyEntry])
    (by simp [entry, Ordinary.Shape.familyEntry])
    (by simp [entry, fact, ConstantFact.Scope, shape, Ordinary.Shape.familyEntry])
    (by simpa only [entry, List.mem_singleton, forall_eq] using h.references)

theorem environment_old (h : Checked.{u,v} entries store pin source recursor mode)
    {r : ConstRef β} {old : ConstantEntry β} (hr : entries r = some old) :
    environment entries source recursor mode r = some old := by
  simp only [environment, Environment.insert,
    if_neg (fresh_ne (h.block.shapeChecked.fresh _ (List.mem_cons_self ..)) hr)]
  exact Ordinary.Shape.publishedEnvironment_old h.block hr

variable {V : Type v} [SetTheory V]

theorem assignment_realizes (h : Checked.{u,v} entries store pin source recursor mode)
    (hE : entries.WF) (constants : Assignment β V) (hM : Realizes constants entries) :
    Realizes (shape.recursorAssignment constants source recursor mode) (environment entries source recursor mode) := by
  have hb := Ordinary.Shape.publishedAssignment_realizes h.block hE constants hM
  have hr := Ordinary.Shape.recursorAssignment_reading h.block.shapeChecked h.block.recursorChecked constants
  apply hb.insert
  constructor
  · exact hb.typeValid _ (shape : Ordinary.Shape β).familyEntry (family_lookup h)
  · exact hb.member _ (shape : Ordinary.Shape β).familyEntry (family_lookup h)
  · intro body hb; cases hb
  · intro body hb; cases hb
  · intro law hl; cases hl
  · intro f hf levels hn _
    cases List.mem_singleton.mp hf
    have he : levels = [] := List.eq_nil_of_length_eq_zero hn
    subst levels
    exact ⟨rfl, meaning h.block.shapeChecked hr.toConstructorReading hM⟩

end Ix.Theory.Certified.Natural

namespace Ix.Theory.Certified.Natural

open Model
universe u v
variable {β : Type u} [DecidableEq β]

def EntrySource (pin : Option (ConstRef β)) (store : Store β) (r : ConstRef β) (e : ConstantEntry β) : Prop :=
  pin = some r ∧ ∃ source recursor mode,
    store.blocks source = some ⟨[shape.source source]⟩ ∧
    shape.RecursorSourceMatches store source recursor mode ∧ r = .member source 0 ∧ e = entry source

theorem environment_source {entries : Environment β} {store : Store β} {pin : ConstRef β}
    {source recursor : β} {mode : Inductive.ElimMode}
    (h : Checked.{u,v} entries store pin source recursor mode) {r : ConstRef β} {e : ConstantEntry β}
    (hr : environment entries source recursor mode r = some e) :
    entries r = some e ∨ Ordinary.EntrySource store r e ∨ EntrySource (some pin) store r e := by
  unfold environment Environment.insert at hr
  split at hr
  next he =>
    cases Option.some.inj hr
    exact Or.inr (Or.inr ⟨congrArg some (h.primitive.trans he.symm), source, recursor, mode,
      h.block.shapeChecked.exactSource, h.block.recursorChecked.exactSource, he, rfl⟩)
  next =>
    rcases Ordinary.publishedEntry_source h.block hr with hold | hnew
    · exact Or.inl hold
    · exact Or.inr (Or.inl hnew)

end Ix.Theory.Certified.Natural
