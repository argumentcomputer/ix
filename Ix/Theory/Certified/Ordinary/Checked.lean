/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Ordinary.RuleEquations

namespace Ix.Theory.Certified.Ordinary

open Model Model.SetTheory Inductive

universe u v
variable {β : Type u} [DecidableEq β]

structure BlockWitness (β : Type u) where
  source : β
  recursor : β
  shape : ShapeWitness β
  mode : ElimMode
  constructorTypes : List (Shape.TypeWitness β)
  recursorType : Shape.TypeWitness β
  rules : List (RuleWitness β)

structure CheckedBlock (entries : Environment β) (store : Store β) (source recursor : β)
    (shape : Shape β) (mode : ElimMode) : Prop where
  shapeChecked : CheckedShape.{u,v} entries store source shape
  constructors : shape.ConstructorFormation.{u,v} entries source
  recursorChecked : shape.RecursorFormation.{u,v} entries store source recursor mode
  elimination : ModeEvidence.{u,v} entries shape mode
  rules : ∀ i ctor, shape.constructors[i]? = some ctor →
    shape.RuleFormation.{u,v} (shape.recursorEnvironment entries source recursor mode) source recursor mode i ctor

def checkBlock (fuel : Nat) (entries : Environment β) (store : Store β) (witness : BlockWitness β) :
    Option (CheckedClaim.{u} (CheckedBlock.{u,v} entries store witness.source witness.recursor witness.shape.shape witness.mode)) := do
  let shape ← checkShape.{u,v} fuel entries store witness.source witness.shape
  let mode ← checkMode.{u,v} fuel entries witness.shape witness.mode
  let constructors ← witness.shape.shape.checkConstructorTypes.{u,v} fuel entries witness.source
    witness.shape.shape.constructors witness.constructorTypes
  let recursor ← witness.shape.shape.checkRecursorType.{u,v} fuel entries store witness.source witness.recursor
    witness.mode witness.recursorType
  let rules ← witness.shape.shape.checkRules.{u,v} fuel
    (witness.shape.shape.recursorEnvironment entries witness.source witness.recursor witness.mode)
    witness.source witness.recursor witness.mode witness.shape.shape.constructors.zipIdx witness.rules
  return ⟨⟨shape.down, constructors.down, recursor.down, mode.down, fun i ctor hc =>
    rules.down ctor i (List.mk_mem_zipIdx_iff_getElem?.mpr hc)⟩⟩

theorem checkBlock_sound {fuel : Nat} {entries : Environment β} {store : Store β} {witness : BlockWitness β}
    {result} (_ : checkBlock.{u,v} fuel entries store witness = some result) :
    CheckedBlock.{u,v} entries store witness.source witness.recursor witness.shape.shape witness.mode := result.down

namespace Shape

def publishedRecursorEntry (shape : Shape β) (source recursor : β) (mode : ElimMode) : ConstantEntry β :=
  { shape.recursorEntry source mode with equations := shape.recursorLaws source recursor mode }

def publishedEnvironment (shape : Shape β) (entries : Environment β) (source recursor : β)
    (mode : ElimMode) : Environment β :=
  (shape.constructorEnvironment entries source).insert (.member recursor 0)
    (shape.publishedRecursorEntry source recursor mode)

omit [DecidableEq β] in
theorem recursorLaws_member {shape : Shape β} {source recursor : β} {mode : ElimMode}
    {law : ConstantEquation β} (hl : law ∈ shape.recursorLaws source recursor mode) :
    ∃ i ctor, shape.constructors[i]? = some ctor ∧
      law = ⟨shape.ruleLhs source recursor mode i ctor, shape.ruleRhs source recursor mode i ctor⟩ := by
  obtain ⟨⟨ctor, i⟩, hc, he⟩ := List.mem_map.mp hl
  exact ⟨i, ctor, List.mk_mem_zipIdx_iff_getElem?.mp hc, he.symm⟩

theorem publishedEnvironment_wf {entries : Environment β} {store : Store β} {source recursor : β}
    {shape : Shape β} {mode : ElimMode} (h : CheckedBlock.{u,v} entries store source recursor shape mode)
    (hE : entries.WF) : (shape.publishedEnvironment entries source recursor mode).WF := by
  have hwf := (recursorEnvironment_wf h.shapeChecked hE h.constructors h.recursorChecked).insert
    (r := .member recursor 0) (entry := shape.publishedRecursorEntry source recursor mode)
    h.recursorChecked.closed.typeScope (by simp [publishedRecursorEntry, recursorEntry])
    h.recursorChecked.closed.typeReferences.insert (by simp [publishedRecursorEntry, recursorEntry])
    (by
      intro law hl
      obtain ⟨i, ctor, hc, rfl⟩ := recursorLaws_member hl
      exact (h.rules i ctor hc).scope)
    (by
      intro law hl
      obtain ⟨i, ctor, hc, rfl⟩ := recursorLaws_member hl
      exact (h.rules i ctor hc).references)
    (by simp [publishedRecursorEntry, recursorEntry]) (by simp [publishedRecursorEntry, recursorEntry])
  simpa only [publishedEnvironment, recursorEnvironment, Environment.insert_replace] using hwf

theorem publishedEnvironment_old {entries : Environment β} {store : Store β} {source recursor : β}
    {shape : Shape β} {mode : ElimMode} (h : CheckedBlock.{u,v} entries store source recursor shape mode)
    {r : ConstRef β} {entry : ConstantEntry β} (hr : entries r = some entry) :
    shape.publishedEnvironment entries source recursor mode r = some entry :=
  Environment.insert_old h.recursorChecked.fresh (Environment.overlay_old
    (constructorEntries_fresh h.shapeChecked) (Environment.insert_old
      (h.shapeChecked.fresh _ (List.mem_cons_self ..)) hr))

variable {V : Type v} [SetTheory V]

theorem publishedAssignment_realizes {entries : Environment β} {store : Store β} {source recursor : β}
    {shape : Shape β} {mode : ElimMode} (h : CheckedBlock.{u,v} entries store source recursor shape mode)
    (hE : entries.WF) (constants : Assignment β V) (hM : Realizes constants entries) :
    Realizes (shape.recursorAssignment constants source recursor mode)
      (shape.publishedEnvironment entries source recursor mode) := by
  have hstage := recursorAssignment_realizes h.shapeChecked hE h.constructors h.recursorChecked h.elimination constants hM
  have hlocal : EntryRealization (shape.recursorAssignment constants source recursor mode) (.member recursor 0)
      (shape.publishedRecursorEntry source recursor mode) := by
    constructor
    · exact hstage.typeValid (.member recursor 0) (shape.recursorEntry source mode) (Environment.insert_same ..)
    · exact hstage.member (.member recursor 0) (shape.recursorEntry source mode) (Environment.insert_same ..)
    · intro body hb; cases hb
    · intro body hb; cases hb
    · intro law hl levels hn env
      obtain ⟨i, ctor, hc, rfl⟩ := recursorLaws_member hl
      exact produced_rule_eq h.shapeChecked hE h.constructors h.recursorChecked h.elimination hM hn hc (h.rules i ctor hc) env
    · intro fact hf; cases hf
  have hm := hstage.insert hlocal
  simpa only [publishedEnvironment, recursorEnvironment, Environment.insert_replace] using hm

theorem publishedAssignment_agrees {entries : Environment β} {store : Store β} {source recursor : β}
    {shape : Shape β} {mode : ElimMode} (h : CheckedBlock.{u,v} entries store source recursor shape mode)
    (constants : Assignment β V) :
    Assignment.AgreesOn entries constants (shape.recursorAssignment constants source recursor mode) :=
  (recursorAssignment_reading h.shapeChecked h.recursorChecked constants).agrees

end Shape

/-- Source provenance is data-only. Both blocks and every equation endpoint
are tied to the exact ordinary description and recursor stored in the input. -/
def EntrySource (store : Store β) (r : ConstRef β) (entry : ConstantEntry β) : Prop :=
  ∃ shape : Shape β, ∃ source recursor mode,
    store.blocks source = some ⟨[shape.source source]⟩ ∧
    shape.RecursorSourceMatches store source recursor mode ∧
    ((r = .member source 0 ∧ entry = shape.familyEntry) ∨
      (∃ i ctor, shape.constructors[i]? = some ctor ∧ r = .ctor source 0 i ∧ entry = shape.constructorEntry source ctor) ∨
      (r = .member recursor 0 ∧ entry = shape.publishedRecursorEntry source recursor mode))

theorem publishedEntry_source {entries : Environment β} {store : Store β} {source recursor : β}
    {shape : Shape β} {mode : ElimMode} (h : CheckedBlock.{u,v} entries store source recursor shape mode)
    {r : ConstRef β} {entry : ConstantEntry β}
    (hr : shape.publishedEnvironment entries source recursor mode r = some entry) :
    entries r = some entry ∨ EntrySource store r entry := by
  have wrap : ∀ entry, ((r = .member source 0 ∧ entry = shape.familyEntry) ∨
      (∃ i ctor, shape.constructors[i]? = some ctor ∧ r = .ctor source 0 i ∧ entry = shape.constructorEntry source ctor) ∨
      (r = .member recursor 0 ∧ entry = shape.publishedRecursorEntry source recursor mode)) → EntrySource store r entry :=
    fun _ hh => ⟨shape, source, recursor, mode, h.shapeChecked.exactSource, h.recursorChecked.exactSource, hh⟩
  unfold Shape.publishedEnvironment Environment.insert at hr
  split at hr
  next he =>
    cases Option.some.inj hr
    exact Or.inr (wrap _ (Or.inr (Or.inr ⟨he, rfl⟩)))
  next =>
    unfold Shape.constructorEnvironment Environment.overlay at hr
    split at hr
    next entry' he =>
      cases Option.some.inj hr
      obtain ⟨i, ctor, hr, hc, he'⟩ := Shape.constructorEntries_some he
      exact Or.inr (wrap _ (Or.inr (Or.inl ⟨i, ctor, hc, hr, he'⟩)))
    next =>
      unfold Shape.familyEnvironment Environment.insert at hr
      split at hr
      next he =>
        cases Option.some.inj hr
        exact Or.inr (wrap _ (Or.inl ⟨he, rfl⟩))
      next => exact Or.inl hr

end Ix.Theory.Certified.Ordinary
