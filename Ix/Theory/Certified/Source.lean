/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Store

/-! Every admitted entry retains the exact type and universe arity of its
source member or constructor. Semantic facts and equations add evidence;
they do not replace the authenticated declaration's statement. -/

namespace Ix.Theory.Certified

open Model Model.SetTheory

universe u v
variable {β : Type u}

structure SourceHeader (store : Store β) (ref : ConstRef β) (entry : ConstantEntry β) : Prop where
  type : store.type ref = some entry.type.erase
  universes : store.uvars ref = some entry.universes

namespace Ordinary.Shape

theorem family_sourceHeader {store : Store β} {shape : Ordinary.Shape β} {source : β}
    (h : store.blocks source = some ⟨[shape.source source]⟩) :
    SourceHeader store (.member source 0) shape.familyEntry := by
  constructor <;> simp [Store.type, Store.uvars, Store.lookup, h, Shape.source, familyEntry,
    Const.type, Const.uvars]

theorem constructor_sourceHeader {store : Store β} {shape : Ordinary.Shape β} {source : β}
    {index : Nat} {ctor : Ordinary.Constructor β}
    (h : store.blocks source = some ⟨[shape.source source]⟩)
    (hc : shape.constructors[index]? = some ctor) :
    SourceHeader store (.ctor source 0 index) (shape.constructorEntry source ctor) := by
  constructor <;> simp [Store.type, Store.uvars, Store.lookup, Store.lookupCtor, h,
    Shape.source, List.getElem?_map, hc, Ordinary.Constructor.source, constructorEntry]

theorem recursor_sourceHeader {store : Store β} {shape : Ordinary.Shape β} {source recursor : β}
    {mode : Inductive.ElimMode} (h : shape.RecursorSourceMatches store source recursor mode) :
    SourceHeader store (.member recursor 0) (shape.publishedRecursorEntry source recursor mode) := by
  rcases h with h | ⟨_, h⟩ <;>
    constructor <;> simp [Store.type, Store.uvars, Store.lookup, h,
      recursorSource, publishedRecursorEntry, recursorEntry, Const.type, Const.uvars]

end Ordinary.Shape

theorem Ordinary.EntrySource.header {store : Store β} {ref : ConstRef β} {entry : ConstantEntry β}
    (h : Ordinary.EntrySource store ref entry) : SourceHeader store ref entry := by
  rcases h with ⟨shape, source, recursor, mode, hs, hr, h⟩
  rcases h with ⟨rfl, rfl⟩ | ⟨index, ctor, hc, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact shape.family_sourceHeader hs
  · exact shape.constructor_sourceHeader hs hc
  · exact shape.recursor_sourceHeader hr

theorem Standard.EntrySource.header {store : Store β} {ref : ConstRef β} {entry : ConstantEntry β}
    (h : Standard.EntrySource store ref entry) : SourceHeader store ref entry := by
  rcases h with ⟨spec, hs, rfl⟩
  constructor <;> simp [Store.type, Store.uvars, hs, Standard.Spec.source, Standard.Spec.entry,
    Const.type, Const.uvars]

theorem Quotient.EntrySource.header {store : Store β} {ref : ConstRef β} {entry : ConstantEntry β}
    (h : Quotient.EntrySource store ref entry) : SourceHeader store ref entry := by
  rcases h with ⟨refs, kind, hs, rfl, rfl⟩
  have he := hs kind (by cases kind <;> simp [Quotient.kinds])
  constructor <;> cases kind <;>
    simp [Store.type, Store.uvars, he, Quotient.Refs.source, Quotient.Refs.entry,
      Quotient.Refs.entryType, Quotient.Kind.universes, Const.type, Const.uvars]

theorem Structure.EntrySource.header {store : Store β} {ref : ConstRef β} {entry : ConstantEntry β}
    (h : Structure.EntrySource store ref entry) : SourceHeader store ref entry := by
  rcases h with ⟨description, source, recursor, mode, hs, _, rfl, rfl⟩
  exact ⟨(description.ordinary.family_sourceHeader hs).type,
    (description.ordinary.family_sourceHeader hs).universes⟩

theorem Natural.EntrySource.header {pin : Option (ConstRef β)} {store : Store β}
    {ref : ConstRef β} {entry : ConstantEntry β}
    (h : Natural.EntrySource pin store ref entry) : SourceHeader store ref entry := by
  rcases h with ⟨_, source, recursor, mode, hs, _, rfl, rfl⟩
  exact ⟨(Ordinary.Shape.family_sourceHeader hs).type,
    (Ordinary.Shape.family_sourceHeader hs).universes⟩

theorem Modeled.EntrySource.header {store : Store β} {ref : ConstRef β} {entry : ConstantEntry β}
    (h : Modeled.EntrySource store ref entry) : SourceHeader store ref entry := by
  obtain ⟨_, companion, hs, rfl, rfl⟩ := h
  exact ⟨hs.1, hs.2.1⟩

/-- This covers every enabled admission form, including pinned primitives,
definition bodies, ordinary constructors and all C4 semantic extensions. -/
theorem EntrySource.header {signature : PrimitiveSignature β} {store : Store β}
    {ref : ConstRef β} {entry : ConstantEntry β}
    (h : EntrySource signature store ref entry) : SourceHeader store ref entry := by
  rcases h with ⟨rfl, rfl, hs⟩ | ⟨rfl, rfl, hs⟩ | ⟨kind, body, _, _, _, hs⟩ | h | h | h | h | h | h
  · constructor <;> simp [Store.type, Store.uvars, hs, PrimitiveSignature.falseDeclaration,
      PrimitiveSignature.falseEntry, Const.type, Const.uvars, AExpr.erase]
  · constructor <;> simp [Store.type, Store.uvars, hs, PrimitiveSignature.falseElimDeclaration,
      PrimitiveSignature.falseElimEntry, Const.type, Const.uvars]
  · constructor <;> simp [Store.type, Store.uvars, hs, Const.type, Const.uvars]
  · exact h.header
  · exact h.header
  · exact h.header
  · exact h.header
  · exact h.header
  · exact h.header

theorem AdmittedEnvironment.sourceHeader {signature : PrimitiveSignature β} {store : Store β}
    (state : AdmittedEnvironment.{u,v} signature store) {ref : ConstRef β} {entry : ConstantEntry β}
    (h : state.entries ref = some entry) : SourceHeader store ref entry :=
  (state.source ref entry h).header

/-- Every requested declaration is tied to its original source header and
is valid in each compatible interpretation of the admitted interface. -/
theorem CheckedStore.subject_sound {signature : PrimitiveSignature β} {store : Store β}
    {subjects : List (ConstRef β)} (result : CheckedStore.{u,v} signature store subjects)
    {ref : ConstRef β} (h : ref ∈ subjects) :
    ∃ entry, result.environment.entries ref = some entry ∧
      SourceHeader store ref entry ∧
      ∀ (V : Type v) [SetTheory V] (constants : Assignment β V),
        signature.Compatible result.environment.entries constants →
        ∀ levels, levels.length = entry.universes → ∀ env,
          WellDenoted constants levels env entry.type ∧
          constants ref levels ∈ˢ interp constants levels env entry.type := by
  have hp := result.targetsPresent ref h
  cases he : result.environment.entries ref with
  | none => simp [he] at hp
  | some entry =>
    refine ⟨entry, rfl, result.environment.sourceHeader he, ?_⟩
    intro V _ constants hM levels hl env
    exact ⟨hM.realizes.typeValid ref entry he levels hl env,
      hM.realizes.member ref entry he levels hl env⟩

/-- The exact source type has an inhabitant in a model constructed by the
checker; the source header is not an additional caller hypothesis. -/
theorem accepted_store_source_sound [DecidableEq β] {fuel : Nat} {signature : PrimitiveSignature β}
    {store : Store β} {subjects : List (ConstRef β)} {witness : List (DeclarationWitness β)}
    (h : acceptsStoreCertified.{u,v} fuel signature store subjects witness = true)
    (V : Type v) [SetTheory V] :
    ∃ result : CheckedStore.{u,v} signature store subjects,
      checkStoreCertified fuel signature store subjects witness = some result ∧
      ∃ constants : Assignment β V,
        signature.Compatible result.environment.entries constants ∧
        ∀ ref ∈ subjects, ∃ entry, result.environment.entries ref = some entry ∧
          SourceHeader store ref entry ∧
          ∀ levels, levels.length = entry.universes → ∀ env,
            WellDenoted constants levels env entry.type ∧
            constants ref levels ∈ˢ interp constants levels env entry.type := by
  obtain ⟨result, checked, constants, compatible, _⟩ := accepted_store_has_model h V
  refine ⟨result, checked, constants, compatible, ?_⟩
  intro ref hr
  obtain ⟨entry, he, hs, hm⟩ := result.subject_sound hr
  exact ⟨entry, he, hs, hm V constants compatible⟩

end Ix.Theory.Certified
