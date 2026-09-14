/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Quotient.Checked

namespace Ix.Theory.Certified.Quotient

open Model Model.SetTheory

universe u v
variable {β : Type u} [DecidableEq β]

def Refs.environment (refs : Refs β) (entries : Environment β) : Environment β :=
  fun r => match refs.kind? r with
    | some kind => some (refs.entry kind)
    | none => entries r

variable {entries : Environment β} {store : Store β} {refs : Refs β}

theorem environment_same (h : Checked.{u,v} entries store refs) (kind : Kind) :
    refs.environment entries (refs.ref kind) = some (refs.entry kind) := by
  simp only [Refs.environment, Refs.kind?_same h.exactSource]

theorem environment_old (h : Checked.{u,v} entries store refs) {r : ConstRef β}
    {entry : ConstantEntry β} (hr : entries r = some entry) : refs.environment entries r = some entry := by
  unfold Refs.environment
  cases hk : refs.kind? r with
  | none => exact hr
  | some kind =>
    have he := Refs.kind?_sound hk
    have hf := h.fresh kind (mem_kinds kind)
    rw [← he, hr] at hf
    contradiction

theorem environment_cases {r : ConstRef β} {entry : ConstantEntry β}
    (hr : refs.environment entries r = some entry) :
    entries r = some entry ∨ ∃ kind, r = refs.ref kind ∧ entry = refs.entry kind := by
  unfold Refs.environment at hr
  split at hr
  · exact Or.inr ⟨_, Refs.kind?_sound ‹_›, (Option.some.inj hr).symm⟩
  · exact Or.inl hr

theorem environment_covers_types (h : Checked.{u,v} entries store refs) {r : ConstRef β}
    {entry : ConstantEntry β} (hr : refs.typeEnvironment entries r = some entry) :
    (refs.environment entries r).isSome := by
  rcases Signature.environment_source hr with hold | ⟨header, hm, he, _⟩
  · simp only [environment_old h hold, Option.isSome_some]
  · obtain ⟨kind, _, rfl⟩ := List.mem_map.mp hm
    subst r
    simp only [Refs.header, environment_same h, Option.isSome_some]

theorem references_from_types (h : Checked.{u,v} entries store refs) {e : AExpr β}
    (hr : e.ReferencesIn (refs.typeEnvironment entries)) : e.ReferencesIn (refs.environment entries) := by
  intro r he
  have hh := hr r he
  cases ht : refs.typeEnvironment entries r with
  | none => simp [ht] at hh
  | some entry => exact environment_covers_types h ht

theorem references_from_old (h : Checked.{u,v} entries store refs) {e : AExpr β}
    (hr : e.ReferencesIn entries) : e.ReferencesIn (refs.environment entries) := by
  intro r he
  have hh := hr r he
  cases ht : entries r with
  | none => simp [ht] at hh
  | some entry => simp only [environment_old h ht, Option.isSome_some]

theorem fact_references_from_old (h : Checked.{u,v} entries store refs) {fact : ConstantFact β}
    (hr : fact.ReferencesIn entries) : fact.ReferencesIn (refs.environment entries) := by
  intro r he
  have hh := hr r he
  cases ht : entries r with
  | none => simp [ht] at hh
  | some entry => simp only [environment_old h ht, Option.isSome_some]

theorem equation_scope (h : Checked.{u,v} entries store refs) (kind : Kind)
    {law : ConstantEquation β} (hl : law ∈ refs.equations kind) :
    law.lhs.Scope kind.universes 0 ∧ law.rhs.Scope kind.universes 0 := by
  cases kind with
  | type | ctor | sound => cases hl
  | lift =>
    have he := List.mem_singleton.mp hl
    subst law
    exact h.liftRule.scope.2
  | ind =>
    have he := List.mem_singleton.mp hl
    subst law
    exact h.indRule.scope.2

theorem equation_references (h : Checked.{u,v} entries store refs) (kind : Kind)
    {law : ConstantEquation β} (hl : law ∈ refs.equations kind) :
    law.lhs.ReferencesIn (refs.environment entries) ∧ law.rhs.ReferencesIn (refs.environment entries) := by
  cases kind with
  | type | ctor | sound => cases hl
  | lift =>
    have he := List.mem_singleton.mp hl
    subst law
    exact ⟨references_from_types h h.liftRule.references.2.1, references_from_types h h.liftRule.references.2.2⟩
  | ind =>
    have he := List.mem_singleton.mp hl
    subst law
    exact ⟨references_from_types h h.indRule.references.2.1, references_from_types h h.indRule.references.2.2⟩

theorem entry_closed (h : Checked.{u,v} entries store refs) (hE : entries.WF) (kind : Kind) :
    EntryClosed (refs.environment entries) (refs.entry kind) := by
  have ht := h.types.wf hE
  have hl := typeEnvironment_lookup h kind
  constructor
  · exact ht.typeScope _ (refs.header kind).entry hl
  · intro body hb; cases hb
  · exact references_from_types h (ht.typeReferences _ (refs.header kind).entry hl)
  · intro body hb; cases hb
  · exact fun _ hh => equation_scope h kind hh
  · exact fun _ hh => equation_references h kind hh
  · intro fact hf; cases hf
  · intro fact hf; cases hf

theorem environment_wf (h : Checked.{u,v} entries store refs) (hE : entries.WF) :
    (refs.environment entries).WF := by
  have hc : ∀ r entry, refs.environment entries r = some entry → EntryClosed (refs.environment entries) entry := by
    intro r entry hr
    rcases environment_cases hr with hold | ⟨kind, _, rfl⟩
    · exact ⟨hE.typeScope _ _ hold, hE.bodyScope _ _ hold,
        references_from_old h (hE.typeReferences _ _ hold),
        fun body hb => references_from_old h (hE.bodyReferences _ _ hold body hb),
        hE.equationScope _ _ hold,
        fun law hl => ⟨references_from_old h (hE.equationReferences _ _ hold law hl).1,
          references_from_old h (hE.equationReferences _ _ hold law hl).2⟩,
        hE.factScope _ _ hold,
        fun fact hf => fact_references_from_old h (hE.factReferences _ _ hold fact hf)⟩
    · exact entry_closed h hE kind
  exact ⟨fun r e hr => (hc r e hr).typeScope, fun r e hr => (hc r e hr).bodyScope,
    fun r e hr => (hc r e hr).typeReferences, fun r e hr => (hc r e hr).bodyReferences,
    fun r e hr => (hc r e hr).equationScope, fun r e hr => (hc r e hr).equationReferences,
    fun r e hr => (hc r e hr).factScope, fun r e hr => (hc r e hr).factReferences⟩

/-- The exact five source declarations, including the safe soundness axiom,
determine each published type and computation equation. -/
def EntrySource (store : Store β) (r : ConstRef β) (entry : ConstantEntry β) : Prop :=
  ∃ refs : Refs β, ∃ kind, refs.ExactSource store ∧ r = refs.ref kind ∧ entry = refs.entry kind

theorem environment_source (h : Checked.{u,v} entries store refs) {r : ConstRef β} {entry : ConstantEntry β}
    (hr : refs.environment entries r = some entry) : entries r = some entry ∨ EntrySource store r entry := by
  rcases environment_cases hr with hold | ⟨kind, he, hv⟩
  · exact Or.inl hold
  · exact Or.inr ⟨refs, kind, h.exactSource, he, hv⟩

variable {V : Type v} [SetTheory V]

theorem equation_value (h : Checked.{u,v} entries store refs) (hE : entries.WF)
    (constants : Assignment β V) (hM : Realizes constants entries) (kind : Kind)
    {law : ConstantEquation β} (hl : law ∈ refs.equations kind)
    (levels : List Nat) (hn : levels.length = kind.universes) (env : Nat → V) :
    interp (refs.assignment constants) levels env law.lhs = interp (refs.assignment constants) levels env law.rhs := by
  cases kind with
  | type | ctor | sound => cases hl
  | lift =>
    have he := List.mem_singleton.mp hl
    subst law
    cases levels with
    | nil => cases hn
    | cons u tail =>
      obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp (Nat.succ.inj hn)
      exact liftRule_eq (assignment_reading h constants) h.equality
        (hM.of_agrees hE (assignment_agrees h constants)) u v env
  | ind =>
    have he := List.mem_singleton.mp hl
    subst law
    exact indRule_eq _ _ _ _

theorem assignment_realizes (h : Checked.{u,v} entries store refs) (hE : entries.WF)
    (constants : Assignment β V) (hM : Realizes constants entries) :
    Realizes (refs.assignment constants) (refs.environment entries) := by
  have hs := typeAssignment_realizes h hE constants hM
  have ho := hM.of_agrees hE (assignment_agrees h constants)
  have he : ∀ r entry, refs.environment entries r = some entry → EntryRealization (refs.assignment constants) r entry := by
    intro r entry hr
    rcases environment_cases hr with hold | ⟨kind, rfl, rfl⟩
    · exact ⟨ho.typeValid _ _ hold, ho.member _ _ hold, ho.bodyValid _ _ hold,
        ho.bodyValue _ _ hold, ho.equationValue _ _ hold, ho.factMeaning _ _ hold⟩
    · have ht := typeEnvironment_lookup h kind
      constructor
      · exact hs.typeValid _ (refs.header kind).entry ht
      · exact hs.member _ (refs.header kind).entry ht
      · intro body hb; cases hb
      · intro body hb; cases hb
      · exact fun law hl => equation_value h hE constants hM kind hl
      · intro fact hf; cases hf
  exact ⟨fun r e hr => (he r e hr).typeValid, fun r e hr => (he r e hr).member,
    fun r e hr => (he r e hr).bodyValid, fun r e hr => (he r e hr).bodyValue,
    fun r e hr => (he r e hr).equationValue, fun r e hr => (he r e hr).factMeaning⟩

end Ix.Theory.Certified.Quotient
