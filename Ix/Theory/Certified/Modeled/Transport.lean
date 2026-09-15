/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Modeled.Equation
import Ix.Theory.Model.ReferenceMap

/-! Simultaneous publication of source companions. Every target is already
in the checked prefix; exact mapped types and complete model equations are
validated here. Source kind and stored-rule correspondence are a separate
mandatory check before this internal result becomes declaration admission. -/

namespace Ix.Theory.Certified.Modeled

open Model Model.SetTheory

universe u v
variable {β : Type u} [DecidableEq β]

structure Companion (β : Type u) where
  header : Signature.Header β
  model : ConstRef β
  rules : List (Signature.Rule β)

def Companion.entry (companion : Companion β) : ConstantEntry β :=
  ⟨companion.header.universes, companion.header.type, none,
    companion.rules.map (fun rule => ⟨rule.lhs, rule.rhs⟩), []⟩

def lookupCompanion : List (Companion β) → ConstRef β → Option (Companion β)
  | [], _ => none
  | companion :: rest, ref =>
    if companion.header.ref = ref then some companion else lookupCompanion rest ref

theorem lookupCompanion_sound {companions : List (Companion β)} {ref : ConstRef β} {companion : Companion β}
    (h : lookupCompanion companions ref = some companion) :
    companion ∈ companions ∧ companion.header.ref = ref := by
  induction companions with
  | nil => cases h
  | cons head rest ih =>
    unfold lookupCompanion at h
    split at h
    · cases Option.some.inj h
      exact ⟨List.mem_cons_self, ‹companion.header.ref = ref›⟩
    · obtain ⟨hm, hr⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hm, hr⟩

theorem lookupCompanion_of_mem {companions : List (Companion β)}
    (unique : (companions.map (·.header.ref)).Nodup) {companion : Companion β}
    (member : companion ∈ companions) : lookupCompanion companions companion.header.ref = some companion := by
  induction companions with
  | nil => cases member
  | cons head rest ih =>
    have hu := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with rfl | hm
    · simp [lookupCompanion]
    · have hne : head.header.ref ≠ companion.header.ref := by
        intro he
        apply hu.1
        change head.header.ref ∈ rest.map (·.header.ref)
        rw [he]
        exact List.mem_map.mpr ⟨companion, hm, rfl⟩
      simp only [lookupCompanion, if_neg hne]
      exact ih hu.2 hm

def mapping (companions : List (Companion β)) (ref : ConstRef β) : ConstRef β :=
  match lookupCompanion companions ref with
  | none => ref
  | some companion => companion.model

def additions (companions : List (Companion β)) : Environment β :=
  fun ref => (lookupCompanion companions ref).map Companion.entry

def environment (entries : Environment β) (companions : List (Companion β)) : Environment β :=
  entries.overlay (additions companions)

def mapRule (companions : List (Companion β)) (rule : Signature.Rule β) : Signature.Rule β :=
  ⟨rule.universes, rule.type.mapRefs (mapping companions),
    rule.lhs.mapRefs (mapping companions), rule.rhs.mapRefs (mapping companions)⟩

structure CompanionChecked (entries : Environment β) (companions : List (Companion β))
    (companion : Companion β) : Prop where
  modelEntry : ∃ entry, entries companion.model = some entry ∧
    entry.universes = companion.header.universes ∧
    entry.type = companion.header.type.mapRefs (mapping companions)
  scope : companion.header.type.Scope companion.header.universes 0
  references : companion.header.type.ReferencesIn (environment entries companions)
  ruleScopes : ∀ rule ∈ companion.rules, rule.universes = companion.header.universes ∧
    rule.lhs.Scope companion.header.universes 0 ∧ rule.rhs.Scope companion.header.universes 0
  ruleReferences : ∀ rule ∈ companion.rules,
    rule.lhs.ReferencesIn (environment entries companions) ∧ rule.rhs.ReferencesIn (environment entries companions)
  rules : ∀ rule ∈ companion.rules, CheckedEquation.{u,v} entries (mapRule companions rule)

structure CheckedCompanions (entries : Environment β) (companions : List (Companion β)) : Prop where
  unique : (companions.map (·.header.ref)).Nodup
  fresh : ∀ companion ∈ companions, entries companion.header.ref = none
  checked : ∀ companion ∈ companions, CompanionChecked.{u,v} entries companions companion

def checkRules? (fuel : Nat) (entries : Environment β) (companions : List (Companion β)) :
    (rules : List (Signature.Rule β)) → List (EquationWitness β) →
    Option (CheckedClaim.{u} (∀ rule ∈ rules, CheckedEquation.{u,v} entries (mapRule companions rule)))
  | [], [] => some ⟨by simp⟩
  | rule :: rules, witness :: witnesses => do
    let first ← checkEquation?.{u,v} fuel entries (mapRule companions rule) witness
    let rest ← checkRules? fuel entries companions rules witnesses
    return ⟨by
      intro candidate h
      rcases List.mem_cons.mp h with rfl | h
      · exact first.down
      · exact rest.down candidate h⟩
  | _, _ => none

def checkCompanion? (fuel : Nat) (entries : Environment β) (companions : List (Companion β))
    (companion : Companion β) (witnesses : List (EquationWitness β)) :
    Option (CheckedClaim.{u} (CompanionChecked.{u,v} entries companions companion)) :=
  match he : entries companion.model with
  | none => none
  | some entry =>
    if hn : entry.universes = companion.header.universes then
      if ht : entry.type = companion.header.type.mapRefs (mapping companions) then
        if hs : companion.header.type.Scope companion.header.universes 0 then
          if hr : companion.header.type.ReferencesIn (environment entries companions) then
            if hqs : ∀ rule ∈ companion.rules, rule.universes = companion.header.universes ∧
                rule.lhs.Scope companion.header.universes 0 ∧ rule.rhs.Scope companion.header.universes 0 then
              if hqr : ∀ rule ∈ companion.rules,
                  rule.lhs.ReferencesIn (environment entries companions) ∧
                  rule.rhs.ReferencesIn (environment entries companions) then do
                let rules ← checkRules?.{u,v} fuel entries companions companion.rules witnesses
                return ⟨⟨entry, he, hn, ht⟩, hs, hr, hqs, hqr, rules.down⟩
              else none
            else none
          else none
        else none
      else none
    else none

def checkEach? (fuel : Nat) (entries : Environment β) (companions : List (Companion β)) :
    (pending : List (Companion β)) → List (List (EquationWitness β)) →
    Option (CheckedClaim.{u} (∀ companion ∈ pending, CompanionChecked.{u,v} entries companions companion))
  | [], [] => some ⟨by simp⟩
  | companion :: rest, witnesses :: remaining => do
    let first ← checkCompanion?.{u,v} fuel entries companions companion witnesses
    let others ← checkEach? fuel entries companions rest remaining
    return ⟨by
      intro candidate h
      rcases List.mem_cons.mp h with rfl | h
      · exact first.down
      · exact others.down candidate h⟩
  | _, _ => none

def checkCompanions? (fuel : Nat) (entries : Environment β) (companions : List (Companion β))
    (witnesses : List (List (EquationWitness β))) :
    Option (CheckedClaim.{u} (CheckedCompanions.{u,v} entries companions)) :=
  if hu : (companions.map (·.header.ref)).Nodup then
    if hf : ∀ companion ∈ companions, entries companion.header.ref = none then do
      let checked ← checkEach?.{u,v} fuel entries companions companions witnesses
      return ⟨hu, hf, checked.down⟩
    else none
  else none

theorem CheckedCompanions.fixed_old {entries : Environment β} {companions : List (Companion β)}
    (checked : CheckedCompanions.{u,v} entries companions) {ref : ConstRef β} {entry : ConstantEntry β}
    (old : entries ref = some entry) : mapping companions ref = ref := by
  cases hc : lookupCompanion companions ref with
  | none => simp [mapping, hc]
  | some companion =>
    obtain ⟨hm, hr⟩ := lookupCompanion_sound hc
    have hf := checked.fresh companion hm
    rw [hr, old] at hf
    cases hf

theorem CheckedCompanions.fresh_overlay {entries : Environment β} {companions : List (Companion β)}
    (checked : CheckedCompanions.{u,v} entries companions) : entries.Fresh (additions companions) := by
  intro ref entry he
  cases hc : lookupCompanion companions ref with
  | none => simp [additions, hc] at he
  | some companion =>
    obtain ⟨hm, hr⟩ := lookupCompanion_sound hc
    rw [← hr]
    exact checked.fresh companion hm

theorem CompanionChecked.closed {entries : Environment β} {companions : List (Companion β)}
    {companion : Companion β} (checked : CompanionChecked.{u,v} entries companions companion) :
    EntryClosed (environment entries companions) companion.entry := by
  constructor
  · exact checked.scope
  · intro body h; cases h
  · exact checked.references
  · intro body h; cases h
  · intro law hl
    obtain ⟨rule, hr, rfl⟩ := List.mem_map.mp hl
    exact (checked.ruleScopes rule hr).2
  · intro law hl
    obtain ⟨rule, hr, rfl⟩ := List.mem_map.mp hl
    exact checked.ruleReferences rule hr
  · intro fact hf; cases hf
  · intro fact hf; cases hf

/-- New entries may refer to one another. All are checked against the final
finite signature, while old entries retain their established closure. -/
theorem environment_wf {entries : Environment β} {companions : List (Companion β)}
    (checked : CheckedCompanions.{u,v} entries companions) (wf : entries.WF) :
    (environment entries companions).WF := by
  have hnew : ∀ ref entry, additions companions ref = some entry →
      EntryClosed (environment entries companions) entry := by
    intro ref entry he
    cases hc : lookupCompanion companions ref with
    | none => simp [additions, hc] at he
    | some companion =>
      have hm := (lookupCompanion_sound hc).1
      have heq : companion.entry = entry := by simpa [additions, hc] using he
      rw [← heq]
      exact (checked.checked companion hm).closed
  constructor
  all_goals
    intro ref entry he
    change entries.overlay (additions companions) ref = some entry at he
    unfold Environment.overlay at he
    split at he
    · cases Option.some.inj he
      first
      | exact (hnew _ _ ‹_›).typeScope
      | exact (hnew _ _ ‹_›).bodyScope
      | exact (hnew _ _ ‹_›).typeReferences
      | exact (hnew _ _ ‹_›).bodyReferences
      | exact (hnew _ _ ‹_›).equationScope
      | exact (hnew _ _ ‹_›).equationReferences
      | exact (hnew _ _ ‹_›).factScope
      | exact (hnew _ _ ‹_›).factReferences
    · first
      | exact wf.typeScope ref entry he
      | exact wf.bodyScope ref entry he
      | exact (wf.typeReferences ref entry he).overlay
      | exact fun body hb => (wf.bodyReferences ref entry he body hb).overlay
      | exact wf.equationScope ref entry he
      | exact fun law hl => ⟨(wf.equationReferences ref entry he law hl).1.overlay,
          (wf.equationReferences ref entry he law hl).2.overlay⟩
      | exact wf.factScope ref entry he
      | exact fun fact hf => (wf.factReferences ref entry he fact hf).overlay

variable {V : Type v} [SetTheory V]

def assignment (constants : Assignment β V) (companions : List (Companion β)) : Assignment β V :=
  fun ref levels => constants (mapping companions ref) levels

omit [SetTheory V] in
theorem assignment_agrees {entries : Environment β} {companions : List (Companion β)}
    (checked : CheckedCompanions.{u,v} entries companions) (constants : Assignment β V) :
    Assignment.AgreesOn entries constants (assignment constants companions) := by
  intro ref entry he levels
  simp only [assignment, checked.fixed_old he]

theorem assignment_realizes {entries : Environment β} {companions : List (Companion β)}
    (checked : CheckedCompanions.{u,v} entries companions) (wf : entries.WF)
    (constants : Assignment β V) (model : Realizes constants entries) :
    Realizes (assignment constants companions) (environment entries companions) := by
  apply (model.of_agrees wf (assignment_agrees checked constants)).overlay
  intro ref entry he
  cases hc : lookupCompanion companions ref with
  | none => simp [additions, hc] at he
  | some companion =>
    obtain ⟨hm, hr⟩ := lookupCompanion_sound hc
    have heq : companion.entry = entry := by simpa [additions, hc] using he
    rw [← heq]
    have hcomp := checked.checked companion hm
    obtain ⟨target, ht, hn, htype⟩ := hcomp.modelEntry
    constructor
    · intro levels hlevels env
      have h := model.typeValid companion.model target ht levels (hlevels.trans hn.symm) env
      rw [htype, wellDenoted_mapRefs] at h
      exact h
    · intro levels hlevels env
      have h := model.member companion.model target ht levels (hlevels.trans hn.symm) env
      rw [htype, interp_mapRefs] at h
      change constants (mapping companions ref) levels ∈ˢ
        interp (fun ref values => constants (mapping companions ref) values) levels env companion.header.type
      rw [mapping, hc]
      exact h
    · intro body hb; cases hb
    · intro body hb; cases hb
    · intro law hl levels _ env
      obtain ⟨rule, hmem, rfl⟩ := List.mem_map.mp hl
      have h := (hcomp.rules rule hmem).equality V constants model levels env
        (Context.valid_nil constants levels env)
      change interp (fun ref values => constants (mapping companions ref) values) levels env rule.lhs =
        interp (fun ref values => constants (mapping companions ref) values) levels env rule.rhs
      simpa only [mapRule, interp_mapRefs] using h
    · intro fact hf; cases hf

end Ix.Theory.Certified.Modeled
