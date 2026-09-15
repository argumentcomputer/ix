/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Frontier

namespace Ix.Theory.Certified

open Model

universe u v
variable {β : Type u} [DecidableEq β]

/-- Enumerate source members, retaining exact block and member positions. -/
def sourceMembers (store : Store β) : List (ConstRef β) :=
  store.dom.flatMap fun block => match store.blocks block with
    | none => []
    | some contents => (List.range contents.members.length).map (.member block ·)

omit [DecidableEq β] in
theorem lookup_mem_sourceMembers {store : Store β} {ref : ConstRef β} {source : Const β}
    (h : store.lookup ref = some source) : ref ∈ sourceMembers store := by
  cases ref with
  | ctor => cases h
  | member block index =>
    cases hb : store.blocks block with
    | none => simp [Store.lookup, hb] at h
    | some contents =>
      have hm : contents.members[index]? = some source := by simpa [Store.lookup, hb] using h
      have hi : index < contents.members.length := (List.getElem?_eq_some_iff.mp hm).choose
      apply List.mem_flatMap.mpr
      refine ⟨block, (store.mem_dom block).mp (by simp [hb]), ?_⟩
      simp only [hb]
      exact List.mem_map.mpr ⟨index, List.mem_range.mpr hi, rfl⟩

def isLogicalAxiom (store : Store β) (ref : ConstRef β) : Bool :=
  match store.lookup ref with
  | some (.axiom ..) => true
  | _ => false

/-- The manifest records all admitted source axioms, even unused ones. It is
computed from source kinds and the actual checked environment; it never
subtracts checked subjects or trusts a prover's declaration of axiom use. -/
def logicalAxioms (store : Store β) (entries : Environment β) : List (ConstRef β) :=
  (sourceMembers store).filter fun ref => isLogicalAxiom store ref && (entries ref).isSome

omit [DecidableEq β] in
theorem mem_logicalAxioms {store : Store β} {entries : Environment β} {ref : ConstRef β} :
    ref ∈ logicalAxioms store entries ↔
      (∃ n type safety, store.lookup ref = some (.axiom n type safety)) ∧
      ∃ entry, entries ref = some entry := by
  constructor
  · intro h
    obtain ⟨_, h⟩ := List.mem_filter.mp h
    have hh : isLogicalAxiom store ref = true ∧ (entries ref).isSome = true := by simpa using h
    obtain ⟨ha, he⟩ := hh
    have hs : ∃ n type safety, store.lookup ref = some (.axiom n type safety) := by
      unfold isLogicalAxiom at ha
      cases hl : store.lookup ref with
      | none => simp [hl] at ha
      | some source => cases source <;> simp_all
    exact ⟨hs, Option.isSome_iff_exists.mp he⟩
  · rintro ⟨⟨n, type, safety, hs⟩, entry, he⟩
    exact List.mem_filter.mpr ⟨lookup_mem_sourceMembers hs, by simp [isLogicalAxiom, hs, he]⟩

omit [DecidableEq β] in
theorem logicalAxioms_monotone {signature : PrimitiveSignature β} {store : Store β}
    {a b : Environment β} (h : Extends.{u,v} signature a b) {ref : ConstRef β}
    (hr : ref ∈ logicalAxioms store a) : ref ∈ logicalAxioms store b := by
  obtain ⟨source, entry, he⟩ := mem_logicalAxioms.mp hr
  exact mem_logicalAxioms.mpr ⟨source, entry, h.lookup ref entry he⟩

theorem CheckedFrontier.no_axioms {signature : PrimitiveSignature β} {store : Store β}
    (frontier : CheckedFrontier.{u,v} signature store) {ref : ConstRef β} {entry : ConstantEntry β}
    {n : Nat} {type : VExpr β} {safety : Safety}
    (hs : store.lookup ref = some (.axiom n type safety)) :
    frontier.interface.entries ref ≠ some entry := by
  intro hr
  rcases Signature.environment_source hr with old | ⟨header, hh, rfl, _⟩
  · have hv := (signature.validate_iff store).mp frontier.validated
    unfold PrimitiveSignature.environment at old
    split at old
    · subst ref; rw [hv.1] at hs; cases hs
    · split at old
      · subst ref; rw [hv.2] at hs; cases hs
      · cases old
  · obtain ⟨reading, _, rfl⟩ := List.mem_map.mp hh
    have ha := reading.allowed
    simp [deferredSource, hs] at ha

omit [DecidableEq β] in
/-- Every object axiom in an admitted interface is one of the exactly realized
standard schemas or quotient soundness, with its original source preserved. -/
theorem EntrySource.axiom_policy {signature : PrimitiveSignature β} {store : Store β}
    {ref : ConstRef β} {entry : ConstantEntry β} {n : Nat} {type : VExpr β} {safety : Safety}
    (source : EntrySource signature store ref entry)
    (hs : store.lookup ref = some (.axiom n type safety)) :
    Standard.EntrySource store ref entry ∨ Quotient.EntrySource store ref entry := by
  rcases source with ⟨_, _, he⟩ | ⟨_, _, he⟩ | ⟨_, _, _, _, _, he⟩ | h | h | h | h | h | h
  · rw [he] at hs; cases hs
  · rw [he] at hs; cases hs
  · rw [he] at hs; cases hs
  · rcases h with ⟨shape, block, recursor, mode, hb, hr, h⟩
    rcases h with ⟨rfl, _⟩ | ⟨index, ctor, _, rfl, _⟩ | ⟨rfl, _⟩
    · simp [Store.lookup, hb, Ordinary.Shape.source] at hs
    · cases hs
    · rcases hr with hr | ⟨_, hr⟩ <;>
        simp [Store.lookup, hr, Ordinary.Shape.recursorSource] at hs
  · exact Or.inl h
  · exact Or.inr h
  · rcases h with ⟨description, block, recursor, mode, hb, _, rfl, _⟩
    simp [Store.lookup, hb, Ordinary.Shape.source] at hs
  · rcases h with ⟨_, block, recursor, mode, hb, _, rfl, _⟩
    simp [Store.lookup, hb, Ordinary.Shape.source] at hs
  · exact False.elim (h.not_axiom hs)

theorem ConditionalStore.logical_axioms_authorized {signature : PrimitiveSignature β}
    {store : Store β} {subjects : List (ConstRef β)}
    (receipt : ConditionalStore.{u,v} signature store subjects) {ref : ConstRef β}
    (h : ref ∈ logicalAxioms store receipt.checked.result.entries) :
    ∃ entry, receipt.checked.result.entries ref = some entry ∧
      (Standard.EntrySource store ref entry ∨ Quotient.EntrySource store ref entry) := by
  obtain ⟨⟨n, type, safety, hs⟩, entry, he⟩ := mem_logicalAxioms.mp h
  refine ⟨entry, he, ?_⟩
  rcases receipt.checked.source ref entry he with old | new
  · exact False.elim (receipt.frontier.no_axioms hs old)
  · exact new.axiom_policy hs

end Ix.Theory.Certified
