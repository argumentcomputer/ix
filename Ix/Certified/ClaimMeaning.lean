/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.ClaimCheck

namespace Ix.Certified

open Ix.Theory Ix.Theory.Certified Ix.Theory.Model Ix.Theory.Model.SetTheory

universe v
variable {source : Ixon.Env} {snapshot : SourceSnapshot source}
  {fuel : Nat} {envelope : Envelope} {witness : LogicalWitness}

theorem OptionalTreeOpening.none_leaves (opening : OptionalTreeOpening fuel none bytes) :
    opening.leaves = [] := by
  cases bytes with
  | none => exact opening.evidence
  | some => exact False.elim opening.evidence

theorem OptionalTreeOpening.closed_leaves (opening : OptionalTreeOpening fuel root bytes)
    (closed : root = none) : opening.leaves = [] := by
  subst root
  exact opening.none_leaves

theorem LogicalChecking.target_entry
    (checked : LogicalChecking.{v} snapshot fuel envelope witness)
    {ref : ConstRef Address} (hr : ref ∈ checked.subjects) :
    ∃ entry, checked.batch.receipt.checked.result.entries ref = some entry ∧
      EntrySource checked.signature checked.store ref entry := by
  have validated := (checked.signature.validate_iff checked.store).mp checked.batch.receipt.frontier.validated
  by_cases hF : ref = checked.signature.falseType
  · subst ref
    exact ⟨PrimitiveSignature.falseEntry, checked.batch.receipt.checked.result.present.1,
      Or.inl ⟨rfl, rfl, validated.1⟩⟩
  · by_cases hE : ref = checked.signature.falseElim
    · subst ref
      exact ⟨checked.signature.falseElimEntry, checked.batch.receipt.checked.result.present.2,
        Or.inr (Or.inl ⟨rfl, rfl, validated.2⟩)⟩
    · have owned := (checked.exactSubjects ref).mpr (mem_ownedReferences.mpr ⟨hr, hF, hE⟩)
      have hp := checked.batch.receipt.present ref owned
      obtain ⟨entry, he⟩ := Option.isSome_iff_exists.mp hp
      refine ⟨entry, he, ?_⟩
      rcases checked.batch.receipt.checked.source ref entry he with old | new
      · rw [checked.batch.receipt.fresh ref owned] at old
        cases old
      · exact new

theorem LogicalChecking.original_subject
    (checked : LogicalChecking.{v} snapshot fuel envelope witness)
    {ref : ConstRef Address} (hr : ref ∈ checked.subjects) :
    ∃ entry, checked.batch.receipt.checked.result.entries ref = some entry ∧
      SourceDeclarationReading source snapshot.decodedObjects snapshot.decodedNaturals ref entry := by
  obtain ⟨entry, he, hs⟩ := checked.target_entry hr
  exact ⟨entry, he, snapshot.declaration_reading checked.storeReading hs.header⟩

theorem LogicalChecking.original_frontier
    (checked : LogicalChecking.{v} snapshot fuel envelope witness)
    {ref : ConstRef Address} (hr : ref ∈ checked.frontierRefs) :
    ∃ entry, checked.batch.receipt.frontier.interface.entries ref = some entry ∧
      SourceDeclarationReading source snapshot.decodedObjects snapshot.decodedNaturals ref entry := by
  have hm := (checked.exactFrontier ref).mpr hr
  obtain ⟨header, hh, rfl⟩ := List.mem_map.mp hm
  exact ⟨header.entry, checked.batch.receipt.frontier.formed.lookup hh,
    snapshot.declaration_reading checked.storeReading (checked.batch.receipt.frontier.header_source hh)⟩

/-- The claim's public axiom tree contains every use, including uses retained
from leaves. Each address resolves to an exactly realized source schema. -/
theorem LogicalChecking.logical_policy
    (checked : LogicalChecking.{v} snapshot fuel envelope witness)
    {ref : ConstRef Address} (hr : ref ∈ checked.axiomRefs) :
    ∃ entry, Standard.EntrySource checked.store ref entry ∨ Quotient.EntrySource checked.store ref entry :=
  checked.batch.logicalUses_authorized ((checked.exactAxioms ref).mpr hr)

theorem LogicalChecking.closed_frontier
    (checked : LogicalChecking.{v} snapshot fuel envelope witness)
    (closed : claimFrontier envelope.claim = none) : checked.batch.receipt.frontier.refs = [] := by
  have hl : checked.frontier.leaves = [] := by
    exact checked.frontier.closed_leaves closed
  have hr : checked.frontierRefs = [] := by
    have h := checked.frontierReading
    rw [hl] at h
    simpa using h.symm
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro ref hm
  have h := (checked.exactFrontier ref).mp hm
  rw [hr] at h
  cases h

/-- Conditional soundness of every original source member or constructor in
the exact committed subject set. All declared frontier values are preserved
at every universe instance while the shared interpretation is extended. -/
theorem LogicalReceipt.subject_meaning
    (receipt : LogicalReceipt.{v} source fuel envelope witness)
    (V : Type v) [SetTheory V] (constants : Assignment Address V)
    (hM : receipt.checked.signature.Compatible receipt.checked.batch.receipt.frontier.interface.entries constants) :
    ∃ constants' : Assignment Address V,
      receipt.checked.signature.Compatible receipt.checked.batch.receipt.checked.result.entries constants' ∧
      Assignment.AgreesOn receipt.checked.batch.receipt.frontier.interface.entries constants constants' ∧
      ∀ ref ∈ receipt.checked.subjects, ∃ entry,
        SourceDeclarationReading source receipt.snapshot.decodedObjects receipt.snapshot.decodedNaturals ref entry ∧
        ∀ levels, levels.length = entry.universes → ∀ env,
          WellDenoted constants' levels env entry.type ∧
          constants' ref levels ∈ˢ interp constants' levels env entry.type := by
  obtain ⟨constants', hm, ha⟩ := receipt.checked.batch.receipt.checked.extension.models V constants hM
  refine ⟨constants', hm, ha, ?_⟩
  intro ref hr
  obtain ⟨entry, he, hs⟩ := receipt.checked.original_subject hr
  refine ⟨entry, hs, ?_⟩
  intro levels hl env
  exact ⟨hm.realizes.typeValid ref entry he levels hl env,
    hm.realizes.member ref entry he levels hl env⟩

/-- A public claim with no structural frontier constructs its model. This
does not assert that its separately recorded logical-axiom set is empty. -/
theorem LogicalReceipt.closed_subject_meaning
    (receipt : LogicalReceipt.{v} source fuel envelope witness)
    (closed : claimFrontier envelope.claim = none) (V : Type v) [SetTheory V] :
    ∃ constants : Assignment Address V,
      receipt.checked.signature.Compatible receipt.checked.batch.receipt.checked.result.entries constants ∧
      ∀ ref ∈ receipt.checked.subjects, ∃ entry,
        SourceDeclarationReading source receipt.snapshot.decodedObjects receipt.snapshot.decodedNaturals ref entry ∧
        ∀ levels, levels.length = entry.universes → ∀ env,
          WellDenoted constants levels env entry.type ∧
          constants ref levels ∈ˢ interp constants levels env entry.type := by
  have hf := receipt.checked.closed_frontier closed
  have initial : receipt.checked.signature.Compatible receipt.checked.batch.receipt.frontier.interface.entries
      (receipt.checked.signature.assignment (V := V)) := by
    rw [receipt.checked.batch.receipt.frontier.empty_interface hf]
    exact receipt.checked.signature.compatible_assignment
  obtain ⟨constants, hm, _, subjects⟩ := receipt.subject_meaning V receipt.checked.signature.assignment initial
  exact ⟨constants, hm, subjects⟩

theorem LogicalReceipt.no_False
    (receipt : LogicalReceipt.{v} source fuel envelope witness)
    (closed : claimFrontier envelope.claim = none) {ref : ConstRef Address}
    (subject : ref ∈ receipt.checked.subjects)
    (type : receipt.checked.store.type ref = some receipt.checked.signature.falseExpr)
    (V : Type v) [SetTheory V] : False := by
  have hf := receipt.checked.closed_frontier closed
  obtain ⟨constants, hm, _⟩ := receipt.checked.batch.closed_has_model hf V
  obtain ⟨entry, he, hs⟩ := receipt.checked.target_entry subject
  have hc : entry.type = .const receipt.checked.signature.falseType [] :=
    AExpr.eq_const_of_erase_eq (Option.some.inj (hs.header.type.symm.trans type))
  have hmem := hm.realizes.member ref entry he (List.replicate entry.universes 0) (by simp) (fun _ => empty)
  rw [hc] at hmem
  simp only [interp, List.map_nil, hm.falseValue] at hmem
  exact not_mem_empty _ hmem

end Ix.Certified
