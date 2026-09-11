/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.Bytes
import Ix.Theory.Certified.Store

namespace Ix.Certified

open Ix.Theory Ix.Theory.Certified Ix.Theory.Model Ix.Theory.Model.SetTheory

universe v

/-- A block subject requests every member and constructor. A projection
subject must resolve to its actual matching source kind and position. -/
def subjectReferences? (objects : Objects) (subject : Address) : Option (List (ConstRef Address)) := do
  let source ← lookup objects subject
  match source.info with
  | .muts members =>
    if members.isEmpty then none else
    return members.toList.zipIdx.flatMap fun (member, index) =>
      .member subject index :: match member with
        | .indc family => (List.range family.ctors.size).map (.ctor subject index ·)
        | _ => []
  | _ => return [← resolveReference? objects subject]

structure PreparedStore where
  signature : PrimitiveSignature Address
  store : Store Address
  targets : List (ConstRef Address)

def prepareStoreObjects? (fuel : Nat) (profile : Profile) (subjects : List Address)
    (objects : Objects) (naturals : Naturals) : Option PreparedStore := do
  let signature ← readSignature? profile objects
  let store ← readStore? fuel objects naturals
  let targets ← subjects.flatMapM (subjectReferences? objects)
  if targets.length > fuel then none else return ⟨signature, store, targets⟩

def prepareStore? (fuel : Nat) (profile : Profile) (subjects : List Address)
    (blobs : ConstantBlobs) (literalBlobs : ConstantBlobs := []) : Option PreparedStore := do
  if !((blobs ++ literalBlobs).map Prod.fst).Nodup then none else do
  let naturals ← decodeNaturals? literalBlobs
  let objects ← decodeObjects? blobs
  prepareStoreObjects? fuel profile subjects objects naturals

def acceptsSerializedStore (fuel : Nat) (profile : Profile) (subjects : List Address)
    (blobs : ConstantBlobs) (witness : List (DeclarationWitness Address))
    (literalBlobs : ConstantBlobs := []) : Bool :=
  match prepareStore? fuel profile subjects blobs literalBlobs with
  | none => false
  | some prepared => acceptsStoreCertified.{0,v} fuel prepared.signature prepared.store prepared.targets witness

theorem accepted_serialized_store_has_model {fuel : Nat} {profile : Profile} {subjects : List Address}
    {blobs literalBlobs : ConstantBlobs} {witness : List (DeclarationWitness Address)}
    (h : acceptsSerializedStore.{v} fuel profile subjects blobs witness literalBlobs = true)
    (V : Type v) [SetTheory V] :
    ∃ prepared, prepareStore? fuel profile subjects blobs literalBlobs = some prepared ∧
      ∃ result : CheckedStore.{0,v} prepared.signature prepared.store prepared.targets,
        checkStoreCertified fuel prepared.signature prepared.store prepared.targets witness = some result ∧
        ∃ constants : Assignment Address V,
          prepared.signature.Compatible result.environment.entries constants ∧
          ∀ r ∈ prepared.targets, ∃ entry, result.environment.entries r = some entry ∧
            EntrySource prepared.signature prepared.store r entry ∧
            ∀ levels, levels.length = entry.universes → ∀ env : Nat → V,
              WellDenoted constants levels env entry.type ∧
              constants r levels ∈ˢ interp constants levels env entry.type := by
  unfold acceptsSerializedStore at h
  cases hp : prepareStore? fuel profile subjects blobs literalBlobs with
  | none => simp [hp] at h
  | some prepared =>
    exact ⟨prepared, rfl, accepted_store_has_model (by simpa only [hp] using h) V⟩

end Ix.Certified
