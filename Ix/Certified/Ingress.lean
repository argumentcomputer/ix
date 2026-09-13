/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.Store

/-! Certified lazy reads from the actual Ixon environment. Only selected
addresses are visited. Materialized source caches and kernel judgment caches
cannot replace authenticated bytes. The reusable cache stores decoded data;
each hit also compares the exact current source bytes. -/

namespace Ix.Certified

open Ix.Theory Ix.Theory.Certified Ix.Theory.Model Ix.Theory.Model.SetTheory

universe v

/-- A constant window must be wholly inside its backing buffer. The cached
materialization in `LazyConstant` is intentionally not an input to this read. -/
def constantBytes? (source : Ixon.Env) (address : Address) : Option ByteArray := do
  let entry ← source.consts.get? address
  if entry.off ≤ entry.buf.size ∧ entry.len ≤ entry.buf.size - entry.off then
    some entry.rawBytes
  else none

abbrev DecodedNatural (address : Address) (bytes : ByteArray) :=
  { value : Nat //
    address.hash.size = 32 ∧ Address.blake3 bytes = address ∧
    Nat.fromBytesLE bytes.data = value ∧ ByteArray.mk value.toBytesLE = bytes }

theorem decodeObject_complete {address : Address} {bytes : ByteArray}
    (value : DecodedObject address bytes) : decodeObject? address bytes = some value := by
  rcases value with ⟨value, hs, hh, hp, hc⟩
  unfold decodeObject?
  split
  · rename_i auth
    have he : canonicalObject? address bytes auth (Ixon.runGetExact Ixon.getConstant bytes) rfl =
        canonicalObject? address bytes auth (.ok value) hp := by congr 1
    rw [he]
    simp [canonicalObject?, hc]
  · rename_i h
    exact False.elim (h ⟨hs, hh⟩)

theorem decodeNatural_complete {address : Address} {bytes : ByteArray}
    (value : DecodedNatural address bytes) : decodeNatural? address bytes = some value := by
  rcases value with ⟨value, hs, hh, hp, hc⟩
  simp [decodeNatural?, hs, hh, hp, hc]

structure CachedObject where
  address : Address
  bytes : ByteArray
  decoded : DecodedObject address bytes

structure CachedNatural where
  address : Address
  bytes : ByteArray
  decoded : DecodedNatural address bytes

/-- The public driver starts with this empty cache. Entries contain only
canonical, authenticated data; no typing, conversion or admission verdicts. -/
structure InputCache where
  objects : List CachedObject := []
  naturals : List CachedNatural := []
  hits : Nat := 0
  misses : Nat := 0

namespace InputCache

def object? (address : Address) (bytes : ByteArray) :
    List CachedObject → Option (DecodedObject address bytes)
  | [] => none
  | entry :: rest =>
    if ha : entry.address = address then
      if hb : entry.bytes = bytes then some (by simpa only [← ha, ← hb] using entry.decoded)
      else object? address bytes rest
    else object? address bytes rest

def natural? (address : Address) (bytes : ByteArray) :
    List CachedNatural → Option (DecodedNatural address bytes)
  | [] => none
  | entry :: rest =>
    if ha : entry.address = address then
      if hb : entry.bytes = bytes then some (by simpa only [← ha, ← hb] using entry.decoded)
      else natural? address bytes rest
    else natural? address bytes rest

end InputCache

structure SourceObject (source : Ixon.Env) extends CachedObject where
  fromSource : constantBytes? source address = some bytes

structure SourceNatural (source : Ixon.Env) extends CachedNatural where
  fromSource : source.getBlob? address = some bytes

abbrev Read (_source : Ixon.Env) := StateT InputCache Option

def readObject? (source : Ixon.Env) (address : Address) : Read source (SourceObject source) := fun cache =>
  match hs : constantBytes? source address with
  | none => none
  | some bytes =>
    match InputCache.object? address bytes cache.objects with
    | some decoded => some (⟨⟨address, bytes, decoded⟩, hs⟩, { cache with hits := cache.hits + 1 })
    | none => do
      let decoded ← decodeObject? address bytes
      let entry : CachedObject := ⟨address, bytes, decoded⟩
      return (⟨entry, hs⟩, { cache with objects := entry :: cache.objects, misses := cache.misses + 1 })

def readNatural? (source : Ixon.Env) (address : Address) : Read source (SourceNatural source) := fun cache =>
  match hs : source.getBlob? address with
  | none => none
  | some bytes =>
    match InputCache.natural? address bytes cache.naturals with
    | some decoded => some (⟨⟨address, bytes, decoded⟩, hs⟩, { cache with hits := cache.hits + 1 })
    | none => do
      let decoded ← decodeNatural? address bytes
      let entry : CachedNatural := ⟨address, bytes, decoded⟩
      return (⟨entry, hs⟩, { cache with naturals := entry :: cache.naturals, misses := cache.misses + 1 })

/-- An untrusted finite selection of source addresses. It must include all
source groups and raw blobs required by the independently checked witness. -/
structure InputSelection where
  objects : List Address
  naturals : List Address := []

structure SourceSnapshot (source : Ixon.Env) where
  objects : List (SourceObject source)
  naturals : List (SourceNatural source)

namespace SourceSnapshot

def blobs (snapshot : SourceSnapshot source) : ConstantBlobs :=
  snapshot.objects.map fun entry => (entry.address, entry.bytes)

def literalBlobs (snapshot : SourceSnapshot source) : ConstantBlobs :=
  snapshot.naturals.map fun entry => (entry.address, entry.bytes)

def decodedObjects (snapshot : SourceSnapshot source) : Objects :=
  snapshot.objects.map fun entry => (entry.address, entry.decoded.val)

def decodedNaturals (snapshot : SourceSnapshot source) : Naturals :=
  snapshot.naturals.map fun entry => (entry.address, entry.decoded.val)

theorem objects_decode (snapshot : SourceSnapshot source) :
    decodeObjects? snapshot.blobs = some snapshot.decodedObjects := by
  rcases snapshot with ⟨objects, naturals⟩
  simp only [blobs, decodedObjects, decodeObjects?]
  induction objects with
  | nil => rfl
  | cons entry rest ih =>
    dsimp only [bind, pure] at ih
    simp only [List.map_cons, List.mapM_cons, decodeObject_complete entry.decoded,
      bind, Option.bind_some, ih, pure]

theorem naturals_decode (snapshot : SourceSnapshot source) :
    decodeNaturals? snapshot.literalBlobs = some snapshot.decodedNaturals := by
  rcases snapshot with ⟨objects, naturals⟩
  simp only [literalBlobs, decodedNaturals, decodeNaturals?]
  induction naturals with
  | nil => rfl
  | cons entry rest ih =>
    dsimp only [bind, pure] at ih
    simp only [List.map_cons, List.mapM_cons, decodeNatural_complete entry.decoded,
      bind, Option.bind_some, ih, pure]

/-- Reusing decoded data saves hashing/parsing. Scope, source metadata,
primitive selection, dependency order and semantic validation still run. -/
def prepare? (fuel : Nat) (profile : Profile) (target : Address)
    (snapshot : SourceSnapshot source) : Option PreparedInput := do
  if !((snapshot.blobs ++ snapshot.literalBlobs).map Prod.fst).Nodup then none else do
  let signature ← readSignature? profile snapshot.decodedObjects
  let input ← readProofInput? fuel snapshot.decodedObjects target snapshot.decodedNaturals
  return ⟨signature, input⟩

theorem prepare_eq (fuel : Nat) (profile : Profile) (target : Address)
    (snapshot : SourceSnapshot source) :
    Ix.Certified.prepare? fuel profile target snapshot.blobs snapshot.literalBlobs =
      snapshot.prepare? fuel profile target := by
  simp only [Ix.Certified.prepare?, prepare?, snapshot.objects_decode, snapshot.naturals_decode,
    bind, Option.bind_some]

/-- Each byte string consumed by the cached checker comes from the current
source environment, even when that address occurred in an earlier request. -/
theorem objects_from_source (snapshot : SourceSnapshot source) {address : Address} {bytes : ByteArray}
    (h : (address, bytes) ∈ snapshot.blobs) : constantBytes? source address = some bytes := by
  obtain ⟨entry, _, he⟩ := List.mem_map.mp h
  cases he
  exact entry.fromSource

theorem naturals_from_source (snapshot : SourceSnapshot source) {address : Address} {bytes : ByteArray}
    (h : (address, bytes) ∈ snapshot.literalBlobs) : source.getBlob? address = some bytes := by
  obtain ⟨entry, _, he⟩ := List.mem_map.mp h
  cases he
  exact entry.fromSource

end SourceSnapshot

/-- Failure returns no partially loaded snapshot or semantic verdict. -/
def readSnapshot? (fuel : Nat) (source : Ixon.Env) (selection : InputSelection) :
    Read source (SourceSnapshot source) := do
  if selection.objects.length + selection.naturals.length > fuel then failure else do
  let objects ← selection.objects.mapM (readObject? source)
  let naturals ← selection.naturals.mapM (readNatural? source)
  return ⟨objects, naturals⟩

/-- A receipt is produced only after complete checking against the snapshot.
All semantic fields are computed by the validator; they are not input data. -/
structure SourceReceipt (source : Ixon.Env) (fuel : Nat) (profile : Profile) (target : Address)
    (witness : ProofWitness Address) where
  snapshot : SourceSnapshot source
  prepared : PreparedInput
  preparation : snapshot.prepare? fuel profile target = some prepared
  proof : CheckedProof.{0,v} prepared.signature prepared.input
  checked : checkProofCertified fuel prepared.signature prepared.input witness = some proof

def checkSource? (fuel : Nat) (source : Ixon.Env) (profile : Profile) (target : Address)
    (selection : InputSelection) (witness : ProofWitness Address) :
    Read source (SourceReceipt.{v} source fuel profile target witness) := do
  let snapshot ← readSnapshot? fuel source selection
  match hp : snapshot.prepare? fuel profile target with
  | none => failure
  | some prepared =>
    match hc : checkProofCertified fuel prepared.signature prepared.input witness with
    | none => failure
    | some proof => return ⟨snapshot, prepared, hp, proof, hc⟩

namespace SourceReceipt

theorem serialized (receipt : SourceReceipt.{v} source fuel profile target witness) :
    acceptsSerialized.{v} fuel profile target receipt.snapshot.blobs witness receipt.snapshot.literalBlobs = true := by
  have hp := receipt.snapshot.prepare_eq fuel profile target
  rw [receipt.preparation] at hp
  simp only [acceptsSerialized, hp, acceptsCertified, receipt.checked, Option.isSome_some]

theorem has_model (receipt : SourceReceipt.{v} source fuel profile target witness)
    (V : Type v) [SetTheory V] (levels : List Nat) (env : Nat → V) :
    ∃ constants : Assignment Address V,
      receipt.prepared.signature.Compatible receipt.proof.environment.entries constants ∧
      WellDenoted constants levels env receipt.proof.proof.val ∧
      WellDenoted constants levels env receipt.proof.proposition.val ∧
      interp constants levels env receipt.proof.proof.val ∈ˢ
        interp constants levels env receipt.proof.proposition.val := by
  have ha : acceptsCertified.{0,v} fuel receipt.prepared.signature receipt.prepared.input witness = true := by
    simp only [acceptsCertified, receipt.checked, Option.isSome_some]
  obtain ⟨result, hr, constants, hM, hW, hP, hm⟩ := accepted_has_model ha V levels env
  have he : result = receipt.proof := Option.some.inj (hr.symm.trans receipt.checked)
  subst result
  exact ⟨constants, hM, hW, hP, hm⟩

end SourceReceipt


namespace SourceSnapshot

def prepareStore? (fuel : Nat) (profile : Profile) (subjects : List Address)
    (snapshot : SourceSnapshot source) : Option PreparedStore := do
  if !((snapshot.blobs ++ snapshot.literalBlobs).map Prod.fst).Nodup then none else
  prepareStoreObjects? fuel profile subjects snapshot.decodedObjects snapshot.decodedNaturals

theorem prepareStore_eq (fuel : Nat) (profile : Profile) (subjects : List Address)
    (snapshot : SourceSnapshot source) :
    Ix.Certified.prepareStore? fuel profile subjects snapshot.blobs snapshot.literalBlobs =
      snapshot.prepareStore? fuel profile subjects := by
  simp only [Ix.Certified.prepareStore?, prepareStore?, snapshot.objects_decode, snapshot.naturals_decode,
    bind, Option.bind_some]

end SourceSnapshot

structure StoreReceipt (source : Ixon.Env) (fuel : Nat) (profile : Profile) (subjects : List Address)
    (witness : List (DeclarationWitness Address)) where
  snapshot : SourceSnapshot source
  prepared : PreparedStore
  preparation : snapshot.prepareStore? fuel profile subjects = some prepared
  result : CheckedStore.{0,v} prepared.signature prepared.store prepared.targets
  checked : checkStoreCertified fuel prepared.signature prepared.store prepared.targets witness = some result

def checkSourceStore? (fuel : Nat) (source : Ixon.Env) (profile : Profile) (subjects : List Address)
    (selection : InputSelection) (witness : List (DeclarationWitness Address)) :
    Read source (StoreReceipt.{v} source fuel profile subjects witness) := do
  let snapshot ← readSnapshot? fuel source selection
  match hp : snapshot.prepareStore? fuel profile subjects with
  | none => failure
  | some prepared =>
    match hc : checkStoreCertified fuel prepared.signature prepared.store prepared.targets witness with
    | none => failure
    | some result => return ⟨snapshot, prepared, hp, result, hc⟩

namespace StoreReceipt

theorem serialized (receipt : StoreReceipt.{v} source fuel profile subjects witness) :
    acceptsSerializedStore.{v} fuel profile subjects receipt.snapshot.blobs witness receipt.snapshot.literalBlobs = true := by
  have hp := receipt.snapshot.prepareStore_eq fuel profile subjects
  rw [receipt.preparation] at hp
  simp only [acceptsSerializedStore, hp, acceptsStoreCertified, receipt.checked, Option.isSome_some]

theorem has_model (receipt : StoreReceipt.{v} source fuel profile subjects witness)
    (V : Type v) [SetTheory V] :
    ∃ constants : Assignment Address V,
      receipt.prepared.signature.Compatible receipt.result.environment.entries constants ∧
      ∀ r ∈ receipt.prepared.targets, ∃ entry, receipt.result.environment.entries r = some entry ∧
        EntrySource receipt.prepared.signature receipt.prepared.store r entry ∧
        ∀ levels, levels.length = entry.universes → ∀ env : Nat → V,
          WellDenoted constants levels env entry.type ∧
          constants r levels ∈ˢ interp constants levels env entry.type := by
  have ha : acceptsStoreCertified.{0,v} fuel receipt.prepared.signature receipt.prepared.store
      receipt.prepared.targets witness = true := by
    simp only [acceptsStoreCertified, receipt.checked, Option.isSome_some]
  obtain ⟨result, hr, hM⟩ := accepted_store_has_model ha V
  have he : result = receipt.result := Option.some.inj (hr.symm.trans receipt.checked)
  subst result
  exact hM

end StoreReceipt

end Ix.Certified
