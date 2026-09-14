/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.SourceStore
import Ix.Kernel.Certified

/-! Authenticated source-statement meaning for successful certified source
runs. The original bytes, raw type and table-resolved reading occur together
in the contract; semantic equality never substitutes for byte identity. -/

namespace Ix.Certified

open Ix.Theory Ix.Theory.Certified Ix.Theory.Model Ix.Theory.Model.SetTheory

universe v

def ObjectBytes (source : Ixon.Env) (address : Address) (bytes : ByteArray) (value : Ixon.Constant) : Prop :=
  constantBytes? source address = some bytes ∧ address.hash.size = 32 ∧
    Address.blake3 bytes = address ∧ Ixon.runGetExact Ixon.getConstant bytes = .ok value ∧
    Ixon.serConstant value = bytes

def NaturalBytes (source : Ixon.Env) (address : Address) (bytes : ByteArray) (value : Nat) : Prop :=
  source.getBlob? address = some bytes ∧ address.hash.size = 32 ∧
    Address.blake3 bytes = address ∧ Nat.fromBytesLE bytes.data = value ∧
    ByteArray.mk value.toBytesLE = bytes

theorem SourceSnapshot.object_bytes (snapshot : SourceSnapshot source) {address : Address} {value : Ixon.Constant}
    (h : lookup snapshot.decodedObjects address = some value) : ∃ bytes, ObjectBytes source address bytes value := by
  obtain ⟨entry, _, he⟩ := List.mem_map.mp (lookup_mem h)
  rcases Prod.mk.inj he with ⟨rfl, rfl⟩
  exact ⟨entry.bytes, entry.fromSource, entry.decoded.property⟩

theorem SourceSnapshot.natural_bytes (snapshot : SourceSnapshot source) {address : Address} {value : Nat}
    (h : lookup snapshot.decodedNaturals address = some value) : ∃ bytes, NaturalBytes source address bytes value := by
  obtain ⟨entry, _, he⟩ := List.mem_map.mp (lookup_mem h)
  rcases Prod.mk.inj he with ⟨rfl, rfl⟩
  exact ⟨entry.bytes, entry.fromSource, entry.decoded.property⟩

def SignatureReading (profile : Profile) (objects : Objects) (signature : PrimitiveSignature Address) : Prop :=
  ReferenceMeaning objects profile.falseType signature.falseType ∧
  ReferenceMeaning objects profile.falseElim signature.falseElim ∧
  match profile.natType, signature.natType with
  | none, none => True
  | some address, some ref => ReferenceMeaning objects address ref
  | _, _ => False

theorem readSignature_sound {profile : Profile} {objects : Objects} {signature : PrimitiveSignature Address}
    (h : readSignature? profile objects = some signature) : SignatureReading profile objects signature := by
  rcases profile with ⟨falseAddress, elimAddress, natural⟩
  cases natural with
  | none =>
    simp only [readSignature?, bind, Option.bind_some, Option.bind_eq_some_iff] at h
    obtain ⟨falseType, hF, falseElim, hE, h⟩ := h
    split at h
    · cases Option.some.inj h
      exact ⟨resolveReference_iff.mp hF, resolveReference_iff.mp hE, trivial⟩
    · cases h
  | some address =>
    simp only [readSignature?, bind, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨falseType, hF, falseElim, hE, _, ⟨ref, hn, rfl⟩, h⟩ := h
    split at h
    · cases Option.some.inj h
      exact ⟨resolveReference_iff.mp hF, resolveReference_iff.mp hE, resolveReference_iff.mp hn⟩
    · cases h

theorem SourceSnapshot.prepareStore_parts {source : Ixon.Env} (snapshot : SourceSnapshot source)
    {fuel : Nat} {profile : Profile} {subjects : List Address} {prepared : PreparedStore}
    (h : snapshot.prepareStore? fuel profile subjects = some prepared) :
    readSignature? profile snapshot.decodedObjects = some prepared.signature ∧
    readStore? fuel snapshot.decodedObjects snapshot.decodedNaturals = some prepared.store ∧
    subjects.flatMapM (subjectReferences? snapshot.decodedObjects) = some prepared.targets := by
  unfold SourceSnapshot.prepareStore? at h
  split at h
  · cases h
  · simp only [prepareStoreObjects?, bind, Option.bind_eq_some_iff] at h
    obtain ⟨signature, hs, store, hstore, targets, ht, h⟩ := h
    split at h
    · cases h
    · cases Option.some.inj h
      exact ⟨hs, hstore, ht⟩

theorem SourceSnapshot.prepare_parts {source : Ixon.Env} (snapshot : SourceSnapshot source)
    {fuel : Nat} {profile : Profile} {target : Address} {prepared : PreparedInput}
    (h : snapshot.prepare? fuel profile target = some prepared) :
    readSignature? profile snapshot.decodedObjects = some prepared.signature ∧
    readProofInput? fuel snapshot.decodedObjects target snapshot.decodedNaturals = some prepared.input := by
  unfold SourceSnapshot.prepare? at h
  split at h
  · cases h
  · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨signature, hs, input, hi, rfl⟩ := h
    exact ⟨hs, hi⟩

def SourceDeclarationReading (source : Ixon.Env) (objects : Objects) (naturals : Naturals)
    (ref : ConstRef Address) (entry : ConstantEntry Address) : Prop :=
  ∃ bytes declaration rawType,
    ObjectBytes source ref.block bytes declaration ∧ lookup objects ref.block = some declaration ∧
    rawHeader? declaration ref = some (entry.universes, rawType) ∧
    ExprReading objects naturals ref.block declaration rawType entry.type.erase

theorem SourceSnapshot.declaration_reading {source : Ixon.Env} (snapshot : SourceSnapshot source)
    {fuel : Nat} {store : Store Address} {ref : ConstRef Address} {entry : ConstantEntry Address}
    (h : readStore? fuel snapshot.decodedObjects snapshot.decodedNaturals = some store)
    (hh : SourceHeader store ref entry) :
    SourceDeclarationReading source snapshot.decodedObjects snapshot.decodedNaturals ref entry := by
  obtain ⟨declaration, rawType, hs, ht, hr⟩ := readStore_sourceHeader h hh
  obtain ⟨bytes, hb⟩ := snapshot.object_bytes hs
  exact ⟨bytes, declaration, rawType, hb, hs, ht, hr⟩

/-- Every original requested source declaration is realized in every compatible
model, with its complete canonical bytes and its original raw type retained. -/
theorem StoreReceipt.subject_meaning
    (receipt : StoreReceipt.{v} source fuel profile subjects witness)
    {ref : ConstRef Address} (hr : ref ∈ receipt.prepared.targets) :
    ∃ entry, receipt.result.environment.entries ref = some entry ∧
      SourceDeclarationReading source receipt.snapshot.decodedObjects receipt.snapshot.decodedNaturals ref entry ∧
      ∀ (V : Type v) [SetTheory V] (constants : Assignment Address V),
        receipt.prepared.signature.Compatible receipt.result.environment.entries constants →
        ∀ levels, levels.length = entry.universes → ∀ env,
          WellDenoted constants levels env entry.type ∧
          constants ref levels ∈ˢ interp constants levels env entry.type := by
  obtain ⟨entry, he, hh, hm⟩ := receipt.result.subject_sound hr
  exact ⟨entry, he, receipt.snapshot.declaration_reading
    (receipt.snapshot.prepareStore_parts receipt.preparation).2.1 hh, hm⟩

theorem readProofInput_parts {fuel : Nat} {objects : Objects} {naturals : Naturals} {target : Address}
    {input : ProofInput Address} (h : readProofInput? fuel objects target naturals = some input) :
    readStore? fuel objects naturals = some input.store ∧
    ∃ ref declaration, resolveReference? objects target = some ref ∧
      input.store.lookup ref = some declaration ∧ input.universes = declaration.uvars ∧
      input.proof = .const ref (VLevel.params input.universes) ∧ input.proposition = declaration.type := by
  unfold readProofInput? at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨store, hs, ref, hr, declaration, hd, h⟩ := h
  split at h
  · cases Option.some.inj h
    exact ⟨hs, ref, declaration, hr, hd, rfl, rfl, rfl⟩
  · cases h

theorem SourceReceipt.target_entry
    (receipt : SourceReceipt.{v} source fuel profile target witness) :
    ∃ ref entry, ReferenceMeaning receipt.snapshot.decodedObjects target ref ∧
      receipt.proof.environment.entries ref = some entry ∧
      SourceDeclarationReading source receipt.snapshot.decodedObjects receipt.snapshot.decodedNaturals ref entry ∧
      receipt.prepared.input.universes = entry.universes ∧
      receipt.prepared.input.proposition = entry.type.erase := by
  have hp := receipt.snapshot.prepare_parts receipt.preparation
  obtain ⟨hs, ref, declaration, hr, hd, hu, he, ht⟩ := readProofInput_parts hp.2
  have hproof : receipt.proof.proof.val = .const ref (VLevel.params receipt.prepared.input.universes) :=
    AExpr.eq_const_of_erase_eq (receipt.proof.proof.property.1.trans he)
  have hmem : (receipt.proof.environment.entries ref).isSome = true := by
    simpa [hproof, AExpr.ReferencesIn, AExpr.references] using receipt.proof.proofReferences
  cases hf : receipt.proof.environment.entries ref with
  | none => simp [hf] at hmem
  | some entry =>
    have hh := receipt.proof.environment.sourceHeader hf
    have hu' : declaration.uvars = entry.universes := by simpa [Store.uvars, hd] using hh.universes
    have ht' : declaration.type = entry.type.erase := by simpa [Store.type, hd] using hh.type
    exact ⟨ref, entry, resolveReference_iff.mp hr, hf,
      receipt.snapshot.declaration_reading hs hh, hu.trans hu', ht.trans ht'⟩

/-- This is the original serialized proposition's type field, with its exact
source bytes and a validated reading of the original tables. The proposition
is inhabited in every compatible interpretation, not just a chosen model. -/
theorem SourceReceipt.proposition_meaning
    (receipt : SourceReceipt.{v} source fuel profile target witness) :
    SignatureReading profile receipt.snapshot.decodedObjects receipt.prepared.signature ∧
    ∃ ref bytes declaration rawType,
      ReferenceMeaning receipt.snapshot.decodedObjects target ref ∧
      ObjectBytes source ref.block bytes declaration ∧
      rawHeader? declaration ref = some (receipt.prepared.input.universes, rawType) ∧
      ExprReading receipt.snapshot.decodedObjects receipt.snapshot.decodedNaturals ref.block declaration
        rawType receipt.proof.proposition.val.erase ∧
      ∀ (V : Type v) [SetTheory V] (constants : Assignment Address V),
        receipt.prepared.signature.Compatible receipt.proof.environment.entries constants → ∀ levels env,
          WellDenoted constants levels env receipt.proof.proposition.val ∧
          interp constants levels env receipt.proof.proposition.val ∈ˢ univ 0 ∧
          interp constants levels env receipt.proof.proof.val ∈ˢ
            interp constants levels env receipt.proof.proposition.val := by
  refine ⟨readSignature_sound (receipt.snapshot.prepare_parts receipt.preparation).1, ?_⟩
  obtain ⟨ref, entry, hr, _, ⟨bytes, declaration, rawType, hb, _, ht, hread⟩, hu, hp⟩ := receipt.target_entry
  refine ⟨ref, bytes, declaration, rawType, hr, hb, hu ▸ ht, ?_, ?_⟩
  · rw [receipt.proof.proposition.property.1, hp]
    exact hread
  · intro V _ constants hM levels env
    have hs := receipt.proof.isProp V constants hM.realizes levels env (Context.valid_nil constants levels env)
    exact ⟨hs.1, hs.2.2, (receipt.proof.typing V constants hM.realizes levels env
      (Context.valid_nil constants levels env)).2.2⟩

def SubjectReading (objects : Objects) (subject : Address) (refs : List (ConstRef Address)) : Prop :=
  ∃ source, lookup objects subject = some source ∧
    match source.info with
    | .muts members => members.isEmpty = false ∧ refs =
        (members.toList.zipIdx.flatMap fun (member, index) =>
          .member subject index :: match member with
            | .indc family => (List.range family.ctors.size).map (.ctor subject index ·)
            | _ => [])
    | _ => ∃ ref, ReferenceMeaning objects subject ref ∧ refs = [ref]

theorem subjectReferences_iff {objects : Objects} {subject : Address} {refs : List (ConstRef Address)} :
    subjectReferences? objects subject = some refs ↔ SubjectReading objects subject refs := by
  cases hs : lookup objects subject with
  | none => simp [subjectReferences?, SubjectReading, hs]
  | some source =>
    rcases source with ⟨info, sharing, references, levels⟩
    cases info <;>
      simp only [subjectReferences?, SubjectReading, hs, ← resolveReference_iff, bind,
        Option.bind_some, Option.bind_eq_some_iff, pure, Option.some.injEq, exists_eq_left']
    all_goals try solve | simp only [eq_comm]
    rename_i members
    cases he : members.isEmpty <;> simp [eq_comm]
    rfl

theorem flatMapM_mem_iff {α β : Type} {f : α → Option (List β)} {xs : List α} {ys : List β}
    (h : xs.flatMapM f = some ys) (value : β) :
    value ∈ ys ↔ ∃ source ∈ xs, ∃ values, f source = some values ∧ value ∈ values := by
  induction xs generalizing ys with
  | nil => simp at h; subst ys; simp
  | cons x xs ih =>
    simp only [List.flatMapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨values, hv, tail, ht, rfl⟩ := h
    constructor
    · intro hm
      rcases List.mem_append.mp hm with hm | hm
      · exact ⟨x, List.mem_cons_self .., values, hv, hm⟩
      · obtain ⟨source, hs, values, hf, hm⟩ := (ih ht).mp hm
        exact ⟨source, List.mem_cons_of_mem _ hs, values, hf, hm⟩
    · rintro ⟨source, hs, result, hf, hm⟩
      rcases List.mem_cons.mp hs with rfl | hs
      · cases Option.some.inj (hv.symm.trans hf)
        exact List.mem_append_left _ hm
      · exact List.mem_append_right _ ((ih ht).mpr ⟨source, hs, result, hf, hm⟩)

/-- Exact subject coverage: projection owners, every block member and every
constructor are retained. No unrelated declaration is silently discharged. -/
theorem StoreReceipt.subject_coverage
    (receipt : StoreReceipt.{v} source fuel profile subjects witness) (ref : ConstRef Address) :
    ref ∈ receipt.prepared.targets ↔
      ∃ subject ∈ subjects, ∃ refs, SubjectReading receipt.snapshot.decodedObjects subject refs ∧ ref ∈ refs := by
  have h := flatMapM_mem_iff (receipt.snapshot.prepareStore_parts receipt.preparation).2.2 ref
  simpa only [subjectReferences_iff] using h

end Ix.Certified
