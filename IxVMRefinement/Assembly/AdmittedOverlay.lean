import IxVMRefinement.Assembly.AdmittedStore
import IxVMRefinement.Assembly.ReaderFootprint
import IxVMRefinement.Assembly.RolePreludeBridge

/-! # A concrete union of selected role records and traced records

Only stored records selected by the coherent admission order are added from the role
environment. Byte agreement at overlaps follows from their actual view provenance and
the collision alternative. Missing role-order owners may remain supplied by the fallback.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency (ReaderAdmissionWitness)
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

noncomputable def admittedOverlay {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) (trace : Ixon.Env) (keepTrace : _root_.Address → Prop) : Ixon.Env :=
  subEnvRole trace (fun a => a ∈ w.order ∨ keepTrace a) (roleSuppOf w.env w.order)
    (Ix.Cert.blobsOf w.env w.order)

noncomputable def admittedCore {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) (trace : Ixon.Env) (keepTrace : _root_.Address → Prop) : Ixon.Env :=
  coreEnvRole trace (fun a => a ∈ w.order ∨ keepTrace a) (roleSuppOf w.env w.order)
    (Ix.Cert.blobsOf w.env w.order) w.prelude

theorem admitted_role_entry {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {a : _root_.Address} {raw : ByteArray} {c : Ixon.Constant}
    (h : (a, raw, c) ∈ roleSuppOf w.env w.order) :
    _root_.Address.blake3Pure raw = a ∧ Ixon.deConstantExact raw = .ok c ∧ V.Preimage a raw := by
  obtain ⟨ha, lc, hget, hrecord, rfl⟩ := mem_roleSuppOf_iff.mp h
  obtain ⟨_, _, hauth, _⟩ := admitted_bare_byteFacts w
  have hmem : (a, lc.rawBytes) ∈ Ix.Cert.recordsOf w.env w.order :=
    List.mem_filterMap.mpr ⟨a, ha, by rw [hget]; rfl⟩
  have hhash := hauth.1 (a, lc.rawBytes) hmem
  rw [_root_.Address.admissionHash_eq] at hhash
  obtain ⟨lc', hget', hdecode⟩ := ReaderFootprint.coherent_recordAt_exact w.coherent hrecord
  have hlc := Option.some.inj (hget'.symm.trans hget)
  subst lc'
  obtain ⟨lcV, hview, hraw⟩ := w.selectedRecordsInView a ha lc hget
  exact ⟨hhash.symm, hdecode, .inl ⟨lcV, hview, hraw⟩⟩

theorem admitted_role_blob {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {a : _root_.Address} {bytes : ByteArray}
    (h : (a, bytes) ∈ Ix.Cert.blobsOf w.env w.order) :
    _root_.Address.blake3Pure bytes = a ∧ V.Preimage a bytes := by
  obtain ⟨_, _, hauth, _⟩ := admitted_bare_byteFacts w
  have hhash := hauth.2 (a, bytes) h
  rw [_root_.Address.admissionHash_eq] at hhash
  exact ⟨hhash.symm, .inr (.inl (w.draws.2 a bytes (Ix.Cert.Stream.mem_blobsOf h)))⟩

theorem admittedOverlay_draws {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) (trace : Ixon.Env) (keepTrace : _root_.Address → Prop) :
    IxVM.Consistency.DrawsRole (admittedOverlay w trace keepTrace) trace V.env := by
  apply subEnvRole_drawsRoleLocal
  · intro a raw c hm
    obtain ⟨ha, lc, hget, _, hraw⟩ := mem_roleSuppOf_iff.mp hm
    obtain ⟨lcV, hview, hbytes⟩ := w.selectedRecordsInView a ha lc hget
    exact .inl ⟨lcV, hview, hbytes.trans hraw⟩
  · intro a bytes hm
    exact w.draws.2 a bytes (Ix.Cert.Stream.mem_blobsOf hm)

theorem admittedOverlay_authentic_exact {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (hload : IxVM.Consistency.LoadedBy calls trace)
    (hdecoded : L1.EnvDecoded trace) :
    (∀ a lc, (admittedOverlay w trace keepTrace).consts.get? a = some lc →
      _root_.Address.blake3Pure lc.rawBytes = a ∧
      ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c) ∧
    (∀ a bytes, (admittedOverlay w trace keepTrace).blobs.get? a = some bytes →
      _root_.Address.blake3Pure bytes = a) :=
  subEnvRole_authentic_exact hload hdecoded
    (fun _ _ _ hm => ⟨(admitted_role_entry w hm).1, (admitted_role_entry w hm).2.1⟩)
    (fun _ _ hm => (admitted_role_blob w hm).1)

/-- Every selected stored role record survives the union. No claim is made that each
address in the role order was stored in the witness environment. -/
theorem admittedOverlay_recordAt {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (hload : IxVM.Consistency.LoadedBy calls trace)
    (hdecoded : L1.EnvDecoded trace) {extra : List ByteArray}
    (hno : ¬ V.HashedCollision extra calls)
    {a : _root_.Address} (ha : a ∈ w.order) {c : Ixon.Constant}
    (hrecord : Ix.Cert.recordAt w.env a = some c) :
    Ix.Cert.recordAt (admittedOverlay w trace keepTrace) a = some c := by
  obtain ⟨lc, hget, hdecode⟩ := ReaderFootprint.coherent_recordAt_exact w.coherent hrecord
  cases htrace : trace.consts.get? a with
  | some found =>
    have hbytes := ReaderFootprint.selected_record_agrees w hno ha hget
      (hload.1 a found htrace).1 (hload.1 a found htrace).2
    obtain ⟨decoded, hcache, hdecodeTrace⟩ := hdecoded a found htrace
    rw [hbytes, hdecode] at hdecodeTrace
    have heq := Except.ok.inj hdecodeTrace
    subst decoded
    have htraceRecord : Ix.Cert.recordAt trace a = some c := by
      unfold Ix.Cert.recordAt
      rw [htrace]
      exact hcache
    exact recordAt_subEnv_of_keep trace _ _ (.inl ha) htraceRecord
  | none =>
    have habsent : trace.consts.contains a = false := by
      rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, htrace]
      rfl
    have hmember := mem_roleSuppOf_iff.mpr ⟨ha, lc, hget, hrecord, rfl⟩
    have hnew := addSupplements_get?_of_mem_nodup trace.consts
      (restrictConsts trace.consts (fun a => a ∈ w.order ∨ keepTrace a))
      (roleSuppOf_nodup w.closure.nodup) hmember habsent
    unfold Ix.Cert.recordAt
    change ((addSupplements trace.consts
      (restrictConsts trace.consts (fun a => a ∈ w.order ∨ keepTrace a))
      (roleSuppOf w.env w.order)).get? a >>= Ixon.LazyConstant.get?) = some c
    rw [hnew]
    rfl

theorem admittedOverlay_blob {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (hload : IxVM.Consistency.LoadedBy calls trace)
    {extra : List ByteArray} (hno : ¬ V.HashedCollision extra calls)
    {a : _root_.Address} {bytes : ByteArray} (hm : (a, bytes) ∈ Ix.Cert.blobsOf w.env w.order) :
    (admittedOverlay w trace keepTrace).blobs.get? a = some bytes := by
  cases htrace : trace.blobs.get? a with
  | some found =>
    have heq : found = bytes := by
      by_contra different
      exact hno (.inl ⟨a, bytes, found, .inl (admitted_role_blob w hm).2,
        (hload.2 a found htrace).1, different, (hload.2 a found htrace).2⟩)
    subst found
    have hpresent : trace.blobs.contains a = true := by
      rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, htrace]
      rfl
    change (addBlobSupplements trace.blobs (Ix.Cert.blobsOf w.env w.order)).get? a = some bytes
    rw [addBlobSupplements_get?_of_contains trace.blobs _ hpresent]
    exact htrace
  | none =>
    have habsent : trace.blobs.contains a = false := by
      rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, htrace]
      rfl
    exact addBlobSupplements_get?_of_mem_nodup trace.blobs (Ix.Cert.Stream.blobsOf_keys _ _) hm habsent

theorem admittedCore_good {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (env : Env .anon) (lim : Option Nat)
    (claimBytes : ByteArray) (hload : IxVM.Consistency.LoadedBy calls trace)
    (hbound : IxVM.Consistency.Bounded calls)
    (hno : ¬ V.HashedCollision (claimBytes :: b.bytes :: IxVM.Consistency.readerImages V) calls) :
    Core.Good ⟨admittedCore w trace keepTrace, env, w.table, lim⟩ calls := by
  apply coreEnvRole_good rolePreludeInputs env lim _ hload w.preludeRead _ _ hno hbound
  · intro image member
    simp [IxVM.Consistency.readerImages, member]
  · intro a raw c hm
    have h := admitted_role_entry w hm
    exact ⟨h.1, .inl h.2.2⟩
  · intro a bytes hm
    exact (admitted_role_blob w hm).2

theorem admittedCore_decoded {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {trace : Ixon.Env} (keepTrace : _root_.Address → Prop)
    (hdecoded : L1.EnvDecoded trace) : L1.EnvDecoded (admittedCore w trace keepTrace) := by
  apply subEnv_envDecoded hdecoded
  intro a raw c hm
  rcases List.mem_append.mp hm with role | fallback
  · exact (admitted_role_entry w role).2.1
  · unfold fallbackSupp at fallback
    obtain ⟨⟨a', c'⟩, hmember, heq⟩ := List.mem_map.mp fallback
    cases heq
    have hwire := (rolePreludeInputs.serConstant_mem_committedImages w.preludeRead
      (Array.mem_toList_iff.mp hmember)).2.2.1
    exact Ixon.Verify.deConstantExact_serConstant c' hwire

end IxVM.Refinement.Assembly
