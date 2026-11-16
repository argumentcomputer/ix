import IxVMRefinement.Assembly.AdmittedOverlay
import IxVMRefinement.Assembly.SafeRefsBridge

/-! # The actual reader store backed by the admitted and traced union

The prelude-backed reader store embeds into the concrete core store. Projection byte
agreement uses either the selected raw view footprint or a hash call from the actual
walked constructor check.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency (ReaderAdmissionWitness)
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

theorem admittedCore_of_overlay {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {trace : Ixon.Env} {keepTrace : _root_.Address → Prop}
    {a : _root_.Address} {c : Ixon.Constant}
    (h : Ix.Cert.recordAt (admittedOverlay w trace keepTrace) a = some c) :
    Ix.Cert.recordAt (admittedCore w trace keepTrace) a = some c :=
  recordAt_coreEnvRole_of_subEnvRole (roleSuppOf_nodup w.closure.nodup) h

theorem admittedCore_fallback {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray)
    (hload : IxVM.Consistency.LoadedBy calls trace) (hdecoded : L1.EnvDecoded trace)
    (hno : ¬ V.HashedCollision (claimBytes :: b.bytes :: IxVM.Consistency.readerImages V) calls)
    {a : _root_.Address} {c : Ixon.Constant} (hc : (a, c) ∈ w.prelude.records ++ w.prelude.evidence) :
    Ix.Cert.recordAt (admittedCore w trace keepTrace) a = some c := by
  apply recordAt_coreEnvRole_of_fallback rolePreludeInputs _ hload hdecoded hno w.preludeRead _ hc
  · intro image himage
    simp [IxVM.Consistency.readerImages, himage]
  · intro a raw found expected hrole hfallback
    have hdecode := (admitted_role_entry w hrole).2.1
    obtain ⟨ha, lc, hget, _, rfl⟩ := mem_roleSuppOf_iff.mp hrole
    have hraw := w.fallbackRecordsAgree a ha lc hget expected hfallback
    have hwire := (rolePreludeInputs.serConstant_mem_committedImages w.preludeRead hfallback).2.2.1
    rw [hraw, Ixon.Verify.deConstantExact_serConstant expected hwire] at hdecode
    exact (Except.ok.inj hdecode).symm

/-- Every lookup of the actual prelude-backed reader is decoded identically in the core
store, for any chosen reading order. -/
theorem admittedReaderStore_sub_core {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) (order : List _root_.Address)
    (hload : IxVM.Consistency.LoadedBy calls trace) (hdecoded : L1.EnvDecoded trace)
    (hno : ¬ V.HashedCollision (claimBytes :: b.bytes :: IxVM.Consistency.readerImages V) calls)
    {a : _root_.Address} {c : Ixon.Constant}
    (h : (Admission.streamContext _root_.Address.admissionHash w.table w.prelude
      (Ix.Cert.Stream.decodedOf (admittedOverlay w trace keepTrace) order)
      (Ix.Cert.blobsOf (admittedOverlay w trace keepTrace) order)
      (Ix.Cert.hintsOf (admittedOverlay w trace keepTrace))).store a = some c) :
    Ix.Cert.recordAt (admittedCore w trace keepTrace) a = some c := by
  rcases streamContext_store_mem h with input | fallback
  · obtain ⟨a', _, hmap⟩ := List.mem_filterMap.mp input
    obtain ⟨c', hrecord, heq⟩ := Option.map_eq_some_iff.mp hmap
    cases heq
    exact admittedCore_of_overlay w hrecord
  · exact admittedCore_fallback w keepTrace claimBytes hload hdecoded hno fallback

/-- A selected record's actual decoded projection image cannot disagree with a traced
record at the reconstructed address. -/
theorem admitted_projection_trace_agrees {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (claimBytes : ByteArray) (hload : IxVM.Consistency.LoadedBy calls trace)
    (hno : ¬ V.HashedCollision (claimBytes :: b.bytes :: IxVM.Consistency.readerImages V) calls)
    {owner : _root_.Address} (howner : owner ∈ w.order) {record : Ixon.Constant}
    (hrecord : Ix.Cert.recordAt w.env owner = some record) {bytes : ByteArray}
    (himage : bytes ∈ IxVM.Consistency.recordProjectionImages owner record)
    {lc : Ixon.LazyConstant} (hget : trace.consts.get? (_root_.Address.blake3Pure bytes) = some lc) :
    lc.rawBytes = bytes := by
  have hheld := ReaderFootprint.selected_projection_covered w howner hrecord himage
  exact ReaderFootprint.held_image_agrees hno
    (by simp [IxVM.Consistency.readerImages, hheld])
    (hload.1 _ lc hget).1 (hload.1 _ lc hget).2

/-- Walked constructor wrappers have an actual source hash call. This covers a traced
family that is absent from the selected role records and the committed fallback. -/
theorem admittedCore_walked_ctor_bytes {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray)
    (hbound : IxVM.Consistency.Bounded calls) (hload : IxVM.Consistency.LoadedBy calls trace)
    (hdecoded : L1.EnvDecoded trace)
    (hno : ¬ V.HashedCollision (claimBytes :: b.bytes :: IxVM.Consistency.readerImages V) calls)
    {block : _root_.Address} {record : Ixon.Constant} {members : Array Ixon.MutConst}
    {i j : Nat} {ind : Ixon.Inductive} {ctor : Ixon.Constructor}
    (hwalked : WkAll calls b.address w.table trace block)
    (hsafe : ¬ IxVM.Consistency.OutsideLogicAt trace block)
    (hrecord : Ix.Cert.recordAt trace block = some record) (hinfo : record.info = .muts members)
    (hind : members[i]? = some (.indc ind)) (hctor : ind.ctors[j]? = some ctor)
    {lc : Ixon.LazyConstant}
    (hget : (admittedCore w trace keepTrace).consts.get?
      (_root_.Address.blake3Pure (Ixon.serConstant (IxVM.Consistency.constructorProjection block i j))) = some lc) :
    lc.rawBytes = Ixon.serConstant (IxVM.Consistency.constructorProjection block i j) := by
  have hhash := indBlockCtor_hashed_of_exact_noCollision hbound hload hdecoded hno
    hwalked hsafe hrecord hinfo hind hctor
  have hgood := admittedCore_good w keepTrace Env.empty none claimBytes hload hbound hno
  exact (Core.load_escape hget hgood.1 _ hhash rfl).symm

end IxVM.Refinement.Assembly
