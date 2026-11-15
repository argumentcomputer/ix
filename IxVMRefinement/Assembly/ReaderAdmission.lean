import IxVMRefinement.Assembly.CoherentStore
import IxVMRefinement.Assembly.ReaderDecode
import Ix.IxVM.Consistency.ReaderAdmission

/-! # Executable construction of coherent reader admission

The check rebuilds the cache before discovering the role closure. It reads that closure
once, retains the reader state, and checks the same declarations used in the witness.
Agreement checks inspect only selected records, selected blobs, and prelude overlaps.
-/

namespace IxVM.Refinement.Assembly

universe u

open Ix.Kernel
open Ix.Kernel.Admission (Binding)
open IxVM.Consistency (ReaderAdmissionWitness ReaderCacheCoherent)

namespace ReaderAdmission

private theorem bytes_eq_of_beq {a b : ByteArray} (h : (a == b) = true) : a = b := by
  have hdata : (a.data == b.data) = true := h
  exact ByteArray.ext (eq_of_beq hdata)

private def fallbackAgrees (E : Ixon.Env) (order : List _root_.Address)
    (pre : Reader.Prelude .anon) : Bool :=
  let selected := Ix.Cert.TableAdmission.setOf order
  let blobKeys := Ix.Cert.TableAdmission.setOf ((Ix.Cert.blobsOf E order).map Prod.fst)
  (pre.records ++ pre.evidence).all fun (a, c) =>
    let expected := Ixon.serConstant c
    let recordOk := if selected.contains a then
      match E.consts.get? a with
      | none => true
      | some lc => lc.rawBytes == expected
      else true
    let blobOk := if blobKeys.contains a then
      match E.blobs.get? a with
      | none => true
      | some bytes => bytes == expected
      else true
    recordOk && blobOk

private def selectedAgrees (E : Ixon.Env) (order : List _root_.Address) : Bool :=
  let selected := Ix.Cert.TableAdmission.setOf order
  (Ix.Cert.blobsOf E order).all fun (a, bytes) =>
    if selected.contains a then
      match E.consts.get? a with
      | none => true
      | some lc => bytes == lc.rawBytes
    else true

private theorem fallbackAgrees_records {E : Ixon.Env} {order : List _root_.Address}
    {pre : Reader.Prelude .anon} (h : fallbackAgrees E order pre = true)
    {a : _root_.Address} (ha : a ∈ order) {lc : Ixon.LazyConstant}
    (hget : E.consts.get? a = some lc) {c : Ixon.Constant}
    (hc : (a, c) ∈ pre.records ++ pre.evidence) : lc.rawBytes = Ixon.serConstant c := by
  dsimp only [fallbackAgrees] at h
  have hrow := List.all_eq_true.mp h (a, c) hc
  have hselected := Ix.Cert.TableAdmission.contains_setOf.mpr ha
  simp only [hselected, ↓reduceIte, hget, Bool.and_eq_true] at hrow
  exact bytes_eq_of_beq hrow.1

private theorem fallbackAgrees_blobs {E : Ixon.Env} {order : List _root_.Address}
    {pre : Reader.Prelude .anon} (h : fallbackAgrees E order pre = true)
    {a : _root_.Address} {bytes : ByteArray} (hb : (a, bytes) ∈ Ix.Cert.blobsOf E order)
    {c : Ixon.Constant} (hc : (a, c) ∈ pre.records ++ pre.evidence) :
    bytes = Ixon.serConstant c := by
  dsimp only [fallbackAgrees] at h
  have hrow := List.all_eq_true.mp h (a, c) hc
  have hselected := Ix.Cert.TableAdmission.contains_setOf.mpr
    (List.mem_map.mpr ⟨(a, bytes), hb, rfl⟩ : a ∈ (Ix.Cert.blobsOf E order).map Prod.fst)
  have hget := Ix.Cert.Stream.mem_blobsOf hb
  simp only [hselected, ↓reduceIte, hget, Bool.and_eq_true] at hrow
  exact bytes_eq_of_beq hrow.2

private theorem selectedAgrees_sound {E : Ixon.Env} {order : List _root_.Address}
    (h : selectedAgrees E order = true) {a : _root_.Address} (ha : a ∈ order)
    {lc : Ixon.LazyConstant} (hget : E.consts.get? a = some lc)
    {bytes : ByteArray} (hb : (a, bytes) ∈ Ix.Cert.blobsOf E order) : bytes = lc.rawBytes := by
  have hrow := List.all_eq_true.mp h (a, bytes) hb
  have hselected := Ix.Cert.TableAdmission.contains_setOf.mpr ha
  simp only [hselected, ↓reduceIte, hget] at hrow
  exact bytes_eq_of_beq hrow

/-- Byte preparation retaining the full reader's state and declarations. -/
def read (t : RoleTable) (E : Ixon.Env) (order : List _root_.Address)
    (pre : Reader.Prelude .anon) : Except Admission.Error
      (Reader.State .anon × Array (Reader.CDecl .anon)) := do
  let limits := Ix.Cert.TableAdmission.admissionLimits
  let records := Ix.Cert.recordsOf E order
  let blobs := Ix.Cert.blobsOf E order
  (Admission.preflight limits records blobs).mapError Admission.Error.ofBytes
  (Admission.uniqueKeys records blobs).mapError Admission.Error.ofBytes
  (Admission.authenticate _root_.Address.admissionHash records blobs).mapError Admission.Error.ofBytes
  let constants ← (Admission.decodeRecords limits records).mapError Admission.Error.ofBytes
  let hints := Ix.Cert.TableAdmission.hintsAt (Ix.Cert.TableAdmission.hintsProjAt E) E
  let cx := Admission.streamContext _root_.Address.admissionHash t pre constants blobs hints
  match Reader.readRecords cx pre.state constants.toArray with
  | .error (e, i) => throw (.read i e)
  | .ok (st, ds) =>
    if Reader.State.keepsPrelude pre.state st then pure (st, ds) else throw .preludeCopy

private theorem read_spec {b : Binding} {t : RoleTable} {E : Ixon.Env}
    {order : List _root_.Address} {pre : Reader.Prelude .anon}
    {st : Reader.State .anon} {ds : Array (Reader.CDecl .anon)}
    (hadm : Admission.admitBinding _root_.Address.admissionHash b = .ok t)
    (hcoherent : ReaderCacheCoherent E) (h : read t E order pre = .ok (st, ds)) :
    Reader.readRecords
      (Admission.streamContext _root_.Address.admissionHash t pre
        (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
      pre.state (Ix.Cert.Stream.decodedOf E order).toArray = .ok (st, ds) ∧
    Admission.prepareWith _root_.Address.admissionHash b pre
      Ix.Cert.TableAdmission.admissionLimits (Ix.Cert.recordsOf E order)
      (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E) =
      .ok (Reader.evidenceOf
        (Admission.streamContext _root_.Address.admissionHash t pre
          (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E)) st t,
        Frontend.preparePrelude pre.ix ds) := by
  unfold read at h
  simp only [Ix.Cert.TableAdmission.hintsAt_hintsProjAt] at h
  cases hpf : Admission.preflight Ix.Cert.TableAdmission.admissionLimits
      (Ix.Cert.recordsOf E order) (Ix.Cert.blobsOf E order) with
  | error e => simp [hpf, Except.mapError, bind, Except.bind] at h
  | ok _ =>
    cases huq : Admission.uniqueKeys (Ix.Cert.recordsOf E order) (Ix.Cert.blobsOf E order) with
    | error e => simp [hpf, huq, Except.mapError, bind, Except.bind] at h
    | ok _ =>
      cases hau : Admission.authenticate _root_.Address.admissionHash
          (Ix.Cert.recordsOf E order) (Ix.Cert.blobsOf E order) with
      | error e => simp [hpf, huq, hau, Except.mapError, bind, Except.bind] at h
      | ok _ =>
        cases hdec : Admission.decodeRecords Ix.Cert.TableAdmission.admissionLimits
            (Ix.Cert.recordsOf E order) with
        | error e => simp [hpf, huq, hau, hdec, Except.mapError, bind, Except.bind] at h
        | ok constants =>
          have heq := recordsRead_decodedOf_coherent E order
            (fun a _ lc hget c hd => by rw [hcoherent a lc hget, hd]; rfl)
            ((Admission.decodeRecords_ok_iff _ _ _).mp hdec)
          subst constants
          cases hr : Reader.readRecords
              (Admission.streamContext _root_.Address.admissionHash t pre
                (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
              pre.state (Ix.Cert.Stream.decodedOf E order).toArray with
          | error e =>
            obtain ⟨e, i⟩ := e
            simp [hpf, huq, hau, hdec, hr, Except.mapError, bind, Except.bind] at h
          | ok result =>
            obtain ⟨st', ds'⟩ := result
            cases hk : Reader.State.keepsPrelude pre.state st' with
            | false =>
              simp [hpf, huq, hau, hdec, hr, hk, Except.mapError, bind, Except.bind] at h
            | true =>
              simp only [hpf, huq, hau, hdec, hr, hk, ↓reduceIte, Except.mapError,
                bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨rfl, ?_⟩
              unfold Admission.prepareWith Admission.readStream
              simp only [hpf, huq, hau, hadm, hdec, hr, hk, ↓reduceIte,
                Except.mapError, bind, Except.bind, pure, Except.pure]

/-- Run the pure checker on the same full reader output, retaining only the admission verdict. -/
def preparedCheck (t : RoleTable) (E : Ixon.Env) (order : List _root_.Address)
    (pre : Reader.Prelude .anon) : Bool :=
  Ix.Cert.TableAdmission.preparedOkWith (.ok () : Except Unit Unit)
    (fun _ => read t E order pre)
    (fun st ds =>
      let cx := Admission.streamContext _root_.Address.admissionHash t pre
        (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order)
        (Ix.Cert.TableAdmission.hintsAt (Ix.Cert.TableAdmission.hintsProjAt E) E)
      Cached.checkDecls .verified (Reader.evidenceOf cx st t)
        ((Frontend.preparePrelude pre.ix ds).map IxVM.Refinement.thmToOpaqueDefn))
    (fun envA st ds =>
      let cx := Admission.streamContext _root_.Address.admissionHash t pre
        (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order)
        (Ix.Cert.TableAdmission.hintsAt (Ix.Cert.TableAdmission.hintsProjAt E) E)
      Ix.Cert.TableAdmission.declsOk t envA (Reader.evidenceOf cx st t)
        (Frontend.preparePrelude pre.ix ds).toList &&
      Ix.Cert.TableAdmission.isOk (checkUnits (Frontend.preparePrelude pre.ix ds)) &&
      (st.projRewrites == 0) && fallbackAgrees E order pre && selectedAgrees E order)

/-- Check one proposed order; order discovery remains outside the trusted proof. -/
def checkAt (t : RoleTable) (E : Ixon.Env)
    (wit : List (_root_.Address × Option _root_.Address)) (order : List _root_.Address) : Bool :=
  let seeds := Ix.Cert.TableAdmission.seedList t
  let idx := Ix.Cert.artifactRecIndex E
  Ix.Cert.TableAdmission.literalSupportOk t && seeds.all E.consts.contains &&
    Ix.Cert.TableAdmission.orderedCheck E order &&
    Ix.Cert.TableAdmission.closedCheck t E idx seeds order &&
    Ix.Cert.TableAdmission.reachCheck t E idx seeds wit order &&
    match Reader.preludeFor t with
    | .error _ => false
    | .ok pre => preparedCheck t E order pre

/-- Rebuild a coherent cache from bounded canonical decoding before discovering or checking. -/
def check (b : Binding) (source : Ixon.Env) : Bool :=
  let E := decodeReaderEnv source
  match Admission.admitBinding _root_.Address.admissionHash b with
  | .error _ => false
  | .ok t =>
    let (wit, order) := Ix.Cert.TableAdmission.candidate t E (Ix.Cert.artifactRecIndex E)
    checkAt t E wit order

theorem checkAt_sound (W : Type u) [SetTheory W]
    {V : IxVM.Refinement.View} {b : Binding} {t : RoleTable} {E : Ixon.Env}
    {wit : List (_root_.Address × Option _root_.Address)} {order : List _root_.Address}
    (hadm : Admission.admitBinding _root_.Address.admissionHash b = .ok t)
    (hdraws : IxVM.Refinement.Draws E V.env) (hcoherent : ReaderCacheCoherent E)
    (h : checkAt t E wit order = true) : Nonempty (ReaderAdmissionWitness V b) := by
  unfold checkAt at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hlit, hseeds⟩, hord⟩, hclosed⟩, hreach⟩, hprepared⟩ := h
  cases hpre : Reader.preludeFor (md := .anon) t with
  | error e => simp [hpre] at hprepared
  | ok pre =>
    simp only [hpre] at hprepared
    obtain ⟨_, st, ds, envA, _, hr, hck, hfin⟩ :=
      Ix.Cert.TableAdmission.preparedOkWith_sound hprepared
    simp only [Ix.Cert.TableAdmission.hintsAt_hintsProjAt] at hck hfin
    obtain ⟨hread, hprep⟩ := read_spec hadm hcoherent hr
    have haccepted := Cached.checkDecls_refines_ref W rfl hck
    rw [Array.toList_map] at haccepted
    simp only [Bool.and_eq_true] at hfin
    obtain ⟨⟨⟨⟨hdecls, hunits⟩, hproj⟩, hfallback⟩, hselected⟩ := hfin
    obtain ⟨hthms, haxioms, hspecs⟩ := Ix.Cert.TableAdmission.declsOk_sound (b := b) hdecls
    have hunits' : checkUnits (Frontend.preparePrelude pre.ix ds) = .ok () := by
      cases hu : checkUnits (Frontend.preparePrelude pre.ix ds) with
      | error e => simp [hu, Ix.Cert.TableAdmission.isOk] at hunits
      | ok result => cases result; rfl
    refine ⟨{
      table := t
      env := E
      limits := Ix.Cert.TableAdmission.admissionLimits
      order := order
      prelude := pre
      state := st
      fullDecls := ds
      checkedEnv := envA
      admitted := hadm
      literalSupport := Ix.Cert.TableAdmission.literalSupportBound_of hlit
      draws := hdraws
      coherent := hcoherent
      seedsStored := fun a ha => List.all_eq_true.mp hseeds a (Ix.Cert.TableAdmission.mem_seedList.mpr ha)
      closure := Ix.Cert.TableAdmission.closureOrderAt_of_checks
        (fun _ => Ix.Cert.TableAdmission.mem_seedList) hord hclosed hreach
      preludeRead := hpre
      read := hread
      prepared := hprep
      accepted := haccepted
      theorems := hthms
      specifications := hspecs
      userAxioms := haxioms
      units := hunits'
      noProjRewrites := beq_iff_eq.mp hproj
      fallbackRecordsAgree := fun _ ha _ hget _ hc => fallbackAgrees_records hfallback ha hget hc
      fallbackRecordBlobsAgree := fun _ _ hb _ hc => fallbackAgrees_blobs hfallback hb hc
      selectedRecordBlobsAgree := fun _ ha _ hget _ hb => selectedAgrees_sound hselected ha hget hb
    }⟩

/-- The executable verdict constructs the approved witness using the view's own bytes. -/
theorem check_sound (W : Type u) [SetTheory W] {V : IxVM.Refinement.View} {b : Binding}
    (h : check b V.env = true) : Nonempty (ReaderAdmissionWitness V b) := by
  unfold check at h
  cases hadm : Admission.admitBinding _root_.Address.admissionHash b with
  | error e => simp [hadm] at h
  | ok t =>
    simp only [hadm] at h
    exact checkAt_sound W hadm (decodeReaderEnv_draws V.env)
      (fun _ _ hg => decodeReaderEnv_coherent V.env hg) h

end ReaderAdmission

end IxVM.Refinement.Assembly
