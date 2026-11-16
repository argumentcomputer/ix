import IxVMRefinement.Assembly.AdmittedExpr

/-! # Actual singleton axiom and quotient record replay

These record readings do not depend on declaration heights or projection-rewrite state.
Their actual key and type readings therefore replay unchanged in the selected context.
-/

namespace IxVM.Refinement.Assembly.ReaderStoreTransfer

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert.Loop (except_bind_ok)
open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

theorem admitted_singleton_memberKey {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) {order : List _root_.Address}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    {extra : List ByteArray} (noCollision : ¬ V.HashedCollision extra calls)
    {owner : _root_.Address} {record : Ixon.Constant}
    (selected : owner ∈ w.order) (original : Ix.Cert.recordAt w.env owner = some record)
    (retained : owner ∈ order)
    (singleton : match record.info with | .defn _ | .recr _ | .axio _ | .quot _ => True | _ => False) :
    (readerContext w.table w.prelude (admittedOverlay w trace keepTrace) order).memberKey (.member owner 0) =
      (readerContext w.table w.prelude w.env w.order).memberKey (.member owner 0) := by
  have checked := check_of_admitBinding w.admitted
  have oldStored := ReaderStoreTransfer.selected (table := w.table) (prelude := w.prelude) selected original
  have newStored := ReaderStoreTransfer.selected (table := w.table) (prelude := w.prelude) retained
    (admittedOverlay_recordAt w keepTrace loaded decoded noCollision selected original)
  have oldKey := streamContext_memberKey_singleton (admitted_streamStore_authentic w) checked oldStored singleton
  have newKey := streamContext_memberKey_singleton
    (admittedReaderStore_authentic w keepTrace order loaded decoded) checked newStored singleton
  exact newKey.trans oldKey.symm

theorem admitted_plain_replay {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) {order : List _root_.Address}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: b.bytes :: readerImages V) calls)
    {seeds : _root_.Address → Prop}
    (closure : UsedClosureOrderAt w.table (admittedOverlay w trace keepTrace) seeds order)
    {owner : _root_.Address} {record : Ixon.Constant}
    (selected : owner ∈ w.order) (original : Ix.Cert.recordAt w.env owner = some record)
    (retained : owner ∈ order)
    (kind : match record.info with | .axio _ | .quot _ => True | _ => False)
    {source target : State .anon} {full : Read .anon}
    (read : readRecord (readerContext w.table w.prelude w.env w.order) source owner record = .ok full) :
    readRecordBare (readerContext w.table w.prelude (admittedOverlay w trace keepTrace) order)
      target owner record = .ok full := by
  have singleton : (match record.info with | .defn _ | .recr _ | .axio _ | .quot _ => True | _ => False) := by
    cases info : record.info <;> simp_all
  have keyed := admitted_singleton_memberKey w keepTrace loaded decoded noCollision selected original retained singleton
  cases info : record.info with
  | axio ax =>
    simp only [readRecord, info] at read
    simp only [readRecordBare, info, readRecord]
    cases unsafeFlag : ax.isUnsafe with
    | true => simp [unsafeFlag, declined, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at read
    | false =>
      simp only [unsafeFlag, Bool.false_eq_true, ↓reduceIte] at read ⊢
      obtain ⟨name, nameRead, read⟩ := except_bind_ok.mp read
      obtain ⟨type, typeRead, returned⟩ := except_bind_ok.mp read
      have replay := admitted_memberReader_read w keepTrace claimBytes loaded decoded noCollision closure
        selected original retained id (fun _ => none)
        (fun i used => by simp [usedRefIdxs, info, used]) typeRead
      rw [keyed, nameRead]
      dsimp only [bind, Except.bind]
      rw [replay]
      exact returned
  | quot q =>
    simp only [readRecord, info] at read
    simp only [readRecordBare, info, readRecord]
    obtain ⟨name, nameRead, read⟩ := except_bind_ok.mp read
    obtain ⟨type, typeRead, returned⟩ := except_bind_ok.mp read
    have replay := admitted_memberReader_read w keepTrace claimBytes loaded decoded noCollision closure
      selected original retained id (fun _ => none)
      (fun i used => by simp [usedRefIdxs, info, used]) typeRead
    rw [keyed, nameRead]
    dsimp only [bind, Except.bind]
    rw [replay]
    exact returned
  | _ => simp [info] at kind

/-- The admitted run itself supplies the successful original record reading. -/
theorem admitted_plain_record {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) {order : List _root_.Address}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: b.bytes :: readerImages V) calls)
    {seeds : _root_.Address → Prop}
    (closure : UsedClosureOrderAt w.table (admittedOverlay w trace keepTrace) seeds order)
    {owner : _root_.Address} {record : Ixon.Constant}
    (selected : owner ∈ w.order) (original : Ix.Cert.recordAt w.env owner = some record)
    (retained : owner ∈ order)
    (kind : match record.info with | .axio _ | .quot _ => True | _ => False)
    (target : State .anon) :
    ∃ full, readRecordBare (readerContext w.table w.prelude (admittedOverlay w trace keepTrace) order)
      target owner record = .ok full ∧ ∀ decl ∈ full.decls, decl ∈ w.fullDecls := by
  have present := Ix.Cert.RecursorIndex.mem_decoded.mpr ⟨selected, original⟩
  obtain ⟨source, full, read, declared⟩ :=
    (readRecords_spec w.read).mem (Array.mem_toList_iff.mpr present)
  exact ⟨full, admitted_plain_replay w keepTrace claimBytes loaded decoded noCollision closure
    selected original retained kind read, declared⟩

end IxVM.Refinement.Assembly.ReaderStoreTransfer
