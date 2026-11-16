import IxVMRefinement.Assembly.AdmittedBlobs
import IxVMRefinement.Assembly.UsedRecordTransfer

/-! # Actual expression replay for retained admitted records

The reader contexts may have different indexes and unused entries. Used constant keys
and referenced literal bytes are nevertheless preserved. Singleton self references also
retain their actual reader key, so their expression readings need no naming premise.
-/

namespace IxVM.Refinement.Assembly.ReaderStoreTransfer

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

theorem admitted_refsLeOn {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) {order : List _root_.Address}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: b.bytes :: readerImages V) calls)
    {seeds : _root_.Address → Prop}
    (closure : UsedClosureOrderAt w.table (admittedOverlay w trace keepTrace) seeds order)
    {owner : _root_.Address} {record : Ixon.Constant}
    (selected : owner ∈ w.order) (original : Ix.Cert.recordAt w.env owner = some record)
    (retained : owner ∈ order) :
    UsedRecordTransfer.RefsLeOn (fun i => i ∈ usedRefIdxs record) record
      (readerContext w.table w.prelude w.env w.order)
      (readerContext w.table w.prelude (admittedOverlay w trace keepTrace) order) where
  keyAt := by
    intro i used a reference key read
    exact admitted_used_keyAt w keepTrace claimBytes loaded decoded noCollision closure retained
      (admittedOverlay_recordAt w keepTrace loaded decoded noCollision selected original) used reference read
  blob := fun _ reference _ read =>
    admitted_referenced_blob w keepTrace claimBytes loaded decoded noCollision selected original retained reference read

theorem admitted_memberReader_read {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) {order : List _root_.Address}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: b.bytes :: readerImages V) calls)
    {seeds : _root_.Address → Prop}
    (closure : UsedClosureOrderAt w.table (admittedOverlay w trace keepTrace) seeds order)
    {owner : _root_.Address} {record : Ixon.Constant}
    (selected : owner ∈ w.order) (original : Ix.Cert.recordAt w.env owner = some record)
    (retained : owner ∈ order) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName .anon)))
    {raw : Ixon.Expr} (support : ReaderAnalysis.RefsIn (fun i => i ∈ usedRefIdxs record) raw)
    {value : CExpr .anon}
    (read : (MemberReader.mk' (readerContext w.table w.prelude w.env w.order)
      record param self).read raw = .ok value) :
    (MemberReader.mk' (readerContext w.table w.prelude (admittedOverlay w trace keepTrace) order)
      record param self).read raw = .ok value := by
  apply UsedRecordTransfer.read_le
    (admitted_refsLeOn w keepTrace claimBytes loaded decoded noCollision closure selected original retained)
    param self _ support read
  intro expression member i used
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨expression, member, used⟩)

def singletonSelf (cx : Ctx .anon) (owner : _root_.Address) : Nat → Option (ReadM (CName .anon)) :=
  fun i => if i == 0 then some (cx.memberKey (.member owner 0)) else none

theorem admitted_singletonSelf {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) {order : List _root_.Address}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    {extra : List ByteArray} (noCollision : ¬ V.HashedCollision extra calls)
    {owner : _root_.Address} {record : Ixon.Constant}
    (selected : owner ∈ w.order) (original : Ix.Cert.recordAt w.env owner = some record)
    (retained : owner ∈ order)
    (singleton : match record.info with | .defn _ | .recr _ | .axio _ | .quot _ => True | _ => False) :
    singletonSelf (readerContext w.table w.prelude w.env w.order) owner =
      singletonSelf (readerContext w.table w.prelude (admittedOverlay w trace keepTrace) order) owner := by
  have checked := check_of_admitBinding w.admitted
  have oldStored := ReaderStoreTransfer.selected (table := w.table) (prelude := w.prelude) selected original
  have newStored := ReaderStoreTransfer.selected (table := w.table) (prelude := w.prelude) retained
    (admittedOverlay_recordAt w keepTrace loaded decoded noCollision selected original)
  have oldKey := streamContext_memberKey_singleton (admitted_streamStore_authentic w) checked oldStored singleton
  have newKey := streamContext_memberKey_singleton
    (admittedReaderStore_authentic w keepTrace order loaded decoded) checked newStored singleton
  funext i
  simp only [singletonSelf, oldKey, newKey]

/-- A singleton's own recursive-reference callback is the actual new callback, rather
than a caller-supplied equality of member keys. -/
theorem admitted_singleton_read {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) {order : List _root_.Address}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: b.bytes :: readerImages V) calls)
    {seeds : _root_.Address → Prop}
    (closure : UsedClosureOrderAt w.table (admittedOverlay w trace keepTrace) seeds order)
    {owner : _root_.Address} {record : Ixon.Constant}
    (selected : owner ∈ w.order) (original : Ix.Cert.recordAt w.env owner = some record)
    (retained : owner ∈ order)
    (singleton : match record.info with | .defn _ | .recr _ | .axio _ | .quot _ => True | _ => False)
    (param : Nat → LevelParam) {raw : Ixon.Expr}
    (support : ReaderAnalysis.RefsIn (fun i => i ∈ usedRefIdxs record) raw) {value : CExpr .anon}
    (read : (MemberReader.mk' (readerContext w.table w.prelude w.env w.order) record param
      (singletonSelf (readerContext w.table w.prelude w.env w.order) owner)).read raw = .ok value) :
    (MemberReader.mk' (readerContext w.table w.prelude (admittedOverlay w trace keepTrace) order) record param
      (singletonSelf (readerContext w.table w.prelude (admittedOverlay w trace keepTrace) order) owner)).read raw =
      .ok value := by
  rw [← admitted_singletonSelf w keepTrace loaded decoded noCollision selected original retained singleton]
  exact admitted_memberReader_read w keepTrace claimBytes loaded decoded noCollision closure
    selected original retained param _ support read

end IxVM.Refinement.Assembly.ReaderStoreTransfer
