import IxVMRefinement.Assembly.RecEntryOrigin
import IxVMRefinement.Assembly.AdmittedIndexReplay
import IxVMRefinement.Assembly.AdmittedKeys

/-! # Exact recursor entries after selected-store reconstruction

Canonical/twin status can change with the walked-first order. The retained payload's
family, motive, major carrier and level-parameter mapping still come from the same actual
analysis and family record.
-/

namespace IxVM.Refinement.Assembly.ReaderStoreTransfer

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

theorem admitted_rec_entry_origin {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {owner : _root_.Address} {constant : Ixon.Constant}
    (selected : owner ∈ w.order) (record : Ix.Cert.recordAt w.env owner = some constant)
    {j : Nat} {recursor : Ixon.Recursor} (member : (j, recursor) ∈ recursorMembers constant)
    {entry : RecEntry}
    (indexed : (readerContext w.table w.prelude w.env w.order).index.recs[ConstRef.member owner j]? = some entry ∨
      (readerContext w.table w.prelude w.env w.order).index.twins[ConstRef.member owner j]? = some entry) :
    RecEntryAt (store w.table w.prelude w.env w.order) owner constant recursor entry := by
  let records := (Ix.Cert.Stream.decodedOf w.env w.order).toArray
  have keys : (records.toList.map Prod.fst).Nodup := by
    simpa only [records, List.toList_toArray] using
      (Ix.Cert.Stream.decodedOf_keys w.env w.order).nodup w.closure.nodup
  exact contextOf_member_entry w.table w.prelude records (Ix.Cert.blobsOf w.env w.order)
    (Ix.Cert.hintsOf w.env) (Admission.projectionAddress _root_.Address.admissionHash)
    w.preludeRead keys (Ix.Cert.RecursorIndex.mem_decoded.mpr ⟨selected, record⟩) member indexed

theorem admitted_rec_entry_transfer {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) {order : List _root_.Address}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: b.bytes :: readerImages V) calls)
    {seeds : _root_.Address → Prop}
    (closure : UsedClosureOrderAt w.table (admittedOverlay w trace keepTrace) seeds order)
    {owner : _root_.Address} {constant : Ixon.Constant}
    (selected : owner ∈ w.order) (record : Ix.Cert.recordAt w.env owner = some constant)
    (retained : owner ∈ order) {j : Nat} {recursor : Ixon.Recursor}
    (member : (j, recursor) ∈ recursorMembers constant) {entry : RecEntry}
    (origin : RecEntryAt (store w.table w.prelude w.env w.order) owner constant recursor entry) :
    RecEntryAt (store w.table w.prelude (admittedOverlay w trace keepTrace) order)
      owner constant recursor entry := by
  obtain ⟨carriers, analysis, block, members, slot, first, found, kind, firstAt, large⟩ := origin
  have transferred := admitted_analysis_transfer w keepTrace claimBytes loaded decoded noCollision
    closure selected record retained member analysis
  have familyRetained := admitted_analysis_family_retained w keepTrace claimBytes loaded decoded
    noCollision closure selected record retained member analysis
  have found' := admitted_selected w keepTrace claimBytes order loaded decoded noCollision familyRetained found
  exact ⟨carriers, transferred, block, members, slot, first, found', kind, firstAt, large⟩

/-- A retained admitted payload keeps its complete entry, including the large-elimination
flag. The rebuilt index may put that entry in either the canonical or the twin map. -/
theorem admitted_rec_entry_pruned {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) {order : List _root_.Address}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: b.bytes :: readerImages V) calls)
    {seeds : _root_.Address → Prop}
    (closure : UsedClosureOrderAt w.table (admittedOverlay w trace keepTrace) seeds order)
    {owner : _root_.Address} {constant : Ixon.Constant}
    (selected : owner ∈ w.order) (record : Ix.Cert.recordAt w.env owner = some constant)
    (retained : owner ∈ order) {j : Nat} {recursor : Ixon.Recursor}
    (member : (j, recursor) ∈ recursorMembers constant) {entry : RecEntry}
    (indexed : (readerContext w.table w.prelude w.env w.order).index.recs[ConstRef.member owner j]? = some entry ∨
      (readerContext w.table w.prelude w.env w.order).index.twins[ConstRef.member owner j]? = some entry) :
    let cx := readerContext w.table w.prelude (admittedOverlay w trace keepTrace) order
    cx.index.recs[ConstRef.member owner j]? = some entry ∨
      cx.index.twins[ConstRef.member owner j]? = some entry := by
  have original := admitted_rec_entry_origin w selected record member indexed
  have transported := admitted_rec_entry_transfer w keepTrace claimBytes loaded decoded noCollision
    closure selected record retained member original
  obtain ⟨entry', indexed'⟩ := admitted_rec_indexed_pruned w keepTrace claimBytes loaded decoded
    noCollision closure selected record retained member
  let records := (Ix.Cert.Stream.decodedOf (admittedOverlay w trace keepTrace) order).toArray
  have keys : (records.toList.map Prod.fst).Nodup := by
    simpa only [records, List.toList_toArray] using
      (Ix.Cert.Stream.decodedOf_keys (admittedOverlay w trace keepTrace) order).nodup closure.nodup
  have present : (owner, constant) ∈ records := Ix.Cert.RecursorIndex.mem_decoded.mpr
    ⟨retained, admittedOverlay_recordAt w keepTrace loaded decoded noCollision selected record⟩
  have newOrigin := contextOf_member_entry w.table w.prelude records
    (Ix.Cert.blobsOf (admittedOverlay w trace keepTrace) order)
    (Ix.Cert.hintsOf (admittedOverlay w trace keepTrace))
    (Admission.projectionAddress _root_.Address.admissionHash) w.preludeRead keys present member indexed'
  have same : entry = entry' := transported.unique newOrigin
  rwa [← same] at indexed'

end IxVM.Refinement.Assembly.ReaderStoreTransfer
