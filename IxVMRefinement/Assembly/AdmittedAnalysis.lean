import IxVMRefinement.Assembly.AdmittedStoreTransfer
import IxVMRefinement.Assembly.ReaderAnalysisSupport
import IxVMRefinement.Assembly.AdmittedRecSlots
import IxVMRefinement.Assembly.FallbackOwners

/-! # Actual admitted recursor analyses survive used-reference pruning

The selected union preserves each old analysis's used reference and projection owner.
Owners supplied only by the committed fallback are handled by its proved owner closure.
The resulting analysis is independent of which recursor a rebuilt index chooses first.
-/

namespace IxVM.Refinement.Assembly.ReaderStoreTransfer

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency
open Ix.Cert.EvidenceCheck (fallbackStore)
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

/-- The owner needed to resolve a retained used reference preserves every old store answer. -/
theorem admitted_used_owner {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) {order : List _root_.Address}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: b.bytes :: readerImages V) calls)
    {seeds : _root_.Address → Prop}
    (closure : UsedClosureOrderAt w.table (admittedOverlay w trace keepTrace) seeds order)
    {sourceOwner a : _root_.Address} {record value ownerRecord : Ixon.Constant}
    (retained : sourceOwner ∈ order)
    (stored : Ix.Cert.recordAt (admittedOverlay w trace keepTrace) sourceOwner = some record)
    {i : Nat} (used : i ∈ usedRefIdxs record) (reference : record.refs[i]? = some a)
    (found : store w.table w.prelude w.env w.order a = some value)
    (ownerFound : store w.table w.prelude w.env w.order (Ix.Cert.ownerOf a value) = some ownerRecord) :
    store w.table w.prelude (admittedOverlay w trace keepTrace) order
      (Ix.Cert.ownerOf a value) = some ownerRecord := by
  rcases streamContext_store_mem found with input | fallback
  · have original := Ix.Cert.RecursorIndex.mem_decoded.mp (Array.mem_toList_iff.mp input)
    have recordAt := admittedOverlay_recordAt w keepTrace loaded decoded noCollision
      original.1 original.2
    have present := readOrder_ref closure retained stored used reference (contains_of_recordAt recordAt)
    exact admitted_selected w keepTrace claimBytes order loaded decoded noCollision
      (readOrder_owner closure present recordAt) ownerFound
  · obtain ⟨committedOwner, ownerStored⟩ := fallback_owner_stored w.preludeRead
      (fallback_of_mem w.preludeRead fallback)
    have oldCore := admitted_original_core w keepTrace claimBytes loaded decoded noCollision ownerFound
    have committedCore := admittedCore_fallback w keepTrace claimBytes loaded decoded noCollision
      (Array.mem_toList_iff.mp (Ix.Cert.EvidenceCheck.fallbackStore_mem ownerStored))
    have same := Option.some.inj (oldCore.symm.trans committedCore)
    rw [same]
    exact admitted_fallback w keepTrace claimBytes order loaded decoded noCollision ownerStored

/-- Every actual selected admission recursor retains its exact successful filing analysis
in the used-reference reader store. This asserts analysis survival, not identical index order. -/
theorem admitted_analysis_survives {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) {order : List _root_.Address}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: b.bytes :: readerImages V) calls)
    {seeds : _root_.Address → Prop}
    (closure : UsedClosureOrderAt w.table (admittedOverlay w trace keepTrace) seeds order)
    {owner : _root_.Address} {constant : Ixon.Constant}
    (selected : owner ∈ w.order) (record : Ix.Cert.recordAt w.env owner = some constant)
    (retained : owner ∈ order) {j : Nat} {rc : Ixon.Recursor}
    (member : (j, rc) ∈ recursorMembers constant) :
    let original := Admission.streamContext _root_.Address.admissionHash w.table w.prelude
      (Ix.Cert.Stream.decodedOf w.env w.order) (Ix.Cert.blobsOf w.env w.order)
      (Ix.Cert.hintsOf w.env)
    ∃ entry carriers,
      (original.index.recs[ConstRef.member owner j]? = some entry ∨
        original.index.twins[ConstRef.member owner j]? = some entry) ∧
      Ix.Cert.recursorAnalysis?
        (store w.table w.prelude (admittedOverlay w trace keepTrace) order) owner constant rc =
        some (entry.block, entry.motive, carriers, entry.major) := by
  obtain ⟨entry, carriers, indexed, analysis⟩ := admitted_rec_analysis w selected record member
  refine ⟨entry, carriers, indexed, ?_⟩
  have stored := admittedOverlay_recordAt w keepTrace loaded decoded noCollision selected record
  let D := fun a => ∀ bc, store w.table w.prelude w.env w.order a = some bc →
    store w.table w.prelude (admittedOverlay w trace keepTrace) order a = some bc
  have own : D owner := fun _ found =>
    admitted_selected w keepTrace claimBytes order loaded decoded noCollision retained found
  have references : ∀ i ∈ usedRefIdxs constant, ∀ a, constant.refs[i]? = some a →
      ∀ q, resolve (store w.table w.prelude w.env w.order) a = some q →
      resolve (store w.table w.prelude (admittedOverlay w trace keepTrace) order) a = some q ∧
        D q.block := by
    intro i used a reference q resolved
    obtain ⟨value, found, source⟩ := Option.bind_eq_some_iff.mp resolved
    have kept := admitted_used_reference w keepTrace claimBytes loaded decoded noCollision
      closure retained stored used reference found
    have ownerKept : D (Ix.Cert.ownerOf a value) := by
      intro ownerRecord ownerFound
      exact admitted_used_owner w keepTrace claimBytes loaded decoded noCollision
        closure retained stored used reference found ownerFound
    refine ⟨resolve_of_local found kept ownerKept resolved, ?_⟩
    rw [Ix.Cert.RecursorIndex.resolveSource_block source]
    exact ownerKept
  exact (ReaderAnalysis.analysis_transfer_used member own references
    (fun _ bc kept found => kept bc found) analysis).1

end IxVM.Refinement.Assembly.ReaderStoreTransfer
