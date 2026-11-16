import IxVMRefinement.Assembly.AdmittedAnalysis
import IxVMRefinement.Assembly.AdmittedIndexFilter
import IxVMRefinement.Assembly.AdmittedFallbackRecords
import IxVMRefinement.Assembly.RecIndexCoverage

/-! # Actual recursor coverage after selecting the used-reference closure

Admitted analyses retain their referenced families. The original whole-record filter
then proves that every retained record is eligible in the new index. Canonical and twin
entries may be regrouped; each actual payload is still indexed.
-/

namespace IxVM.Refinement.Assembly.ReaderStoreTransfer

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

theorem admitted_used_family_retained {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) {order : List _root_.Address}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: b.bytes :: readerImages V) calls)
    {seeds : _root_.Address → Prop}
    (closure : UsedClosureOrderAt w.table (admittedOverlay w trace keepTrace) seeds order)
    {owner family : _root_.Address} {constant familyRecord : Ixon.Constant}
    (retained : owner ∈ order)
    (stored : Ix.Cert.recordAt (admittedOverlay w trace keepTrace) owner = some constant)
    (usedOwner : ReaderAnalysis.UsedOwner (store w.table w.prelude w.env w.order) owner constant family)
    (familyFound : store w.table w.prelude w.env w.order family = some familyRecord)
    {members : Array Ixon.MutConst} (familyInfo : familyRecord.info = .muts members) :
    family ∈ order := by
  rcases usedOwner with same | ⟨i, used, a, reference, value, found, resolves, ownerEq⟩
  · rwa [same]
  · have nonmutual : ∀ ms, value.info ≠ .muts ms := by
      intro ms info
      simp [resolveSource, info] at resolves
    have nonself : Ix.Cert.ownerOf a value ≠ a := by
      intro same
      have addressEq : family = a := ownerEq.symm.trans same
      have familyHere := familyFound
      rw [addressEq] at familyHere
      have valueEq := Option.some.inj (found.symm.trans familyHere)
      exact nonmutual members (by rw [valueEq]; exact familyInfo)
    have rawRecord : Ix.Cert.recordAt (admittedOverlay w trace keepTrace) a = some value := by
      rcases streamContext_store_mem found with input | fallback
      · have original := Ix.Cert.RecursorIndex.mem_decoded.mp (Array.mem_toList_iff.mp input)
        exact admittedOverlay_recordAt w keepTrace loaded decoded noCollision original.1 original.2
      · obtain ⟨selected, record⟩ := admitted_fallback_nonself w
          (fallback_of_mem w.preludeRead fallback) nonself nonmutual
        exact admittedOverlay_recordAt w keepTrace loaded decoded noCollision selected record
    have referenceRetained := readOrder_ref closure retained stored used reference
      (contains_of_recordAt rawRecord)
    have ownerRetained := readOrder_owner closure referenceRetained rawRecord
    rwa [ownerEq] at ownerRetained

/-- Every analysed family of a retained admitted recursor is retained by actual used
reference closure, including families named through committed projections. -/
theorem admitted_analysis_family_retained {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) {order : List _root_.Address}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: b.bytes :: readerImages V) calls)
    {seeds : _root_.Address → Prop}
    (closure : UsedClosureOrderAt w.table (admittedOverlay w trace keepTrace) seeds order)
    {owner : _root_.Address} {constant : Ixon.Constant}
    (selected : owner ∈ w.order) (record : Ix.Cert.recordAt w.env owner = some constant)
    (retained : owner ∈ order) {j : Nat} {rc : Ixon.Recursor}
    (member : (j, rc) ∈ recursorMembers constant)
    {result : _root_.Address × Nat × Array (ConstRef _root_.Address) × ConstRef _root_.Address}
    (analysis : Ix.Cert.recursorAnalysis? (store w.table w.prelude w.env w.order)
      owner constant rc = some result) : result.1 ∈ order := by
  have used := (ReaderAnalysis.analysis_used_owners member analysis).1
  obtain ⟨_, _, blockRecord, members, _, _, _, blockFound, blockInfo, _⟩ :=
    Ix.Cert.RecursorIndex.recursorAnalysis_spec.mp analysis
  exact admitted_used_family_retained w keepTrace claimBytes loaded decoded noCollision closure
    retained (admittedOverlay_recordAt w keepTrace loaded decoded noCollision selected record)
    used blockFound blockInfo

/-- The original actual input filter remains true for a retained admitted record. -/
theorem admitted_input_indexed_pruned {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) {order : List _root_.Address}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: b.bytes :: readerImages V) calls)
    {seeds : _root_.Address → Prop}
    (closure : UsedClosureOrderAt w.table (admittedOverlay w trace keepTrace) seeds order)
    {owner : _root_.Address} {constant : Ixon.Constant}
    (selected : owner ∈ w.order) (record : Ix.Cert.recordAt w.env owner = some constant)
    (retained : owner ∈ order) :
    let records := (Ix.Cert.Stream.decodedOf (admittedOverlay w trace keepTrace) order).toArray
    let known := records.foldl (fun known (key, _) => known.insert key) ({} : Std.HashSet _root_.Address)
    inputIndexed (store w.table w.prelude (admittedOverlay w trace keepTrace) order)
      known (w.prelude.records ++ w.prelude.evidence) owner constant = true := by
  by_cases fallback : (w.prelude.records ++ w.prelude.evidence).contains (owner, constant) = true
  · simp only [inputIndexed, fallback, Bool.or_true]
  · have notFallback : (w.prelude.records ++ w.prelude.evidence).contains (owner, constant) = false :=
      Bool.eq_false_iff.mpr fallback
    apply Bool.or_eq_true_iff.mpr
    left
    apply Array.all_eq_true_iff_forall_mem.mpr
    rintro ⟨j, rc⟩ member
    obtain ⟨entry, carriers, _, analysis⟩ := admitted_rec_analysis w selected record member
    obtain ⟨rawAnalysis, firstIndex, familyRecord, members, slot, first, firstCarrier,
      familyFound, familyInfo, firstFound, valid⟩ := Ix.Cert.RecursorIndex.recursorAnalysis_spec.mp analysis
    obtain ⟨originalFamily, familyInput⟩ := input_indexed_family
      (admitted_input_indexed w selected record member) notFallback member rawAnalysis firstCarrier
    have original := Ix.Cert.RecursorIndex.mem_decoded.mp familyInput
    have familyRetained := admitted_analysis_family_retained w keepTrace claimBytes loaded decoded
      noCollision closure selected record retained member analysis
    have newFamily := admittedOverlay_recordAt w keepTrace loaded decoded noCollision original.1 original.2
    have familyKnown := Ix.Cert.RecursorIndex.known_contains
      (Ix.Cert.RecursorIndex.mem_decoded.mpr ⟨familyRetained, newFamily⟩)
    have transferred := admitted_analysis_transfer w keepTrace claimBytes loaded decoded noCollision
      closure selected record retained member analysis
    have rawTransferred := (Ix.Cert.RecursorIndex.recursorAnalysis_spec.mp transferred).1
    dsimp only
    simp only [rawTransferred, firstCarrier]
    exact familyKnown

/-- Rebuilding the actual pruned context indexes every retained admitted recursor payload,
with no fixed canonical choice and no caller-supplied index preservation condition. -/
theorem admitted_rec_indexed_pruned {V : IxVM.Refinement.View} {b : Admission.Binding}
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
    let cx := Admission.streamContext _root_.Address.admissionHash w.table w.prelude
      (Ix.Cert.Stream.decodedOf (admittedOverlay w trace keepTrace) order)
      (Ix.Cert.blobsOf (admittedOverlay w trace keepTrace) order)
      (Ix.Cert.hintsOf (admittedOverlay w trace keepTrace))
    ∃ entry, cx.index.recs[ConstRef.member owner j]? = some entry ∨
      cx.index.twins[ConstRef.member owner j]? = some entry := by
  let input := (Ix.Cert.Stream.decodedOf (admittedOverlay w trace keepTrace) order).toArray
  let target := store w.table w.prelude (admittedOverlay w trace keepTrace) order
  have present : (owner, constant) ∈ input := Ix.Cert.RecursorIndex.mem_decoded.mpr
    ⟨retained, admittedOverlay_recordAt w keepTrace loaded decoded noCollision selected record⟩
  have eligible := admitted_input_indexed_pruned w keepTrace claimBytes loaded decoded noCollision
    closure selected record retained
  have scanned : (owner, constant) ∈ indexedRecords target input
      (w.prelude.records ++ w.prelude.evidence) := by
    simp only [indexedRecords, Array.mem_append, Array.mem_filter]
    exact .inl ⟨present, eligible⟩
  obtain ⟨entry, carriers, _, analysis⟩ := admitted_analysis_survives w keepTrace claimBytes loaded
    decoded noCollision closure selected record retained member
  exact buildIndex_ref_covered target _ scanned member analysis

end IxVM.Refinement.Assembly.ReaderStoreTransfer
