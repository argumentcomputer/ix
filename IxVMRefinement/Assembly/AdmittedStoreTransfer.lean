import IxVMRefinement.Assembly.AdmittedReaderStore
import IxVMRefinement.Assembly.ReaderSupport
import Ix.Cert.EvidenceTransfer

/-! # Lookup transport into the selected admitted reader store

Selected admission rows retain their exact decoded value. Fallback rows remain available
at every selected order because overlapping input and fallback records decode identically
in the concrete core store. Used-reference closure then supplies local lookup transport.
-/

namespace IxVM.Refinement.Assembly.ReaderStoreTransfer

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency
open Ix.Cert.EvidenceCheck (fallbackStore)
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

abbrev store (table : RoleTable) (prelude : Prelude .anon) (env : Ixon.Env)
    (order : List _root_.Address) : Store :=
  (Admission.streamContext _root_.Address.admissionHash table prelude
    (Ix.Cert.Stream.decodedOf env order) (Ix.Cert.blobsOf env order)
    (Ix.Cert.hintsOf env)).store

theorem lookup (table : RoleTable) (prelude : Prelude .anon) (env : Ixon.Env)
    (order : List _root_.Address) (a : _root_.Address) :
    store table prelude env order a =
      ((if a ∈ order then Ix.Cert.recordAt env a else none) <|> fallbackStore prelude a) := by
  change ((recordMap (Ix.Cert.Stream.decodedOf env order).toArray)[a]? <|>
    ((recordMap (prelude.records ++ prelude.evidence))[a]? <|> none)) = _
  rw [Ix.Cert.ReaderClosureKeys.recordMap_get, List.toList_toArray,
    Ix.Cert.EvidenceTransfer.decodedOf_lookup]
  simp [fallbackStore]

theorem selected {table : RoleTable} {prelude : Prelude .anon} {env : Ixon.Env}
    {order : List _root_.Address} {a : _root_.Address} {c : Ixon.Constant}
    (present : a ∈ order) (record : Ix.Cert.recordAt env a = some c) :
    store table prelude env order a = some c := by
  rw [lookup]
  simp only [present, ↓reduceIte, record, Option.orElse_some]

theorem fallback_of_mem {table : RoleTable} {prelude : Prelude .anon}
    (prepared : preludeFor table = .ok prelude) {a : _root_.Address} {c : Ixon.Constant}
    (present : (a, c) ∈ prelude.records ++ prelude.evidence) :
    fallbackStore prelude a = some c := by
  unfold fallbackStore
  rw [Ix.Cert.ReaderClosureKeys.recordMap_get]
  exact Ix.Cert.ReaderClosureKeys.lookup_of_nodup
    (Ix.Cert.ReaderFallback.preludeFor_keys prepared) (Array.mem_toList_iff.mpr present)

/-- The concrete fallback is preserved for every selected reading order. Overlap agreement
is derived from the common decoded core store, not imposed as a new global premise. -/
theorem admitted_fallback {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) (order : List _root_.Address)
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: b.bytes :: readerImages V) calls)
    {a : _root_.Address} {c : Ixon.Constant} (found : fallbackStore w.prelude a = some c) :
    store w.table w.prelude (admittedOverlay w trace keepTrace) order a = some c := by
  have fallbackCore := admittedCore_fallback w keepTrace claimBytes loaded decoded noCollision
    (Array.mem_toList_iff.mp (Ix.Cert.EvidenceCheck.fallbackStore_mem found))
  rw [lookup]
  by_cases present : a ∈ order
  · simp only [present, ↓reduceIte]
    cases input : Ix.Cert.recordAt (admittedOverlay w trace keepTrace) a with
    | none => simp only [Option.orElse_none, found]
    | some value =>
      have inputCore := admittedCore_of_overlay w input
      have same := Option.some.inj (inputCore.symm.trans fallbackCore)
      simp only [Option.orElse_some, same]
  · simp only [present, ↓reduceIte, Option.orElse_none, found]

/-- At an address selected by the new reading, every old admitted-store answer survives. -/
theorem admitted_selected {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) (order : List _root_.Address)
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: b.bytes :: readerImages V) calls)
    {a : _root_.Address} (present : a ∈ order) {c : Ixon.Constant}
    (found : store w.table w.prelude w.env w.order a = some c) :
    store w.table w.prelude (admittedOverlay w trace keepTrace) order a = some c := by
  rcases streamContext_store_mem found with input | fallback
  · have original := Ix.Cert.RecursorIndex.mem_decoded.mp (Array.mem_toList_iff.mp input)
    exact selected present
      (admittedOverlay_recordAt w keepTrace loaded decoded noCollision original.1 original.2)
  · exact admitted_fallback w keepTrace claimBytes order loaded decoded noCollision
      (fallback_of_mem w.preludeRead fallback)

/-- A used reference of a retained raw record is kept whenever the old admitted reader
could look it up. References supplied only by the committed fallback need no input row. -/
theorem admitted_used_reference {V : IxVM.Refinement.View} {b : Admission.Binding}
    (w : ReaderAdmissionWitness V b) {calls : List (Call F)} {trace : Ixon.Env}
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray) {order : List _root_.Address}
    (loaded : LoadedBy calls trace) (decoded : L1.EnvDecoded trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: b.bytes :: readerImages V) calls)
    {seeds : _root_.Address → Prop}
    (closure : UsedClosureOrderAt w.table (admittedOverlay w trace keepTrace) seeds order)
    {owner a : _root_.Address} {record value : Ixon.Constant}
    (retained : owner ∈ order)
    (stored : Ix.Cert.recordAt (admittedOverlay w trace keepTrace) owner = some record)
    {i : Nat} (used : i ∈ usedRefIdxs record) (reference : record.refs[i]? = some a)
    (found : store w.table w.prelude w.env w.order a = some value) :
    store w.table w.prelude (admittedOverlay w trace keepTrace) order a = some value := by
  rcases streamContext_store_mem found with input | fallback
  · have original := Ix.Cert.RecursorIndex.mem_decoded.mp (Array.mem_toList_iff.mp input)
    have recordAt := admittedOverlay_recordAt w keepTrace loaded decoded noCollision
      original.1 original.2
    have present := readOrder_ref closure retained stored used reference (contains_of_recordAt recordAt)
    exact selected present recordAt
  · exact admitted_fallback w keepTrace claimBytes order loaded decoded noCollision
      (fallback_of_mem w.preludeRead fallback)

end IxVM.Refinement.Assembly.ReaderStoreTransfer
