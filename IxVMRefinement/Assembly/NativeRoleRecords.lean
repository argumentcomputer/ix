import IxVMRefinement.Assembly.AdmittedReaderStore
import IxVMRefinement.Assembly.AdmittedKeys
import IxVMRefinement.Assembly.RawQueryCoverage

/-! # Actual role records for native naming

A non-trust bound address is a seed of the admitted role order. Actual hash/decode evidence
identifies its record there using the witness's selected byte footprint. The original role
reader's lookups also embed into the complete core metadata store.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

/-- Every non-compiler-trust bound address is selected and physically stored by admission. -/
theorem admitted_bound_record_selected {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : ReaderAdmissionWitness V binding) {role : Role} {address : _root_.Address}
    (bound : (role, address) ∈ witness.table.bound.toList)
    (notTrust : IxVM.Refinement.compilerTrust role = false) :
    address ∈ witness.order ∧ ∃ entry, witness.env.consts.get? address = some entry := by
  have seed : IxVM.Refinement.BindingSeeds witness.table address := .inl ⟨role, notTrust,
    Ix.Cert.ReadingKeys.addressOf_of_bound (check_of_admitBinding witness.admitted) bound⟩
  have held := witness.seedsStored address seed
  have selected := (witness.closure.complete address).mpr (.seed seed held)
  rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?] at held
  exact ⟨selected, Option.isSome_iff_exists.mp held⟩

/-- The actual bytes hashed at a bound non-trust address identify its selected admitted
record. This constructs cache agreement from the real selected view footprint. -/
theorem admitted_bound_record_of_hashed {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : ReaderAdmissionWitness V binding) {calls : List (Call F)} {extra : List ByteArray}
    (noCollision : ¬ V.HashedCollision extra calls)
    {role : Role} {address : _root_.Address} {bytes : ByteArray} {value : Ixon.Constant}
    (bound : (role, address) ∈ witness.table.bound.toList)
    (notTrust : IxVM.Refinement.compilerTrust role = false)
    (hashed : Hashed calls bytes) (hashEq : Address.blake3Pure bytes = address)
    (decoded : Ixon.deConstantExact bytes = .ok value) :
    address ∈ witness.order ∧ Ix.Cert.recordAt witness.env address = some value := by
  obtain ⟨selected, entry, found⟩ := admitted_bound_record_selected witness bound notTrust
  obtain ⟨held, heldAt, heldBytes⟩ := witness.selectedRecordsInView address selected entry found
  have preimage : V.Preimage address entry.rawBytes := .inl ⟨held, heldAt, heldBytes⟩
  have same : bytes = entry.rawBytes := by
    by_contra different
    exact noCollision (.inl ⟨address, entry.rawBytes, bytes, .inl preimage, hashed, different, hashEq⟩)
  have cached : entry.get? = some value := by
    rw [witness.coherent address entry found, ← same, decoded]
    rfl
  refine ⟨selected, ?_⟩
  unfold Ix.Cert.recordAt
  rw [found]
  exact cached

/-- Every actual original role-reader lookup has the same decoded value in the complete
core metadata store, including its committed fallback entries. -/
theorem admitted_role_reader_sub_core {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : ReaderAdmissionWitness V binding) {calls : List (Call F)} {trace : Ixon.Env}
    {seeds : List _root_.Address} (phase : Claim.WalkedL6 calls witness.table trace seeds)
    (keepTrace : _root_.Address → Prop) (claimBytes : ByteArray)
    (loaded : LoadedBy calls trace)
    (noCollision : ¬ V.HashedCollision (claimBytes :: binding.bytes :: readerImages V) calls)
    {address : _root_.Address} {value : Ixon.Constant}
    (read : (ReaderStoreTransfer.readerContext witness.table witness.prelude witness.env witness.order).store
      address = some value) :
    Ix.Cert.recordAt (admittedCore witness trace keepTrace) address = some value := by
  rcases streamContext_store_mem read with input | fallback
  · obtain ⟨actualAddress, selected, mapped⟩ := List.mem_filterMap.mp input
    obtain ⟨actualValue, record, same⟩ := Option.map_eq_some_iff.mp mapped
    cases same
    exact admittedCore_of_overlay witness
      (admittedOverlay_recordAt witness keepTrace loaded (walked_envDecoded phase) noCollision selected record)
  · exact admittedCore_fallback witness keepTrace claimBytes loaded (walked_envDecoded phase) noCollision fallback

end IxVM.Refinement.Assembly
