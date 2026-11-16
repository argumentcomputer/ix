import IxVMRefinement.Assembly.AdmittedReaderStore
import IxVMRefinement.Assembly.AdmittedKeys
import IxVMRefinement.Assembly.RawQueryCoverage
import Ix.Cert.RecursorIndex

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

/-- An actual successful projection-record read has a resolving target in the same store. -/
theorem readRecord_projection_resolves {cx : Ctx .anon} {state : State .anon}
    {address : _root_.Address} {value : Ixon.Constant} {result : Read .anon}
    (read : readRecord cx state address value = .ok result)
    (projection : IsProjInfo value.info) (stored : cx.store address = some value) :
    ∃ target, resolve cx.store address = some target := by
  cases kind : value.info <;> simp only [IsProjInfo, kind] at projection
  all_goals
    simp only [readRecord, kind] at read
    rcases Ix.Cert.CtxAgree.ite_ok' read with ⟨_, rejected⟩ | ⟨available, _⟩
    · exact (Ix.Cert.ReaderUnits.throw_ok rejected).elim
    · cases resolved : resolveSource cx.store address value with
      | none => simp [resolved] at available
      | some target =>
        refine ⟨target, ?_⟩
        unfold resolve
        rw [stored]
        exact resolved

/-- A selected admitted projection was actually read, so its target resolves in the original
role reader context. This uses the real projection guard, not merely cached record presence. -/
theorem admitted_projection_resolves {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : ReaderAdmissionWitness V binding) {address : _root_.Address} {value : Ixon.Constant}
    (selected : address ∈ witness.order) (record : Ix.Cert.recordAt witness.env address = some value)
    (projection : IsProjInfo value.info) :
    ∃ target, resolve
      (ReaderStoreTransfer.readerContext witness.table witness.prelude witness.env witness.order).store
        address = some target := by
  have decoded : (address, value) ∈ (Ix.Cert.Stream.decodedOf witness.env witness.order).toArray :=
    Ix.Cert.RecursorIndex.mem_decoded.mpr ⟨selected, record⟩
  obtain ⟨state, result, read, _⟩ := (readRecords_spec witness.read).mem (Array.mem_toList_iff.mpr decoded)
  have stored :
      (ReaderStoreTransfer.readerContext witness.table witness.prelude witness.env witness.order).store
        address = some value :=
    ReaderStoreTransfer.selected (table := witness.table) (prelude := witness.prelude) selected record
  exact readRecord_projection_resolves read projection stored

/-- Actual bound-address bytes and the admitted projection guard supply both exact record
identity and original-context resolution for a non-trust bound projection. -/
theorem admitted_bound_projection_resolves {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : ReaderAdmissionWitness V binding) {calls : List (Call F)} {extra : List ByteArray}
    (noCollision : ¬ V.HashedCollision extra calls)
    {role : Role} {address : _root_.Address} {bytes : ByteArray} {value : Ixon.Constant}
    (bound : (role, address) ∈ witness.table.bound.toList)
    (notTrust : IxVM.Refinement.compilerTrust role = false)
    (hashed : Hashed calls bytes) (hashEq : Address.blake3Pure bytes = address)
    (decoded : Ixon.deConstantExact bytes = .ok value) (projection : IsProjInfo value.info) :
    address ∈ witness.order ∧ Ix.Cert.recordAt witness.env address = some value ∧
      ∃ target, resolve
        (ReaderStoreTransfer.readerContext witness.table witness.prelude witness.env witness.order).store
          address = some target := by
  obtain ⟨selected, record⟩ := admitted_bound_record_of_hashed witness noCollision bound notTrust hashed hashEq decoded
  exact ⟨selected, record, admitted_projection_resolves witness selected record projection⟩


/-- A non-trust bound projection selects its owning block in the admitted role closure.
This follows from the actual projected record and the ordinary owner edge. -/
theorem admitted_bound_projection_owner_selected {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : ReaderAdmissionWitness V binding) {calls : List (Call F)} {extra : List ByteArray}
    (noCollision : ¬ V.HashedCollision extra calls)
    {role : Role} {address : _root_.Address} {bytes : ByteArray} {value : Ixon.Constant}
    {layout : Egress.ProjectionLayout} {target : ConstRef _root_.Address}
    (bound : (role, address) ∈ witness.table.bound.toList)
    (notTrust : IxVM.Refinement.compilerTrust role = false)
    (hashed : Hashed calls bytes) (hashEq : Address.blake3Pure bytes = address)
    (decoded : Ixon.deConstantExact bytes = .ok value)
    (projection : Egress.ProjectionReads value layout target) : target.block ∈ witness.order := by
  obtain ⟨selected, record⟩ := admitted_bound_record_of_hashed witness noCollision bound notTrust hashed hashEq decoded
  have ownerEq : Ix.Cert.ownerOf address value = target.block := by cases projection <;> rfl
  by_cases same : target.block = address
  · rwa [same]
  · apply (witness.closure.complete target.block).mpr
    exact .step ((witness.closure.complete address).mp selected) ⟨value, record, .inl ⟨ownerEq, same⟩⟩


/-- For an owner outside the admitted role closure, any binding of its actual hashed
projection must be one of the explicitly excluded compiler-trust roles. -/
theorem new_owner_projection_bound_is_compilerTrust {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : ReaderAdmissionWitness V binding) {calls : List (Call F)} {extra : List ByteArray}
    (noCollision : ¬ V.HashedCollision extra calls)
    {role : Role} {address : _root_.Address} {bytes : ByteArray} {value : Ixon.Constant}
    {layout : Egress.ProjectionLayout} {target : ConstRef _root_.Address}
    (newOwner : target.block ∉ witness.order)
    (bound : (role, address) ∈ witness.table.bound.toList)
    (hashed : Hashed calls bytes) (hashEq : Address.blake3Pure bytes = address)
    (decoded : Ixon.deConstantExact bytes = .ok value)
    (projection : Egress.ProjectionReads value layout target) :
    IxVM.Refinement.compilerTrust role = true := by
  cases trusted : IxVM.Refinement.compilerTrust role with
  | true => rfl
  | false =>
    exact (newOwner (admitted_bound_projection_owner_selected witness noCollision bound trusted
      hashed hashEq decoded projection)).elim


end IxVM.Refinement.Assembly
