import IxVMRefinement.Assembly.NativeRoleKeys
import IxVMRefinement.Assembly.AdmittedFallbackRecords

/-! # Actual parent records of bound projections

Successful projection resolution has read a mutual parent from the same context. The original
admitted reader supplies that parent either from its selected input or its committed prelude.
This identifies the two concrete branches needed by the role-prefix name argument.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

/-- Successful resolution of a projection reads a mutual parent at its encoded owner. -/
theorem resolveSource_projection_parent {store : Store} {address : _root_.Address}
    {value : Ixon.Constant} {target : ConstRef _root_.Address}
    (projection : IsProjInfo value.info) (resolved : resolveSource store address value = some target) :
    ∃ parent members, store (Ix.Cert.ownerOf address value) = some parent ∧ parent.info = .muts members := by
  cases kind : value.info <;> simp only [IsProjInfo, kind] at projection
  all_goals
    unfold resolveSource at resolved
    rw [kind] at resolved
    simp only [Option.bind_eq_bind] at resolved
    obtain ⟨_, _, resolved⟩ := Option.bind_eq_some_iff.mp resolved
    obtain ⟨parent, stored, rest⟩ := Option.bind_eq_some_iff.mp resolved
    refine ⟨parent, ?_⟩
    cases parentKind : parent.info with
    | muts members => exact ⟨members, by simpa only [Ix.Cert.ownerOf, kind] using stored, parentKind⟩
    | _ => simp [parentKind] at rest

/-- The committed evidence entries are definitions, so a fallback mutual record belongs
to the prelude-record portion. -/
theorem fallback_muts_in_prelude {table : RoleTable} {prelude : Prelude .anon}
    (prepared : preludeFor table = .ok prelude)
    {address : _root_.Address} {value : Ixon.Constant} {members : Array Ixon.MutConst}
    (present : (address, value) ∈ prelude.records ++ prelude.evidence)
    (kind : value.info = .muts members) : (address, value) ∈ prelude.records := by
  rcases Array.mem_append.mp present with inPrelude | inEvidence
  · exact inPrelude
  · obtain ⟨_, evidenceRead⟩ := Ix.Cert.ReaderFallback.preludeFor_records prepared
    obtain ⟨evidence, read, _, definitions⟩ := RoleVal.evidenceRecords_spec
    have same : prelude.evidence = evidence := Except.ok.inj (evidenceRead.symm.trans read)
    rw [same] at inEvidence
    obtain ⟨definition, info⟩ := definitions (address, value) (Array.mem_toList_iff.mpr inEvidence)
    change value.info = .defn definition at info
    rw [kind] at info
    cases info

/-- Actual bound projection bytes expose their parent's concrete selected-input or prelude
origin. No assumption that the parent was emitted by the input stream is made. -/
theorem admitted_bound_projection_parent {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : ReaderAdmissionWitness V binding) {calls : List (Call F)} {extra : List ByteArray}
    (noCollision : ¬ V.HashedCollision extra calls)
    {role : Role} {address : _root_.Address} {bytes : ByteArray} {value : Ixon.Constant}
    {layout : Egress.ProjectionLayout} {target : ConstRef _root_.Address}
    (bound : (role, address) ∈ witness.table.bound.toList)
    (notTrust : IxVM.Refinement.compilerTrust role = false)
    (hashed : Hashed calls bytes) (hashEq : Address.blake3Pure bytes = address)
    (decoded : Ixon.deConstantExact bytes = .ok value)
    (projection : Egress.ProjectionReads value layout target) :
    ∃ parent members,
      (ReaderStoreTransfer.readerContext witness.table witness.prelude witness.env witness.order).store
        target.block = some parent ∧ parent.info = .muts members ∧
      ((target.block ∈ witness.order ∧ Ix.Cert.recordAt witness.env target.block = some parent) ∨
        (target.block, parent) ∈ witness.prelude.records) := by
  let cx := ReaderStoreTransfer.readerContext witness.table witness.prelude witness.env witness.order
  obtain ⟨selected, record⟩ := admitted_bound_record_of_hashed witness noCollision bound notTrust hashed hashEq decoded
  have resolved := admitted_bound_projection_target witness noCollision bound notTrust hashed hashEq decoded projection
  have stored : cx.store address = some value :=
    ReaderStoreTransfer.selected (table := witness.table) (prelude := witness.prelude) selected record
  have sourceRead : resolveSource cx.store address value = some target := by
    have direct := resolved
    change resolve cx.store address = some target at direct
    unfold resolve at direct
    rw [stored] at direct
    exact direct
  have isProjection : IsProjInfo value.info := by cases projection <;> trivial
  obtain ⟨parent, members, parentAt, parentKind⟩ := resolveSource_projection_parent isProjection sourceRead
  have ownerEq : Ix.Cert.ownerOf address value = target.block := by cases projection <;> rfl
  rw [ownerEq] at parentAt
  refine ⟨parent, members, parentAt, parentKind, ?_⟩
  rcases streamContext_store_mem parentAt with input | fallback
  · obtain ⟨actualAddress, parentSelected, mapped⟩ := List.mem_filterMap.mp input
    obtain ⟨actualValue, parentRecord, same⟩ := Option.map_eq_some_iff.mp mapped
    have addressEq : actualAddress = target.block := congrArg Prod.fst same
    have valueEq : actualValue = parent := congrArg Prod.snd same
    subst actualAddress actualValue
    exact .inl ⟨parentSelected, parentRecord⟩
  · exact .inr (fallback_muts_in_prelude witness.preludeRead fallback parentKind)

end IxVM.Refinement.Assembly
