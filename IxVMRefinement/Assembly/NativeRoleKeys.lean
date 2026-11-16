import IxVMRefinement.Assembly.NativeRoleRecords
import IxVMRefinement.Assembly.NativeMemberKeys
import Ix.Cert.InductiveSegments

/-! # Constructed keys for actual bound native projections

The original admitted reader checked each selected projection record. Its actual resolution
has the target encoded by those bytes, and the admitted role binding gives that target the
same key as the core context. No global member-key correspondence is assumed.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

/-- Actual admitted projection reading resolves to the reference encoded by the projection. -/
theorem admitted_bound_projection_target {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : ReaderAdmissionWitness V binding) {calls : List (Call F)} {extra : List ByteArray}
    (noCollision : ¬ V.HashedCollision extra calls)
    {role : Role} {address : _root_.Address} {bytes : ByteArray} {value : Ixon.Constant}
    {layout : Egress.ProjectionLayout} {target : ConstRef _root_.Address}
    (bound : (role, address) ∈ witness.table.bound.toList)
    (notTrust : IxVM.Refinement.compilerTrust role = false)
    (hashed : Hashed calls bytes) (hashEq : Address.blake3Pure bytes = address)
    (decoded : Ixon.deConstantExact bytes = .ok value)
    (projection : Egress.ProjectionReads value layout target) :
    resolve (ReaderStoreTransfer.readerContext witness.table witness.prelude witness.env witness.order).store
      address = some target := by
  have isProjection : IsProjInfo value.info := by cases projection <;> trivial
  obtain ⟨selected, record, actual, resolved⟩ :=
    admitted_bound_projection_resolves witness noCollision bound notTrust hashed hashEq decoded isProjection
  let cx := ReaderStoreTransfer.readerContext witness.table witness.prelude witness.env witness.order
  have stored : cx.store address = some value :=
    ReaderStoreTransfer.selected (table := witness.table) (prelude := witness.prelude) selected record
  have sourceRead : resolveSource cx.store address value = some actual := by
    simpa only [resolve, stored, Option.bind_some] using resolved
  have same : actual = target := by
    cases projection with
    | definition p => exact Ix.Cert.DefinitionSegments.resolveSource_dPrj rfl sourceRead
    | inductive p => exact Ix.Cert.InductiveSegments.resolveSource_iPrj rfl sourceRead
    | recursor p => exact Ix.Cert.InductiveSegments.resolveSource_rPrj rfl sourceRead
    | constructor p => exact Ix.Cert.InductiveSegments.resolveSource_cPrj rfl sourceRead
  rwa [same] at resolved

/-- A real non-trust bound projection gets its actual core key in the original admitted
role reader. The successful lookup and local binding evidence are constructed here. -/
theorem admitted_bound_projection_key {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : ReaderAdmissionWitness V binding) {calls : List (Call F)} {extra : List ByteArray}
    (noCollision : ¬ V.HashedCollision extra calls)
    {role : Role} {address : _root_.Address} {bytes : ByteArray} {value : Ixon.Constant}
    {layout : Egress.ProjectionLayout} {target : ConstRef _root_.Address}
    (bound : (role, address) ∈ witness.table.bound.toList)
    (notTrust : IxVM.Refinement.compilerTrust role = false)
    (hashed : Hashed calls bytes) (hashEq : Address.blake3Pure bytes = address)
    (decoded : Ixon.deConstantExact bytes = .ok value)
    (projection : Egress.ProjectionReads value layout target) :
    (ReaderStoreTransfer.readerContext witness.table witness.prelude witness.env witness.order).memberKey target =
      .ok (Core.keyOf witness.table address) := by
  let cx := ReaderStoreTransfer.readerContext witness.table witness.prelude witness.env witness.order
  have resolved := admitted_bound_projection_target witness noCollision bound notTrust hashed hashEq decoded projection
  have authentic := admitted_streamStore_authentic witness
  have checked := check_of_admitBinding witness.admitted
  have unique : ∀ other, resolve cx.store other = some target → other = address :=
    fun _ found => authentic.resolve_inj resolved found
  have named : cx.roles.names[target]? = some (.role role) :=
    Ix.Cert.ReadingKeys.bindings_bound checked bound resolved unique
  rw [Ctx.memberKey_of_role named, keyOf_eq_of_bound checked bound]

end IxVM.Refinement.Assembly
