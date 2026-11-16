import IxVMRefinement.Assembly.NativeMemberKeys
import IxVMRefinement.Assembly.NativeFormerReader
import IxVMRefinement.Assembly.NativeOuter

/-! # Native declared names at local reader projections

Expression self references and emitted declaration headers have separate naming obligations.
These lemmas connect an actual former or constructor row to its core key using resolution at
that row's own bound projection, without asserting coverage of other implicit names.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open Ix.Kernel.Reader

/-- The produced former annotation stores the actual reader row once its own local member
key is identified. The annotation and binder data remain exactly those already produced. -/
theorem NativeFormerRunInput.stored_reader_row {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : L1.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {row : NativeFormerRow} {calls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind row.1.type calls)
    {cx : Ctx .anon} {prelude : Prelude .anon} {constants : List (_root_.Address × Ixon.Constant)}
    {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : Ix.Kernel.ConstRef _root_.Address → Option Ix.Kernel.ReducibilityHint}
    (context : cx = Ix.Kernel.Admission.streamContext _root_.Address.admissionHash base.t prelude constants blobs hint)
    (authentic : AuthenticExactStore cx.store) (checked : base.t.check = .ok ())
    (stored : cx.store (Core.ixAddr block) = some source.value)
    {mr : MemberReader .anon}
    (frame : NativeFormerReaderFrame cx (Core.ixAddr block) mr (ZMod.val i, ind) row)
    (boundResolved : ∀ role,
      (role, Core.iprjAddr (Core.ixAddr block) (ZMod.val i)) ∈ base.t.bound.toList →
      resolve cx.store (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)) =
        some (.member (Core.ixAddr block) (ZMod.val i))) :
    IxVM.Consistency.ValStored input.annotated row.1 := by
  have memberAt : members[ZMod.val i]? = some (.indc ind) := by
    simpa only [Array.getElem?_toList] using input.memberAt
  have bound : ZMod.val i < UInt64.size := Nat.lt_trans (ZMod.val_lt i) (by decide)
  have named : cx.memberKey (.member (Core.ixAddr block) (ZMod.val i)) =
      .ok (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) :=
    streamContext_memberKey_member_of_local_resolution context authentic checked stored
      input.blockShape memberAt bound boundResolved
  have rowName := Except.ok.inj (frame.1.symm.trans named)
  exact ⟨input.stored.1.trans rowName.symm, input.stored.2.1.trans frame.2.2.1.symm, input.stored.2.2⟩

/-- One actual constructor row has its core key under its own local bound-resolution fact. -/
theorem NativeCtorReaderFrame.name_of_local_resolution {cx : Ctx .anon} {owner : _root_.Address}
    {mr : MemberReader .anon} {slot : NativeCtorSlot} {row : NativeCtorRow}
    (frame : NativeCtorReaderFrame cx owner mr slot row)
    {table : Ix.Kernel.RoleTable} {prelude : Prelude .anon}
    {constants : List (_root_.Address × Ixon.Constant)} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : Ix.Kernel.ConstRef _root_.Address → Option Ix.Kernel.ReducibilityHint}
    (context : cx = Ix.Kernel.Admission.streamContext _root_.Address.admissionHash table prelude constants blobs hint)
    (authentic : AuthenticExactStore cx.store) (checked : table.check = .ok ())
    (memberBound : slot.1 < UInt64.size) (ctorBound : slot.2.2 < UInt64.size)
    (boundResolved : ∀ role, (role, Core.cprjAddr owner slot.1 slot.2.2) ∈ table.bound.toList →
      resolve cx.store (Core.cprjAddr owner slot.1 slot.2.2) = some (.ctor owner slot.1 slot.2.2)) :
    row.1.name = Core.keyOf table (Core.cprjAddr owner slot.1 slot.2.2) := by
  have named := streamContext_ctor_key_of_local_resolution context authentic checked memberBound ctorBound boundResolved
  exact Except.ok.inj (frame.1.symm.trans named)

end IxVM.Refinement.Assembly
