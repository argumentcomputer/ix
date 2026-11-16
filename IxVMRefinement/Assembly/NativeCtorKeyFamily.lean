import IxVMRefinement.Assembly.NativeReaderKeys
import IxVMRefinement.Assembly.NativeCtorReads

/-! # Constructor member-key families from actual hashes

The native loop contributes every constructor projection hash. Authentic reader resolution and
lookup transport then give the Source role-table key for every actual reader constructor row.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- All constructor member keys are fixed by the actual native-loop hashes and reader rows. -/
theorem native_ctor_member_keys {base : Core.Ctx} {cx : Ix.Kernel.Reader.Ctx .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {constants : List (_root_.Address × Ixon.Constant)}
    {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : Ix.Kernel.ConstRef _root_.Address → Option Ix.Kernel.ReducibilityHint}
    (context : cx = Ix.Kernel.Admission.streamContext _root_.Address.admissionHash
      base.t pre constants blobs hint)
    (authentic : AuthenticExactStore cx.store) (tableChecked : base.t.check = .ok ())
    (boundStored : ∀ role address, (role, address) ∈ base.t.bound.toList → ∃ value, cx.store address = some value)
    (transport : ∀ address value, cx.store address = some value → Ix.Cert.recordAt base.E address = some value)
    (decoded : L1.EnvDecoded base.E)
    {block : Bytes.Address} {i : F} (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (parentStored : cx.store (Core.ixAddr block) = some source.value)
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)} {rows : List NativeCtorRow}
    (frames : List.Forall₂ (NativeCtorReaderCheckedFrame cx (Core.ixAddr block)
      (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self))
      (nativeCtorSlots [(ZMod.val i, ind)]) rows)
    {params indices levels : Nat} {rootCalls loopCalls : List (Call F)}
    (countBound : ind.ctors.size < 549755813888) (good : Core.Good base rootCalls)
    {rc former bp sortLevel result : SourceValue F} {h h' : Heap F}
    (blockRep : Bytes.RepAddressRef Core.addrTy h block bp)
    (subset : ∀ call ∈ loopCalls, call ∈ rootCalls)
    (loop : ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
      [rc, former, .field (params : F), .field (indices : F), .field (ind.ctors.size : F),
        .field (levels : F), bp, .field i, sortLevel, .field 0, .field 0] h result h' loopCalls) :
    ∀ j < ind.ctors.size, cx.memberKey (.ctor (Core.ixAddr block) (ZMod.val i) j) =
      .ok (base.κ (Core.cprjAddr (Core.ixAddr block) (ZMod.val i) j)) := by
  subst cx
  have rowLength : rows.length = ind.ctors.size := by
    simpa [nativeCtorSlots] using frames.length_eq.symm
  have memberArray : members[ZMod.val i]? = some (.indc ind) := by
    simpa only [Array.getElem?_toList] using memberAt
  let hashContext : Core.ScopedCtx := { toCtx := base, allowed := fun _ => False }
  have hashes := native_ctor_projection_hashes hashContext countBound ind.ctors.size 0 (by omega)
    blockRep subset loop
  intro j bound
  have rowBound : j < rows.length := by simpa only [rowLength] using bound
  let ctor := ind.ctors[j]
  have ctorAt : ind.ctors[j]? = some ctor := by simp [ctor, bound]
  have frameAt := (List.forall₂_iff_get.mp frames).2 j
    (by simpa [nativeCtorSlots] using bound) rowBound
  have ctorIndex : ctor.cidx.toNat = j := by
    simpa [nativeCtorSlots, ctor] using frameAt.2.1
  have hash : Hashed rootCalls (Ixon.serConstant
      (IxVM.Consistency.constructorProjection (Core.ixAddr block) (ZMod.val i) j)) := by
    simpa only [Nat.zero_add] using hashes j bound
  have memberBound : ZMod.val i < UInt64.size := Nat.lt_trans (ZMod.val_lt i) (by decide)
  have ctorBound : j < UInt64.size := Nat.lt_trans bound (Nat.lt_trans countBound (by decide))
  exact streamContext_memberKey_cprj_of_hash authentic tableChecked parentStored blockShape
    memberArray ctorAt ctorIndex memberBound ctorBound boundStored decoded good.1 hash transport

end IxVM.Refinement.Assembly
