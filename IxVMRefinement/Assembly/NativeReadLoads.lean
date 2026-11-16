import IxVMRefinement.Assembly.NativeFormerLoads
import IxVMRefinement.Assembly.NativeFormerReader
import IxVMRefinement.Assembly.NativeOuter

/-! # Current-former load branches from actual reader origins

The produced former input retains its first annotation trace. Its actual reader row supplies
the original expression read, so selected repeated loads agree with the former installed at
the constructor stage. These branches do not use unrestricted load compatibility assumptions.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- The actual reader row and produced input supply a selected direct reload of the current former. -/
theorem NativeFormerRunInput.getIprj_current_of_blobAgreement {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : L1.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {row : NativeFormerRow} {rootCalls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind row.1.type rootCalls)
    {parts : Ix.Kernel.InductiveShape .anon} {isRec : Bool}
    (runs : List (Decl.NativeCtorCoreRun rootCalls))
    {cx : Ix.Kernel.Reader.Ctx .anon} {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    (frame : NativeFormerReaderFrame cx (Core.ixAddr block)
      (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self) (ZMod.val i, ind) row)
    {bp ptr : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (loaded : ObsFn Core.W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' calls)
    (good : Core.CoreGood (Decl.nativeCtorCoreCtx (input.stageCtx parts isRec) runs) calls)
    (allowed : (Decl.nativeCtorCoreCtx (input.stageCtx parts isRec) runs).allowedTop
      "Ingress::get_ci_iprj" [bp, .field i] h)
    (blockRep : Bytes.RepAddressRef Core.addrTy h block bp)
    (keyed : ∀ address key, cx.keyAt address = .ok key → key = base.κ address)
    (selfKeyed : ∀ index address reading key,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      self index = some reading → reading = .ok key → key = base.κ address)
    (blobReads : L1.HashedBlobReadAgreement cx.blob rootCalls) :
    ∃ ci, (input.stageCtx parts isRec).env.find?
      (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) = some ci ∧ Core.CIPtrRep base.κ h' ptr ci := by
  exact native_former_reload_scoped_staged_of_blobAgreement (base := { base with lim := some input.limit })
    source input.blockShape input.memberAt input.stored input.built input.planned input.image
    frame.2.1 input.varsBounded input.levelsDefined runs (Ix.Kernel.nativeCapsAt parts isRec)
    loaded good allowed blockRep keyed selfKeyed blobReads

/-- Compatibility with full observed-blob membership. -/
theorem NativeFormerRunInput.getIprj_current {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : L1.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {row : NativeFormerRow} {rootCalls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind row.1.type rootCalls)
    {parts : Ix.Kernel.InductiveShape .anon} {isRec : Bool}
    (runs : List (Decl.NativeCtorCoreRun rootCalls))
    {cx : Ix.Kernel.Reader.Ctx .anon} {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    (frame : NativeFormerReaderFrame cx (Core.ixAddr block)
      (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self) (ZMod.val i, ind) row)
    {bp ptr : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (loaded : ObsFn Core.W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' calls)
    (good : Core.CoreGood (Decl.nativeCtorCoreCtx (input.stageCtx parts isRec) runs) calls)
    (allowed : (Decl.nativeCtorCoreCtx (input.stageCtx parts isRec) runs).allowedTop
      "Ingress::get_ci_iprj" [bp, .field i] h)
    (blockRep : Bytes.RepAddressRef Core.addrTy h block bp)
    (keyed : ∀ address key, cx.keyAt address = .ok key → key = base.κ address)
    (selfKeyed : ∀ index address reading key,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      self index = some reading → reading = .ok key → key = base.κ address)
    (blobReads : ∀ address bytes, Hashed rootCalls bytes → Address.blake3Pure bytes = address →
      cx.blob address = some bytes) :
    ∃ ci, (input.stageCtx parts isRec).env.find?
      (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) = some ci ∧ Core.CIPtrRep base.κ h' ptr ci := by
  exact NativeFormerRunInput.getIprj_current_of_blobAgreement input runs frame loaded good allowed
    blockRep keyed selfKeyed (L1.HashedBlobReadAgreement.of_stored blobReads)

/-- A selected get_ci of the current former reduces to its actual direct projection subcall.
The canonical projection source and role-table injectivity identify the target. -/
theorem NativeFormerRunInput.getCI_current_of_blobAgreement {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : L1.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {row : NativeFormerRow} {rootCalls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind row.1.type rootCalls)
    {parts : Ix.Kernel.InductiveShape .anon} {isRec : Bool}
    (runs : List (Decl.NativeCtorCoreRun rootCalls)) (tableWf : base.t.wf = true)
    {cx : Ix.Kernel.Reader.Ctx .anon} {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    (frame : NativeFormerReaderFrame cx (Core.ixAddr block)
      (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self) (ZMod.val i, ind) row)
    {ap ptr : SourceValue F} {h h' : Heap F} {calls : List (Call F)} {address : Bytes.Address}
    (loaded : ObsFn Core.W "Ingress::get_ci" [ap] h ptr h' calls)
    (good : Core.CoreGood (Decl.nativeCtorCoreCtx (input.stageCtx parts isRec) runs) calls)
    (_allowed : (Decl.nativeCtorCoreCtx (input.stageCtx parts isRec) runs).allowedTop "Ingress::get_ci" [ap] h)
    (addressRep : Bytes.RepAddressRef Core.addrTy h address ap)
    (current : base.κ (Core.ixAddr address) = base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)))
    (keyed : ∀ address key, cx.keyAt address = .ok key → key = base.κ address)
    (selfKeyed : ∀ index address reading key,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      self index = some reading → reading = .ok key → key = base.κ address)
    (blobReads : L1.HashedBlobReadAgreement cx.blob rootCalls) :
    ∃ ci, (input.stageCtx parts isRec).env.find? (base.κ (Core.ixAddr address)) = some ci ∧
      Core.CIPtrRep base.κ h' ptr ci := by
  have addressEq : Core.ixAddr address = Core.iprjAddr (Core.ixAddr block) (ZMod.val i) :=
    Decl.nat_keyOf_injective tableWf current
  obtain ⟨projection, projectionShape⟩ := input.projectionSource
  let sourceAt := projection.reindex addressEq
  have sourceShape : sourceAt.value.info = .iPrj ⟨(ZMod.val i).toUInt64, Core.ixAddr block⟩ :=
    projectionShape
  obtain ⟨parent, blockArg, middle, inner, parentEq, _, parentRep, direct, subset, member⟩ :=
    L1.get_ci_iPrj_subcall (base := input.stageCtx parts isRec) sourceAt sourceShape addressRep good.raw loaded
  have parentSame : parent = block := Decl.ixAddr_inj parentEq
  subst parent
  have index64 : ZMod.val i < UInt64.size := Nat.lt_trans (ZMod.val_lt i) (by decide)
  have readIndex : (ZMod.val i).toUInt64.toNat = ZMod.val i := UInt64.toNat_ofNat_of_lt index64
  have castIndex : (((ZMod.val i).toUInt64.toNat : Nat) : F) = i :=
    (congrArg (fun n : Nat => (n : F)) readIndex).trans (ZMod.natCast_zmod_val i)
  rw [castIndex] at direct member
  obtain ⟨ci, found, represented⟩ := input.getIprj_current_of_blobAgreement runs frame direct (good.sub subset)
    (good.allowedTop member) parentRep keyed selfKeyed blobReads
  exact ⟨ci, by rwa [current], represented⟩

/-- Compatibility with full observed-blob membership. -/
theorem NativeFormerRunInput.getCI_current {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : L1.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {row : NativeFormerRow} {rootCalls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind row.1.type rootCalls)
    {parts : Ix.Kernel.InductiveShape .anon} {isRec : Bool}
    (runs : List (Decl.NativeCtorCoreRun rootCalls)) (tableWf : base.t.wf = true)
    {cx : Ix.Kernel.Reader.Ctx .anon} {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    (frame : NativeFormerReaderFrame cx (Core.ixAddr block)
      (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self) (ZMod.val i, ind) row)
    {ap ptr : SourceValue F} {h h' : Heap F} {calls : List (Call F)} {address : Bytes.Address}
    (loaded : ObsFn Core.W "Ingress::get_ci" [ap] h ptr h' calls)
    (good : Core.CoreGood (Decl.nativeCtorCoreCtx (input.stageCtx parts isRec) runs) calls)
    (_allowed : (Decl.nativeCtorCoreCtx (input.stageCtx parts isRec) runs).allowedTop "Ingress::get_ci" [ap] h)
    (addressRep : Bytes.RepAddressRef Core.addrTy h address ap)
    (current : base.κ (Core.ixAddr address) = base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)))
    (keyed : ∀ address key, cx.keyAt address = .ok key → key = base.κ address)
    (selfKeyed : ∀ index address reading key,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      self index = some reading → reading = .ok key → key = base.κ address)
    (blobReads : ∀ address bytes, Hashed rootCalls bytes → Address.blake3Pure bytes = address →
      cx.blob address = some bytes) :
    ∃ ci, (input.stageCtx parts isRec).env.find? (base.κ (Core.ixAddr address)) = some ci ∧
      Core.CIPtrRep base.κ h' ptr ci := by
  exact NativeFormerRunInput.getCI_current_of_blobAgreement input runs tableWf frame loaded good _allowed
    addressRep current keyed selfKeyed (L1.HashedBlobReadAgreement.of_stored blobReads)

end IxVM.Refinement.Assembly
