import IxVMRefinement.Assembly.NativeCtorFamily

/-! # Constructor scope properties from actual reader rows and Source checks

The conversion-origin proof already supplies the raw type's scope and level bounds. These
companions retain them for every row of the constructor family used by semantic checking.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- The actual scope check and raw reader row determine all syntactic type-scope properties. -/
theorem CtorScopeRead.type_scope_of_blobAgreement {base : Core.Ctx} {block : Bytes.Address} {i j : F}
    {params levels : Nat} {calls : List (Call F)}
    (checked : CtorScopeRead block i j 0 params levels calls)
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {ctor : Ixon.Constructor}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    (ctorAt : ind.ctors.toList[ZMod.val j]? = some ctor)
    {cx : Ix.Kernel.Reader.Ctx .anon} {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {row : NativeCtorRow}
    (frame : NativeCtorReaderFrame cx (Core.ixAddr block)
      (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self) (ZMod.val i, ctor, ZMod.val j) row)
    (good : Core.Good base calls)
    (keyed : ∀ address key, cx.keyAt address = .ok key → key = base.κ address)
    (selfKeyed : ∀ index address reading key,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      self index = some reading → reading = .ok key → key = base.κ address)
    (blobReads : L1.HashedBlobReadAgreement cx.blob calls) :
    row.1.type.looseBVarsBounded 0 = true ∧
      row.1.type.allLevelParamsDefined row.1.levelParams = true ∧ row.1.type.hasFvar = false := by
  obtain ⟨_, _, _, _, _, _, varsBounded, levelsDefined, noFvars, _⟩ :=
    observed_native_ctor_input_raw_origin_of_blobAgreement (base := base) source blockShape memberAt ctorAt
      checked.loaded (good.sub checked.loadSubset) checked.blockRep checked.tag checked.slotChecked
      checked.extended good.2 checked.scopeRun checked.scopeMember frame.2.1 keyed selfKeyed
      (fun address bytes hashed hashEq => blobReads address bytes
        (Core.hashed_mono checked.loadSubset hashed) hashEq)
  refine ⟨varsBounded, ?_, noFvars⟩
  simpa only [frame.2.2.1] using levelsDefined

/-- Compatibility with full observed-blob membership. -/
theorem CtorScopeRead.type_scope {base : Core.Ctx} {block : Bytes.Address} {i j : F}
    {params levels : Nat} {calls : List (Call F)}
    (checked : CtorScopeRead block i j 0 params levels calls)
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {ctor : Ixon.Constructor}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    (ctorAt : ind.ctors.toList[ZMod.val j]? = some ctor)
    {cx : Ix.Kernel.Reader.Ctx .anon} {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {row : NativeCtorRow}
    (frame : NativeCtorReaderFrame cx (Core.ixAddr block)
      (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self) (ZMod.val i, ctor, ZMod.val j) row)
    (good : Core.Good base calls)
    (keyed : ∀ address key, cx.keyAt address = .ok key → key = base.κ address)
    (selfKeyed : ∀ index address reading key,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      self index = some reading → reading = .ok key → key = base.κ address)
    (blobReads : ∀ address bytes, Hashed calls bytes → Address.blake3Pure bytes = address →
      cx.blob address = some bytes) :
    row.1.type.looseBVarsBounded 0 = true ∧
      row.1.type.allLevelParamsDefined row.1.levelParams = true ∧ row.1.type.hasFvar = false := by
  exact CtorScopeRead.type_scope_of_blobAgreement checked source blockShape memberAt ctorAt frame good
    keyed selfKeyed (L1.HashedBlobReadAgreement.of_stored blobReads)

/-- The successful constructor loop supplies raw scope properties for all corresponding
reader rows; no separate well-scopedness or free-variable premise is required. -/
theorem native_ctor_reader_scope_of_blobAgreement {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {params indices levels : Nat} {rc former bp sortLevel result : SourceValue F}
    {h h' : Heap F} {rootCalls loopCalls : List (Call F)}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    (countBound : ind.ctors.size < 549755813888)
    (blockRep : Bytes.RepAddressRef Core.addrTy h block bp)
    (subset : ∀ call ∈ loopCalls, call ∈ rootCalls)
    (loop : ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
      [rc, former, .field (params : F), .field (indices : F), .field (ind.ctors.size : F),
        .field (levels : F), bp, .field i, sortLevel, .field 0, .field 0] h result h' loopCalls)
    {cx : Ix.Kernel.Reader.Ctx .anon} {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {rows : List NativeCtorRow}
    (frames : List.Forall₂
      (NativeCtorReaderCheckedFrame cx (Core.ixAddr block)
        (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self))
      (nativeCtorSlots [(ZMod.val i, ind)]) rows)
    (good : Core.Good base rootCalls)
    (keyed : ∀ address key, cx.keyAt address = .ok key → key = base.κ address)
    (selfKeyed : ∀ index address reading key,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      self index = some reading → reading = .ok key → key = base.κ address)
    (blobReads : L1.HashedBlobReadAgreement cx.blob rootCalls) :
    ∀ row ∈ rows, row.1.type.looseBVarsBounded 0 = true ∧
      row.1.type.allLevelParamsDefined row.1.levelParams = true ∧ row.1.type.hasFvar = false := by
  have rowLength : rows.length = ind.ctors.size := by
    simpa [nativeCtorSlots] using frames.length_eq.symm
  intro row member
  obtain ⟨slot, slotBound, rfl⟩ := List.getElem_of_mem member
  have ctorBound : slot < ind.ctors.size := by simpa only [rowLength] using slotBound
  have slotValue : ZMod.val (slot : F) = slot :=
    ZMod.val_natCast_of_lt (Nat.lt_trans ctorBound (Nat.lt_trans countBound (by decide)))
  let ctor := ind.ctors[slot]
  have ctorAt : ind.ctors.toList[ZMod.val (slot : F)]? = some ctor := by
    simp [slotValue, ctor, ctorBound]
  have frameAt := (List.forall₂_iff_get.mp frames).2 slot
    (by simpa [nativeCtorSlots] using ctorBound) slotBound
  have frame : NativeCtorReaderCheckedFrame cx (Core.ixAddr block)
      (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self)
      (ZMod.val i, ctor, ZMod.val (slot : F)) rows[slot] := by
    simpa [nativeCtorSlots, ctor, slotValue] using frameAt
  have present : Nonempty (CtorScopeRead block i (slot : F) 0 params levels rootCalls) := by
    simpa only [Nat.zero_add] using native_ctor_scope_reads countBound ind.ctors.size 0 (Nat.add_zero _)
      blockRep subset loop slot ctorBound
  obtain ⟨checked⟩ := present
  exact checked.type_scope_of_blobAgreement source blockShape memberAt ctorAt frame.1 good keyed selfKeyed blobReads

/-- Compatibility with full observed-blob membership. -/
theorem native_ctor_reader_scope {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {params indices levels : Nat} {rc former bp sortLevel result : SourceValue F}
    {h h' : Heap F} {rootCalls loopCalls : List (Call F)}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    (countBound : ind.ctors.size < 549755813888)
    (blockRep : Bytes.RepAddressRef Core.addrTy h block bp)
    (subset : ∀ call ∈ loopCalls, call ∈ rootCalls)
    (loop : ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
      [rc, former, .field (params : F), .field (indices : F), .field (ind.ctors.size : F),
        .field (levels : F), bp, .field i, sortLevel, .field 0, .field 0] h result h' loopCalls)
    {cx : Ix.Kernel.Reader.Ctx .anon} {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {rows : List NativeCtorRow}
    (frames : List.Forall₂
      (NativeCtorReaderCheckedFrame cx (Core.ixAddr block)
        (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self))
      (nativeCtorSlots [(ZMod.val i, ind)]) rows)
    (good : Core.Good base rootCalls)
    (keyed : ∀ address key, cx.keyAt address = .ok key → key = base.κ address)
    (selfKeyed : ∀ index address reading key,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      self index = some reading → reading = .ok key → key = base.κ address)
    (blobReads : ∀ address bytes, Hashed rootCalls bytes → Address.blake3Pure bytes = address →
      cx.blob address = some bytes) :
    ∀ row ∈ rows, row.1.type.looseBVarsBounded 0 = true ∧
      row.1.type.allLevelParamsDefined row.1.levelParams = true ∧ row.1.type.hasFvar = false := by
  exact native_ctor_reader_scope_of_blobAgreement source blockShape memberAt countBound blockRep subset
    loop frames good keyed selfKeyed (L1.HashedBlobReadAgreement.of_stored blobReads)

end IxVM.Refinement.Assembly
