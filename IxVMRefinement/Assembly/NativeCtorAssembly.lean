import IxVMRefinement.Assembly.NativeCtorFamily
import IxVMRefinement.Assembly.NativeBlockShape
import IxVMRefinement.L1.NativeBounds
import IxVMRefinement.Assembly.NativeCtorKeyFamily

/-! # Actual native constructor family assembly

The native route observation identifies the unique inductive member, the real reader fixes
its constructor rows, and the Source loop constructs their indexed load family.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- Assemble a constructor load family from actual reader and Source observations. The
annotation/raw lists and one-family reader order are both derived, not supplied by a caller. -/
theorem native_ctor_family_of_reading {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {rootCalls modeCalls loopCalls : List (Call F)}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    (countBound : ind.ctors.size < 549755813888)
    (paramsBound : ind.params.toNat < 72057594037927936)
    (levelsBound : ind.lvls.toNat < 4294967296)
    {modeArg : SourceValue F} {modeBefore modeAfter : Heap F}
    (modeSubset : ∀ call ∈ modeCalls, call ∈ rootCalls)
    (modeBlock : Bytes.RepAddressRef Core.addrTy modeBefore block modeArg)
    (modeRun : ObsFn Core.W "KernelModeled::block_is_modeled" [modeArg]
      modeBefore (.field 0) modeAfter modeCalls)
    {rc former bp sortLevel result : SourceValue F} {h h' : Heap F}
    (blockRep : Bytes.RepAddressRef Core.addrTy h block bp)
    (subset : ∀ call ∈ loopCalls, call ∈ rootCalls)
    (loop : ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
      [rc, former, .field (ind.params.toNat : F), .field (ind.indices.toNat : F),
        .field (ind.ctors.size : F), .field (ind.lvls.toNat : F), bp, .field i, sortLevel, .field 0, .field 0]
      h result h' loopCalls)
    {cx : Ix.Kernel.Reader.Ctx .anon} {state : Ix.Kernel.Reader.State .anon}
    {records : Array (_root_.Address × Ixon.Constant)} {reading : Ix.Kernel.Reader.Read .anon}
    (indexBuilt : cx.index = Ix.Kernel.Reader.buildIndex cx.store records)
    (parentStored : cx.store (Core.ixAddr block) = some source.value)
    (read : Ix.Kernel.Reader.readInductive cx state (Core.ixAddr block) source.value members = .ok reading)
    (memberKeys : ∀ j < ind.ctors.size,
      cx.memberKey (.ctor (Core.ixAddr block) (ZMod.val i) j) =
        .ok (base.κ (Core.cprjAddr (Core.ixAddr block) (ZMod.val i) j)))
    (good : Core.Good base rootCalls)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = base.κ a)
    (selfKeyed : ∀ k a m name,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      (if k < members.size then some (cx.memberKey (.member (Core.ixAddr block) k)) else none) = some m →
      m = .ok name → name = base.κ a)
    (blobReads : ∀ a bytes, Hashed rootCalls bytes → Address.blake3Pure bytes = a →
      cx.blob a = some bytes) :
    ∃ (generated : List (Ix.Kernel.Declaration .anon)) (bare : Ix.Kernel.Reader.Read .anon)
      (readerBlock : Ix.Kernel.Reader.BlockRead .anon)
      (annotated : List (Ix.Kernel.ConstantVal .anon × Nat)) (rawTypes : List Core.KExpr),
      reading.decls.toList = generated ++ bare.decls.toList ∧
      Ix.Kernel.Reader.lowerInductiveBare readerBlock = .ok bare ∧
      readerBlock.ctors.size = ind.ctors.size ∧
      Decl.CtorLoadAtIndex base.t block ind.params.toNat i rootCalls
        (readerBlock.ctors.toList.map (fun row => (row.1, row.2.2))) annotated rawTypes ∧
      (∀ row ∈ readerBlock.ctors.toList, row.2.1 = ind.params.toNat ∧
        row.1.levelParams = List.range ind.lvls.toNat) := by
  have few := native_block_inductive_count source blockShape (good.sub modeSubset) modeBlock modeRun
  have memberArray : members[ZMod.val i]? = some (.indc ind) := by
    simpa only [Array.getElem?_toList] using memberAt
  have one := native_inductives_singleton few memberArray
  obtain ⟨generated, bare, readerBlock, declarations, lowered, frames⟩ :=
    readInductive_one_family_frames indexBuilt parentStored blockShape memberArray one read
  have length : readerBlock.ctors.size = ind.ctors.size := by
    simpa [nativeCtorSlots] using frames.length_eq.symm
  obtain ⟨annotated, rawTypes, loads, headers⟩ := native_ctor_load_family
    source blockShape memberAt countBound paramsBound levelsBound blockRep subset loop frames memberKeys
    good keyed selfKeyed blobReads
  exact ⟨generated, bare, readerBlock, annotated, rawTypes, declarations, lowered, length, loads, headers⟩

/-- The actual former load also supplies all header/count bounds for family assembly. -/
theorem native_ctor_family_of_observations {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {rootCalls modeCalls loopCalls : List (Call F)}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    {headerArg headerPtr : SourceValue F} {headerBefore headerAfter : Heap F}
    {headerCalls : List (Call F)}
    (headerSubset : ∀ call ∈ headerCalls, call ∈ rootCalls)
    (headerBlock : Bytes.RepAddressRef Core.addrTy headerBefore block headerArg)
    (headerRun : ObsFn Core.W "Ingress::get_ci_iprj" [headerArg, .field i]
      headerBefore headerPtr headerAfter headerCalls)
    {modeArg : SourceValue F} {modeBefore modeAfter : Heap F}
    (modeSubset : ∀ call ∈ modeCalls, call ∈ rootCalls)
    (modeBlock : Bytes.RepAddressRef Core.addrTy modeBefore block modeArg)
    (modeRun : ObsFn Core.W "KernelModeled::block_is_modeled" [modeArg]
      modeBefore (.field 0) modeAfter modeCalls)
    {rc former bp sortLevel result : SourceValue F} {h h' : Heap F}
    (blockRep : Bytes.RepAddressRef Core.addrTy h block bp)
    (subset : ∀ call ∈ loopCalls, call ∈ rootCalls)
    (loop : ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
      [rc, former, .field (ind.params.toNat : F), .field (ind.indices.toNat : F),
        .field (ind.ctors.size : F), .field (ind.lvls.toNat : F), bp, .field i, sortLevel, .field 0, .field 0]
      h result h' loopCalls)
    {cx : Ix.Kernel.Reader.Ctx .anon} {state : Ix.Kernel.Reader.State .anon}
    {records : Array (_root_.Address × Ixon.Constant)} {reading : Ix.Kernel.Reader.Read .anon}
    (indexBuilt : cx.index = Ix.Kernel.Reader.buildIndex cx.store records)
    (parentStored : cx.store (Core.ixAddr block) = some source.value)
    (read : Ix.Kernel.Reader.readInductive cx state (Core.ixAddr block) source.value members = .ok reading)
    (memberKeys : ∀ j < ind.ctors.size,
      cx.memberKey (.ctor (Core.ixAddr block) (ZMod.val i) j) =
        .ok (base.κ (Core.cprjAddr (Core.ixAddr block) (ZMod.val i) j)))
    (good : Core.Good base rootCalls)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = base.κ a)
    (selfKeyed : ∀ k a m name,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      (if k < members.size then some (cx.memberKey (.member (Core.ixAddr block) k)) else none) = some m →
      m = .ok name → name = base.κ a)
    (blobReads : ∀ a bytes, Hashed rootCalls bytes → Address.blake3Pure bytes = a →
      cx.blob a = some bytes) :
    ∃ (generated : List (Ix.Kernel.Declaration .anon)) (bare : Ix.Kernel.Reader.Read .anon)
      (readerBlock : Ix.Kernel.Reader.BlockRead .anon)
      (annotated : List (Ix.Kernel.ConstantVal .anon × Nat)) (rawTypes : List Core.KExpr),
      reading.decls.toList = generated ++ bare.decls.toList ∧
      Ix.Kernel.Reader.lowerInductiveBare readerBlock = .ok bare ∧
      readerBlock.ctors.size = ind.ctors.size ∧
      Decl.CtorLoadAtIndex base.t block ind.params.toNat i rootCalls
        (readerBlock.ctors.toList.map (fun row => (row.1, row.2.2))) annotated rawTypes ∧
      (∀ row ∈ readerBlock.ctors.toList, row.2.1 = ind.params.toNat ∧
        row.1.levelParams = List.range ind.lvls.toNat) := by
  obtain ⟨levelsBound, paramsBound, _, countBound⟩ :=
    L1.get_ci_iprj_header_bounds source blockShape memberAt (good.sub headerSubset) headerBlock headerRun
  exact native_ctor_family_of_reading source blockShape memberAt countBound paramsBound levelsBound
    modeSubset modeBlock modeRun blockRep subset loop indexBuilt parentStored read memberKeys
    good keyed selfKeyed blobReads

/-- In the authentic stream context, the same actual loop discharges constructor member-key
agreement through its projection hashes. No constructor-key premise or count certificate remains. -/
theorem native_ctor_family_in_stream_context {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {rootCalls modeCalls loopCalls : List (Call F)}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    {headerArg headerPtr : SourceValue F} {headerBefore headerAfter : Heap F}
    {headerCalls : List (Call F)}
    (headerSubset : ∀ call ∈ headerCalls, call ∈ rootCalls)
    (headerBlock : Bytes.RepAddressRef Core.addrTy headerBefore block headerArg)
    (headerRun : ObsFn Core.W "Ingress::get_ci_iprj" [headerArg, .field i]
      headerBefore headerPtr headerAfter headerCalls)
    {modeArg : SourceValue F} {modeBefore modeAfter : Heap F}
    (modeSubset : ∀ call ∈ modeCalls, call ∈ rootCalls)
    (modeBlock : Bytes.RepAddressRef Core.addrTy modeBefore block modeArg)
    (modeRun : ObsFn Core.W "KernelModeled::block_is_modeled" [modeArg]
      modeBefore (.field 0) modeAfter modeCalls)
    {rc former bp sortLevel result : SourceValue F} {h h' : Heap F}
    (blockRep : Bytes.RepAddressRef Core.addrTy h block bp)
    (subset : ∀ call ∈ loopCalls, call ∈ rootCalls)
    (loop : ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
      [rc, former, .field (ind.params.toNat : F), .field (ind.indices.toNat : F),
        .field (ind.ctors.size : F), .field (ind.lvls.toNat : F), bp, .field i, sortLevel, .field 0, .field 0]
      h result h' loopCalls)
    {cx : Ix.Kernel.Reader.Ctx .anon} {state : Ix.Kernel.Reader.State .anon}
    {records : Array (_root_.Address × Ixon.Constant)} {reading : Ix.Kernel.Reader.Read .anon}
    (indexBuilt : cx.index = Ix.Kernel.Reader.buildIndex cx.store records)
    (parentStored : cx.store (Core.ixAddr block) = some source.value)
    (read : Ix.Kernel.Reader.readInductive cx state (Core.ixAddr block) source.value members = .ok reading)
    {pre : Ix.Kernel.Reader.Prelude .anon} {constants : List (_root_.Address × Ixon.Constant)}
    {readerBlobs : Ix.Kernel.Ingress.Blobs}
    {hint : Ix.Kernel.ConstRef _root_.Address → Option Ix.Kernel.ReducibilityHint}
    (context : cx = Ix.Kernel.Admission.streamContext _root_.Address.admissionHash
      base.t pre constants readerBlobs hint)
    (authentic : AuthenticExactStore cx.store) (tableChecked : base.t.check = .ok ())
    (boundStored : ∀ role address, (role, address) ∈ base.t.bound.toList → ∃ value, cx.store address = some value)
    (transport : ∀ address value, cx.store address = some value → Ix.Cert.recordAt base.E address = some value)
    (decoded : L1.EnvDecoded base.E)
    (good : Core.Good base rootCalls)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = base.κ a)
    (selfKeyed : ∀ k a m name,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      (if k < members.size then some (cx.memberKey (.member (Core.ixAddr block) k)) else none) = some m →
      m = .ok name → name = base.κ a)
    (blobReads : ∀ a bytes, Hashed rootCalls bytes → Address.blake3Pure bytes = a →
      cx.blob a = some bytes) :
    ∃ (generated : List (Ix.Kernel.Declaration .anon)) (bare : Ix.Kernel.Reader.Read .anon)
      (readerBlock : Ix.Kernel.Reader.BlockRead .anon)
      (annotated : List (Ix.Kernel.ConstantVal .anon × Nat)) (rawTypes : List Core.KExpr),
      reading.decls.toList = generated ++ bare.decls.toList ∧
      Ix.Kernel.Reader.lowerInductiveBare readerBlock = .ok bare ∧
      readerBlock.ctors.size = ind.ctors.size ∧
      Decl.CtorLoadAtIndex base.t block ind.params.toNat i rootCalls
        (readerBlock.ctors.toList.map (fun row => (row.1, row.2.2))) annotated rawTypes ∧
      (∀ row ∈ readerBlock.ctors.toList, row.2.1 = ind.params.toNat ∧
        row.1.levelParams = List.range ind.lvls.toNat) := by
  obtain ⟨levelsBound, paramsBound, _, countBound⟩ :=
    L1.get_ci_iprj_header_bounds source blockShape memberAt (good.sub headerSubset) headerBlock headerRun
  have few := native_block_inductive_count source blockShape (good.sub modeSubset) modeBlock modeRun
  have memberArray : members[ZMod.val i]? = some (.indc ind) := by
    simpa only [Array.getElem?_toList] using memberAt
  have one := native_inductives_singleton few memberArray
  obtain ⟨generated, bare, readerBlock, declarations, lowered, frames⟩ :=
    readInductive_one_family_frames indexBuilt parentStored blockShape memberArray one read
  have length : readerBlock.ctors.size = ind.ctors.size := by
    simpa [nativeCtorSlots] using frames.length_eq.symm
  have memberKeys := native_ctor_member_keys context authentic tableChecked boundStored transport decoded
    source parentStored blockShape memberAt frames countBound good blockRep subset loop
  obtain ⟨annotated, rawTypes, loads, headers⟩ := native_ctor_load_family
    source blockShape memberAt countBound paramsBound levelsBound blockRep subset loop frames memberKeys
    good keyed selfKeyed blobReads
  exact ⟨generated, bare, readerBlock, annotated, rawTypes, declarations, lowered, length, loads, headers⟩

end IxVM.Refinement.Assembly
