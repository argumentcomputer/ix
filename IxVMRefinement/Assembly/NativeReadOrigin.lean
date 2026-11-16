import IxVMRefinement.Assembly.NativeFormerReader
import IxVMRefinement.Assembly.NativeWalkedInputs
import IxVMRefinement.Assembly.NativeRawDispatch
import IxVMRefinement.Assembly.NativeOuter

/-! # Native former origins from the actual reader and walked checks

The successful reader supplies the former expression read used by the Source conversion
producer. The resulting input keeps the same actual row, declaration prefix and member index.
Reader naming and blob agreement remain explicit until their support-local producers apply.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- Compose an actual singleton-family reader run with its admitted walked member check.
The original former expression read is extracted from the reader loop. -/
theorem admitted_native_former_input_of_reader_of_blobAgreement {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {trace : Ixon.Env} {calls : List (Call F)} {seeds : List _root_.Address}
    (phase : Claim.WalkedL6 calls witness.table trace seeds)
    (loaded : IxVM.Consistency.LoadedBy calls trace) (bounded : IxVM.Consistency.Bounded calls)
    (env : Ix.Kernel.Env .anon) (lim : Option Nat) (claimBytes : ByteArray)
    (noCollision : ¬ V.HashedCollision
      (claimBytes :: binding.bytes :: IxVM.Consistency.readerImages V) calls)
    {bindingAddr : _root_.Address} {block : Bytes.Address} {members : Array Ixon.MutConst}
    {slot : Nat} {ind : Ixon.Inductive}
    (source : L1.CanonicalRecordAt (nativeOriginCtx witness trace env lim).E (Core.ixAddr block))
    (shape : source.value.info = .muts members) (memberAt : members[slot]? = some (.indc ind))
    (walked : WkAll calls bindingAddr witness.table trace (Core.ixAddr block))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(slot, ind)])
    {cx : Ix.Kernel.Reader.Ctx .anon} {state : Ix.Kernel.Reader.State .anon}
    {records : Array (_root_.Address × Ixon.Constant)} {result : Ix.Kernel.Reader.Read .anon}
    (indexBuilt : cx.index = Ix.Kernel.Reader.buildIndex cx.store records)
    (readerSource : cx.store (Core.ixAddr block) = some source.value)
    (read : Ix.Kernel.Reader.readInductive cx state (Core.ixAddr block) source.value members = .ok result)
    (keyed : ∀ address key, cx.keyAt address = .ok key →
      key = (nativeOriginCtx witness trace env lim).κ address)
    (selfKeyed : ∀ index address reading key,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      (if index < members.size then some (cx.memberKey (.member (Core.ixAddr block) index)) else none) =
        some reading → reading = .ok key → key = (nativeOriginCtx witness trace env lim).κ address)
    (blobReads : L1.HashedBlobReadAgreement cx.blob calls) :
    ∃ (generated : List (Ix.Kernel.Declaration .anon)) (bare : Ix.Kernel.Reader.Read .anon)
      (readerBlock : Ix.Kernel.Reader.BlockRead .anon) (row : NativeFormerRow),
      result.decls.toList = generated ++ bare.decls.toList ∧
      Ix.Kernel.Reader.lowerInductiveBare readerBlock = .ok bare ∧ readerBlock.types.toList = [row] ∧
      NativeFormerReaderFrame cx (Core.ixAddr block)
        (Ix.Kernel.Reader.MemberReader.mk' cx source.value id
          (fun index => if index < members.size then
            some (cx.memberKey (.member (Core.ixAddr block) index)) else none))
        (slot, ind) row ∧
      Nonempty (NativeFormerRunInput (nativeOriginCtx witness trace env lim) block (slot : F)
        source members ind row.1.type calls) := by
  obtain ⟨generated, bare, readerBlock, row, declarations, lowered, types, frame⟩ :=
    readInductive_one_former_frame indexBuilt readerSource shape memberAt one read
  refine ⟨generated, bare, readerBlock, row, declarations, lowered, types, frame, ?_⟩
  exact admitted_native_former_input_of_blobAgreement witness phase loaded bounded env lim claimBytes noCollision
    source shape memberAt walked {} frame.2.1 keyed selfKeyed blobReads

/-- Compatibility with full observed-blob membership. -/
theorem admitted_native_former_input_of_reader {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {trace : Ixon.Env} {calls : List (Call F)} {seeds : List _root_.Address}
    (phase : Claim.WalkedL6 calls witness.table trace seeds)
    (loaded : IxVM.Consistency.LoadedBy calls trace) (bounded : IxVM.Consistency.Bounded calls)
    (env : Ix.Kernel.Env .anon) (lim : Option Nat) (claimBytes : ByteArray)
    (noCollision : ¬ V.HashedCollision
      (claimBytes :: binding.bytes :: IxVM.Consistency.readerImages V) calls)
    {bindingAddr : _root_.Address} {block : Bytes.Address} {members : Array Ixon.MutConst}
    {slot : Nat} {ind : Ixon.Inductive}
    (source : L1.CanonicalRecordAt (nativeOriginCtx witness trace env lim).E (Core.ixAddr block))
    (shape : source.value.info = .muts members) (memberAt : members[slot]? = some (.indc ind))
    (walked : WkAll calls bindingAddr witness.table trace (Core.ixAddr block))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(slot, ind)])
    {cx : Ix.Kernel.Reader.Ctx .anon} {state : Ix.Kernel.Reader.State .anon}
    {records : Array (_root_.Address × Ixon.Constant)} {result : Ix.Kernel.Reader.Read .anon}
    (indexBuilt : cx.index = Ix.Kernel.Reader.buildIndex cx.store records)
    (readerSource : cx.store (Core.ixAddr block) = some source.value)
    (read : Ix.Kernel.Reader.readInductive cx state (Core.ixAddr block) source.value members = .ok result)
    (keyed : ∀ address key, cx.keyAt address = .ok key →
      key = (nativeOriginCtx witness trace env lim).κ address)
    (selfKeyed : ∀ index address reading key,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      (if index < members.size then some (cx.memberKey (.member (Core.ixAddr block) index)) else none) =
        some reading → reading = .ok key → key = (nativeOriginCtx witness trace env lim).κ address)
    (blobReads : ∀ address bytes, Hashed calls bytes → Address.blake3Pure bytes = address →
      cx.blob address = some bytes) :
    ∃ (generated : List (Ix.Kernel.Declaration .anon)) (bare : Ix.Kernel.Reader.Read .anon)
      (readerBlock : Ix.Kernel.Reader.BlockRead .anon) (row : NativeFormerRow),
      result.decls.toList = generated ++ bare.decls.toList ∧
      Ix.Kernel.Reader.lowerInductiveBare readerBlock = .ok bare ∧ readerBlock.types.toList = [row] ∧
      NativeFormerReaderFrame cx (Core.ixAddr block)
        (Ix.Kernel.Reader.MemberReader.mk' cx source.value id
          (fun index => if index < members.size then
            some (cx.memberKey (.member (Core.ixAddr block) index)) else none))
        (slot, ind) row ∧
      Nonempty (NativeFormerRunInput (nativeOriginCtx witness trace env lim) block (slot : F)
        source members ind row.1.type calls) := by
  exact admitted_native_former_input_of_reader_of_blobAgreement witness phase loaded bounded env lim
    claimBytes noCollision source shape memberAt walked one indexBuilt readerSource read keyed selfKeyed
    (L1.HashedBlobReadAgreement.of_stored blobReads)

/-- The actual walked dispatch and reader run construct the native branch's complete former
origin and shape calls, or retain the actual modeled call. No singleton-family premise is supplied. -/
theorem admitted_native_reader_dispatch_with_ctor_frames_of_blobAgreement {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {trace : Ixon.Env} {calls : List (Call F)} {seeds : List _root_.Address}
    (phase : Claim.WalkedL6 calls witness.table trace seeds)
    (loaded : IxVM.Consistency.LoadedBy calls trace) (bounded : IxVM.Consistency.Bounded calls)
    (env : Ix.Kernel.Env .anon) (lim : Option Nat) (claimBytes : ByteArray)
    (noCollision : ¬ V.HashedCollision
      (claimBytes :: binding.bytes :: IxVM.Consistency.readerImages V) calls)
    {bindingAddr : _root_.Address} {block : Bytes.Address} {members : Array Ixon.MutConst}
    {slot : Nat} {ind : Ixon.Inductive}
    (source : L1.CanonicalRecordAt (nativeOriginCtx witness trace env lim).E (Core.ixAddr block))
    (shape : source.value.info = .muts members) (memberAt : members[slot]? = some (.indc ind))
    (walked : WkAll calls bindingAddr witness.table trace (Core.ixAddr block))
    {cx : Ix.Kernel.Reader.Ctx .anon} {state : Ix.Kernel.Reader.State .anon}
    {records : Array (_root_.Address × Ixon.Constant)} {result : Ix.Kernel.Reader.Read .anon}
    (indexBuilt : cx.index = Ix.Kernel.Reader.buildIndex cx.store records)
    (readerSource : cx.store (Core.ixAddr block) = some source.value)
    (read : Ix.Kernel.Reader.readInductive cx state (Core.ixAddr block) source.value members = .ok result)
    (keyed : ∀ address key, cx.keyAt address = .ok key →
      key = (nativeOriginCtx witness trace env lim).κ address)
    (selfKeyed : ∀ index address reading key,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      (if index < members.size then some (cx.memberKey (.member (Core.ixAddr block) index)) else none) =
        some reading → reading = .ok key → key = (nativeOriginCtx witness trace env lim).κ address)
    (blobReads : L1.HashedBlobReadAgreement cx.blob calls) :
    ZMod.val (slot : F) = slot ∧
    ((∃ (generated : List (Ix.Kernel.Declaration .anon)) (bare : Ix.Kernel.Reader.Read .anon)
        (readerBlock : Ix.Kernel.Reader.BlockRead .anon) (row : NativeFormerRow),
        result.decls.toList = generated ++ bare.decls.toList ∧
        Ix.Kernel.Reader.lowerInductiveBare readerBlock = .ok bare ∧ readerBlock.types.toList = [row] ∧
        NativeFormerReaderFrame cx (Core.ixAddr block)
          (Ix.Kernel.Reader.MemberReader.mk' cx source.value id
            (fun index => if index < members.size then
              some (cx.memberKey (.member (Core.ixAddr block) index)) else none))
          (slot, ind) row ∧
        List.Forall₂
          (NativeCtorReaderCheckedFrame cx (Core.ixAddr block)
            (Ix.Kernel.Reader.MemberReader.mk' cx source.value id
              (fun index => if index < members.size then
                some (cx.memberKey (.member (Core.ixAddr block) index)) else none)))
          (nativeCtorSlots [(slot, ind)]) readerBlock.ctors.toList ∧
        readerBlock.numParams = ind.params.toNat ∧
        ∃ input : NativeFormerRunInput (nativeOriginCtx witness trace env lim) block (slot : F)
            source members ind row.1.type calls,
          ∃ native : input.NativeCall,
            Nonempty (Decl.NativeShapeCalls input.rc input.typePtr input.blockPtr (.field (slot : F))
              (L1.repBoolField ind.isUnsafe) ind.params.toNat ind.indices.toNat ind.ctors.size ind.lvls.toNat
              native.before calls)) ∨
      ∃ (blockPtr : SourceValue F) (heap : Heap F),
        Bytes.RepAddressRef Core.addrTy heap block blockPtr ∧ Decl.ModeledInductCall blockPtr heap calls) := by
  obtain ⟨slotValue, _, _, blockPtr, heap, blockRep, branch⟩ :=
    admitted_native_raw_dispatch witness phase loaded bounded env lim claimBytes noCollision
      source shape memberAt walked
  refine ⟨slotValue, ?_⟩
  rcases branch with ⟨one, _⟩ | modeled
  · obtain ⟨generated, bare, readerBlock, row, declarations, lowered, types, frame, ctorFrames, paramCount⟩ :=
      readInductive_one_native_frames_with_params indexBuilt readerSource shape memberAt one read
    obtain ⟨input⟩ := admitted_native_former_input_of_blobAgreement witness phase loaded bounded env lim claimBytes noCollision
      source shape memberAt walked {} frame.2.1 keyed selfKeyed blobReads
    rcases input.dispatch with native | modeled
    · obtain ⟨native, shapeCalls⟩ := native
      exact .inl ⟨generated, bare, readerBlock, row, declarations, lowered, types, frame, ctorFrames, paramCount,
        input, native, shapeCalls⟩
    · exact .inr ⟨input.blockPtr, input.heap, input.blockRep, modeled⟩
  · exact .inr ⟨blockPtr, heap, blockRep, modeled⟩

/-- Compatibility with full observed-blob membership. -/
theorem admitted_native_reader_dispatch_with_ctor_frames {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {trace : Ixon.Env} {calls : List (Call F)} {seeds : List _root_.Address}
    (phase : Claim.WalkedL6 calls witness.table trace seeds)
    (loaded : IxVM.Consistency.LoadedBy calls trace) (bounded : IxVM.Consistency.Bounded calls)
    (env : Ix.Kernel.Env .anon) (lim : Option Nat) (claimBytes : ByteArray)
    (noCollision : ¬ V.HashedCollision
      (claimBytes :: binding.bytes :: IxVM.Consistency.readerImages V) calls)
    {bindingAddr : _root_.Address} {block : Bytes.Address} {members : Array Ixon.MutConst}
    {slot : Nat} {ind : Ixon.Inductive}
    (source : L1.CanonicalRecordAt (nativeOriginCtx witness trace env lim).E (Core.ixAddr block))
    (shape : source.value.info = .muts members) (memberAt : members[slot]? = some (.indc ind))
    (walked : WkAll calls bindingAddr witness.table trace (Core.ixAddr block))
    {cx : Ix.Kernel.Reader.Ctx .anon} {state : Ix.Kernel.Reader.State .anon}
    {records : Array (_root_.Address × Ixon.Constant)} {result : Ix.Kernel.Reader.Read .anon}
    (indexBuilt : cx.index = Ix.Kernel.Reader.buildIndex cx.store records)
    (readerSource : cx.store (Core.ixAddr block) = some source.value)
    (read : Ix.Kernel.Reader.readInductive cx state (Core.ixAddr block) source.value members = .ok result)
    (keyed : ∀ address key, cx.keyAt address = .ok key →
      key = (nativeOriginCtx witness trace env lim).κ address)
    (selfKeyed : ∀ index address reading key,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      (if index < members.size then some (cx.memberKey (.member (Core.ixAddr block) index)) else none) =
        some reading → reading = .ok key → key = (nativeOriginCtx witness trace env lim).κ address)
    (blobReads : ∀ address bytes, Hashed calls bytes → Address.blake3Pure bytes = address →
      cx.blob address = some bytes) :
    ZMod.val (slot : F) = slot ∧
    ((∃ (generated : List (Ix.Kernel.Declaration .anon)) (bare : Ix.Kernel.Reader.Read .anon)
        (readerBlock : Ix.Kernel.Reader.BlockRead .anon) (row : NativeFormerRow),
        result.decls.toList = generated ++ bare.decls.toList ∧
        Ix.Kernel.Reader.lowerInductiveBare readerBlock = .ok bare ∧ readerBlock.types.toList = [row] ∧
        NativeFormerReaderFrame cx (Core.ixAddr block)
          (Ix.Kernel.Reader.MemberReader.mk' cx source.value id
            (fun index => if index < members.size then
              some (cx.memberKey (.member (Core.ixAddr block) index)) else none))
          (slot, ind) row ∧
        List.Forall₂
          (NativeCtorReaderCheckedFrame cx (Core.ixAddr block)
            (Ix.Kernel.Reader.MemberReader.mk' cx source.value id
              (fun index => if index < members.size then
                some (cx.memberKey (.member (Core.ixAddr block) index)) else none)))
          (nativeCtorSlots [(slot, ind)]) readerBlock.ctors.toList ∧
        readerBlock.numParams = ind.params.toNat ∧
        ∃ input : NativeFormerRunInput (nativeOriginCtx witness trace env lim) block (slot : F)
            source members ind row.1.type calls,
          ∃ native : input.NativeCall,
            Nonempty (Decl.NativeShapeCalls input.rc input.typePtr input.blockPtr (.field (slot : F))
              (L1.repBoolField ind.isUnsafe) ind.params.toNat ind.indices.toNat ind.ctors.size ind.lvls.toNat
              native.before calls)) ∨
      ∃ (blockPtr : SourceValue F) (heap : Heap F),
        Bytes.RepAddressRef Core.addrTy heap block blockPtr ∧ Decl.ModeledInductCall blockPtr heap calls) := by
  exact admitted_native_reader_dispatch_with_ctor_frames_of_blobAgreement witness phase loaded bounded
    env lim claimBytes noCollision source shape memberAt walked indexBuilt readerSource read keyed
    selfKeyed (L1.HashedBlobReadAgreement.of_stored blobReads)

/-- Compatibility projection retaining the former origin and actual route. -/
theorem admitted_native_reader_dispatch_of_blobAgreement {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {trace : Ixon.Env} {calls : List (Call F)} {seeds : List _root_.Address}
    (phase : Claim.WalkedL6 calls witness.table trace seeds)
    (loaded : IxVM.Consistency.LoadedBy calls trace) (bounded : IxVM.Consistency.Bounded calls)
    (env : Ix.Kernel.Env .anon) (lim : Option Nat) (claimBytes : ByteArray)
    (noCollision : ¬ V.HashedCollision
      (claimBytes :: binding.bytes :: IxVM.Consistency.readerImages V) calls)
    {bindingAddr : _root_.Address} {block : Bytes.Address} {members : Array Ixon.MutConst}
    {slot : Nat} {ind : Ixon.Inductive}
    (source : L1.CanonicalRecordAt (nativeOriginCtx witness trace env lim).E (Core.ixAddr block))
    (shape : source.value.info = .muts members) (memberAt : members[slot]? = some (.indc ind))
    (walked : WkAll calls bindingAddr witness.table trace (Core.ixAddr block))
    {cx : Ix.Kernel.Reader.Ctx .anon} {state : Ix.Kernel.Reader.State .anon}
    {records : Array (_root_.Address × Ixon.Constant)} {result : Ix.Kernel.Reader.Read .anon}
    (indexBuilt : cx.index = Ix.Kernel.Reader.buildIndex cx.store records)
    (readerSource : cx.store (Core.ixAddr block) = some source.value)
    (read : Ix.Kernel.Reader.readInductive cx state (Core.ixAddr block) source.value members = .ok result)
    (keyed : ∀ address key, cx.keyAt address = .ok key →
      key = (nativeOriginCtx witness trace env lim).κ address)
    (selfKeyed : ∀ index address reading key,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      (if index < members.size then some (cx.memberKey (.member (Core.ixAddr block) index)) else none) =
        some reading → reading = .ok key → key = (nativeOriginCtx witness trace env lim).κ address)
    (blobReads : L1.HashedBlobReadAgreement cx.blob calls) :
    ZMod.val (slot : F) = slot ∧
    ((∃ (generated : List (Ix.Kernel.Declaration .anon)) (bare : Ix.Kernel.Reader.Read .anon)
        (readerBlock : Ix.Kernel.Reader.BlockRead .anon) (row : NativeFormerRow),
        result.decls.toList = generated ++ bare.decls.toList ∧
        Ix.Kernel.Reader.lowerInductiveBare readerBlock = .ok bare ∧ readerBlock.types.toList = [row] ∧
        NativeFormerReaderFrame cx (Core.ixAddr block)
          (Ix.Kernel.Reader.MemberReader.mk' cx source.value id
            (fun index => if index < members.size then
              some (cx.memberKey (.member (Core.ixAddr block) index)) else none))
          (slot, ind) row ∧
        ∃ input : NativeFormerRunInput (nativeOriginCtx witness trace env lim) block (slot : F)
            source members ind row.1.type calls,
          ∃ native : input.NativeCall,
            Nonempty (Decl.NativeShapeCalls input.rc input.typePtr input.blockPtr (.field (slot : F))
              (L1.repBoolField ind.isUnsafe) ind.params.toNat ind.indices.toNat ind.ctors.size ind.lvls.toNat
              native.before calls)) ∨
      ∃ (blockPtr : SourceValue F) (heap : Heap F),
        Bytes.RepAddressRef Core.addrTy heap block blockPtr ∧ Decl.ModeledInductCall blockPtr heap calls) := by
  obtain ⟨slotValue, branch⟩ := admitted_native_reader_dispatch_with_ctor_frames_of_blobAgreement witness phase loaded bounded
    env lim claimBytes noCollision source shape memberAt walked indexBuilt readerSource read keyed selfKeyed blobReads
  refine ⟨slotValue, ?_⟩
  rcases branch with native | modeled
  · obtain ⟨generated, bare, readerBlock, row, declarations, lowered, types, frame, _, _, input, native, shapeCalls⟩ := native
    exact .inl ⟨generated, bare, readerBlock, row, declarations, lowered, types, frame, input, native, shapeCalls⟩
  · exact .inr modeled


/-- Compatibility with full observed-blob membership. -/
theorem admitted_native_reader_dispatch {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {trace : Ixon.Env} {calls : List (Call F)} {seeds : List _root_.Address}
    (phase : Claim.WalkedL6 calls witness.table trace seeds)
    (loaded : IxVM.Consistency.LoadedBy calls trace) (bounded : IxVM.Consistency.Bounded calls)
    (env : Ix.Kernel.Env .anon) (lim : Option Nat) (claimBytes : ByteArray)
    (noCollision : ¬ V.HashedCollision
      (claimBytes :: binding.bytes :: IxVM.Consistency.readerImages V) calls)
    {bindingAddr : _root_.Address} {block : Bytes.Address} {members : Array Ixon.MutConst}
    {slot : Nat} {ind : Ixon.Inductive}
    (source : L1.CanonicalRecordAt (nativeOriginCtx witness trace env lim).E (Core.ixAddr block))
    (shape : source.value.info = .muts members) (memberAt : members[slot]? = some (.indc ind))
    (walked : WkAll calls bindingAddr witness.table trace (Core.ixAddr block))
    {cx : Ix.Kernel.Reader.Ctx .anon} {state : Ix.Kernel.Reader.State .anon}
    {records : Array (_root_.Address × Ixon.Constant)} {result : Ix.Kernel.Reader.Read .anon}
    (indexBuilt : cx.index = Ix.Kernel.Reader.buildIndex cx.store records)
    (readerSource : cx.store (Core.ixAddr block) = some source.value)
    (read : Ix.Kernel.Reader.readInductive cx state (Core.ixAddr block) source.value members = .ok result)
    (keyed : ∀ address key, cx.keyAt address = .ok key →
      key = (nativeOriginCtx witness trace env lim).κ address)
    (selfKeyed : ∀ index address reading key,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      (if index < members.size then some (cx.memberKey (.member (Core.ixAddr block) index)) else none) =
        some reading → reading = .ok key → key = (nativeOriginCtx witness trace env lim).κ address)
    (blobReads : ∀ address bytes, Hashed calls bytes → Address.blake3Pure bytes = address →
      cx.blob address = some bytes) :
    ZMod.val (slot : F) = slot ∧
    ((∃ (generated : List (Ix.Kernel.Declaration .anon)) (bare : Ix.Kernel.Reader.Read .anon)
        (readerBlock : Ix.Kernel.Reader.BlockRead .anon) (row : NativeFormerRow),
        result.decls.toList = generated ++ bare.decls.toList ∧
        Ix.Kernel.Reader.lowerInductiveBare readerBlock = .ok bare ∧ readerBlock.types.toList = [row] ∧
        NativeFormerReaderFrame cx (Core.ixAddr block)
          (Ix.Kernel.Reader.MemberReader.mk' cx source.value id
            (fun index => if index < members.size then
              some (cx.memberKey (.member (Core.ixAddr block) index)) else none))
          (slot, ind) row ∧
        ∃ input : NativeFormerRunInput (nativeOriginCtx witness trace env lim) block (slot : F)
            source members ind row.1.type calls,
          ∃ native : input.NativeCall,
            Nonempty (Decl.NativeShapeCalls input.rc input.typePtr input.blockPtr (.field (slot : F))
              (L1.repBoolField ind.isUnsafe) ind.params.toNat ind.indices.toNat ind.ctors.size ind.lvls.toNat
              native.before calls)) ∨
      ∃ (blockPtr : SourceValue F) (heap : Heap F),
        Bytes.RepAddressRef Core.addrTy heap block blockPtr ∧ Decl.ModeledInductCall blockPtr heap calls) := by
  exact admitted_native_reader_dispatch_of_blobAgreement witness phase loaded bounded env lim claimBytes
    noCollision source shape memberAt walked indexBuilt readerSource read keyed selfKeyed
    (L1.HashedBlobReadAgreement.of_stored blobReads)

end IxVM.Refinement.Assembly
