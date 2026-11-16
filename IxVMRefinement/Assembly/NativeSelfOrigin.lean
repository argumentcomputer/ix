import IxVMRefinement.Assembly.NativeAdmittedOrigin
import IxVMRefinement.L1.RawSelfReads

/-! # Actual native origins with reached self-name evidence

The walked load, canonical record, reader loop and actual native dispatch compose using
self-name agreement only for recursive references reached from the former's raw type.
Constructor frames stay concrete outputs; their own type reads and header names keep their
separate correspondence obligations.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- The actual native-origin step uses only the former type's reached recursive-reference names. -/
theorem native_former_input_of_checked_at_of_selfReads {base : Core.Ctx} {bindingAddr : _root_.Address}
    {block : Bytes.Address} {index : UInt64} {slot : Nat} {calls : List (Call F)}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    (projection : L1.CanonicalRecordAt base.E (Core.iprjAddr (Core.ixAddr block) slot))
    (projectionShape : projection.value.info = .iPrj ⟨index, Core.ixAddr block⟩)
    (indexToSlot : index.toNat = slot)
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members[slot]? = some (.indc ind))
    (checked : Claim.CheckedAtFull calls bindingAddr base.t
      (Core.iprjAddr (Core.ixAddr block) slot))
    (good : Core.Good base calls)
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)} {rawType : Core.KExpr}
    (caps : Ix.Kernel.IndCaps .anon)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ind.typ = .ok rawType)
    (keyed : ∀ address key, cx.keyAt address = .ok key → key = base.κ address)
    (selfKeyed : ∀ slot address reading key,
      L1.RecurUsed source.value.sharing.toList slot ind.typ →
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[slot]? = some address →
      self slot = some reading → reading = .ok key → key = base.κ address)
    (blobReads : L1.HashedBlobReadAgreement cx.blob calls) :
    Nonempty (NativeFormerRunInput base block (slot : F) source members ind rawType calls) := by
  obtain ⟨limit, beforeLoad, checkHeap, afterCheck, rc, addr, ptr, value, result, loadCalls, checkCalls,
    _, roles, addressRep, _, loaded, _, loadSubset, valueAt, checkedRun, checkedMember, checkSubset⟩ := checked
  obtain ⟨address, addressRep, addressEq⟩ := addressRep
  let projectionAt := projection.reindex addressEq
  have projectionAtShape : projectionAt.value.info = .iPrj ⟨index, Core.ixAddr block⟩ := projectionShape
  obtain ⟨parent, parentArg, middle, inner, parentEq, indexBound, parentRep, directLoad, innerSubset, _⟩ :=
    L1.get_ci_iPrj_subcall (base := base) projectionAt projectionAtShape addressRep
      (good.sub loadSubset) loaded
  have parentSame : parent = block := Decl.ixAddr_inj parentEq
  subst parent
  rw [indexToSlot] at directLoad indexBound
  have indexValue : ZMod.val (slot : F) = slot :=
    ZMod.val_natCast_of_lt (Nat.lt_trans indexBound (by decide))
  have memberAtField : members.toList[ZMod.val (slot : F)]? = some (.indc ind) := by
    rw [indexValue]
    simpa only [Array.getElem?_toList] using memberAt
  have directSubset : ∀ call ∈ inner, call ∈ calls :=
    fun call member => loadSubset call (innerSubset call member)
  obtain ⟨levelsBound, paramsBound, indicesBound, ctorCountBound⟩ :=
    L1.get_ci_iprj_header_bounds (base := base) source blockShape memberAtField
      (good.sub directSubset) parentRep directLoad
  obtain ⟨typePtr, blockPtr, actualBlock, payload, blockRep, blockEq⟩ :=
    native_former_header_exact (base := base) source blockShape memberAtField
      (good.sub directSubset) parentRep directLoad
  have blockSame : actualBlock = block := Decl.ixAddr_inj blockEq
  subst actualBlock
  have valueEq := Except.ok.inj (valueAt.symm.trans payload)
  subst value
  obtain ⟨localPrelude⟩ := Decl.native_prelude_calls checkedRun
  let prelude := localPrelude.mono checkSubset
  obtain ⟨annotated, tree, plan, stored, exactInput, built, planned, image,
    varsBounded, levelsDefined, noFvars⟩ :=
    observed_native_former_input_of_selfReads (base := base) (calls := calls) source blockShape memberAtField caps
      directLoad (good.sub directSubset) parentRep payload prelude.initialExtended good.2
      prelude.scopeRun prelude.scopeMember read keyed selfKeyed
      (fun address bytes hashed hashEq => blobReads address bytes (Core.hashed_mono directSubset hashed) hashEq)
  obtain ⟨exactValue, exactAt, exactInfo⟩ := exactInput
  have sameValue := Except.ok.inj (exactAt.symm.trans payload)
  subst exactValue
  exact ⟨{
    projectionSource := canonicalProjection_at_field projection projectionShape indexToSlot indexValue
    blockShape := blockShape, memberAt := memberAtField, levelsBound := levelsBound
    paramsBound := paramsBound, indicesBound := indicesBound, ctorCountBound := ctorCountBound
    limit := limit, rc := rc, typePtr := typePtr, blockPtr := blockPtr, heap := checkHeap
    annotated := annotated, addressPtr := addr, checkResult := result, checkAfter := afterCheck
    checkCalls := checkCalls, checkedRun := checkedRun, checkMember := checkedMember, checkSubset := checkSubset
    prelude := prelude, roles := roles.toRCRep, blockRep := blockRep
    stored := stored, represented := Decl.CIRepExact.induct_valRep exactInfo
    varsBounded := varsBounded, levelsDefined := levelsDefined, noFvars := noFvars
    tree := tree, plan := plan, built := built, planned := planned, image := image }⟩

/-- The actual native-origin step uses only the former type's reached recursive-reference names. -/
theorem native_former_input_of_member_of_selfReads {base : Core.Ctx} {bindingAddr : _root_.Address}
    {block : Bytes.Address} {members : Array Ixon.MutConst} {slot : Nat} {ind : Ixon.Inductive}
    {calls : List (Call F)}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    (blockShape : source.value.info = .muts members)
    (memberAt : members[slot]? = some (.indc ind))
    (checked : Claim.MutsMemberCheckedAtFull calls bindingAddr base.t (Core.ixAddr block) members slot)
    (good : Core.Good base calls) (coverage : L1.CanonicalHashCoverage base.E calls)
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)} {rawType : Core.KExpr}
    (caps : Ix.Kernel.IndCaps .anon)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ind.typ = .ok rawType)
    (keyed : ∀ address key, cx.keyAt address = .ok key → key = base.κ address)
    (selfKeyed : ∀ index address reading key,
      L1.RecurUsed source.value.sharing.toList index ind.typ →
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      self index = some reading → reading = .ok key → key = base.κ address)
    (blobReads : L1.HashedBlobReadAgreement cx.blob calls) :
    Nonempty (NativeFormerRunInput base block (slot : F) source members ind rawType calls) := by
  have slotBound := native_member_slot_bound (base := base) checked memberAt good.2
  have indexNat : slot.toUInt64.toNat = slot :=
    UInt64.toNat_ofNat_of_lt (Nat.lt_trans slotBound (by decide))
  obtain ⟨projection, shape, full⟩ := native_member_checked_source (base := base) checked memberAt good coverage
  have projectedInfo : projection.value.info = .iPrj ⟨slot.toUInt64, Core.ixAddr block⟩ :=
    congrArg Ixon.Constant.info shape
  exact native_former_input_of_checked_at_of_selfReads (base := base) (block := block)
    (index := slot.toUInt64) (slot := slot) source projection projectedInfo indexNat
    blockShape memberAt full good caps read keyed selfKeyed blobReads

/-- The actual native-origin step uses only the former type's reached recursive-reference names. -/
theorem admitted_native_former_input_of_selfReads {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
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
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)} {rawType : Core.KExpr}
    (caps : Ix.Kernel.IndCaps .anon)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ind.typ = .ok rawType)
    (keyed : ∀ address key, cx.keyAt address = .ok key → key = (nativeOriginCtx witness trace env lim).κ address)
    (selfKeyed : ∀ index address reading key,
      L1.RecurUsed source.value.sharing.toList index ind.typ →
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      self index = some reading → reading = .ok key → key = (nativeOriginCtx witness trace env lim).κ address)
    (blobReads : L1.HashedBlobReadAgreement cx.blob calls) :
    Nonempty (NativeFormerRunInput (nativeOriginCtx witness trace env lim) block (slot : F)
      source members ind rawType calls) := by
  have good : Core.Good (nativeOriginCtx witness trace env lim) calls :=
    admittedCore_good witness (fun _ => True) env lim claimBytes loaded bounded noCollision
  have coverage : L1.CanonicalHashCoverage (nativeOriginCtx witness trace env lim).E calls :=
    admitted_canonicalHashCoverage witness phase
  have member := admitted_native_member_check witness env lim source shape memberAt walked good
  exact native_former_input_of_member_of_selfReads source shape memberAt member good coverage caps read keyed selfKeyed blobReads

/-- The actual native-origin step uses only the former type's reached recursive-reference names. -/
theorem admitted_native_reader_dispatch_with_ctor_frames_of_selfReads {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
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
      L1.RecurUsed source.value.sharing.toList index ind.typ →
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
    obtain ⟨input⟩ := admitted_native_former_input_of_selfReads witness phase loaded bounded env lim claimBytes noCollision
      source shape memberAt walked {} frame.2.1 keyed selfKeyed blobReads
    rcases input.dispatch with native | modeled
    · obtain ⟨native, shapeCalls⟩ := native
      exact .inl ⟨generated, bare, readerBlock, row, declarations, lowered, types, frame, ctorFrames, paramCount,
        input, native, shapeCalls⟩
    · exact .inr ⟨input.blockPtr, input.heap, input.blockRep, modeled⟩
  · exact .inr ⟨blockPtr, heap, blockRep, modeled⟩

/-- The actual native-origin step uses only the former type's reached recursive-reference names. -/
theorem admitted_native_reader_origin_in_context_of_selfReads {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    (keepTrace : _root_.Address → Prop) (order : List _root_.Address)
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
    {state : Ix.Kernel.Reader.State .anon}
    {result : Ix.Kernel.Reader.Read .anon}
    (readerSource : (admittedNativeReaderCtx witness trace keepTrace order).store (Core.ixAddr block) =
      some source.value)
    (read : Ix.Kernel.Reader.readInductive (admittedNativeReaderCtx witness trace keepTrace order) state
      (Core.ixAddr block) source.value members = .ok result)
    (selfKeyed : ∀ index address reading key,
      L1.RecurUsed source.value.sharing.toList index ind.typ →
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      (if index < members.size then some ((admittedNativeReaderCtx witness trace keepTrace order).memberKey (.member (Core.ixAddr block) index)) else none) =
        some reading → reading = .ok key → key = (nativeOriginCtx witness trace env lim).κ address)
    :
    ZMod.val (slot : F) = slot ∧
    ((∃ (generated : List (Ix.Kernel.Declaration .anon)) (bare : Ix.Kernel.Reader.Read .anon)
        (readerBlock : Ix.Kernel.Reader.BlockRead .anon) (row : NativeFormerRow),
        result.decls.toList = generated ++ bare.decls.toList ∧
        Ix.Kernel.Reader.lowerInductiveBare readerBlock = .ok bare ∧ readerBlock.types.toList = [row] ∧
        NativeFormerReaderFrame (admittedNativeReaderCtx witness trace keepTrace order) (Core.ixAddr block)
          (Ix.Kernel.Reader.MemberReader.mk' (admittedNativeReaderCtx witness trace keepTrace order) source.value id
            (fun index => if index < members.size then
              some ((admittedNativeReaderCtx witness trace keepTrace order).memberKey (.member (Core.ixAddr block) index)) else none))
          (slot, ind) row ∧
        List.Forall₂
          (NativeCtorReaderCheckedFrame (admittedNativeReaderCtx witness trace keepTrace order) (Core.ixAddr block)
            (Ix.Kernel.Reader.MemberReader.mk' (admittedNativeReaderCtx witness trace keepTrace order) source.value id
              (fun index => if index < members.size then
                some ((admittedNativeReaderCtx witness trace keepTrace order).memberKey (.member (Core.ixAddr block) index)) else none)))
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
  have built : ∃ records : Array (_root_.Address × Ixon.Constant),
      (admittedNativeReaderCtx witness trace keepTrace order).index =
        Ix.Kernel.Reader.buildIndex (admittedNativeReaderCtx witness trace keepTrace order).store records :=
    ⟨_, rfl⟩
  obtain ⟨records, indexBuilt⟩ := built
  have agreement := admitted_native_reader_agreement witness phase keepTrace order claimBytes loaded noCollision
  exact admitted_native_reader_dispatch_with_ctor_frames_of_selfReads witness phase loaded bounded
    env lim claimBytes noCollision source shape memberAt walked indexBuilt readerSource read
    agreement.1 selfKeyed agreement.2

end IxVM.Refinement.Assembly
