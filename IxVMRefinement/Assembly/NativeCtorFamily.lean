import IxVMRefinement.Assembly.NativeCtorReads

/-! # Constructor load families from actual Source and reader runs

The Source loop supplies a guarded read at every slot. The reader frames identify the declared
rows. Their constructed raw/semantic origins then supply every repeated constructor load.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- The constructor rows of one native family have a complete indexed load contract. All
annotations and raw types are chosen from the actual guarded reads produced by the loop. -/
theorem native_ctor_load_family {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {params indices levels : Nat} {rootCalls loopCalls : List (Call F)}
    {rc former bp sortLevel result : SourceValue F} {h h' : Heap F}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    (countBound : ind.ctors.size < 549755813888)
    (paramsBound : params < 72057594037927936) (levelsBound : levels < 4294967296)
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
    (memberKeys : ∀ j < ind.ctors.size,
      cx.memberKey (.ctor (Core.ixAddr block) (ZMod.val i) j) =
        .ok (base.κ (Core.cprjAddr (Core.ixAddr block) (ZMod.val i) j)))
    (good : Core.Good base rootCalls)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = base.κ a)
    (selfKeyed : ∀ k a m name,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      self k = some m → m = .ok name → name = base.κ a)
    (blobReads : ∀ a bytes, Hashed rootCalls bytes → Address.blake3Pure bytes = a →
      cx.blob a = some bytes) :
    ∃ (annotated : List (Ix.Kernel.ConstantVal .anon × Nat)) (rawTypes : List Core.KExpr),
      Decl.CtorLoadAtIndex base.t block params i rootCalls
        (rows.map (fun row => (row.1, row.2.2))) annotated rawTypes ∧
      (∀ row ∈ rows, row.2.1 = params ∧ row.1.levelParams = List.range levels) := by
  have rowLength : rows.length = ind.ctors.size := by
    simpa [nativeCtorSlots] using frames.length_eq.symm
  have each : ∀ index : Fin rows.length,
      ∃ (cv : Ix.Kernel.ConstantVal .anon) (rawSyntax : Core.KExpr),
        IxVM.Consistency.ValStored cv rows[index.val].1 ∧
        rows[index.val].2.1 = params ∧ rows[index.val].1.levelParams = List.range levels ∧
        ∀ (bp ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)),
          (∀ call ∈ cs, call ∈ rootCalls) → Bytes.RepAddressRef Core.addrTy h block bp →
          ObsFn Core.W "Ingress::get_ci_cprj" [bp, .field i, .field (index.val : F)] h ptr h' cs →
          ∃ (ty parentPtr : SourceValue F) (parent : Bytes.Address),
            loadValue h' ptr = .ok (.construct Core.kciEnum "Ctor"
              [.field (levels : F), ty, parentPtr, .field i, .field (index.val : F),
                .field (params : F), .field (rows[index.val].2.2 : F), .field 0]) ∧
            Bytes.RepAddressRef Core.addrTy h' parent parentPtr ∧ Core.ixAddr parent = Core.ixAddr block ∧
            (∀ d Γ, Decl.RawTmExact base.κ d Γ h' 0 rawSyntax
              (Core.posOf cv.levelParams cv.type) ty) ∧
            Decl.CIRepExact base.κ h' (.construct Core.kciEnum "Ctor"
              [.field (levels : F), ty, parentPtr, .field i, .field (index.val : F),
                .field (params : F), .field (rows[index.val].2.2 : F), .field 0])
              (.ctorInfo cv params rows[index.val].2.2) := by
    intro index
    have slotBound : index.val < ind.ctors.size := by simpa only [rowLength] using index.isLt
    have slotValue : ZMod.val (index.val : F) = index.val :=
      ZMod.val_natCast_of_lt (Nat.lt_trans slotBound (Nat.lt_trans countBound (by decide)))
    let ctor := ind.ctors[index.val]
    have ctorAt : ind.ctors.toList[ZMod.val (index.val : F)]? = some ctor := by
      simp [slotValue, ctor, slotBound]
    have frameAt := (List.forall₂_iff_get.mp frames).2 index.val
      (by simpa [nativeCtorSlots] using slotBound) index.isLt
    have reader : NativeCtorReaderCheckedFrame cx (Core.ixAddr block)
        (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self)
        (ZMod.val i, ctor, ZMod.val (index.val : F)) rows[index.val] := by
      simpa [nativeCtorSlots, ctor, slotValue] using frameAt
    have nameKeyed : rows[index.val].1.name =
        base.κ (Core.cprjAddr (Core.ixAddr block) (ZMod.val i) (ZMod.val (index.val : F))) := by
      have keyRead : cx.memberKey (.ctor (Core.ixAddr block) (ZMod.val i) index.val) =
          .ok rows[index.val].1.name := by simpa only [slotValue] using reader.1.1
      rw [slotValue]
      exact Except.ok.inj (keyRead.symm.trans (memberKeys index.val slotBound))
    have observed : Nonempty (CtorScopeRead block i (index.val : F) 0 params levels rootCalls) := by
      simpa only [Nat.zero_add] using native_ctor_scope_reads countBound ind.ctors.size 0 (by omega)
        blockRep subset loop index.val slotBound
    obtain ⟨checked⟩ := observed
    exact checked.load_contract paramsBound levelsBound source
      blockShape memberAt ctorAt reader nameKeyed good keyed selfKeyed blobReads
  choose cvOf rawOf contract using each
  let annotated := List.ofFn fun index : Fin rows.length => (cvOf index, rows[index.val].2.2)
  let rawTypes := List.ofFn rawOf
  refine ⟨annotated, rawTypes, ⟨?_, ?_⟩, ?_⟩
  · simp [annotated]
  · intro j bound
    have rowBound : j < rows.length := by simpa using bound
    let index : Fin rows.length := ⟨j, rowBound⟩
    obtain ⟨stored, _, _, reload⟩ := contract index
    refine ⟨(rows[j].1, rows[j].2.2), cvOf index, ?_, ?_, stored, ?_⟩
    · simp [rowBound]
    · simp [annotated, index, rowBound]
    · intro blockArg ptr before after calls included represented evaluated
      obtain ⟨ty, parentPtr, parent, loaded, parentRep, parentEq, rawRep, exactInfo⟩ :=
        reload blockArg ptr before after calls included represented evaluated
      refine ⟨.field (levels : F), ty, parentPtr, .field (params : F), .field (rows[j].2.2 : F),
        parent, loaded, parentRep, parentEq, ?_, exactInfo⟩
      simpa [rawTypes, index, rowBound] using rawRep
  · intro row member
    obtain ⟨j, bound, rfl⟩ := List.getElem_of_mem member
    exact ⟨(contract ⟨j, bound⟩).2.1, (contract ⟨j, bound⟩).2.2.1⟩

end IxVM.Refinement.Assembly
