import IxVMRefinement.Assembly.NativeCtorInputs
import IxVMRefinement.L1.AnnotationCorrespondence
import IxVMRefinement.L1.RawSelfTrace

/-! # Native former inputs and repeated loads

Actual conversion traces determine the annotation used for a former. The same immutable record
can then be read again with that annotation while its semantic capability data stays explicit.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core (KKey KExpr)

/-- The actual former annotation needs self-name agreement only at recursive leaves reached by its raw type and sharing entries. -/
theorem native_former_value_of_trace_of_selfReads {κ : _root_.Address → KKey} [∀ a, Core.Resolved (κ a)]
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {ind : Ixon.Inductive} {block : _root_.Address} {index : Nat}
    {value : SourceValue F} {plan : List Core.KLevel} {rawType : KExpr}
    (caps : Ix.Kernel.IndCaps .anon)
    (raw : L1.RawInductValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h ind block index value)
    (levels : L1.CITypeBinderLevels "Induct" h value plan)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read ind.typ = .ok rawType)
    (varsBounded : rawType.looseBVarsBounded 0 = true)
    (levelsDefined : rawType.allLevelParamsDefined (List.range ind.lvls.toNat) = true)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (selfKeyed : ∀ i a m k, L1.RecurUsed src.sharing.toList i ind.typ →
      recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (blobReads : L1.BlobReadAgreement cx.blob blobs) :
    ∃ cv : Ix.Kernel.ConstantVal .anon,
      IxVM.Consistency.ValStored cv
        ⟨κ (Core.iprjAddr block index), List.range ind.lvls.toNat, rawType⟩ ∧
      Decl.CIRepExact κ h value (.indInfo cv caps) ∧
      L1.applyBinderTrace
        (fun level => Core.bmeta (L1.invPosLevel (List.range ind.lvls.toNat) level)) rawType plan =
          some (cv.type, []) := by
  obtain ⟨levelBound, paramsBound, indicesBound, ctorBound, indexBound,
    typePtr, blockPtr, parent, parentEq, parentRep, rfl, rawTypeRep⟩ := raw
  obtain ⟨count, observedType, fields, shape, trace⟩ := levels
  simp only [Value.construct.injEq, List.cons.injEq, true_and] at shape
  obtain ⟨rfl, rfl, rfl⟩ := shape
  have positionalRead :
      (Ix.Kernel.Reader.MemberReader.mk' cx src
        (Ix.Kernel.Reader.recParam (List.range ind.lvls.toNat)) self).read ind.typ = .ok rawType := by
    rw [recParam_range]
    exact read
  obtain ⟨annotated, annotation, represented, readTrace⟩ := rawTypeRep.toTmCExactTrace_of_selfReads
    (ps := List.range ind.lvls.toNat) (by simp)
    (by simpa only [List.length_range] using levelBound)
    keyed selfKeyed blobReads positionalRead varsBounded levelsDefined
  let cv : Ix.Kernel.ConstantVal .anon :=
    ⟨κ (Core.iprjAddr block index), List.range ind.lvls.toNat, annotated⟩
  have valueRep : Decl.ValRepExact κ h (.field (ind.lvls.toNat : F)) typePtr cv := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [cv]
    · simpa only [cv, List.length_range] using levelBound
    · simp only [cv, List.length_range]
      exact .refl _
    · exact represented
  have indexValue : ZMod.val (index : F) = index :=
    ZMod.val_natCast_of_lt (Nat.lt_trans indexBound (by decide))
  refine ⟨cv, ⟨rfl, rfl, annotation⟩,
    .induct valueRep ⟨ind.params.toNat, ind.indices.toNat, ind.ctors.size,
      rfl, rfl, rfl, paramsBound, indicesBound, ctorBound⟩
      ⟨parent, (index : F), parentRep, rfl, ?_⟩, ?_⟩
  · simp only [cv, indexValue, parentEq]
  · simpa only [cv, List.append_nil] using readTrace plan trace []

/-- The exact type trace chooses the annotated value represented by a raw former load. -/
theorem native_former_value_of_trace_of_blobAgreement {κ : _root_.Address → KKey} [∀ a, Core.Resolved (κ a)]
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {ind : Ixon.Inductive} {block : _root_.Address} {index : Nat}
    {value : SourceValue F} {plan : List Core.KLevel} {rawType : KExpr}
    (caps : Ix.Kernel.IndCaps .anon)
    (raw : L1.RawInductValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h ind block index value)
    (levels : L1.CITypeBinderLevels "Induct" h value plan)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read ind.typ = .ok rawType)
    (varsBounded : rawType.looseBVarsBounded 0 = true)
    (levelsDefined : rawType.allLevelParamsDefined (List.range ind.lvls.toNat) = true)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (selfKeyed : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (blobReads : L1.BlobReadAgreement cx.blob blobs) :
    ∃ cv : Ix.Kernel.ConstantVal .anon,
      IxVM.Consistency.ValStored cv
        ⟨κ (Core.iprjAddr block index), List.range ind.lvls.toNat, rawType⟩ ∧
      Decl.CIRepExact κ h value (.indInfo cv caps) ∧
      L1.applyBinderTrace
        (fun level => Core.bmeta (L1.invPosLevel (List.range ind.lvls.toNat) level)) rawType plan =
          some (cv.type, []) := by
  exact native_former_value_of_trace_of_selfReads caps raw levels read varsBounded levelsDefined keyed
    (fun i a m k _ => selfKeyed i a m k) blobReads

/-- Compatibility with full observed-blob membership. -/
theorem native_former_value_of_trace {κ : _root_.Address → KKey} [∀ a, Core.Resolved (κ a)]
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {ind : Ixon.Inductive} {block : _root_.Address} {index : Nat}
    {value : SourceValue F} {plan : List Core.KLevel} {rawType : KExpr}
    (caps : Ix.Kernel.IndCaps .anon)
    (raw : L1.RawInductValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h ind block index value)
    (levels : L1.CITypeBinderLevels "Induct" h value plan)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read ind.typ = .ok rawType)
    (varsBounded : rawType.looseBVarsBounded 0 = true)
    (levelsDefined : rawType.allLevelParamsDefined (List.range ind.lvls.toNat) = true)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (selfKeyed : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (blobReads : ∀ a bytes, (a, bytes) ∈ blobs → cx.blob a = some bytes) :
    ∃ cv : Ix.Kernel.ConstantVal .anon,
      IxVM.Consistency.ValStored cv
        ⟨κ (Core.iprjAddr block index), List.range ind.lvls.toNat, rawType⟩ ∧
      Decl.CIRepExact κ h value (.indInfo cv caps) ∧
      L1.applyBinderTrace
        (fun level => Core.bmeta (L1.invPosLevel (List.range ind.lvls.toNat) level)) rawType plan =
          some (cv.type, []) := by
  exact native_former_value_of_trace_of_blobAgreement caps raw levels read varsBounded levelsDefined keyed selfKeyed (L1.BlobReadAgreement.of_mem blobReads)

/-- The actual former load and scope check construct their input using self-name agreement only at reached recursive leaves of this former type. -/
theorem observed_native_former_input_of_selfReads {base : Core.Ctx}
    {calls loadCalls scopeCalls : List (Call F)} {h₀ h₁ h₂ h₃ : Heap F}
    {block : Bytes.Address} {i : F} {blockArg ptr result : SourceValue F}
    {nl ty np ni nc safe parent memberIndex : SourceValue F}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)} {rawType : KExpr}
    (caps : Ix.Kernel.IndCaps .anon)
    (loaded : ObsFn Core.W "Ingress::get_ci_iprj" [blockArg, .field i]
      h₀ ptr h₁ loadCalls)
    (goodLoad : Core.Good base loadCalls)
    (blockRep : Bytes.RepAddressRef Core.addrTy h₀ block blockArg)
    (tag : loadValue h₁ ptr = .ok (.construct Core.kciEnum "Induct"
      [nl, ty, np, ni, nc, safe, parent, memberIndex]))
    (extended : Heap.Extends h₁ h₂)
    (bounded : IxVM.Consistency.Bounded calls)
    (validated : ObsFn Core.W "KernelCheck::validate_expr_well_scoped"
      [ty, .field 0, nl] h₂ result h₃ scopeCalls)
    (scopeMember : (⟨"KernelCheck::validate_expr_well_scoped",
      [ty, .field 0, nl], h₂⟩ : Call F) ∈ calls)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ind.typ = .ok rawType)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = base.κ a)
    (selfKeyed : ∀ k a m name, L1.RecurUsed source.value.sharing.toList k ind.typ →
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      self k = some m → m = .ok name → name = base.κ a)
    (blobReads : L1.HashedBlobReadAgreement cx.blob loadCalls) :
    ∃ (cv : Ix.Kernel.ConstantVal .anon) (tree : L1.BinderTreeData) (plan : List Core.KLevel),
      IxVM.Consistency.ValStored cv
        ⟨base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)), List.range ind.lvls.toNat, rawType⟩ ∧
      Decl.CIPtrRepExact base.κ h₁ ptr (.indInfo cv caps) ∧
      L1.BinderTreeBuilt (L1.binderLeavesData source.value.binders.toList) tree ∧
      L1.binderRootPlan tree source.value.sharing.toList
        ((L1.mutsRootOffset members.toList (ZMod.val i) : Nat) : F) ind.typ = some plan ∧
      L1.applyBinderTrace
        (fun level => Core.bmeta (L1.invPosLevel (List.range ind.lvls.toNat) level)) rawType plan =
          some (cv.type, []) ∧
      rawType.looseBVarsBounded 0 = true ∧
      rawType.allLevelParamsDefined (List.range ind.lvls.toNat) = true ∧ rawType.hasFvar = false := by
  obtain ⟨_, _, bytes, src, ms, member, blobs, value, hashed, address, decoded, _,
    srcShape, memberAt', hashedBlobs, valueAt, raw, tree, plan, built, planned, levels⟩ :=
    L1.get_ci_iprj_origin_spec goodLoad.2 blockRep loaded
  have bytesEq := Core.load_escape source.stored goodLoad.1 bytes hashed address
  rw [bytesEq, source.decoded] at decoded
  injection decoded with sourceEq
  subst src
  rw [blockShape] at srcShape
  injection srcShape with membersEq
  subst ms
  rw [memberAt] at memberAt'
  injection memberAt' with memberEq
  injection memberEq with memberEq
  subst member
  have originalRaw := raw
  obtain ⟨levelBound, _, _, _, _, typePtr, parentPtr, _, _, _, valueEq, rawTypeRep⟩ := raw
  subst value
  have fieldsEq := Except.ok.inj (tag.symm.trans valueAt)
  simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at fieldsEq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := fieldsEq
  obtain ⟨_, varsBounded, levelsDefined⟩ :=
    validate_expr_well_scoped_spec bounded levelBound rawTypeRep extended read validated scopeMember
  obtain ⟨cv, stored, represented, image⟩ := native_former_value_of_trace_of_selfReads caps originalRaw levels
    read varsBounded levelsDefined keyed selfKeyed
    (fun a bytes member => blobReads a bytes
      (hashedBlobs (a, bytes) member).1 (hashedBlobs (a, bytes) member).2)
  exact ⟨cv, tree, plan, stored, ⟨_, valueAt, represented⟩, built, planned, image,
    varsBounded, levelsDefined, memberReader_read_noFvar read⟩

/-- One actual former load and its scope check construct the exact annotation and its
serialized origin. No semantic lookup of that former is required. -/
theorem observed_native_former_input_of_blobAgreement {base : Core.Ctx}
    {calls loadCalls scopeCalls : List (Call F)} {h₀ h₁ h₂ h₃ : Heap F}
    {block : Bytes.Address} {i : F} {blockArg ptr result : SourceValue F}
    {nl ty np ni nc safe parent memberIndex : SourceValue F}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)} {rawType : KExpr}
    (caps : Ix.Kernel.IndCaps .anon)
    (loaded : ObsFn Core.W "Ingress::get_ci_iprj" [blockArg, .field i]
      h₀ ptr h₁ loadCalls)
    (goodLoad : Core.Good base loadCalls)
    (blockRep : Bytes.RepAddressRef Core.addrTy h₀ block blockArg)
    (tag : loadValue h₁ ptr = .ok (.construct Core.kciEnum "Induct"
      [nl, ty, np, ni, nc, safe, parent, memberIndex]))
    (extended : Heap.Extends h₁ h₂)
    (bounded : IxVM.Consistency.Bounded calls)
    (validated : ObsFn Core.W "KernelCheck::validate_expr_well_scoped"
      [ty, .field 0, nl] h₂ result h₃ scopeCalls)
    (scopeMember : (⟨"KernelCheck::validate_expr_well_scoped",
      [ty, .field 0, nl], h₂⟩ : Call F) ∈ calls)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ind.typ = .ok rawType)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = base.κ a)
    (selfKeyed : ∀ k a m name,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      self k = some m → m = .ok name → name = base.κ a)
    (blobReads : L1.HashedBlobReadAgreement cx.blob loadCalls) :
    ∃ (cv : Ix.Kernel.ConstantVal .anon) (tree : L1.BinderTreeData) (plan : List Core.KLevel),
      IxVM.Consistency.ValStored cv
        ⟨base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)), List.range ind.lvls.toNat, rawType⟩ ∧
      Decl.CIPtrRepExact base.κ h₁ ptr (.indInfo cv caps) ∧
      L1.BinderTreeBuilt (L1.binderLeavesData source.value.binders.toList) tree ∧
      L1.binderRootPlan tree source.value.sharing.toList
        ((L1.mutsRootOffset members.toList (ZMod.val i) : Nat) : F) ind.typ = some plan ∧
      L1.applyBinderTrace
        (fun level => Core.bmeta (L1.invPosLevel (List.range ind.lvls.toNat) level)) rawType plan =
          some (cv.type, []) ∧
      rawType.looseBVarsBounded 0 = true ∧
      rawType.allLevelParamsDefined (List.range ind.lvls.toNat) = true ∧ rawType.hasFvar = false := by
  exact observed_native_former_input_of_selfReads source blockShape memberAt caps loaded goodLoad blockRep tag
    extended bounded validated scopeMember read keyed (fun k a m name _ => selfKeyed k a m name) blobReads

/-- Compatibility with full observed-blob membership. -/
theorem observed_native_former_input {base : Core.Ctx}
    {calls loadCalls scopeCalls : List (Call F)} {h₀ h₁ h₂ h₃ : Heap F}
    {block : Bytes.Address} {i : F} {blockArg ptr result : SourceValue F}
    {nl ty np ni nc safe parent memberIndex : SourceValue F}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)} {rawType : KExpr}
    (caps : Ix.Kernel.IndCaps .anon)
    (loaded : ObsFn Core.W "Ingress::get_ci_iprj" [blockArg, .field i]
      h₀ ptr h₁ loadCalls)
    (goodLoad : Core.Good base loadCalls)
    (blockRep : Bytes.RepAddressRef Core.addrTy h₀ block blockArg)
    (tag : loadValue h₁ ptr = .ok (.construct Core.kciEnum "Induct"
      [nl, ty, np, ni, nc, safe, parent, memberIndex]))
    (extended : Heap.Extends h₁ h₂)
    (bounded : IxVM.Consistency.Bounded calls)
    (validated : ObsFn Core.W "KernelCheck::validate_expr_well_scoped"
      [ty, .field 0, nl] h₂ result h₃ scopeCalls)
    (scopeMember : (⟨"KernelCheck::validate_expr_well_scoped",
      [ty, .field 0, nl], h₂⟩ : Call F) ∈ calls)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ind.typ = .ok rawType)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = base.κ a)
    (selfKeyed : ∀ k a m name,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      self k = some m → m = .ok name → name = base.κ a)
    (blobReads : ∀ a bytes, Hashed loadCalls bytes → Address.blake3Pure bytes = a →
      cx.blob a = some bytes) :
    ∃ (cv : Ix.Kernel.ConstantVal .anon) (tree : L1.BinderTreeData) (plan : List Core.KLevel),
      IxVM.Consistency.ValStored cv
        ⟨base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)), List.range ind.lvls.toNat, rawType⟩ ∧
      Decl.CIPtrRepExact base.κ h₁ ptr (.indInfo cv caps) ∧
      L1.BinderTreeBuilt (L1.binderLeavesData source.value.binders.toList) tree ∧
      L1.binderRootPlan tree source.value.sharing.toList
        ((L1.mutsRootOffset members.toList (ZMod.val i) : Nat) : F) ind.typ = some plan ∧
      L1.applyBinderTrace
        (fun level => Core.bmeta (L1.invPosLevel (List.range ind.lvls.toNat) level)) rawType plan =
          some (cv.type, []) ∧
      rawType.looseBVarsBounded 0 = true ∧
      rawType.allLevelParamsDefined (List.range ind.lvls.toNat) = true ∧ rawType.hasFvar = false := by
  exact observed_native_former_input_of_blobAgreement source blockShape memberAt caps loaded goodLoad blockRep tag extended bounded validated scopeMember read keyed selfKeyed (L1.HashedBlobReadAgreement.of_stored blobReads)

/-- Any later successful load of the same canonical former has the annotation constructed
by its initial load. Capability data is supplied by the semantic stage, not inferred from bytes. -/
theorem native_former_reload_of_blobAgreement {base : Core.Ctx} {block : Bytes.Address} {i : F}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)} {rawType : KExpr}
    {cv : Ix.Kernel.ConstantVal .anon} {tree : L1.BinderTreeData} {plan : List Core.KLevel}
    (stored : IxVM.Consistency.ValStored cv
      ⟨base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)), List.range ind.lvls.toNat, rawType⟩)
    (built : L1.BinderTreeBuilt (L1.binderLeavesData source.value.binders.toList) tree)
    (planned : L1.binderRootPlan tree source.value.sharing.toList
      ((L1.mutsRootOffset members.toList (ZMod.val i) : Nat) : F) ind.typ = some plan)
    (image : L1.applyBinderTrace
      (fun level => Core.bmeta (L1.invPosLevel (List.range ind.lvls.toNat) level)) rawType plan =
        some (cv.type, []))
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ind.typ = .ok rawType)
    (varsBounded : rawType.looseBVarsBounded 0 = true)
    (levelsDefined : rawType.allLevelParamsDefined (List.range ind.lvls.toNat) = true)
    {h h' : Heap F} {blockArg ptr : SourceValue F} {calls : List (Call F)}
    (caps : Ix.Kernel.IndCaps .anon)
    (loaded : ObsFn Core.W "Ingress::get_ci_iprj" [blockArg, .field i] h ptr h' calls)
    (goodLoad : Core.Good base calls)
    (blockRep : Bytes.RepAddressRef Core.addrTy h block blockArg)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = base.κ a)
    (selfKeyed : ∀ k a m name,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      self k = some m → m = .ok name → name = base.κ a)
    (blobReads : L1.HashedBlobReadAgreement cx.blob calls) :
    Decl.CIPtrRepExact base.κ h' ptr (.indInfo cv caps) := by
  obtain ⟨_, _, bytes, src, ms, member, blobs, value, hashed, address, decoded, _,
    srcShape, memberAt', hashedBlobs, valueAt, raw, tree', plan', built', planned', levels⟩ :=
    L1.get_ci_iprj_origin_spec goodLoad.2 blockRep loaded
  have bytesEq := Core.load_escape source.stored goodLoad.1 bytes hashed address
  rw [bytesEq, source.decoded] at decoded
  injection decoded with sourceEq
  subst src
  rw [blockShape] at srcShape
  injection srcShape with membersEq
  subst ms
  rw [memberAt] at memberAt'
  injection memberAt' with memberEq
  injection memberEq with memberEq
  subst member
  have treeEq := built.unique built'
  cases treeEq
  have planEq := Option.some.inj (planned.symm.trans planned')
  cases planEq
  obtain ⟨cv', stored', represented, image'⟩ := native_former_value_of_trace_of_blobAgreement caps raw levels
    read varsBounded levelsDefined keyed selfKeyed
    (fun a bytes member => blobReads a bytes
      (hashedBlobs (a, bytes) member).1 (hashedBlobs (a, bytes) member).2)
  have nameEq := stored'.1.trans stored.1.symm
  have paramsEq := stored'.2.1.trans stored.2.1.symm
  have typeEq := (L1.applyBinderTrace_unique image' image).1
  have valueEq : cv' = cv := by
    rcases cv' with ⟨name', params', type'⟩
    rcases cv with ⟨name, params, type⟩
    change name' = name at nameEq
    change params' = params at paramsEq
    change type' = type at typeEq
    cases nameEq
    cases paramsEq
    cases typeEq
    rfl
  cases valueEq
  exact ⟨_, valueAt, represented⟩

/-- Compatibility with full observed-blob membership. -/
theorem native_former_reload {base : Core.Ctx} {block : Bytes.Address} {i : F}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)} {rawType : KExpr}
    {cv : Ix.Kernel.ConstantVal .anon} {tree : L1.BinderTreeData} {plan : List Core.KLevel}
    (stored : IxVM.Consistency.ValStored cv
      ⟨base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)), List.range ind.lvls.toNat, rawType⟩)
    (built : L1.BinderTreeBuilt (L1.binderLeavesData source.value.binders.toList) tree)
    (planned : L1.binderRootPlan tree source.value.sharing.toList
      ((L1.mutsRootOffset members.toList (ZMod.val i) : Nat) : F) ind.typ = some plan)
    (image : L1.applyBinderTrace
      (fun level => Core.bmeta (L1.invPosLevel (List.range ind.lvls.toNat) level)) rawType plan =
        some (cv.type, []))
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ind.typ = .ok rawType)
    (varsBounded : rawType.looseBVarsBounded 0 = true)
    (levelsDefined : rawType.allLevelParamsDefined (List.range ind.lvls.toNat) = true)
    {h h' : Heap F} {blockArg ptr : SourceValue F} {calls : List (Call F)}
    (caps : Ix.Kernel.IndCaps .anon)
    (loaded : ObsFn Core.W "Ingress::get_ci_iprj" [blockArg, .field i] h ptr h' calls)
    (goodLoad : Core.Good base calls)
    (blockRep : Bytes.RepAddressRef Core.addrTy h block blockArg)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = base.κ a)
    (selfKeyed : ∀ k a m name,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      self k = some m → m = .ok name → name = base.κ a)
    (blobReads : ∀ a bytes, Hashed calls bytes → Address.blake3Pure bytes = a →
      cx.blob a = some bytes) :
    Decl.CIPtrRepExact base.κ h' ptr (.indInfo cv caps) := by
  exact native_former_reload_of_blobAgreement source blockShape memberAt stored built planned image read varsBounded levelsDefined caps loaded goodLoad blockRep keyed selfKeyed (L1.HashedBlobReadAgreement.of_stored blobReads)

/-- The outer constant loader preserves the same former annotation by its observed
inductive-projection dispatch. Its child load uses only the hashes in that actual subtrace. -/
theorem native_former_getCI_reload_of_blobAgreement {base : Core.Ctx} {block address : Bytes.Address}
    {index : UInt64}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    (projectionSource : L1.CanonicalRecordAt base.E (Core.ixAddr address))
    (projectionShape : projectionSource.value.info = .iPrj ⟨index, Core.ixAddr block⟩)
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val (index.toNat : F)]? = some (.indc ind))
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)} {rawType : KExpr}
    {cv : Ix.Kernel.ConstantVal .anon} {tree : L1.BinderTreeData} {plan : List Core.KLevel}
    (stored : IxVM.Consistency.ValStored cv
      ⟨base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val (index.toNat : F))),
        List.range ind.lvls.toNat, rawType⟩)
    (built : L1.BinderTreeBuilt (L1.binderLeavesData source.value.binders.toList) tree)
    (planned : L1.binderRootPlan tree source.value.sharing.toList
      ((L1.mutsRootOffset members.toList (ZMod.val (index.toNat : F)) : Nat) : F) ind.typ = some plan)
    (image : L1.applyBinderTrace
      (fun level => Core.bmeta (L1.invPosLevel (List.range ind.lvls.toNat) level)) rawType plan =
        some (cv.type, []))
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ind.typ = .ok rawType)
    (varsBounded : rawType.looseBVarsBounded 0 = true)
    (levelsDefined : rawType.allLevelParamsDefined (List.range ind.lvls.toNat) = true)
    {h h' : Heap F} {addr ptr : SourceValue F} {calls : List (Call F)}
    (caps : Ix.Kernel.IndCaps .anon)
    (loaded : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' calls)
    (goodLoad : Core.Good base calls)
    (addressRep : Bytes.RepAddressRef Core.addrTy h address addr)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = base.κ a)
    (selfKeyed : ∀ k a m name,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      self k = some m → m = .ok name → name = base.κ a)
    (blobReads : L1.HashedBlobReadAgreement cx.blob calls) :
    Decl.CIPtrRepExact base.κ h' ptr (.indInfo cv caps) := by
  obtain ⟨parent, blockArg, middle, inner, parentEq, _, parentRep, formerRun, subset, _⟩ :=
    L1.get_ci_iPrj_subcall projectionSource projectionShape addressRep goodLoad loaded
  have parentEq : parent = block := Decl.ixAddr_inj parentEq
  subst parent
  exact native_former_reload_of_blobAgreement source blockShape memberAt stored built planned image read
    varsBounded levelsDefined caps formerRun (goodLoad.sub subset) parentRep keyed selfKeyed
    (fun a bytes hashed hashEq => blobReads a bytes (Core.hashed_mono subset hashed) hashEq)

/-- Compatibility with full observed-blob membership. -/
theorem native_former_getCI_reload {base : Core.Ctx} {block address : Bytes.Address}
    {index : UInt64}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    (projectionSource : L1.CanonicalRecordAt base.E (Core.ixAddr address))
    (projectionShape : projectionSource.value.info = .iPrj ⟨index, Core.ixAddr block⟩)
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val (index.toNat : F)]? = some (.indc ind))
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)} {rawType : KExpr}
    {cv : Ix.Kernel.ConstantVal .anon} {tree : L1.BinderTreeData} {plan : List Core.KLevel}
    (stored : IxVM.Consistency.ValStored cv
      ⟨base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val (index.toNat : F))),
        List.range ind.lvls.toNat, rawType⟩)
    (built : L1.BinderTreeBuilt (L1.binderLeavesData source.value.binders.toList) tree)
    (planned : L1.binderRootPlan tree source.value.sharing.toList
      ((L1.mutsRootOffset members.toList (ZMod.val (index.toNat : F)) : Nat) : F) ind.typ = some plan)
    (image : L1.applyBinderTrace
      (fun level => Core.bmeta (L1.invPosLevel (List.range ind.lvls.toNat) level)) rawType plan =
        some (cv.type, []))
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ind.typ = .ok rawType)
    (varsBounded : rawType.looseBVarsBounded 0 = true)
    (levelsDefined : rawType.allLevelParamsDefined (List.range ind.lvls.toNat) = true)
    {h h' : Heap F} {addr ptr : SourceValue F} {calls : List (Call F)}
    (caps : Ix.Kernel.IndCaps .anon)
    (loaded : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' calls)
    (goodLoad : Core.Good base calls)
    (addressRep : Bytes.RepAddressRef Core.addrTy h address addr)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = base.κ a)
    (selfKeyed : ∀ k a m name,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      self k = some m → m = .ok name → name = base.κ a)
    (blobReads : ∀ a bytes, Hashed calls bytes → Address.blake3Pure bytes = a →
      cx.blob a = some bytes) :
    Decl.CIPtrRepExact base.κ h' ptr (.indInfo cv caps) := by
  exact native_former_getCI_reload_of_blobAgreement source projectionSource projectionShape blockShape memberAt stored built planned image read varsBounded levelsDefined caps loaded goodLoad addressRep keyed selfKeyed (L1.HashedBlobReadAgreement.of_stored blobReads)

end IxVM.Refinement.Assembly
