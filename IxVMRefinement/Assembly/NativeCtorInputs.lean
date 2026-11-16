import IxVMRefinement.L1.ScopedRecords
import IxVMRefinement.L1.AnnotationCorrespondence
import IxVMRefinement.Assembly.ProjSafe
import IxVMRefinement.Assembly.BareState
import IxVMRefinement.Decl.NativeLoads

/-! # Native constructor inputs from actual conversion and scope checks

The scope validator supplies the reader type's bounds before conversion is strengthened to
an exact representation. The annotation and raw syntax belong to this observed read; no
agreement with another load or installed constructor is assumed.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core (KKey KExpr)

/-- The serialized type trace chooses the exact value of a fresh constructor read. -/
theorem native_ctor_value_of_trace {κ : _root_.Address → KKey}
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {ctor : Ixon.Constructor} {block : _root_.Address} {index : Nat}
    {value : SourceValue F} {plan : List Core.KLevel} {rawType : KExpr}
    (raw : L1.RawCtorValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h ctor block index value)
    (levels : L1.CITypeBinderLevels "Ctor" h value plan)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read ctor.typ = .ok rawType)
    (varsBounded : rawType.looseBVarsBounded 0 = true)
    (levelsDefined : rawType.allLevelParamsDefined (List.range ctor.lvls.toNat) = true)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (selfKeyed : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (blobReads : ∀ a bytes, (a, bytes) ∈ blobs → cx.blob a = some bytes) :
    ∃ cv : Ix.Kernel.ConstantVal .anon,
      IxVM.Consistency.ValStored cv
        ⟨κ (Core.cprjAddr block index ctor.cidx.toNat), List.range ctor.lvls.toNat, rawType⟩ ∧
      Decl.CIRepExact κ h value (.ctorInfo cv ctor.params.toNat ctor.fields.toNat) ∧
      L1.applyBinderTrace
        (fun level => Core.bmeta (L1.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
          some (cv.type, []) := by
  obtain ⟨levelBound, ctorIndexBound, paramsBound, fieldsBound, indexBound,
    typePtr, blockPtr, parent, parentEq, parentRep, rfl, rawTypeRep⟩ := raw
  obtain ⟨count, observedType, fields, shape, trace⟩ := levels
  simp only [Value.construct.injEq, List.cons.injEq, true_and] at shape
  obtain ⟨rfl, rfl, rfl⟩ := shape
  have positionalRead :
      (Ix.Kernel.Reader.MemberReader.mk' cx src
        (Ix.Kernel.Reader.recParam (List.range ctor.lvls.toNat)) self).read ctor.typ = .ok rawType := by
    rw [recParam_range]
    exact read
  obtain ⟨annotated, annotation, represented, readTrace⟩ := rawTypeRep.toTmCExactTrace
    (ps := List.range ctor.lvls.toNat) (by simp)
    (by simpa only [List.length_range] using levelBound)
    keyed selfKeyed blobReads positionalRead varsBounded levelsDefined
  let cv : Ix.Kernel.ConstantVal .anon :=
    ⟨κ (Core.cprjAddr block index ctor.cidx.toNat), List.range ctor.lvls.toNat, annotated⟩
  have valueRep : Decl.ValRepExact κ h (.field (ctor.lvls.toNat : F)) typePtr cv := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [cv]
    · simpa only [cv, List.length_range] using levelBound
    · simp only [cv, List.length_range]
      exact .refl _
    · exact represented
  have indexValue : ZMod.val (index : F) = index :=
    ZMod.val_natCast_of_lt (Nat.lt_trans indexBound (by decide))
  have ctorIndexValue : ZMod.val (ctor.cidx.toNat : F) = ctor.cidx.toNat :=
    ZMod.val_natCast_of_lt (Nat.lt_trans ctorIndexBound (by decide))
  refine ⟨cv, ⟨rfl, rfl, annotation⟩,
    .ctor valueRep rfl rfl ⟨paramsBound, fieldsBound⟩
      ⟨parent, (index : F), (ctor.cidx.toNat : F), parentRep, rfl, rfl, ?_⟩, ?_⟩
  · simp only [cv, indexValue, ctorIndexValue, parentEq]
  · simpa only [cv, List.append_nil] using readTrace plan trace []

/-- An actual validation call establishes the raw reader bounds, then exact conversion
produces the annotation and its raw heap syntax. -/
theorem validated_native_type_input {κ : _root_.Address → KKey}
    {calls cs : List (Call F)} {h₀ h h' : Heap F}
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {nlvls : Nat} {expr : Ixon.Expr} {tyPtr result : SourceValue F} {rawType : KExpr}
    (bounded : IxVM.Consistency.Bounded calls) (levelsBound : nlvls < 4294967296)
    (raw : L1.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h₀ 4294967295 expr tyPtr)
    (extended : Heap.Extends h₀ h)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read expr = .ok rawType)
    (validated : ObsFn Core.W "KernelCheck::validate_expr_well_scoped"
      [tyPtr, .field 0, .field (nlvls : F)] h result h' cs)
    (member : (⟨"KernelCheck::validate_expr_well_scoped",
      [tyPtr, .field 0, .field (nlvls : F)], h⟩ : Call F) ∈ calls)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (selfKeyed : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (blobReads : ∀ a bytes, (a, bytes) ∈ blobs → cx.blob a = some bytes) :
    ∃ annotated rawSyntax,
      IxVM.Consistency.Annotates annotated rawType ∧
      Decl.TmCExact κ h₀ annotated tyPtr ∧
      (∀ d Γ, Decl.RawTmExact κ d Γ h₀ 0 rawSyntax annotated tyPtr) ∧
      rawType.looseBVarsBounded 0 = true ∧
      rawType.allLevelParamsDefined (List.range nlvls) = true ∧ rawType.hasFvar = false := by
  obtain ⟨_, varsBound, paramsDefined⟩ :=
    validate_expr_well_scoped_spec bounded levelsBound raw extended read validated member
  have positionalRead :
      (Ix.Kernel.Reader.MemberReader.mk' cx src (Ix.Kernel.Reader.recParam (List.range nlvls))
        self).read expr = .ok rawType := by
    rw [recParam_range]
    exact read
  obtain ⟨annotated, annotation, exactRep⟩ := raw.toTmCExact
    (ps := List.range nlvls) (by simp) (by simpa only [List.length_range] using levelsBound)
    keyed selfKeyed blobReads positionalRead varsBound paramsDefined
  have exactRep : Decl.TmCExact κ h₀ annotated tyPtr := by
    simpa only [Decl.posOf_range] using exactRep
  obtain ⟨rawSyntax, rawRep⟩ := exactRep.raw
  exact ⟨annotated, rawSyntax, annotation, exactRep, rawRep, varsBound, paramsDefined,
    memberReader_read_noFvar read⟩

/-- Conversion plus the constructor's actual scope check supplies its exact constant value
and raw type. The result is local to this read and does not require semantic installation. -/
theorem validated_native_ctor_input {κ : _root_.Address → KKey}
    {calls cs : List (Call F)} {h₀ h h' : Heap F}
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {ctor : Ixon.Constructor} {block : _root_.Address} {index : Nat}
    {tyPtr blockPtr result : SourceValue F} {rawType : KExpr}
    (bounded : IxVM.Consistency.Bounded calls)
    (raw : L1.RawCtorValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h₀ ctor block index (.construct Core.kciEnum "Ctor"
        [.field (ctor.lvls.toNat : F), tyPtr, blockPtr, .field (index : F),
          .field (ctor.cidx.toNat : F), .field (ctor.params.toNat : F),
          .field (ctor.fields.toNat : F), L1.repBoolField ctor.isUnsafe]))
    (extended : Heap.Extends h₀ h)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read ctor.typ = .ok rawType)
    (validated : ObsFn Core.W "KernelCheck::validate_expr_well_scoped"
      [tyPtr, .field 0, .field (ctor.lvls.toNat : F)] h result h' cs)
    (member : (⟨"KernelCheck::validate_expr_well_scoped",
      [tyPtr, .field 0, .field (ctor.lvls.toNat : F)], h⟩ : Call F) ∈ calls)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (selfKeyed : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (blobReads : ∀ a bytes, (a, bytes) ∈ blobs → cx.blob a = some bytes) :
    ∃ (annotated : (Ix.Kernel.ConstantVal .anon)) (rawSyntax : KExpr),
      IxVM.Consistency.ValStored annotated
        ⟨κ (Core.cprjAddr block index ctor.cidx.toNat), List.range ctor.lvls.toNat, rawType⟩ ∧
      Decl.ValRepExact κ h₀ (.field (ctor.lvls.toNat : F)) tyPtr annotated ∧
      (∀ d Γ, Decl.RawTmExact κ d Γ h₀ 0 rawSyntax annotated.type tyPtr) ∧
      Decl.CIRepExact κ h₀ (.construct Core.kciEnum "Ctor"
        [.field (ctor.lvls.toNat : F), tyPtr, blockPtr, .field (index : F),
          .field (ctor.cidx.toNat : F), .field (ctor.params.toNat : F),
          .field (ctor.fields.toNat : F), L1.repBoolField ctor.isUnsafe])
        (.ctorInfo annotated ctor.params.toNat ctor.fields.toNat) ∧
      rawType.looseBVarsBounded 0 = true ∧
      rawType.allLevelParamsDefined (List.range ctor.lvls.toNat) = true ∧ rawType.hasFvar = false := by
  obtain ⟨levelsBound, ctorIndexBound, paramsBound, fieldsBound, indexBound,
    ty, blk, b, blockEq, blockRep, valueEq, rawTy⟩ := raw
  injection valueEq with _ _ fieldsEq
  simp only [List.cons.injEq, true_and, and_true] at fieldsEq
  obtain ⟨typeEq, blockPointerEq⟩ := fieldsEq
  subst ty blk
  obtain ⟨type, rawSyntax, annotation, exactRep, rawRep, varsBound, paramsDefined, closed⟩ :=
    validated_native_type_input bounded levelsBound rawTy extended read validated member
      keyed selfKeyed blobReads
  let cv : (Ix.Kernel.ConstantVal .anon) :=
    ⟨κ (Core.cprjAddr block index ctor.cidx.toNat), List.range ctor.lvls.toNat, type⟩
  have valueRep : Decl.ValRepExact κ h₀ (.field (ctor.lvls.toNat : F)) tyPtr cv := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [cv]
    · simpa only [cv, List.length_range] using levelsBound
    · simp only [cv, List.length_range]
      exact .refl _
    · simpa only [cv, Decl.posOf_range] using exactRep
  have indexValue : ZMod.val (index : F) = index :=
    ZMod.val_natCast_of_lt (Nat.lt_trans indexBound (by decide))
  have ctorIndexValue : ZMod.val (ctor.cidx.toNat : F) = ctor.cidx.toNat :=
    ZMod.val_natCast_of_lt (Nat.lt_trans ctorIndexBound (by decide))
  refine ⟨cv, rawSyntax, ⟨rfl, rfl, annotation⟩, valueRep, rawRep,
    .ctor valueRep rfl rfl ⟨paramsBound, fieldsBound⟩
      ⟨b, (index : F), (ctor.cidx.toNat : F), blockRep, rfl, rfl, ?_⟩,
    varsBound, paramsDefined, closed⟩
  simp only [cv, indexValue, ctorIndexValue, blockEq]

/-- A concrete constructor load, canonical parent record, and the following scope check
produce the annotated constructor input for that invocation. Hash coverage is restricted to
this actual load's trace. -/
theorem observed_native_ctor_input {base : Core.Ctx}
    {calls loadCalls scopeCalls : List (Call F)} {h₀ h₁ h₂ h₃ : Heap F}
    {block : Bytes.Address} {i j : F} {blockArg ptr result : SourceValue F}
    {nl ty blk indIdx ctorIdx np nf safe : SourceValue F}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {ctor : Ixon.Constructor}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    (ctorAt : ind.ctors.toList[ZMod.val j]? = some ctor)
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)} {rawType : Core.KExpr}
    (loaded : ObsFn Core.W "Ingress::get_ci_cprj" [blockArg, .field i, .field j]
      h₀ ptr h₁ loadCalls)
    (goodLoad : Core.Good base loadCalls)
    (blockRep : Bytes.RepAddressRef Core.addrTy h₀ block blockArg)
    (tag : loadValue h₁ ptr = .ok (.construct Core.kciEnum "Ctor"
      [nl, ty, blk, indIdx, ctorIdx, np, nf, safe]))
    (indexChecked : ctorIdx = .field j)
    (extended : Heap.Extends h₁ h₂)
    (bounded : IxVM.Consistency.Bounded calls)
    (validated : ObsFn Core.W "KernelCheck::validate_expr_well_scoped"
      [ty, .field 0, nl] h₂ result h₃ scopeCalls)
    (scopeMember : (⟨"KernelCheck::validate_expr_well_scoped",
      [ty, .field 0, nl], h₂⟩ : Call F) ∈ calls)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ctor.typ = .ok rawType)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = base.κ a)
    (selfKeyed : ∀ k a m name,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      self k = some m → m = .ok name → name = base.κ a)
    (blobReads : ∀ a bytes, Hashed loadCalls bytes → Address.blake3Pure bytes = a →
      cx.blob a = some bytes) :
    ∃ (annotated : Ix.Kernel.ConstantVal .anon) (rawSyntax : Core.KExpr),
      IxVM.Consistency.ValStored annotated
        ⟨base.κ (Core.cprjAddr (Core.ixAddr block) (ZMod.val i) (ZMod.val j)),
          List.range ctor.lvls.toNat, rawType⟩ ∧
      Decl.ValRepExact base.κ h₁ nl ty annotated ∧
      (∀ d Γ, Decl.RawTmExact base.κ d Γ h₁ 0 rawSyntax annotated.type ty) ∧
      Decl.CIPtrRepExact base.κ h₁ ptr (.ctorInfo annotated ctor.params.toNat ctor.fields.toNat) ∧
      rawType.looseBVarsBounded 0 = true ∧
      rawType.allLevelParamsDefined (List.range ctor.lvls.toNat) = true ∧ rawType.hasFvar = false := by
  obtain ⟨_, _, _, bytes, src, ms, member, ct, blobs, value, hh, ha, decoded, _,
    srcShape, memberAt', ctorAt', hashedBlobs, valueAt, raw⟩ :=
    L1.get_ci_cprj_spec goodLoad.2 blockRep loaded
  have bytesEq := Core.load_escape source.stored goodLoad.1 bytes hh ha
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
  rw [ctorAt] at ctorAt'
  injection ctorAt' with ctorEq
  subst ct
  have originalRaw := raw
  obtain ⟨_, ctorIndexBound, _, _, _, typePtr, parentPtr, parent, _, _, valueEq, _⟩ := raw
  subst value
  have fieldsEq := Except.ok.inj (tag.symm.trans valueAt)
  simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at fieldsEq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := fieldsEq
  have ctorIndex : ctor.cidx.toNat = ZMod.val j := by
    have equal := congrArg (fun x : F => ZMod.val x) (Value.field.inj indexChecked)
    rwa [ZMod.val_natCast_of_lt (Nat.lt_trans ctorIndexBound (by decide))] at equal
  obtain ⟨annotated, rawSyntax, stored, exactValue, rawTypeRep, exactInfo,
    varsBound, paramsDefined, closed⟩ :=
    validated_native_ctor_input bounded originalRaw extended read validated scopeMember
      keyed selfKeyed (fun a bytes member =>
        blobReads a bytes (hashedBlobs (a, bytes) member).1 (hashedBlobs (a, bytes) member).2)
  rw [ctorIndex] at stored
  exact ⟨annotated, rawSyntax, stored, exactValue, rawTypeRep, ⟨_, valueAt, exactInfo⟩,
    varsBound, paramsDefined, closed⟩

end IxVM.Refinement.Assembly
