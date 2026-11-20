import IxVMRefinement.Ingress.ScopedRecords
import IxVMRefinement.Ingress.AnnotationCorrespondence
import IxVMRefinement.Ingress.RawSelfTrace
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

/-- The actual constructor type needs self-name agreement only at reached recursive leaves; its raw syntax and exact binder traces are retained together. -/
theorem native_ctor_value_with_raw_trace_of_selfReads {κ : _root_.Address → KKey} [∀ a, Core.Resolved (κ a)]
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {ctor : Ixon.Constructor} {block : _root_.Address} {index : Nat}
    {value : SourceValue F} {plan : List Core.KLevel} {rawType : KExpr}
    (raw : Ingress.RawCtorValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h ctor block index value)
    (levels : Ingress.CITypeBinderLevels "Ctor" h value plan)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read ctor.typ = .ok rawType)
    (varsBounded : rawType.looseBVarsBounded 0 = true)
    (levelsDefined : rawType.allLevelParamsDefined (List.range ctor.lvls.toNat) = true)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (selfKeyed : ∀ i a m k, Ingress.RecurUsed src.sharing.toList i ctor.typ →
      recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (blobReads : Ingress.BlobReadAgreement cx.blob blobs) :
    ∃ (cv : Ix.Kernel.ConstantVal .anon) (rawSyntax : KExpr),
      IxVM.Consistency.ValStored cv
        ⟨κ (Core.cprjAddr block index ctor.cidx.toNat), List.range ctor.lvls.toNat, rawType⟩ ∧
      Decl.CIRepExact κ h value (.ctorInfo cv ctor.params.toNat ctor.fields.toNat) ∧
      (∀ (nl ty parent member ctorIndex params fields safety : SourceValue F),
        value = .construct Core.kciEnum "Ctor" [nl, ty, parent, member, ctorIndex, params, fields, safety] →
        ∀ d Γ, Decl.RawTmExact κ d Γ h 0 rawSyntax cv.type ty) ∧
      Ingress.applyBinderTrace
        (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
          some (cv.type, []) ∧
      Ingress.applyRawBinderTrace
        (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
          some (rawSyntax, []) := by
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
  obtain ⟨rawSyntax, annotated, annotation, rawRepresented, readTrace, rawReadTrace⟩ :=
    rawTypeRep.toRawTmCExactTrace_of_selfReads
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
    · exact fun d Γ => (rawRepresented d Γ).toTmExact
  have indexValue : ZMod.val (index : F) = index :=
    ZMod.val_natCast_of_lt (Nat.lt_trans indexBound (by decide))
  have ctorIndexValue : ZMod.val (ctor.cidx.toNat : F) = ctor.cidx.toNat :=
    ZMod.val_natCast_of_lt (Nat.lt_trans ctorIndexBound (by decide))
  refine ⟨cv, rawSyntax, ⟨rfl, rfl, annotation⟩,
    .ctor valueRep rfl rfl ⟨paramsBound, fieldsBound⟩
      ⟨parent, (index : F), (ctor.cidx.toNat : F), parentRep, rfl, rfl, ?_⟩, ?_, ?_, ?_⟩
  · simp only [cv, indexValue, ctorIndexValue, parentEq]
  · intro nl ty parent member ctorIndex params fields safety shape d Γ
    simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at shape
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := shape
    simpa only [cv, Decl.posOf_range] using rawRepresented d Γ
  · simpa only [cv, List.append_nil] using readTrace plan trace []
  · simpa only [List.append_nil] using rawReadTrace plan trace []

/-- The serialized type trace chooses the exact value of a fresh constructor read. -/
theorem native_ctor_value_with_raw_trace_of_blobAgreement {κ : _root_.Address → KKey} [∀ a, Core.Resolved (κ a)]
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {ctor : Ixon.Constructor} {block : _root_.Address} {index : Nat}
    {value : SourceValue F} {plan : List Core.KLevel} {rawType : KExpr}
    (raw : Ingress.RawCtorValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h ctor block index value)
    (levels : Ingress.CITypeBinderLevels "Ctor" h value plan)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read ctor.typ = .ok rawType)
    (varsBounded : rawType.looseBVarsBounded 0 = true)
    (levelsDefined : rawType.allLevelParamsDefined (List.range ctor.lvls.toNat) = true)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (selfKeyed : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (blobReads : Ingress.BlobReadAgreement cx.blob blobs) :
    ∃ (cv : Ix.Kernel.ConstantVal .anon) (rawSyntax : KExpr),
      IxVM.Consistency.ValStored cv
        ⟨κ (Core.cprjAddr block index ctor.cidx.toNat), List.range ctor.lvls.toNat, rawType⟩ ∧
      Decl.CIRepExact κ h value (.ctorInfo cv ctor.params.toNat ctor.fields.toNat) ∧
      (∀ (nl ty parent member ctorIndex params fields safety : SourceValue F),
        value = .construct Core.kciEnum "Ctor" [nl, ty, parent, member, ctorIndex, params, fields, safety] →
        ∀ d Γ, Decl.RawTmExact κ d Γ h 0 rawSyntax cv.type ty) ∧
      Ingress.applyBinderTrace
        (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
          some (cv.type, []) ∧
      Ingress.applyRawBinderTrace
        (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
          some (rawSyntax, []) := by
  exact native_ctor_value_with_raw_trace_of_selfReads raw levels read varsBounded levelsDefined keyed
    (fun i a m k _ => selfKeyed i a m k) blobReads

/-- Compatibility with full observed-blob membership. -/
theorem native_ctor_value_with_raw_trace {κ : _root_.Address → KKey} [∀ a, Core.Resolved (κ a)]
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {ctor : Ixon.Constructor} {block : _root_.Address} {index : Nat}
    {value : SourceValue F} {plan : List Core.KLevel} {rawType : KExpr}
    (raw : Ingress.RawCtorValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h ctor block index value)
    (levels : Ingress.CITypeBinderLevels "Ctor" h value plan)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read ctor.typ = .ok rawType)
    (varsBounded : rawType.looseBVarsBounded 0 = true)
    (levelsDefined : rawType.allLevelParamsDefined (List.range ctor.lvls.toNat) = true)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (selfKeyed : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (blobReads : ∀ a bytes, (a, bytes) ∈ blobs → cx.blob a = some bytes) :
    ∃ (cv : Ix.Kernel.ConstantVal .anon) (rawSyntax : KExpr),
      IxVM.Consistency.ValStored cv
        ⟨κ (Core.cprjAddr block index ctor.cidx.toNat), List.range ctor.lvls.toNat, rawType⟩ ∧
      Decl.CIRepExact κ h value (.ctorInfo cv ctor.params.toNat ctor.fields.toNat) ∧
      (∀ (nl ty parent member ctorIndex params fields safety : SourceValue F),
        value = .construct Core.kciEnum "Ctor" [nl, ty, parent, member, ctorIndex, params, fields, safety] →
        ∀ d Γ, Decl.RawTmExact κ d Γ h 0 rawSyntax cv.type ty) ∧
      Ingress.applyBinderTrace
        (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
          some (cv.type, []) ∧
      Ingress.applyRawBinderTrace
        (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
          some (rawSyntax, []) := by
  exact native_ctor_value_with_raw_trace_of_blobAgreement raw levels read varsBounded levelsDefined keyed selfKeyed (Ingress.BlobReadAgreement.of_mem blobReads)

/-- Exact constructor value agreement, with the paired raw-syntax evidence omitted. -/
theorem native_ctor_value_of_trace_of_blobAgreement {κ : _root_.Address → KKey} [∀ a, Core.Resolved (κ a)]
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {ctor : Ixon.Constructor} {block : _root_.Address} {index : Nat}
    {value : SourceValue F} {plan : List Core.KLevel} {rawType : KExpr}
    (raw : Ingress.RawCtorValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h ctor block index value)
    (levels : Ingress.CITypeBinderLevels "Ctor" h value plan)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read ctor.typ = .ok rawType)
    (varsBounded : rawType.looseBVarsBounded 0 = true)
    (levelsDefined : rawType.allLevelParamsDefined (List.range ctor.lvls.toNat) = true)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (selfKeyed : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (blobReads : Ingress.BlobReadAgreement cx.blob blobs) :
    ∃ cv : Ix.Kernel.ConstantVal .anon,
      IxVM.Consistency.ValStored cv
        ⟨κ (Core.cprjAddr block index ctor.cidx.toNat), List.range ctor.lvls.toNat, rawType⟩ ∧
      Decl.CIRepExact κ h value (.ctorInfo cv ctor.params.toNat ctor.fields.toNat) ∧
      Ingress.applyBinderTrace
        (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
          some (cv.type, []) := by
  obtain ⟨cv, _, stored, represented, _, image, _⟩ := native_ctor_value_with_raw_trace_of_blobAgreement
    raw levels read varsBounded levelsDefined keyed selfKeyed blobReads
  exact ⟨cv, stored, represented, image⟩

/-- Compatibility with full observed-blob membership. -/
theorem native_ctor_value_of_trace {κ : _root_.Address → KKey} [∀ a, Core.Resolved (κ a)]
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {ctor : Ixon.Constructor} {block : _root_.Address} {index : Nat}
    {value : SourceValue F} {plan : List Core.KLevel} {rawType : KExpr}
    (raw : Ingress.RawCtorValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h ctor block index value)
    (levels : Ingress.CITypeBinderLevels "Ctor" h value plan)
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
      Ingress.applyBinderTrace
        (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
          some (cv.type, []) := by
  exact native_ctor_value_of_trace_of_blobAgreement raw levels read varsBounded levelsDefined keyed selfKeyed (Ingress.BlobReadAgreement.of_mem blobReads)

/-- An actual validation call establishes the raw reader bounds, then exact conversion
produces the annotation and its raw heap syntax. -/
theorem validated_native_type_input_of_blobAgreement {κ : _root_.Address → KKey} [∀ a, Core.Resolved (κ a)]
    {calls cs : List (Call F)} {h₀ h h' : Heap F}
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {nlvls : Nat} {expr : Ixon.Expr} {tyPtr result : SourceValue F} {rawType : KExpr}
    (bounded : IxVM.Consistency.Bounded calls) (levelsBound : nlvls < 4294967296)
    (raw : Ingress.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h₀ 4294967295 expr tyPtr)
    (extended : Heap.Extends h₀ h)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read expr = .ok rawType)
    (validated : ObsFn Core.W "KernelCheck::validate_expr_well_scoped"
      [tyPtr, .field 0, .field (nlvls : F)] h result h' cs)
    (member : (⟨"KernelCheck::validate_expr_well_scoped",
      [tyPtr, .field 0, .field (nlvls : F)], h⟩ : Call F) ∈ calls)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (selfKeyed : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (blobReads : Ingress.BlobReadAgreement cx.blob blobs) :
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
  obtain ⟨annotated, annotation, exactRep⟩ := raw.toTmCExact_of_blobAgreement
    (ps := List.range nlvls) (by simp) (by simpa only [List.length_range] using levelsBound)
    keyed selfKeyed blobReads positionalRead varsBound paramsDefined
  have exactRep : Decl.TmCExact κ h₀ annotated tyPtr := by
    simpa only [Decl.posOf_range] using exactRep
  obtain ⟨rawSyntax, rawRep⟩ := exactRep.raw
  exact ⟨annotated, rawSyntax, annotation, exactRep, rawRep, varsBound, paramsDefined,
    memberReader_read_noFvar read⟩

/-- Compatibility with full observed-blob membership. -/
theorem validated_native_type_input {κ : _root_.Address → KKey} [∀ a, Core.Resolved (κ a)]
    {calls cs : List (Call F)} {h₀ h h' : Heap F}
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {nlvls : Nat} {expr : Ixon.Expr} {tyPtr result : SourceValue F} {rawType : KExpr}
    (bounded : IxVM.Consistency.Bounded calls) (levelsBound : nlvls < 4294967296)
    (raw : Ingress.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
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
  exact validated_native_type_input_of_blobAgreement bounded levelsBound raw extended read validated member keyed selfKeyed (Ingress.BlobReadAgreement.of_mem blobReads)

/-- Conversion plus the constructor's actual scope check supplies its exact constant value
and raw type. The result is local to this read and does not require semantic installation. -/
theorem validated_native_ctor_input_of_blobAgreement {κ : _root_.Address → KKey} [∀ a, Core.Resolved (κ a)]
    {calls cs : List (Call F)} {h₀ h h' : Heap F}
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {ctor : Ixon.Constructor} {block : _root_.Address} {index : Nat}
    {tyPtr blockPtr result : SourceValue F} {rawType : KExpr}
    (bounded : IxVM.Consistency.Bounded calls)
    (raw : Ingress.RawCtorValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h₀ ctor block index (.construct Core.kciEnum "Ctor"
        [.field (ctor.lvls.toNat : F), tyPtr, blockPtr, .field (index : F),
          .field (ctor.cidx.toNat : F), .field (ctor.params.toNat : F),
          .field (ctor.fields.toNat : F), Ingress.repBoolField ctor.isUnsafe]))
    (extended : Heap.Extends h₀ h)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read ctor.typ = .ok rawType)
    (validated : ObsFn Core.W "KernelCheck::validate_expr_well_scoped"
      [tyPtr, .field 0, .field (ctor.lvls.toNat : F)] h result h' cs)
    (member : (⟨"KernelCheck::validate_expr_well_scoped",
      [tyPtr, .field 0, .field (ctor.lvls.toNat : F)], h⟩ : Call F) ∈ calls)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (selfKeyed : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (blobReads : Ingress.BlobReadAgreement cx.blob blobs) :
    ∃ (annotated : (Ix.Kernel.ConstantVal .anon)) (rawSyntax : KExpr),
      IxVM.Consistency.ValStored annotated
        ⟨κ (Core.cprjAddr block index ctor.cidx.toNat), List.range ctor.lvls.toNat, rawType⟩ ∧
      Decl.ValRepExact κ h₀ (.field (ctor.lvls.toNat : F)) tyPtr annotated ∧
      (∀ d Γ, Decl.RawTmExact κ d Γ h₀ 0 rawSyntax annotated.type tyPtr) ∧
      Decl.CIRepExact κ h₀ (.construct Core.kciEnum "Ctor"
        [.field (ctor.lvls.toNat : F), tyPtr, blockPtr, .field (index : F),
          .field (ctor.cidx.toNat : F), .field (ctor.params.toNat : F),
          .field (ctor.fields.toNat : F), Ingress.repBoolField ctor.isUnsafe])
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
    validated_native_type_input_of_blobAgreement bounded levelsBound rawTy extended read validated member
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

/-- Compatibility with full observed-blob membership. -/
theorem validated_native_ctor_input {κ : _root_.Address → KKey} [∀ a, Core.Resolved (κ a)]
    {calls cs : List (Call F)} {h₀ h h' : Heap F}
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {ctor : Ixon.Constructor} {block : _root_.Address} {index : Nat}
    {tyPtr blockPtr result : SourceValue F} {rawType : KExpr}
    (bounded : IxVM.Consistency.Bounded calls)
    (raw : Ingress.RawCtorValRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h₀ ctor block index (.construct Core.kciEnum "Ctor"
        [.field (ctor.lvls.toNat : F), tyPtr, blockPtr, .field (index : F),
          .field (ctor.cidx.toNat : F), .field (ctor.params.toNat : F),
          .field (ctor.fields.toNat : F), Ingress.repBoolField ctor.isUnsafe]))
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
          .field (ctor.fields.toNat : F), Ingress.repBoolField ctor.isUnsafe])
        (.ctorInfo annotated ctor.params.toNat ctor.fields.toNat) ∧
      rawType.looseBVarsBounded 0 = true ∧
      rawType.allLevelParamsDefined (List.range ctor.lvls.toNat) = true ∧ rawType.hasFvar = false := by
  exact validated_native_ctor_input_of_blobAgreement bounded raw extended read validated member keyed selfKeyed (Ingress.BlobReadAgreement.of_mem blobReads)

/-- The observed constructor load and scope check produce their exact input using only the recursive-reference names reached by this constructor type. -/
theorem observed_native_ctor_input_raw_origin_of_selfReads {base : Core.Ctx}
    {calls loadCalls scopeCalls : List (Call F)} {h₀ h₁ h₂ h₃ : Heap F}
    {block : Bytes.Address} {i j : F} {blockArg ptr result : SourceValue F}
    {nl ty blk indIdx ctorIdx np nf safe : SourceValue F}
    (source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block))
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
    (selfKeyed : ∀ k a m name, Ingress.RecurUsed source.value.sharing.toList k ctor.typ →
      (Ingress.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      self k = some m → m = .ok name → name = base.κ a)
    (blobReads : Ingress.HashedBlobReadAgreement cx.blob loadCalls) :
    ∃ (annotated : Ix.Kernel.ConstantVal .anon) (rawSyntax : Core.KExpr),
      IxVM.Consistency.ValStored annotated
        ⟨base.κ (Core.cprjAddr (Core.ixAddr block) (ZMod.val i) (ZMod.val j)),
          List.range ctor.lvls.toNat, rawType⟩ ∧
      Decl.ValRepExact base.κ h₁ nl ty annotated ∧
      (∀ d Γ, Decl.RawTmExact base.κ d Γ h₁ 0 rawSyntax annotated.type ty) ∧
      Decl.CIPtrRepExact base.κ h₁ ptr (.ctorInfo annotated ctor.params.toNat ctor.fields.toNat) ∧
      rawType.looseBVarsBounded 0 = true ∧
      rawType.allLevelParamsDefined (List.range ctor.lvls.toNat) = true ∧ rawType.hasFvar = false ∧
      ∃ (tree : Ingress.BinderTreeData) (plan : List Core.KLevel),
        Ingress.BinderTreeBuilt (Ingress.binderLeavesData source.value.binders.toList) tree ∧
        Ingress.binderRootPlan tree source.value.sharing.toList
          (((Ingress.mutsRootOffset members.toList (ZMod.val i) : Nat) : F) + 1 + j) ctor.typ = some plan ∧
        Ingress.applyBinderTrace
          (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
            some (annotated.type, []) ∧ ctor.cidx.toNat = ZMod.val j ∧
        Ingress.applyRawBinderTrace
          (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
            some (rawSyntax, []) := by
  obtain ⟨_, _, _, bytes, src, ms, member, ct, blobs, value, hh, ha, decoded, _,
    srcShape, memberAt', ctorAt', hashedBlobs, valueAt, raw, tree, plan, built, planned, levels⟩ :=
    Ingress.get_ci_cprj_origin_spec goodLoad.2 blockRep loaded
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
  obtain ⟨levelBound, ctorIndexBound, _, _, _, typePtr, parentPtr, parent, _, _, valueEq, rawTy⟩ := raw
  subst value
  have fieldsEq := Except.ok.inj (tag.symm.trans valueAt)
  simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at fieldsEq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := fieldsEq
  have ctorIndex : ctor.cidx.toNat = ZMod.val j := by
    have equal := congrArg (fun x : F => ZMod.val x) (Value.field.inj indexChecked)
    rwa [ZMod.val_natCast_of_lt (Nat.lt_trans ctorIndexBound (by decide))] at equal
  obtain ⟨_, varsBound, paramsDefined⟩ :=
    validate_expr_well_scoped_spec bounded levelBound rawTy extended read validated scopeMember
  obtain ⟨annotated, rawSyntax, stored, exactInfo, rawAt, image, rawImage⟩ :=
    native_ctor_value_with_raw_trace_of_selfReads originalRaw levels read varsBound paramsDefined keyed selfKeyed
      (fun a bytes member =>
        blobReads a bytes (hashedBlobs (a, bytes) member).1 (hashedBlobs (a, bytes) member).2)
  have exactValue := exactInfo.ctor_valRep
  have rawTypeRep : ∀ d Γ, Decl.RawTmExact base.κ d Γ h₁ 0 rawSyntax annotated.type ty :=
    rawAt _ _ _ _ _ _ _ _ rfl
  rw [ctorIndex] at stored
  exact ⟨annotated, rawSyntax, stored, exactValue, rawTypeRep, ⟨_, valueAt, exactInfo⟩,
    varsBound, paramsDefined, memberReader_read_noFvar read,
    tree, plan, built, planned, image, ctorIndex, rawImage⟩

/-- A concrete constructor load, canonical parent record, and the following scope check
produce the annotated constructor input for that invocation. Hash coverage is restricted to
this actual load's trace. -/
theorem observed_native_ctor_input_raw_origin_of_blobAgreement {base : Core.Ctx}
    {calls loadCalls scopeCalls : List (Call F)} {h₀ h₁ h₂ h₃ : Heap F}
    {block : Bytes.Address} {i j : F} {blockArg ptr result : SourceValue F}
    {nl ty blk indIdx ctorIdx np nf safe : SourceValue F}
    (source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block))
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
      (Ingress.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      self k = some m → m = .ok name → name = base.κ a)
    (blobReads : Ingress.HashedBlobReadAgreement cx.blob loadCalls) :
    ∃ (annotated : Ix.Kernel.ConstantVal .anon) (rawSyntax : Core.KExpr),
      IxVM.Consistency.ValStored annotated
        ⟨base.κ (Core.cprjAddr (Core.ixAddr block) (ZMod.val i) (ZMod.val j)),
          List.range ctor.lvls.toNat, rawType⟩ ∧
      Decl.ValRepExact base.κ h₁ nl ty annotated ∧
      (∀ d Γ, Decl.RawTmExact base.κ d Γ h₁ 0 rawSyntax annotated.type ty) ∧
      Decl.CIPtrRepExact base.κ h₁ ptr (.ctorInfo annotated ctor.params.toNat ctor.fields.toNat) ∧
      rawType.looseBVarsBounded 0 = true ∧
      rawType.allLevelParamsDefined (List.range ctor.lvls.toNat) = true ∧ rawType.hasFvar = false ∧
      ∃ (tree : Ingress.BinderTreeData) (plan : List Core.KLevel),
        Ingress.BinderTreeBuilt (Ingress.binderLeavesData source.value.binders.toList) tree ∧
        Ingress.binderRootPlan tree source.value.sharing.toList
          (((Ingress.mutsRootOffset members.toList (ZMod.val i) : Nat) : F) + 1 + j) ctor.typ = some plan ∧
        Ingress.applyBinderTrace
          (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
            some (annotated.type, []) ∧ ctor.cidx.toNat = ZMod.val j ∧
        Ingress.applyRawBinderTrace
          (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
            some (rawSyntax, []) := by
  exact observed_native_ctor_input_raw_origin_of_selfReads source blockShape memberAt ctorAt loaded goodLoad
    blockRep tag indexChecked extended bounded validated scopeMember read keyed
    (fun k a m name _ => selfKeyed k a m name) blobReads

/-- Compatibility with full observed-blob membership. -/
theorem observed_native_ctor_input_raw_origin {base : Core.Ctx}
    {calls loadCalls scopeCalls : List (Call F)} {h₀ h₁ h₂ h₃ : Heap F}
    {block : Bytes.Address} {i j : F} {blockArg ptr result : SourceValue F}
    {nl ty blk indIdx ctorIdx np nf safe : SourceValue F}
    (source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block))
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
      (Ingress.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
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
      rawType.allLevelParamsDefined (List.range ctor.lvls.toNat) = true ∧ rawType.hasFvar = false ∧
      ∃ (tree : Ingress.BinderTreeData) (plan : List Core.KLevel),
        Ingress.BinderTreeBuilt (Ingress.binderLeavesData source.value.binders.toList) tree ∧
        Ingress.binderRootPlan tree source.value.sharing.toList
          (((Ingress.mutsRootOffset members.toList (ZMod.val i) : Nat) : F) + 1 + j) ctor.typ = some plan ∧
        Ingress.applyBinderTrace
          (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
            some (annotated.type, []) ∧ ctor.cidx.toNat = ZMod.val j ∧
        Ingress.applyRawBinderTrace
          (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
            some (rawSyntax, []) := by
  exact observed_native_ctor_input_raw_origin_of_blobAgreement source blockShape memberAt ctorAt loaded goodLoad blockRep tag indexChecked extended bounded validated scopeMember read keyed selfKeyed (Ingress.HashedBlobReadAgreement.of_stored blobReads)

/-- The constructor annotation origin, with its additional raw-syntax image omitted. -/
theorem observed_native_ctor_input_origin_of_blobAgreement {base : Core.Ctx}
    {calls loadCalls scopeCalls : List (Call F)} {h₀ h₁ h₂ h₃ : Heap F}
    {block : Bytes.Address} {i j : F} {blockArg ptr result : SourceValue F}
    {nl ty blk indIdx ctorIdx np nf safe : SourceValue F}
    (source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block))
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
      (Ingress.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      self k = some m → m = .ok name → name = base.κ a)
    (blobReads : Ingress.HashedBlobReadAgreement cx.blob loadCalls) :
    ∃ (annotated : Ix.Kernel.ConstantVal .anon) (rawSyntax : Core.KExpr),
      IxVM.Consistency.ValStored annotated
        ⟨base.κ (Core.cprjAddr (Core.ixAddr block) (ZMod.val i) (ZMod.val j)),
          List.range ctor.lvls.toNat, rawType⟩ ∧
      Decl.ValRepExact base.κ h₁ nl ty annotated ∧
      (∀ d Γ, Decl.RawTmExact base.κ d Γ h₁ 0 rawSyntax annotated.type ty) ∧
      Decl.CIPtrRepExact base.κ h₁ ptr (.ctorInfo annotated ctor.params.toNat ctor.fields.toNat) ∧
      rawType.looseBVarsBounded 0 = true ∧
      rawType.allLevelParamsDefined (List.range ctor.lvls.toNat) = true ∧ rawType.hasFvar = false ∧
      ∃ (tree : Ingress.BinderTreeData) (plan : List Core.KLevel),
        Ingress.BinderTreeBuilt (Ingress.binderLeavesData source.value.binders.toList) tree ∧
        Ingress.binderRootPlan tree source.value.sharing.toList
          (((Ingress.mutsRootOffset members.toList (ZMod.val i) : Nat) : F) + 1 + j) ctor.typ = some plan ∧
        Ingress.applyBinderTrace
          (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
            some (annotated.type, []) ∧ ctor.cidx.toNat = ZMod.val j := by
  obtain ⟨annotated, rawSyntax, stored, exactValue, rawTypeRep, exactInfo,
    varsBound, paramsDefined, closed, tree, plan, built, planned, image, index, _⟩ :=
    observed_native_ctor_input_raw_origin_of_blobAgreement source blockShape memberAt ctorAt loaded goodLoad blockRep
      tag indexChecked extended bounded validated scopeMember read keyed selfKeyed blobReads
  exact ⟨annotated, rawSyntax, stored, exactValue, rawTypeRep, exactInfo,
    varsBound, paramsDefined, closed, tree, plan, built, planned, image, index⟩

/-- Compatibility with full observed-blob membership. -/
theorem observed_native_ctor_input_origin {base : Core.Ctx}
    {calls loadCalls scopeCalls : List (Call F)} {h₀ h₁ h₂ h₃ : Heap F}
    {block : Bytes.Address} {i j : F} {blockArg ptr result : SourceValue F}
    {nl ty blk indIdx ctorIdx np nf safe : SourceValue F}
    (source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block))
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
      (Ingress.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
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
      rawType.allLevelParamsDefined (List.range ctor.lvls.toNat) = true ∧ rawType.hasFvar = false ∧
      ∃ (tree : Ingress.BinderTreeData) (plan : List Core.KLevel),
        Ingress.BinderTreeBuilt (Ingress.binderLeavesData source.value.binders.toList) tree ∧
        Ingress.binderRootPlan tree source.value.sharing.toList
          (((Ingress.mutsRootOffset members.toList (ZMod.val i) : Nat) : F) + 1 + j) ctor.typ = some plan ∧
        Ingress.applyBinderTrace
          (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
            some (annotated.type, []) ∧ ctor.cidx.toNat = ZMod.val j := by
  exact observed_native_ctor_input_origin_of_blobAgreement source blockShape memberAt ctorAt loaded goodLoad blockRep tag indexChecked extended bounded validated scopeMember read keyed selfKeyed (Ingress.HashedBlobReadAgreement.of_stored blobReads)

/-- The original per-read constructor interface, omitting its retained annotation origin. -/
theorem observed_native_ctor_input_of_blobAgreement {base : Core.Ctx}
    {calls loadCalls scopeCalls : List (Call F)} {h₀ h₁ h₂ h₃ : Heap F}
    {block : Bytes.Address} {i j : F} {blockArg ptr result : SourceValue F}
    {nl ty blk indIdx ctorIdx np nf safe : SourceValue F}
    (source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block))
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
      (Ingress.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      self k = some m → m = .ok name → name = base.κ a)
    (blobReads : Ingress.HashedBlobReadAgreement cx.blob loadCalls) :
    ∃ (annotated : Ix.Kernel.ConstantVal .anon) (rawSyntax : Core.KExpr),
      IxVM.Consistency.ValStored annotated
        ⟨base.κ (Core.cprjAddr (Core.ixAddr block) (ZMod.val i) (ZMod.val j)),
          List.range ctor.lvls.toNat, rawType⟩ ∧
      Decl.ValRepExact base.κ h₁ nl ty annotated ∧
      (∀ d Γ, Decl.RawTmExact base.κ d Γ h₁ 0 rawSyntax annotated.type ty) ∧
      Decl.CIPtrRepExact base.κ h₁ ptr (.ctorInfo annotated ctor.params.toNat ctor.fields.toNat) ∧
      rawType.looseBVarsBounded 0 = true ∧
      rawType.allLevelParamsDefined (List.range ctor.lvls.toNat) = true ∧ rawType.hasFvar = false := by
  obtain ⟨annotated, rawSyntax, stored, exactValue, rawTypeRep, exactInfo,
    varsBound, paramsDefined, closed, _⟩ :=
    observed_native_ctor_input_origin_of_blobAgreement source blockShape memberAt ctorAt loaded goodLoad blockRep
      tag indexChecked extended bounded validated scopeMember read keyed selfKeyed blobReads
  exact ⟨annotated, rawSyntax, stored, exactValue, rawTypeRep, exactInfo, varsBound, paramsDefined, closed⟩

/-- Compatibility with full observed-blob membership. -/
theorem observed_native_ctor_input {base : Core.Ctx}
    {calls loadCalls scopeCalls : List (Call F)} {h₀ h₁ h₂ h₃ : Heap F}
    {block : Bytes.Address} {i j : F} {blockArg ptr result : SourceValue F}
    {nl ty blk indIdx ctorIdx np nf safe : SourceValue F}
    (source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block))
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
      (Ingress.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
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
  exact observed_native_ctor_input_of_blobAgreement source blockShape memberAt ctorAt loaded goodLoad blockRep tag indexChecked extended bounded validated scopeMember read keyed selfKeyed (Ingress.HashedBlobReadAgreement.of_stored blobReads)

/-- A later raw constructor query agrees with the annotation constructed by its actual
scope-checked load, whether or not that constructor is installed in the semantic stage. -/
theorem native_ctor_reload_of_blobAgreement {base : Core.Ctx} {block : Bytes.Address} {i j : F}
    (source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {ctor : Ixon.Constructor}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    (ctorAt : ind.ctors.toList[ZMod.val j]? = some ctor)
    (ctorIndex : ctor.cidx.toNat = ZMod.val j)
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)} {rawType : KExpr}
    {cv : Ix.Kernel.ConstantVal .anon} {tree : Ingress.BinderTreeData} {plan : List Core.KLevel}
    (stored : IxVM.Consistency.ValStored cv
      ⟨base.κ (Core.cprjAddr (Core.ixAddr block) (ZMod.val i) (ZMod.val j)),
        List.range ctor.lvls.toNat, rawType⟩)
    (built : Ingress.BinderTreeBuilt (Ingress.binderLeavesData source.value.binders.toList) tree)
    (planned : Ingress.binderRootPlan tree source.value.sharing.toList
      (((Ingress.mutsRootOffset members.toList (ZMod.val i) : Nat) : F) + 1 + j) ctor.typ = some plan)
    (image : Ingress.applyBinderTrace
      (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
        some (cv.type, []))
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ctor.typ = .ok rawType)
    (varsBounded : rawType.looseBVarsBounded 0 = true)
    (levelsDefined : rawType.allLevelParamsDefined (List.range ctor.lvls.toNat) = true)
    {h h' : Heap F} {blockArg ptr : SourceValue F} {calls : List (Call F)}
    (loaded : ObsFn Core.W "Ingress::get_ci_cprj" [blockArg, .field i, .field j] h ptr h' calls)
    (goodLoad : Core.Good base calls)
    (blockRep : Bytes.RepAddressRef Core.addrTy h block blockArg)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = base.κ a)
    (selfKeyed : ∀ k a m name,
      (Ingress.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      self k = some m → m = .ok name → name = base.κ a)
    (blobReads : Ingress.HashedBlobReadAgreement cx.blob calls) :
    Decl.CIPtrRepExact base.κ h' ptr (.ctorInfo cv ctor.params.toNat ctor.fields.toNat) := by
  obtain ⟨_, _, _, bytes, src, ms, member, ct, blobs, value, hashed, address, decoded, _,
    srcShape, memberAt', ctorAt', hashedBlobs, valueAt, raw, tree', plan', built', planned', levels⟩ :=
    Ingress.get_ci_cprj_origin_spec goodLoad.2 blockRep loaded
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
  rw [ctorAt] at ctorAt'
  injection ctorAt' with ctorEq
  subst ct
  have treeEq := built.unique built'
  cases treeEq
  have planEq := Option.some.inj (planned.symm.trans planned')
  cases planEq
  obtain ⟨cv', stored', represented, image'⟩ := native_ctor_value_of_trace_of_blobAgreement raw levels
    read varsBounded levelsDefined keyed selfKeyed
    (fun a bytes member => blobReads a bytes
      (hashedBlobs (a, bytes) member).1 (hashedBlobs (a, bytes) member).2)
  rw [ctorIndex] at stored'
  have nameEq := stored'.1.trans stored.1.symm
  have paramsEq := stored'.2.1.trans stored.2.1.symm
  have typeEq := (Ingress.applyBinderTrace_unique image' image).1
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
theorem native_ctor_reload {base : Core.Ctx} {block : Bytes.Address} {i j : F}
    (source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {ctor : Ixon.Constructor}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    (ctorAt : ind.ctors.toList[ZMod.val j]? = some ctor)
    (ctorIndex : ctor.cidx.toNat = ZMod.val j)
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)} {rawType : KExpr}
    {cv : Ix.Kernel.ConstantVal .anon} {tree : Ingress.BinderTreeData} {plan : List Core.KLevel}
    (stored : IxVM.Consistency.ValStored cv
      ⟨base.κ (Core.cprjAddr (Core.ixAddr block) (ZMod.val i) (ZMod.val j)),
        List.range ctor.lvls.toNat, rawType⟩)
    (built : Ingress.BinderTreeBuilt (Ingress.binderLeavesData source.value.binders.toList) tree)
    (planned : Ingress.binderRootPlan tree source.value.sharing.toList
      (((Ingress.mutsRootOffset members.toList (ZMod.val i) : Nat) : F) + 1 + j) ctor.typ = some plan)
    (image : Ingress.applyBinderTrace
      (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
        some (cv.type, []))
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ctor.typ = .ok rawType)
    (varsBounded : rawType.looseBVarsBounded 0 = true)
    (levelsDefined : rawType.allLevelParamsDefined (List.range ctor.lvls.toNat) = true)
    {h h' : Heap F} {blockArg ptr : SourceValue F} {calls : List (Call F)}
    (loaded : ObsFn Core.W "Ingress::get_ci_cprj" [blockArg, .field i, .field j] h ptr h' calls)
    (goodLoad : Core.Good base calls)
    (blockRep : Bytes.RepAddressRef Core.addrTy h block blockArg)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = base.κ a)
    (selfKeyed : ∀ k a m name,
      (Ingress.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      self k = some m → m = .ok name → name = base.κ a)
    (blobReads : ∀ a bytes, Hashed calls bytes → Address.blake3Pure bytes = a →
      cx.blob a = some bytes) :
    Decl.CIPtrRepExact base.κ h' ptr (.ctorInfo cv ctor.params.toNat ctor.fields.toNat) := by
  exact native_ctor_reload_of_blobAgreement source blockShape memberAt ctorAt ctorIndex stored built planned image read varsBounded levelsDefined loaded goodLoad blockRep keyed selfKeyed (Ingress.HashedBlobReadAgreement.of_stored blobReads)

/-- Repeated constructor loads also retain the same raw syntax, including let cells. -/
theorem native_ctor_raw_reload_with_shape_of_blobAgreement {base : Core.Ctx} {block : Bytes.Address} {i j : F}
    (source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {ctor : Ixon.Constructor}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    (ctorAt : ind.ctors.toList[ZMod.val j]? = some ctor)
    (ctorIndex : ctor.cidx.toNat = ZMod.val j)
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)} {rawType rawSyntax : KExpr}
    {cv : Ix.Kernel.ConstantVal .anon} {tree : Ingress.BinderTreeData} {plan : List Core.KLevel}
    (stored : IxVM.Consistency.ValStored cv
      ⟨base.κ (Core.cprjAddr (Core.ixAddr block) (ZMod.val i) (ZMod.val j)),
        List.range ctor.lvls.toNat, rawType⟩)
    (built : Ingress.BinderTreeBuilt (Ingress.binderLeavesData source.value.binders.toList) tree)
    (planned : Ingress.binderRootPlan tree source.value.sharing.toList
      (((Ingress.mutsRootOffset members.toList (ZMod.val i) : Nat) : F) + 1 + j) ctor.typ = some plan)
    (image : Ingress.applyBinderTrace
      (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
        some (cv.type, []))
    (rawImage : Ingress.applyRawBinderTrace
      (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
        some (rawSyntax, []))
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ctor.typ = .ok rawType)
    (varsBounded : rawType.looseBVarsBounded 0 = true)
    (levelsDefined : rawType.allLevelParamsDefined (List.range ctor.lvls.toNat) = true)
    {h h' : Heap F} {blockArg ptr : SourceValue F} {calls : List (Call F)}
    (loaded : ObsFn Core.W "Ingress::get_ci_cprj" [blockArg, .field i, .field j] h ptr h' calls)
    (goodLoad : Core.Good base calls)
    (blockRep : Bytes.RepAddressRef Core.addrTy h block blockArg)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = base.κ a)
    (selfKeyed : ∀ k a m name,
      (Ingress.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      self k = some m → m = .ok name → name = base.κ a)
    (blobReads : Ingress.HashedBlobReadAgreement cx.blob calls) :
    ∃ value, loadValue h' ptr = .ok value ∧
      Decl.CIRepExact base.κ h' value (.ctorInfo cv ctor.params.toNat ctor.fields.toNat) ∧
      (∀ (nl ty parent member ctorIndex params fields safety : SourceValue F),
        value = .construct Core.kciEnum "Ctor" [nl, ty, parent, member, ctorIndex, params, fields, safety] →
        ∀ d Γ, Decl.RawTmExact base.κ d Γ h' 0 rawSyntax cv.type ty) ∧
      ctor.params.toNat < 72057594037927936 ∧ ctor.fields.toNat < 72057594037927936 ∧
      ∃ (typePtr parentPtr : SourceValue F) (parent : Bytes.Address),
        value = .construct Core.kciEnum "Ctor"
          [.field (ctor.lvls.toNat : F), typePtr, parentPtr, .field i, .field j,
            .field (ctor.params.toNat : F), .field (ctor.fields.toNat : F), Ingress.repBoolField ctor.isUnsafe] ∧
        Bytes.RepAddressRef Core.addrTy h' parent parentPtr ∧ Core.ixAddr parent = Core.ixAddr block := by
  obtain ⟨_, _, _, bytes, src, ms, member, ct, blobs, value, hashed, address, decoded, _,
    srcShape, memberAt', ctorAt', hashedBlobs, valueAt, raw, tree', plan', built', planned', levels⟩ :=
    Ingress.get_ci_cprj_origin_spec goodLoad.2 blockRep loaded
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
  rw [ctorAt] at ctorAt'
  injection ctorAt' with ctorEq
  subst ct
  have metadata : ctor.params.toNat < 72057594037927936 ∧
      ctor.fields.toNat < 72057594037927936 ∧
      ∃ (typePtr parentPtr : SourceValue F) (parent : Bytes.Address),
        value = .construct Core.kciEnum "Ctor"
          [.field (ctor.lvls.toNat : F), typePtr, parentPtr, .field i, .field j,
            .field (ctor.params.toNat : F), .field (ctor.fields.toNat : F), Ingress.repBoolField ctor.isUnsafe] ∧
        Bytes.RepAddressRef Core.addrTy h' parent parentPtr ∧ Core.ixAddr parent = Core.ixAddr block := by
    obtain ⟨_, _, paramsBound, fieldsBound, _, typePtr, parentPtr, parent,
      parentEq, parentRep, valueShape, _⟩ := raw
    exact ⟨paramsBound, fieldsBound, typePtr, parentPtr, parent,
      by simpa only [ctorIndex, ZMod.natCast_zmod_val] using valueShape, parentRep, parentEq⟩
  have treeEq := built.unique built'
  cases treeEq
  have planEq := Option.some.inj (planned.symm.trans planned')
  cases planEq
  obtain ⟨cv', rawSyntax', stored', represented, rawAt, image', rawImage'⟩ :=
    native_ctor_value_with_raw_trace_of_blobAgreement raw levels
    read varsBounded levelsDefined keyed selfKeyed
    (fun a bytes member => blobReads a bytes
      (hashedBlobs (a, bytes) member).1 (hashedBlobs (a, bytes) member).2)
  rw [ctorIndex] at stored'
  have nameEq := stored'.1.trans stored.1.symm
  have paramsEq := stored'.2.1.trans stored.2.1.symm
  have typeEq := (Ingress.applyBinderTrace_unique image' image).1
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
  have rawEq := (Ingress.applyRawBinderTrace_unique rawImage' rawImage).1
  cases rawEq
  exact ⟨_, valueAt, represented, rawAt, metadata⟩

/-- Compatibility with full observed-blob membership. -/
theorem native_ctor_raw_reload_with_shape {base : Core.Ctx} {block : Bytes.Address} {i j : F}
    (source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {ctor : Ixon.Constructor}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    (ctorAt : ind.ctors.toList[ZMod.val j]? = some ctor)
    (ctorIndex : ctor.cidx.toNat = ZMod.val j)
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)} {rawType rawSyntax : KExpr}
    {cv : Ix.Kernel.ConstantVal .anon} {tree : Ingress.BinderTreeData} {plan : List Core.KLevel}
    (stored : IxVM.Consistency.ValStored cv
      ⟨base.κ (Core.cprjAddr (Core.ixAddr block) (ZMod.val i) (ZMod.val j)),
        List.range ctor.lvls.toNat, rawType⟩)
    (built : Ingress.BinderTreeBuilt (Ingress.binderLeavesData source.value.binders.toList) tree)
    (planned : Ingress.binderRootPlan tree source.value.sharing.toList
      (((Ingress.mutsRootOffset members.toList (ZMod.val i) : Nat) : F) + 1 + j) ctor.typ = some plan)
    (image : Ingress.applyBinderTrace
      (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
        some (cv.type, []))
    (rawImage : Ingress.applyRawBinderTrace
      (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
        some (rawSyntax, []))
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ctor.typ = .ok rawType)
    (varsBounded : rawType.looseBVarsBounded 0 = true)
    (levelsDefined : rawType.allLevelParamsDefined (List.range ctor.lvls.toNat) = true)
    {h h' : Heap F} {blockArg ptr : SourceValue F} {calls : List (Call F)}
    (loaded : ObsFn Core.W "Ingress::get_ci_cprj" [blockArg, .field i, .field j] h ptr h' calls)
    (goodLoad : Core.Good base calls)
    (blockRep : Bytes.RepAddressRef Core.addrTy h block blockArg)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = base.κ a)
    (selfKeyed : ∀ k a m name,
      (Ingress.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      self k = some m → m = .ok name → name = base.κ a)
    (blobReads : ∀ a bytes, Hashed calls bytes → Address.blake3Pure bytes = a →
      cx.blob a = some bytes) :
    ∃ value, loadValue h' ptr = .ok value ∧
      Decl.CIRepExact base.κ h' value (.ctorInfo cv ctor.params.toNat ctor.fields.toNat) ∧
      (∀ (nl ty parent member ctorIndex params fields safety : SourceValue F),
        value = .construct Core.kciEnum "Ctor" [nl, ty, parent, member, ctorIndex, params, fields, safety] →
        ∀ d Γ, Decl.RawTmExact base.κ d Γ h' 0 rawSyntax cv.type ty) ∧
      ctor.params.toNat < 72057594037927936 ∧ ctor.fields.toNat < 72057594037927936 ∧
      ∃ (typePtr parentPtr : SourceValue F) (parent : Bytes.Address),
        value = .construct Core.kciEnum "Ctor"
          [.field (ctor.lvls.toNat : F), typePtr, parentPtr, .field i, .field j,
            .field (ctor.params.toNat : F), .field (ctor.fields.toNat : F), Ingress.repBoolField ctor.isUnsafe] ∧
        Bytes.RepAddressRef Core.addrTy h' parent parentPtr ∧ Core.ixAddr parent = Core.ixAddr block := by
  exact native_ctor_raw_reload_with_shape_of_blobAgreement source blockShape memberAt ctorAt ctorIndex stored built planned image rawImage read varsBounded levelsDefined loaded goodLoad blockRep keyed selfKeyed (Ingress.HashedBlobReadAgreement.of_stored blobReads)

/-- The paired constructor reload interface, omitting the retained metadata shape. -/
theorem native_ctor_raw_reload_of_blobAgreement {base : Core.Ctx} {block : Bytes.Address} {i j : F}
    (source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {ctor : Ixon.Constructor}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    (ctorAt : ind.ctors.toList[ZMod.val j]? = some ctor)
    (ctorIndex : ctor.cidx.toNat = ZMod.val j)
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)} {rawType rawSyntax : KExpr}
    {cv : Ix.Kernel.ConstantVal .anon} {tree : Ingress.BinderTreeData} {plan : List Core.KLevel}
    (stored : IxVM.Consistency.ValStored cv
      ⟨base.κ (Core.cprjAddr (Core.ixAddr block) (ZMod.val i) (ZMod.val j)),
        List.range ctor.lvls.toNat, rawType⟩)
    (built : Ingress.BinderTreeBuilt (Ingress.binderLeavesData source.value.binders.toList) tree)
    (planned : Ingress.binderRootPlan tree source.value.sharing.toList
      (((Ingress.mutsRootOffset members.toList (ZMod.val i) : Nat) : F) + 1 + j) ctor.typ = some plan)
    (image : Ingress.applyBinderTrace
      (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
        some (cv.type, []))
    (rawImage : Ingress.applyRawBinderTrace
      (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
        some (rawSyntax, []))
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ctor.typ = .ok rawType)
    (varsBounded : rawType.looseBVarsBounded 0 = true)
    (levelsDefined : rawType.allLevelParamsDefined (List.range ctor.lvls.toNat) = true)
    {h h' : Heap F} {blockArg ptr : SourceValue F} {calls : List (Call F)}
    (loaded : ObsFn Core.W "Ingress::get_ci_cprj" [blockArg, .field i, .field j] h ptr h' calls)
    (goodLoad : Core.Good base calls)
    (blockRep : Bytes.RepAddressRef Core.addrTy h block blockArg)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = base.κ a)
    (selfKeyed : ∀ k a m name,
      (Ingress.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      self k = some m → m = .ok name → name = base.κ a)
    (blobReads : Ingress.HashedBlobReadAgreement cx.blob calls) :
    ∃ value, loadValue h' ptr = .ok value ∧
      Decl.CIRepExact base.κ h' value (.ctorInfo cv ctor.params.toNat ctor.fields.toNat) ∧
      (∀ (nl ty parent member ctorIndex params fields safety : SourceValue F),
        value = .construct Core.kciEnum "Ctor" [nl, ty, parent, member, ctorIndex, params, fields, safety] →
        ∀ d Γ, Decl.RawTmExact base.κ d Γ h' 0 rawSyntax cv.type ty) := by
  obtain ⟨value, loadedValue, represented, rawAt, _⟩ := native_ctor_raw_reload_with_shape_of_blobAgreement
    source blockShape memberAt ctorAt ctorIndex stored built planned image rawImage read
    varsBounded levelsDefined loaded goodLoad blockRep keyed selfKeyed blobReads
  exact ⟨value, loadedValue, represented, rawAt⟩

/-- Compatibility with full observed-blob membership. -/
theorem native_ctor_raw_reload {base : Core.Ctx} {block : Bytes.Address} {i j : F}
    (source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {ctor : Ixon.Constructor}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    (ctorAt : ind.ctors.toList[ZMod.val j]? = some ctor)
    (ctorIndex : ctor.cidx.toNat = ZMod.val j)
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)} {rawType rawSyntax : KExpr}
    {cv : Ix.Kernel.ConstantVal .anon} {tree : Ingress.BinderTreeData} {plan : List Core.KLevel}
    (stored : IxVM.Consistency.ValStored cv
      ⟨base.κ (Core.cprjAddr (Core.ixAddr block) (ZMod.val i) (ZMod.val j)),
        List.range ctor.lvls.toNat, rawType⟩)
    (built : Ingress.BinderTreeBuilt (Ingress.binderLeavesData source.value.binders.toList) tree)
    (planned : Ingress.binderRootPlan tree source.value.sharing.toList
      (((Ingress.mutsRootOffset members.toList (ZMod.val i) : Nat) : F) + 1 + j) ctor.typ = some plan)
    (image : Ingress.applyBinderTrace
      (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
        some (cv.type, []))
    (rawImage : Ingress.applyRawBinderTrace
      (fun level => Core.bmeta (Ingress.invPosLevel (List.range ctor.lvls.toNat) level)) rawType plan =
        some (rawSyntax, []))
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ctor.typ = .ok rawType)
    (varsBounded : rawType.looseBVarsBounded 0 = true)
    (levelsDefined : rawType.allLevelParamsDefined (List.range ctor.lvls.toNat) = true)
    {h h' : Heap F} {blockArg ptr : SourceValue F} {calls : List (Call F)}
    (loaded : ObsFn Core.W "Ingress::get_ci_cprj" [blockArg, .field i, .field j] h ptr h' calls)
    (goodLoad : Core.Good base calls)
    (blockRep : Bytes.RepAddressRef Core.addrTy h block blockArg)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = base.κ a)
    (selfKeyed : ∀ k a m name,
      (Ingress.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      self k = some m → m = .ok name → name = base.κ a)
    (blobReads : ∀ a bytes, Hashed calls bytes → Address.blake3Pure bytes = a →
      cx.blob a = some bytes) :
    ∃ value, loadValue h' ptr = .ok value ∧
      Decl.CIRepExact base.κ h' value (.ctorInfo cv ctor.params.toNat ctor.fields.toNat) ∧
      (∀ (nl ty parent member ctorIndex params fields safety : SourceValue F),
        value = .construct Core.kciEnum "Ctor" [nl, ty, parent, member, ctorIndex, params, fields, safety] →
        ∀ d Γ, Decl.RawTmExact base.κ d Γ h' 0 rawSyntax cv.type ty) := by
  exact native_ctor_raw_reload_of_blobAgreement source blockShape memberAt ctorAt ctorIndex stored built planned image rawImage read varsBounded levelsDefined loaded goodLoad blockRep keyed selfKeyed (Ingress.HashedBlobReadAgreement.of_stored blobReads)

end IxVM.Refinement.Assembly
