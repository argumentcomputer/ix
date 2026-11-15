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
open IxVM.Refinement.Core (KKey KExpr KConstantVal)

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
    ∃ annotated syntax,
      IxVM.Consistency.Annotates annotated rawType ∧
      Decl.TmCExact κ h₀ annotated tyPtr ∧
      (∀ d Γ, Decl.RawTmExact κ d Γ h₀ 0 syntax annotated tyPtr) ∧
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
  obtain ⟨syntax, rawRep⟩ := exactRep.raw
  exact ⟨annotated, syntax, annotation, exactRep, rawRep, varsBound, paramsDefined,
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
          .field (ctor.fields.toNat : F), Deserialize.repBoolField ctor.isUnsafe]))
    (extended : Heap.Extends h₀ h)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read ctor.typ = .ok rawType)
    (validated : ObsFn Core.W "KernelCheck::validate_expr_well_scoped"
      [tyPtr, .field 0, .field (ctor.lvls.toNat : F)] h result h' cs)
    (member : (⟨"KernelCheck::validate_expr_well_scoped",
      [tyPtr, .field 0, .field (ctor.lvls.toNat : F)], h⟩ : Call F) ∈ calls)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (selfKeyed : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (blobReads : ∀ a bytes, (a, bytes) ∈ blobs → cx.blob a = some bytes) :
    ∃ (annotated : KConstantVal) (syntax : KExpr),
      IxVM.Consistency.ValStored annotated
        ⟨κ (Core.cprjAddr block index ctor.cidx.toNat), List.range ctor.lvls.toNat, rawType⟩ ∧
      Decl.ValRepExact κ h₀ (.field (ctor.lvls.toNat : F)) tyPtr annotated ∧
      (∀ d Γ, Decl.RawTmExact κ d Γ h₀ 0 syntax annotated.type tyPtr) ∧
      Decl.CIRepExact κ h₀ (.construct Core.kciEnum "Ctor"
        [.field (ctor.lvls.toNat : F), tyPtr, blockPtr, .field (index : F),
          .field (ctor.cidx.toNat : F), .field (ctor.params.toNat : F),
          .field (ctor.fields.toNat : F), Deserialize.repBoolField ctor.isUnsafe])
        (.ctorInfo annotated ctor.params.toNat ctor.fields.toNat) ∧
      rawType.looseBVarsBounded 0 = true ∧
      rawType.allLevelParamsDefined (List.range ctor.lvls.toNat) = true ∧ rawType.hasFvar = false := by
  obtain ⟨levelsBound, ctorIndexBound, paramsBound, fieldsBound, indexBound,
    ty, blk, b, blockEq, blockRep, valueEq, rawTy⟩ := raw
  injection valueEq with _ _ fieldsEq
  simp only [List.cons.injEq, true_and, and_true] at fieldsEq
  obtain ⟨rfl, rfl⟩ := fieldsEq
  obtain ⟨type, syntax, annotation, exactRep, rawRep, varsBound, paramsDefined, closed⟩ :=
    validated_native_type_input bounded levelsBound rawTy extended read validated member
      keyed selfKeyed blobReads
  let cv : KConstantVal :=
    ⟨κ (Core.cprjAddr block index ctor.cidx.toNat), List.range ctor.lvls.toNat, type⟩
  have valueRep : Decl.ValRepExact κ h₀ (.field (ctor.lvls.toNat : F)) ty cv := by
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
  refine ⟨cv, syntax, ⟨rfl, rfl, annotation⟩, valueRep, rawRep,
    .ctor valueRep rfl rfl ⟨paramsBound, fieldsBound⟩
      ⟨b, (index : F), (ctor.cidx.toNat : F), blockRep, rfl, rfl, ?_⟩,
    varsBound, paramsDefined, closed⟩
  simp only [cv, indexValue, ctorIndexValue, blockEq]

end IxVM.Refinement.Assembly
