import IxVMRefinement.Assembly.NativeCtorInputs
import IxVMRefinement.L1.AnnotationCorrespondence

/-! # Native former inputs and repeated loads

Actual conversion traces determine the annotation used for a former. The same immutable record
can then be read again with that annotation while its semantic capability data stays explicit.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core (KKey KExpr)

/-- The exact type trace chooses the annotated value represented by a raw former load. -/
theorem native_former_value_of_trace {κ : _root_.Address → KKey}
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
  obtain ⟨levelBound, paramsBound, indicesBound, ctorBound, indexBound,
    typePtr, blockPtr, parent, parentEq, parentRep, rfl, rawTypeRep⟩ := raw
  obtain ⟨count, observedType, fields, shape, trace⟩ := levels
  simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at shape
  obtain ⟨rfl, rfl, rfl⟩ := shape
  have positionalRead :
      (Ix.Kernel.Reader.MemberReader.mk' cx src
        (Ix.Kernel.Reader.recParam (List.range ind.lvls.toNat)) self).read ind.typ = .ok rawType := by
    rw [recParam_range]
    exact read
  obtain ⟨annotated, annotation, represented, readTrace⟩ := rawTypeRep.toTmCExactTrace
    (ps := List.range ind.lvls.toNat) (by simp)
    (by simpa only [List.length_range] using levelBound)
    keyed selfKeyed blobReads positionalRead varsBounded levelsDefined
  let cv : Ix.Kernel.ConstantVal .anon :=
    ⟨κ (Core.iprjAddr block index), List.range ind.lvls.toNat, annotated⟩
  have valueRep : Decl.ValRepExact κ h (.field (ind.lvls.toNat : F)) observedType cv := by
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

end IxVM.Refinement.Assembly
