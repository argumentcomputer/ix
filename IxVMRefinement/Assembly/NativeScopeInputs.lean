import IxVMRefinement.Assembly.NativeCtorScope
import IxVMRefinement.Assembly.NativeFormerInputs

/-! # Native reader scope from actual raw checks

The actual load and scope validator determine bound-variable and universe bounds before
semantic annotation or member naming is related. These companions keep that direct evidence
independent of explicit-key, self-key and literal-value agreement.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core (KKey KExpr)

/-- An actual constructor load and scope validation determine the reader type's scope without naming or blob-value correspondence. -/
theorem observed_native_ctor_type_scope {base : Core.Ctx}
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
    (extended : Heap.Extends h₁ h₂)
    (bounded : IxVM.Consistency.Bounded calls)
    (validated : ObsFn Core.W "KernelCheck::validate_expr_well_scoped"
      [ty, .field 0, nl] h₂ result h₃ scopeCalls)
    (scopeMember : (⟨"KernelCheck::validate_expr_well_scoped",
      [ty, .field 0, nl], h₂⟩ : Call F) ∈ calls)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ctor.typ = .ok rawType)
    :
    rawType.looseBVarsBounded 0 = true ∧
      rawType.allLevelParamsDefined (List.range ctor.lvls.toNat) = true ∧ rawType.hasFvar = false := by
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
  obtain ⟨levelBound, _, _, _, _, typePtr, parentPtr, parent, _, _, valueEq, rawTy⟩ := raw
  subst value
  have fieldsEq := Except.ok.inj (tag.symm.trans valueAt)
  simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at fieldsEq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := fieldsEq
  obtain ⟨_, varsBounded, levelsDefined⟩ :=
    validate_expr_well_scoped_spec bounded levelBound rawTy extended read validated scopeMember
  exact ⟨varsBounded, levelsDefined, memberReader_read_noFvar read⟩

/-- An actual former load and scope validation determine the reader type's scope independently of all member names. -/
theorem observed_native_former_type_scope {base : Core.Ctx}
    {calls loadCalls scopeCalls : List (Call F)} {h₀ h₁ h₂ h₃ : Heap F}
    {block : Bytes.Address} {i : F} {blockArg ptr result : SourceValue F}
    {nl ty np ni nc safe parent memberIndex : SourceValue F}
    (source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)} {rawType : KExpr}
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
    :
    rawType.looseBVarsBounded 0 = true ∧
      rawType.allLevelParamsDefined (List.range ind.lvls.toNat) = true ∧ rawType.hasFvar = false := by
  obtain ⟨_, _, bytes, src, ms, member, blobs, value, hashed, address, decoded, _,
    srcShape, memberAt', hashedBlobs, valueAt, raw, tree, plan, built, planned, levels⟩ :=
    Ingress.get_ci_iprj_origin_spec goodLoad.2 blockRep loaded
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
  obtain ⟨levelBound, _, _, _, _, typePtr, parentPtr, _, _, _, valueEq, rawTypeRep⟩ := raw
  subst value
  have fieldsEq := Except.ok.inj (tag.symm.trans valueAt)
  simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at fieldsEq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := fieldsEq
  obtain ⟨_, varsBounded, levelsDefined⟩ :=
    validate_expr_well_scoped_spec bounded levelBound rawTypeRep extended read validated scopeMember
  exact ⟨varsBounded, levelsDefined, memberReader_read_noFvar read⟩

/-- The actual constructor-scope package gives these reader bounds without semantic naming facts. -/
theorem CtorScopeRead.type_scope_of_observations {base : Core.Ctx} {block : Bytes.Address} {i j : F}
    {params levels : Nat} {calls : List (Call F)}
    (checked : CtorScopeRead block i j 0 params levels calls)
    (source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {ctor : Ixon.Constructor}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    (ctorAt : ind.ctors.toList[ZMod.val j]? = some ctor)
    {cx : Ix.Kernel.Reader.Ctx .anon} {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {row : NativeCtorRow}
    (frame : NativeCtorReaderFrame cx (Core.ixAddr block)
      (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self) (ZMod.val i, ctor, ZMod.val j) row)
    (good : Core.Good base calls) :
    row.1.type.looseBVarsBounded 0 = true ∧
      row.1.type.allLevelParamsDefined row.1.levelParams = true ∧ row.1.type.hasFvar = false := by
  obtain ⟨varsBounded, levelsDefined, noFvars⟩ := observed_native_ctor_type_scope
    source blockShape memberAt ctorAt checked.loaded (good.sub checked.loadSubset) checked.blockRep checked.tag
    checked.extended good.2 checked.scopeRun checked.scopeMember frame.2.1
  refine ⟨varsBounded, ?_, noFvars⟩
  simpa only [frame.2.2.1] using levelsDefined

/-- Every actual constructor-reader row inherits the observed scope check before any key agreement or annotation origin is requested. -/
theorem native_ctor_reader_scope_of_observations {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {params indices levels : Nat} {rc former bp sortLevel result : SourceValue F}
    {h h' : Heap F} {rootCalls loopCalls : List (Call F)}
    (source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block))
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
    (good : Core.Good base rootCalls) :
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
  exact checked.type_scope_of_observations source blockShape memberAt ctorAt frame.1 good

end IxVM.Refinement.Assembly
