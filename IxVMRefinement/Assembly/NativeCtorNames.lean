import IxVMRefinement.Assembly.NativeCtorReads

/-! # Constructor names and separation from the native former

Actual slot loads determine constructor keys. The observed constructor projection hashes
separate those keys from the former's canonical projection under the collision alternative.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- Every actual constructor slot has the key determined by its projected parent and indices. -/
theorem native_ctor_slot_name {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {params indices levels : Nat} {rootCalls : List (Call F)}
    {ctors ctorsA : List (Decl.KConstantVal × Nat)} {rawTypes : List Core.KExpr}
    (family : Decl.CtorLoadAtIndex base.t block params i rootCalls ctors ctorsA rawTypes)
    (countBound : ctors.length < 549755813888)
    {rc former bp sortLevel result : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (blockRep : Bytes.RepAddressRef Core.addrTy h block bp)
    (subset : ∀ call ∈ calls, call ∈ rootCalls)
    (observed : ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
      [rc, former, .field (params : F), .field (indices : F), .field (ctors.length : F),
        .field (levels : F), bp, .field i, sortLevel, .field 0, .field 0] h result h' calls)
    {slot : Nat} (slotBound : slot < ctors.length) {ctor : Decl.KConstantVal × Nat}
    (atSlot : ctors[slot]? = some ctor) :
    ctor.1.name = base.κ (Core.cprjAddr (Core.ixAddr block) (ZMod.val i) slot) := by
  obtain ⟨actual, annotated, found, _, stored, load⟩ := family.2 slot slotBound
  have same := Option.some.inj (found.symm.trans atSlot)
  subst actual
  have scopeRead : Nonempty (CtorScopeRead block i (slot : F) 0 params levels rootCalls) := by
    simpa only [Nat.zero_add] using native_ctor_scope_reads countBound ctors.length 0 (Nat.add_zero _)
      blockRep subset observed slot slotBound
  obtain ⟨checked⟩ := scopeRead
  obtain ⟨_, _, _, _, _, parent, _, parentRep, parentEq, _, represented⟩ :=
    load checked.blockArg checked.ptr checked.before checked.after checked.loadCalls
      checked.loadSubset checked.blockRep checked.loaded
  have named := Decl.CIRepExact.ctor_name represented parentRep
  have slotValue : ZMod.val (slot : F) = slot :=
    ZMod.val_natCast_of_lt (Nat.lt_trans slotBound (Nat.lt_trans countBound (by decide)))
  have addressEq := congrArg₂ (fun parent index => Core.cprjAddr parent (ZMod.val i) index)
    parentEq slotValue
  exact stored.1.symm.trans (named.trans (congrArg base.κ addressEq))

/-- Constructor keys in the actual loop cannot equal its former's key. -/
theorem native_ctors_not_former {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {params indices levels : Nat} {rootCalls : List (Call F)}
    {ctors ctorsA : List (Decl.KConstantVal × Nat)} {rawTypes : List Core.KExpr}
    (family : Decl.CtorLoadAtIndex base.t block params i rootCalls ctors ctorsA rawTypes)
    (countBound : ctors.length < 549755813888)
    (projection : L1.CanonicalRecordAt base.E (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)))
    (projectionShape : projection.value.info = .iPrj ⟨(ZMod.val i).toUInt64, Core.ixAddr block⟩)
    (tableWf : base.t.wf = true) (good : Core.Good base rootCalls)
    {rc former bp sortLevel result : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (blockRep : Bytes.RepAddressRef Core.addrTy h block bp)
    (subset : ∀ call ∈ calls, call ∈ rootCalls)
    (observed : ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
      [rc, former, .field (params : F), .field (indices : F), .field (ctors.length : F),
        .field (levels : F), bp, .field i, sortLevel, .field 0, .field 0] h result h' calls) :
    ∀ ctor ∈ ctors, ctor.1.name ≠ base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)) := by
  intro ctor member sameKey
  obtain ⟨slot, slotBound, atSlot⟩ := List.mem_iff_getElem?.mp member
  have nameEq := native_ctor_slot_name (base := base) family countBound blockRep subset observed slotBound atSlot
  have addressEq := Decl.nat_keyOf_injective (t := base.t) tableWf
    (a₁ := Core.cprjAddr (Core.ixAddr block) (ZMod.val i) slot)
    (a₂ := Core.iprjAddr (Core.ixAddr block) (ZMod.val i)) (nameEq.symm.trans sameKey)
  let context : Core.ScopedCtx := { toCtx := base, allowed := fun _ => False }
  have hashes := native_ctor_projection_hashes context countBound ctors.length 0 (Nat.add_zero _)
    blockRep subset observed
  have hashed : Hashed rootCalls (Ixon.serConstant
      (IxVM.Consistency.constructorProjection (Core.ixAddr block) (ZMod.val i) slot)) := by
    simpa only [Nat.zero_add] using hashes slot slotBound
  have bytesEq := Core.load_escape projection.stored good.1 _ hashed addressEq
  have decoded := projection.decoded
  rw [← bytesEq] at decoded
  have canonical := Ixon.Verify.deConstantExact_serConstant
    (IxVM.Consistency.constructorProjection (Core.ixAddr block) (ZMod.val i) slot)
    (L1.projConstant_wireWF_cPrj (ZMod.val i).toUInt64 slot.toUInt64 block)
  have sameValue := Except.ok.inj (decoded.symm.trans canonical)
  have sameInfo := congrArg Ixon.Constant.info sameValue
  rw [projectionShape] at sameInfo
  cases sameInfo

end IxVM.Refinement.Assembly
