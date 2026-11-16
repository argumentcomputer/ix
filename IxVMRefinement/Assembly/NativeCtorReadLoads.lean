import IxVMRefinement.Assembly.NativeCtorNames
import IxVMRefinement.Assembly.NativeOuter

/-! # Fresh constructor loads in the actual native stage

Canonical metadata identifies the member and bounds the queried constructor slot. The actual
constructor projection hashes preserve freshness across former installation. The produced
reader/conversion family then supplies the raw load and conditional installed agreement.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- A raw constructor query into a singleton native family has its actual member index and
an existing constructor slot. This conclusion uses only canonical metadata. -/
theorem native_ctor_query_shape {base : Core.Ctx} {block : Bytes.Address} {i index slot : F}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (shape : source.value.info = .muts members)
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(ZMod.val i, ind)])
    {bp ptr : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (good : Core.Good base calls) (blockRep : Bytes.RepAddressRef Core.addrTy h block bp)
    (loaded : ObsFn Core.W "Ingress::get_ci_cprj" [bp, .field index, .field slot] h ptr h' calls) :
    index = i ∧ ZMod.val slot < ind.ctors.size := by
  obtain ⟨_, _, _, bytes, src, ms, actual, ctor, _, _, hashed, address, decoded, _,
    blockShape, atMember, atCtor, _⟩ := L1.get_ci_cprj_spec good.2 blockRep loaded
  have bytesEq := Core.load_escape source.stored good.1 bytes hashed address
  rw [bytesEq, source.decoded] at decoded
  injection decoded with sourceEq
  subst src
  rw [shape] at blockShape
  injection blockShape with membersEq
  subst ms
  have memberAt : members[ZMod.val index]? = some (.indc actual) := by
    simpa only [Array.getElem?_toList] using atMember
  have present : (ZMod.val index, actual) ∈ Ix.CompileCert.ReaderIndex.inductives members := by
    apply Array.mem_filterMap.mpr
    exact ⟨(.indc actual, ZMod.val index), Array.mk_mem_zipIdx_iff_getElem?.mpr memberAt, rfl⟩
  rw [one] at present
  have entryEq : (ZMod.val index, actual) = (ZMod.val i, ind) := by simpa using present
  have indexEq : index = i :=
    (ZMod.natCast_zmod_val index).symm.trans
      ((congrArg (fun n : Nat => (n : F)) (congrArg Prod.fst entryEq)).trans (ZMod.natCast_zmod_val i))
  have indEq := congrArg Prod.snd entryEq
  subst actual
  exact ⟨indexEq, by simpa only [Array.length_toList] using (List.getElem?_eq_some_iff.mp atCtor).1⟩

/-- Actual constructor projection hashes keep every declared constructor fresh when the
current former is installed with its native capabilities. -/
theorem NativeFormerRunInput.ctorFreshStage {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : L1.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {rawType : Core.KExpr} {rootCalls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind rawType rootCalls)
    (native : input.NativeCall)
    (shape : Decl.NativeShapeCalls input.rc input.typePtr input.blockPtr (.field i)
      (L1.repBoolField ind.isUnsafe) ind.params.toNat ind.indices.toNat ind.ctors.size ind.lvls.toNat
      native.before rootCalls)
    {parts : Ix.Kernel.InductiveShape .anon} {isRec : Bool}
    {ctors annotated : List (Decl.KConstantVal × Nat)} {rawTypes : List Core.KExpr}
    (family : Decl.CtorLoadAtIndex base.t block ind.params.toNat i rootCalls ctors annotated rawTypes)
    (count : ctors.length = ind.ctors.size) (safe : ind.isUnsafe = false)
    (good : Core.Good base rootCalls) (tableWf : base.t.wf = true)
    (fresh : ∀ ctor ∈ ctors, base.env.find? ctor.1.name = none) :
    ∀ ctor ∈ ctors, (input.stageCtx parts isRec).env.find? ctor.1.name = none := by
  have loop : ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
      [input.rc, input.typePtr, .field (ind.params.toNat : F), .field (ind.indices.toNat : F),
        .field (ctors.length : F), .field (ind.lvls.toNat : F), input.blockPtr, .field i,
        shape.sortLevel, .field 0, .field 0] shape.ctorBefore shape.result shape.after shape.ctorCalls := by
    simpa [count, safe, L1.repBoolField] using shape.ctorRun
  have bound : ctors.length < 549755813888 := by rw [count]; exact input.ctorCountBound
  have blockRep := Bytes.repAddressRef_heapMono₂ Core.addrTy
    (native.initialToShape.trans shape.initial_to_ctors) input.blockRep
  obtain ⟨projection, projectionShape⟩ := input.projectionSource
  have separate := native_ctors_not_former (base := base) family bound projection projectionShape
    tableWf good blockRep shape.ctorSubset loop
  have named : input.annotated.name = base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)) := input.stored.1
  intro ctor member
  change (Ix.Kernel.Env.mk (.indInfo input.annotated (Ix.Kernel.nativeCapsAt parts isRec) :: base.env.consts)).find?
    ctor.1.name = none
  rw [Decl.find?_cons_indInfo_ne _ _ _ (by rw [named]; exact (separate ctor member).symm)]
  exact fresh ctor member

/-- A current-block constructor query supplies the scoped raw-load contract from the actual
family. Its member and slot are derived from the query, and installed agreement follows from
freshness proved with the main traversal's hash commitments. -/
theorem NativeFormerRunInput.getCprj_current {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : L1.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {rawType : Core.KExpr} {rootCalls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind rawType rootCalls)
    (native : input.NativeCall)
    (shape : Decl.NativeShapeCalls input.rc input.typePtr input.blockPtr (.field i)
      (L1.repBoolField ind.isUnsafe) ind.params.toNat ind.indices.toNat ind.ctors.size ind.lvls.toNat
      native.before rootCalls)
    {parts : Ix.Kernel.InductiveShape .anon} {isRec : Bool}
    {ctors annotated : List (Decl.KConstantVal × Nat)} {rawTypes : List Core.KExpr}
    (family : Decl.CtorLoadAtIndex base.t block ind.params.toNat i rootCalls ctors annotated rawTypes)
    (count : ctors.length = ind.ctors.size) (safe : ind.isUnsafe = false)
    (rootGood : Core.Good base rootCalls) (tableWf : base.t.wf = true)
    (fresh : ∀ ctor ∈ ctors, base.env.find? ctor.1.name = none)
    (runs : List (Decl.NativeCtorCoreRun rootCalls))
    {bp ptr : SourceValue F} {h h' : Heap F} {calls : List (Call F)} {index slot : F}
    (loaded : ObsFn Core.W "Ingress::get_ci_cprj" [bp, .field index, .field slot] h ptr h' calls)
    (good : Core.CoreGood (Decl.nativeCtorCoreCtx (input.stageCtx parts isRec) runs) calls)
    (_allowed : (Decl.nativeCtorCoreCtx (input.stageCtx parts isRec) runs).allowedTop
      "Ingress::get_ci_cprj" [bp, .field index, .field slot] h)
    (blockRep : Bytes.RepAddressRef Core.addrTy h block bp) :
    (∃ ci, Core.CIPtrRep base.κ h' ptr ci) ∧
      ∀ ci, (input.stageCtx parts isRec).env.find?
        (base.κ (Core.cprjAddr (Core.ixAddr block) (ZMod.val index) (ZMod.val slot))) = some ci →
        Core.CIPtrRep base.κ h' ptr ci := by
  obtain ⟨indexEq, slotBound⟩ := native_ctor_query_shape (base := input.stageCtx parts isRec)
    source input.blockShape (input.oneFamily native rootGood) good.raw blockRep loaded
  subst index
  have inside : ZMod.val slot < ctors.length := by rwa [count]
  obtain ⟨ctor, stored, ctorAt, _, storedAs, load⟩ := family.2 (ZMod.val slot) inside
  have observed : ObsFn Core.W "Ingress::get_ci_cprj"
      [bp, .field i, .field ((ZMod.val slot : Nat) : F)] h ptr h' calls := by
    simpa only [ZMod.natCast_zmod_val] using loaded
  obtain ⟨nl, typePtr, parentPtr, params, fields, parent, payload, parentRep, parentEq, _, represented⟩ :=
    load bp ptr h h' calls (Decl.nativeCtorCoreCtx_child_subset good) blockRep observed
  have ctorName := Decl.CIRepExact.ctor_name represented parentRep
  have keyEq : ctor.1.name = base.κ (Core.cprjAddr (Core.ixAddr block) (ZMod.val i) (ZMod.val slot)) := by
    have sameAddress := congrArg₂ (fun address index => Core.cprjAddr address (ZMod.val i) index)
      parentEq (congrArg ZMod.val (ZMod.natCast_zmod_val slot))
    exact storedAs.1.symm.trans (ctorName.trans (congrArg base.κ sameAddress))
  have freshStage := input.ctorFreshStage native shape family count safe rootGood tableWf fresh
    ctor (List.mem_of_getElem? ctorAt)
  refine ⟨⟨.ctorInfo stored ind.params.toNat ctor.2, _, payload, represented.toCIRep⟩, ?_⟩
  intro ci found
  rw [keyEq] at freshStage
  rw [freshStage] at found
  cases found

end IxVM.Refinement.Assembly
