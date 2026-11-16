import IxVMRefinement.Assembly.NativeCtorScope
import IxVMRefinement.Assembly.NativeOuter

/-! # Constructor load families before semantic checking

The actual reader frames and Aiur-checker loop construct the repeated-load family and its raw
scope data independently of semantic load facts. The same chosen annotations can then supply
scoped current-block loads and the semantic constructor stage.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- The actual former input and shape call construct their entire constructor load family
before any semantic load contract is requested. -/
theorem NativeFormerRunInput.constructorFamily {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : L1.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {rawType : Core.KExpr} {calls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind rawType calls)
    (native : input.NativeCall)
    (shape : Decl.NativeShapeCalls input.rc input.typePtr input.blockPtr (.field i)
      (L1.repBoolField ind.isUnsafe) ind.params.toNat ind.indices.toNat ind.ctors.size ind.lvls.toNat
      native.before calls)
    (safe : ind.isUnsafe = false) (good : Core.Good base calls)
    {cx : Ix.Kernel.Reader.Ctx .anon} {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {rows : List NativeCtorRow}
    (frames : List.Forall₂
      (NativeCtorReaderCheckedFrame cx (Core.ixAddr block)
        (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self))
      (nativeCtorSlots [(ZMod.val i, ind)]) rows)
    (memberKeys : ∀ slot < ind.ctors.size,
      cx.memberKey (.ctor (Core.ixAddr block) (ZMod.val i) slot) =
        .ok (base.κ (Core.cprjAddr (Core.ixAddr block) (ZMod.val i) slot)))
    (keyed : ∀ address key, cx.keyAt address = .ok key → key = base.κ address)
    (selfKeyed : ∀ index address reading key,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      self index = some reading → reading = .ok key → key = base.κ address)
    (blobReads : ∀ address bytes, Hashed calls bytes → Address.blake3Pure bytes = address →
      cx.blob address = some bytes) :
    ∃ (annotated : List (Decl.KConstantVal × Nat)) (rawTypes : List Core.KExpr),
      Decl.CtorLoadAtIndex base.t block ind.params.toNat i calls
        (rows.map (fun row => (row.1, row.2.2))) annotated rawTypes ∧
      rows.length = ind.ctors.size ∧
      ∀ row ∈ rows,
        row.2.1 = ind.params.toNat ∧ row.1.levelParams = List.range ind.lvls.toNat ∧
        row.1.type.looseBVarsBounded 0 = true ∧
        row.1.type.allLevelParamsDefined (List.range ind.lvls.toNat) = true ∧
        row.1.type.hasFvar = false := by
  have loop : ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
      [input.rc, input.typePtr, .field (ind.params.toNat : F), .field (ind.indices.toNat : F),
        .field (ind.ctors.size : F), .field (ind.lvls.toNat : F), input.blockPtr, .field i,
        shape.sortLevel, .field 0, .field 0] shape.ctorBefore shape.result shape.after shape.ctorCalls := by
    simpa [safe, L1.repBoolField] using shape.ctorRun
  have blockRep := Bytes.repAddressRef_heapMono₂ Core.addrTy
    (native.initialToShape.trans shape.initial_to_ctors) input.blockRep
  obtain ⟨annotated, rawTypes, family, properties⟩ :=
    native_ctor_load_family (base := base) source input.blockShape input.memberAt input.ctorCountBound
      input.paramsBound input.levelsBound blockRep shape.ctorSubset loop frames memberKeys good keyed selfKeyed blobReads
  have scopes := native_ctor_reader_scope (base := base) source input.blockShape input.memberAt input.ctorCountBound
    blockRep shape.ctorSubset loop frames good keyed selfKeyed blobReads
  refine ⟨annotated, rawTypes, family, ?_, fun row member => ?_⟩
  · simpa [nativeCtorSlots] using frames.length_eq.symm
  · exact ⟨(properties row member).1, (properties row member).2, scopes row member⟩

end IxVM.Refinement.Assembly
