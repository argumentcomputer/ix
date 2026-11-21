import IxVMRefinement.Ingress.TraceRecords
import IxVMRefinement.Assembly.NativeCtorReads
import IxVMRefinement.Assembly.NativePeerInputs
import IxVMRefinement.Decl.NativeCtorScoped

/-! # Checked native constructors from canonical observed queries

The actual trace supplies raw query coverage and the unique family's peer facts. The semantic
load premise is restricted to the finite typed-call scope constructed by the traversal.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core (KKey KExpr KLevel)
open IxVM.Refinement.Decl (KConstantVal)
open IxVM.Refinement.KernelLevels (RepKLevel)

/-- Compose canonical query coverage with the actual indexed constructor traversal. Raw
record and peer packages are constructed here; the base semantic facts and scoped semantic
loads remain explicit. -/
theorem native_ctor_scoped_of_records (hLevels : IxVM.Consistency.Levels)
    {base : Core.Ctx} {block : Bytes.Address} {i : F} {T : KKey}
    (source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block))
    (former : Ingress.CanonicalRecordAt base.E (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)))
    (formerShape : former.value.info = .iPrj ⟨(ZMod.val i).toUInt64, Core.ixAddr block⟩)
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members[ZMod.val i]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(ZMod.val i, ind)])
    (tableWf : base.t.wf = true)
    (key : T = base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)))
    {rootCalls : List (Call F)} {ctors ctorsA : List (KConstantVal × Nat)}
    {rawTypes : List KExpr} {ta : KExpr} {resSort indLevel : KLevel}
    (family : Decl.CtorLoadAtIndex base.t block ind.params.toNat i rootCalls ctors ctorsA rawTypes)
    (countEq : ctors.length = ind.ctors.size)
    (levelsBound : ind.lvls.toNat < 4294967296)
    (paramsBound : ind.params.toNat < 72057594037927936)
    (indicesBound : ind.indices.toNat < 72057594037927936)
    (countBound : ctors.length < 549755813888)
    (fieldsBound : ∀ ctor ∈ ctors, ctor.2 < 72057594037927936)
    (sortEq : Core.LvEq resSort indLevel)
    (levels : ∀ ctor ∈ ctors, ctor.1.levelParams = List.range ind.lvls.toNat)
    (varsBounded : ∀ ctor ∈ ctors, ctor.1.type.looseBVarsBounded 0 = true)
    (noFvars : ∀ ctor ∈ ctors, ctor.1.type.hasFvar = false)
    (fresh : ∀ ctor ∈ ctors, base.env.find? ctor.1.name = none)
    (notBasis : ∀ ctor ∈ ctors, Ix.Kernel.reservedBasisNames.contains ctor.1.name = false)
    (notProjection : ∀ ctor ∈ ctors, ctor.1.name.isProjFnShape = false)
    (noFormerProjection : ∀ field, base.env.findProj? T field = none)
    (envFacts : Core.CoreEnvFacts base)
    {rc pta bp pind result : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (subset : ∀ call ∈ calls, call ∈ rootCalls)
    (good : Core.Good base calls)
    (known : Ingress.CanonicalQueryCoverage base.E calls)
    (roleContext : Core.RCRep base.t base.lim h rc)
    (formerRep : Core.Tm base.κ 0 (fun _ => default) h 0 ta pta)
    (blockRep : Bytes.RepAddressRef Core.addrTy h block bp)
    (sortRep : RepKLevel h indLevel pind)
    (observed : ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
      [rc, pta, .field (ind.params.toNat : F), .field (ind.indices.toNat : F),
        .field (ctors.length : F), .field (ind.lvls.toNat : F), bp, .field i, pind, .field 0, .field 0]
      h result h' calls) :
    ∃ runs : List (Decl.NativeCtorCoreRun rootCalls),
      Core.ScopedLoadFacts (Decl.nativeCtorCoreCtx base runs) →
      ∃ sortss : List (List KLevel),
        sortss.length = ctors.length ∧
        ∀ slot < ctors.length, ∃ ctor annotated sorts,
          ctors[slot]? = some ctor ∧ ctorsA[slot]? = some annotated ∧ sortss[slot]? = some sorts ∧
          Decl.NativeCtorOut base.env T (List.range ind.lvls.toNat) ind.params.toNat
            ind.indices.toNat resSort ta (rawTypes.getD slot default) ctor annotated sorts := by
  subst T
  obtain ⟨queries, rawFacts, covered⟩ := Ingress.rawRecordFacts_of_trace (base := base) observed known
  let raw := Ingress.rawQueryCtx base queries
  have rawKeyed : raw.TableKeyed := ⟨rfl⟩
  have peer := native_peer_reads (raw := raw) source former formerShape blockShape memberAt one tableWf
  have peer' : Decl.OneTypePeerReads raw block
      (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)))
      (List.range ind.lvls.toNat).length ind.params.toNat ind.indices.toNat ctors.length i := by
    simpa only [List.length_range, countEq, raw, Ingress.rawQueryCtx, Core.ScopedCtx.κ, Core.Ctx.κ] using peer
  exact Decl.native_ctor_scoped hLevels (cR := raw) (indIndex := i)
    (by simp) (by simpa only [List.length_range] using levelsBound)
    paramsBound indicesBound countBound fieldsBound sortEq family levels varsBounded noFvars
    fresh notBasis notProjection noFormerProjection envFacts.store envFacts rawFacts peer'
    subset good covered roleContext formerRep blockRep sortRep
    (by simpa only [List.length_range] using observed)

/-- Actual former and constructor loads supply every numeric count bound needed by the
scoped constructor proof. -/
theorem native_ctor_scoped_of_observed_bounds (hLevels : IxVM.Consistency.Levels)
    {base : Core.Ctx} {block : Bytes.Address} {i : F} {T : KKey}
    (source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block))
    (former : Ingress.CanonicalRecordAt base.E (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)))
    (formerShape : former.value.info = .iPrj ⟨(ZMod.val i).toUInt64, Core.ixAddr block⟩)
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members[ZMod.val i]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(ZMod.val i, ind)])
    (tableWf : base.t.wf = true)
    (key : T = base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)))
    {rootCalls : List (Call F)} {ctors ctorsA : List (KConstantVal × Nat)}
    {rawTypes : List KExpr} {ta : KExpr} {resSort indLevel : KLevel}
    (family : Decl.CtorLoadAtIndex base.t block ind.params.toNat i rootCalls ctors ctorsA rawTypes)
    (countEq : ctors.length = ind.ctors.size)
    {formerBlockArg formerPtr : SourceValue F} {formerHeap formerAfter : Heap F}
    {formerCalls : List (Call F)}
    (formerGood : Core.Good base formerCalls)
    (formerBlockRep : Bytes.RepAddressRef Core.addrTy formerHeap block formerBlockArg)
    (formerLoad : ObsFn Core.W "Ingress::get_ci_iprj" [formerBlockArg, .field i]
      formerHeap formerPtr formerAfter formerCalls)
    (sortEq : Core.LvEq resSort indLevel)
    (levels : ∀ ctor ∈ ctors, ctor.1.levelParams = List.range ind.lvls.toNat)
    (varsBounded : ∀ ctor ∈ ctors, ctor.1.type.looseBVarsBounded 0 = true)
    (noFvars : ∀ ctor ∈ ctors, ctor.1.type.hasFvar = false)
    (fresh : ∀ ctor ∈ ctors, base.env.find? ctor.1.name = none)
    (notBasis : ∀ ctor ∈ ctors, Ix.Kernel.reservedBasisNames.contains ctor.1.name = false)
    (notProjection : ∀ ctor ∈ ctors, ctor.1.name.isProjFnShape = false)
    (noFormerProjection : ∀ field, base.env.findProj? T field = none)
    (envFacts : Core.CoreEnvFacts base)
    {rc pta bp pind result : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (subset : ∀ call ∈ calls, call ∈ rootCalls)
    (good : Core.Good base calls)
    (known : Ingress.CanonicalQueryCoverage base.E calls)
    (roleContext : Core.RCRep base.t base.lim h rc)
    (formerRep : Core.Tm base.κ 0 (fun _ => default) h 0 ta pta)
    (blockRep : Bytes.RepAddressRef Core.addrTy h block bp)
    (sortRep : RepKLevel h indLevel pind)
    (observed : ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
      [rc, pta, .field (ind.params.toNat : F), .field (ind.indices.toNat : F),
        .field (ctors.length : F), .field (ind.lvls.toNat : F), bp, .field i, pind, .field 0, .field 0]
      h result h' calls) :
    ∃ runs : List (Decl.NativeCtorCoreRun rootCalls),
      Core.ScopedLoadFacts (Decl.nativeCtorCoreCtx base runs) →
      ∃ sortss : List (List KLevel),
        sortss.length = ctors.length ∧
        ∀ slot < ctors.length, ∃ ctor annotated sorts,
          ctors[slot]? = some ctor ∧ ctorsA[slot]? = some annotated ∧ sortss[slot]? = some sorts ∧
          Decl.NativeCtorOut base.env T (List.range ind.lvls.toNat) ind.params.toNat
            ind.indices.toNat resSort ta (rawTypes.getD slot default) ctor annotated sorts := by
  obtain ⟨levelsBound, paramsBound, indicesBound, sourceCountBound⟩ :=
    Ingress.get_ci_iprj_header_bounds (base := base) source blockShape
      (by simpa only [Array.getElem?_toList] using memberAt) formerGood formerBlockRep formerLoad
  have countBound : ctors.length < 549755813888 := by
    rw [countEq]
    exact sourceCountBound
  have fieldsBound := native_ctor_field_bounds (base := base) family countBound blockRep subset observed
  exact native_ctor_scoped_of_records hLevels source former formerShape blockShape memberAt one
    tableWf key family countEq levelsBound paramsBound indicesBound countBound fieldsBound sortEq
    levels varsBounded noFvars fresh notBasis notProjection noFormerProjection envFacts
    subset good known roleContext formerRep blockRep sortRep observed


/-- The successful root trace supplies raw query facts and every count bound for the native
constructor pass. Canonical hash coverage is supplied by the actual claim-phase witness. -/
theorem native_ctor_scoped_of_root (hLevels : IxVM.Consistency.Levels)
    {base : Core.Ctx} {block : Bytes.Address} {i : F} {T : KKey}
    (source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block))
    (former : Ingress.CanonicalRecordAt base.E (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)))
    (formerShape : former.value.info = .iPrj ⟨(ZMod.val i).toUInt64, Core.ixAddr block⟩)
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members[ZMod.val i]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(ZMod.val i, ind)])
    (key : T = base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)))
    {rootCalls : List (Call F)} {ctors ctorsA : List (KConstantVal × Nat)}
    {rootName : String} {rootArgs : List (SourceValue F)}
    {rootBefore rootAfter : Heap F} {rootResult : SourceValue F}
    (rootObserved : ObsFn Core.W rootName rootArgs rootBefore rootResult rootAfter rootCalls)
    (rootGood : Core.Good base rootCalls)
    (rootCoverage : Ingress.CanonicalHashCoverage base.E rootCalls)
    {rawTypes : List KExpr} {ta : KExpr} {resSort indLevel : KLevel}
    (family : Decl.CtorLoadAtIndex base.t block ind.params.toNat i rootCalls ctors ctorsA rawTypes)
    (countEq : ctors.length = ind.ctors.size)
    {formerBlockArg formerPtr : SourceValue F} {formerHeap formerAfter : Heap F}
    {formerCalls : List (Call F)}
    (formerSubset : ∀ call ∈ formerCalls, call ∈ rootCalls)
    (formerBlockRep : Bytes.RepAddressRef Core.addrTy formerHeap block formerBlockArg)
    (formerLoad : ObsFn Core.W "Ingress::get_ci_iprj" [formerBlockArg, .field i]
      formerHeap formerPtr formerAfter formerCalls)
    (sortEq : Core.LvEq resSort indLevel)
    (levels : ∀ ctor ∈ ctors, ctor.1.levelParams = List.range ind.lvls.toNat)
    (varsBounded : ∀ ctor ∈ ctors, ctor.1.type.looseBVarsBounded 0 = true)
    (noFvars : ∀ ctor ∈ ctors, ctor.1.type.hasFvar = false)
    (fresh : ∀ ctor ∈ ctors, base.env.find? ctor.1.name = none)
    (notBasis : ∀ ctor ∈ ctors, Ix.Kernel.reservedBasisNames.contains ctor.1.name = false)
    (notProjection : ∀ ctor ∈ ctors, ctor.1.name.isProjFnShape = false)
    (noFormerProjection : ∀ field, base.env.findProj? T field = none)
    (envFacts : Core.CoreEnvFacts base)
    {rc pta bp pind result : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (subset : ∀ call ∈ calls, call ∈ rootCalls)
    (roleContext : Core.RCRep base.t base.lim h rc)
    (formerRep : Core.Tm base.κ 0 (fun _ => default) h 0 ta pta)
    (blockRep : Bytes.RepAddressRef Core.addrTy h block bp)
    (sortRep : RepKLevel h indLevel pind)
    (observed : ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
      [rc, pta, .field (ind.params.toNat : F), .field (ind.indices.toNat : F),
        .field (ctors.length : F), .field (ind.lvls.toNat : F), bp, .field i, pind, .field 0, .field 0]
      h result h' calls) :
    ∃ runs : List (Decl.NativeCtorCoreRun rootCalls),
      Core.ScopedLoadFacts (Decl.nativeCtorCoreCtx base runs) →
      ∃ sortss : List (List KLevel),
        sortss.length = ctors.length ∧
        ∀ slot < ctors.length, ∃ ctor annotated sorts,
          ctors[slot]? = some ctor ∧ ctorsA[slot]? = some annotated ∧ sortss[slot]? = some sorts ∧
          Decl.NativeCtorOut base.env T (List.range ind.lvls.toNat) ind.params.toNat
            ind.indices.toNat resSort ta (rawTypes.getD slot default) ctor annotated sorts := by
  subst T
  obtain ⟨levelsBound, paramsBound, indicesBound, sourceCountBound⟩ :=
    Ingress.get_ci_iprj_header_bounds (base := base) source blockShape
      (by simpa only [Array.getElem?_toList] using memberAt)
      (rootGood.sub formerSubset) formerBlockRep formerLoad
  have countBound : ctors.length < 549755813888 := by
    rw [countEq]
    exact sourceCountBound
  have fieldsBound := native_ctor_field_bounds (base := base) family countBound blockRep subset observed
  let raw := Ingress.traceRecordCtx base rootCalls
  have rawKeyed : raw.TableKeyed := ⟨rfl⟩
  have rawFacts := Ingress.rawRecordFacts_of_hashed_trace rootObserved rootGood rootCoverage
  have covered := Ingress.traceRecordCtx_coverage base subset
  have peer := native_peer_reads (raw := raw) source former formerShape blockShape memberAt one envFacts.tableWf
  have peer' : Decl.OneTypePeerReads raw block
      (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)))
      (List.range ind.lvls.toNat).length ind.params.toNat ind.indices.toNat ctors.length i := by
    simpa only [List.length_range, countEq, raw, Ingress.traceRecordCtx, Core.ScopedCtx.κ, Core.Ctx.κ] using peer
  exact Decl.native_ctor_scoped hLevels (cR := raw) (indIndex := i)
    (by simp) (by simpa only [List.length_range] using levelsBound)
    paramsBound indicesBound countBound fieldsBound sortEq family levels varsBounded noFvars
    fresh notBasis notProjection noFormerProjection envFacts.store envFacts rawFacts peer'
    subset (rootGood.sub subset) covered roleContext formerRep blockRep sortRep
    (by simpa only [List.length_range] using observed)


end IxVM.Refinement.Assembly
