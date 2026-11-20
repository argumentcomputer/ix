import IxVMRefinement.Assembly.NativeCtorChecked
import IxVMRefinement.Assembly.RawQueryCoverage

/-! # Native constructor checking under the actual admitted trace

The claim-phase witness constructs canonical raw-query coverage in the complete metadata
union. Constructor reader/key framing and the semantic prefix remain explicit inputs;
no unrestricted load adapter is used.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core (KKey KExpr KLevel)
open IxVM.Refinement.Decl (KConstantVal)
open IxVM.Refinement.KernelLevels (RepKLevel)

/-- Complete actual metadata at a particular semantic declaration prefix. -/
noncomputable def nativeOriginCtx {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    (trace : Ixon.Env) (env : Ix.Kernel.Env .anon) (lim : Option Nat) : Core.Ctx :=
  ⟨admittedCore witness trace (fun _ => True), env, witness.table, lim⟩

/-- The actual claim and admission data discharge raw-query and numerical coverage for
native constructors. The remaining semantic load premise is restricted to the produced
finite typing scope; external reader/store correspondence is not assumed here. -/
theorem admitted_native_ctor_scoped (hLevels : IxVM.Consistency.Levels)
    {V : IxVM.Refinement.View} {binding : Ix.Kernel.Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {rootCalls : List (Call F)} {trace : Ixon.Env} {seeds : List _root_.Address}
    (walked : Claim.WalkedClaim rootCalls witness.table trace seeds)
    (loaded : IxVM.Consistency.LoadedBy rootCalls trace)
    (bounded : IxVM.Consistency.Bounded rootCalls)
    (env : Ix.Kernel.Env .anon) (lim : Option Nat) (claimBytes : ByteArray)
    (noCollision : ¬ V.HashedCollision
      (claimBytes :: binding.bytes :: IxVM.Consistency.readerImages V) rootCalls)
    {block : Bytes.Address} {i : F} {T : KKey}
    (source : Ingress.CanonicalRecordAt (nativeOriginCtx witness trace env lim).E (Core.ixAddr block))
    (former : Ingress.CanonicalRecordAt (nativeOriginCtx witness trace env lim).E (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)))
    (formerShape : former.value.info = .iPrj ⟨(ZMod.val i).toUInt64, Core.ixAddr block⟩)
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members[ZMod.val i]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(ZMod.val i, ind)])
    (key : T = (nativeOriginCtx witness trace env lim).κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)))
    {ctors ctorsA : List (KConstantVal × Nat)}
    {rootName : String} {rootArgs : List (SourceValue F)}
    {rootBefore rootAfter : Heap F} {rootResult : SourceValue F}
    (rootObserved : ObsFn Core.W rootName rootArgs rootBefore rootResult rootAfter rootCalls)
    {rawTypes : List KExpr} {ta : KExpr} {resSort indLevel : KLevel}
    (family : Decl.CtorLoadAtIndex (nativeOriginCtx witness trace env lim).t block ind.params.toNat i rootCalls ctors ctorsA rawTypes)
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
    (fresh : ∀ ctor ∈ ctors, (nativeOriginCtx witness trace env lim).env.find? ctor.1.name = none)
    (notBasis : ∀ ctor ∈ ctors, Ix.Kernel.reservedBasisNames.contains ctor.1.name = false)
    (notProjection : ∀ ctor ∈ ctors, ctor.1.name.isProjFnShape = false)
    (noFormerProjection : ∀ field, (nativeOriginCtx witness trace env lim).env.findProj? T field = none)
    (envFacts : Core.CoreEnvFacts (nativeOriginCtx witness trace env lim))
    {rc pta bp pind result : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (subset : ∀ call ∈ calls, call ∈ rootCalls)
    (roleContext : Core.RCRep (nativeOriginCtx witness trace env lim).t (nativeOriginCtx witness trace env lim).lim h rc)
    (formerRep : Core.Tm (nativeOriginCtx witness trace env lim).κ 0 (fun _ => default) h 0 ta pta)
    (blockRep : Bytes.RepAddressRef Core.addrTy h block bp)
    (sortRep : RepKLevel h indLevel pind)
    (observed : ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
      [rc, pta, .field (ind.params.toNat : F), .field (ind.indices.toNat : F),
        .field (ctors.length : F), .field (ind.lvls.toNat : F), bp, .field i, pind, .field 0, .field 0]
      h result h' calls) :
    ∃ runs : List (Decl.NativeCtorCoreRun rootCalls),
      Core.ScopedLoadFacts (Decl.nativeCtorCoreCtx (nativeOriginCtx witness trace env lim) runs) →
      ∃ sortss : List (List KLevel),
        sortss.length = ctors.length ∧
        ∀ slot < ctors.length, ∃ ctor annotated sorts,
          ctors[slot]? = some ctor ∧ ctorsA[slot]? = some annotated ∧ sortss[slot]? = some sorts ∧
          Decl.NativeCtorOut (nativeOriginCtx witness trace env lim).env T (List.range ind.lvls.toNat) ind.params.toNat
            ind.indices.toNat resSort ta (rawTypes.getD slot default) ctor annotated sorts := by
  have rootGood : Core.Good (nativeOriginCtx witness trace env lim) rootCalls :=
    admittedCore_good witness (fun _ => True) env lim claimBytes loaded bounded noCollision
  have rootCoverage : Ingress.CanonicalHashCoverage
      (nativeOriginCtx witness trace env lim).E rootCalls :=
    admitted_canonicalHashCoverage witness walked
  exact native_ctor_scoped_of_root hLevels source former formerShape blockShape memberAt one key
    rootObserved rootGood rootCoverage family countEq formerSubset formerBlockRep formerLoad sortEq
    levels varsBounded noFvars fresh notBasis notProjection noFormerProjection envFacts
    subset roleContext formerRep blockRep sortRep observed

end IxVM.Refinement.Assembly
