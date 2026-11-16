import IxVMRefinement.Assembly.NativeReadFamily
import IxVMRefinement.Assembly.NativeOuter
import IxVMRefinement.Assembly.NativeCtorNames
import IxVMRefinement.Decl.NativeCtorRun

/-! # The actual scoped native constructor stage

The former's observed check and guard construct the stage facts. Actual projection hashes
preserve constructor freshness across the former installation, and the result-sort observation
connects the stage to the constructor checks and their semantic constructor-pass relation.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core (KExpr KLevel)
open IxVM.Refinement.Decl (KConstantVal)

/-- Compose the actual former and shape observations into the scoped constructor stage.
Base prefix freshness, reader framing, and the genuine selected semantic loads remain explicit. -/
theorem NativeFormerRunInput.constructorStage (hLevels : IxVM.Consistency.Levels) {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : L1.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {rawType : KExpr} {calls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind rawType calls)
    (native : input.NativeCall)
    (shape : Decl.NativeShapeCalls input.rc input.typePtr input.blockPtr (.field i)
      (L1.repBoolField ind.isUnsafe) ind.params.toNat ind.indices.toNat ind.ctors.size ind.lvls.toNat
      native.before calls)
    {parts : Ix.Kernel.InductiveShape .anon} {isRec : Bool}
    (params : parts.nP = ind.params.toNat) (indices : parts.nIdx = ind.indices.toNat)
    (safe : ind.isUnsafe = false)
    {rootName : String} {rootArgs : List (SourceValue F)} {before after : Heap F} {result : SourceValue F}
    (observedRoot : ObsFn Core.W rootName rootArgs before result after calls)
    (good : Core.Good base calls) (coverage : L1.CanonicalHashCoverage base.E calls)
    (facts : Core.CoreEnvFacts { base with lim := some input.limit })
    (freshFormer : base.env.find? (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) = none)
    (formerNotBasis : Ix.Kernel.reservedBasisNames.contains
      (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) = false)
    (noProjection : ∀ field, base.env.findProj? (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) field = none)
    (formerLoads : Core.ScopedLoadFacts
      (Decl.nativeFormerCheckCtx { base with lim := some input.limit } input.prelude))
    (sortLoads : Core.ScopedLoadFacts (Decl.nativeShapeSortCtx (input.stageCtx parts isRec) shape))
    {ctors annotated : List (KConstantVal × Nat)} {rawTypes : List KExpr}
    (family : Decl.CtorLoadAtIndex base.t block ind.params.toNat i calls ctors annotated rawTypes)
    (countEq : ctors.length = ind.ctors.size)
    (levels : ∀ ctor ∈ ctors, ctor.1.levelParams = List.range ind.lvls.toNat)
    (varsBounded : ∀ ctor ∈ ctors, ctor.1.type.looseBVarsBounded 0 = true)
    (closed : ∀ ctor ∈ ctors, ctor.1.type.hasFvar = false)
    (freshCtors : ∀ ctor ∈ ctors, base.env.find? ctor.1.name = none)
    (ctorsNotBasis : ∀ ctor ∈ ctors, Ix.Kernel.reservedBasisNames.contains ctor.1.name = false) :
    ∃ sort : KLevel,
      KernelLevels.RepKLevel shape.ctorBefore sort shape.sortLevel ∧
      (∀ binders level, input.annotated.type.stripPis (ind.params.toNat + ind.indices.toNat) =
        some (binders, .sort level) → Core.LvEq level sort) ∧
      ∃ runs : List (Decl.NativeCtorCoreRun calls),
        Core.ScopedLoadFacts (Decl.nativeCtorCoreCtx (input.stageCtx parts isRec) runs) →
        ∃ sortss : List (List KLevel),
          sortss.length = ctors.length ∧
          (∀ slot < ctors.length, ∃ ctor stored sorts,
            ctors[slot]? = some ctor ∧ annotated[slot]? = some stored ∧ sortss[slot]? = some sorts ∧
            Decl.NativeCtorOut (input.stageCtx parts isRec).env
              (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) (List.range ind.lvls.toNat)
              ind.params.toNat ind.indices.toNat sort input.annotated.type
              (rawTypes.getD slot default) ctor stored sorts) ∧
          Ix.Kernel.Semantics.SumCtorsRunJ Ix.Kernel.Model.rulesJ
            (input.stageCtx parts isRec).env (input.stageCtx parts isRec).env
            (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) (List.range ind.lvls.toNat)
            ind.params.toNat ind.indices.toNat sort (Ix.Kernel.Level.isEquiv sort .zero == some true)
            false input.annotated ctors annotated sortss := by
  let stage := input.stageCtx parts isRec
  have stageFacts : Core.CoreEnvFacts stage :=
    input.stageFacts native shape params indices facts good freshFormer formerNotBasis formerLoads
  have stageGood : Core.Good stage calls := good
  have sumBound : ind.params.toNat + ind.indices.toNat < 18446744069414584321 := by
    have hp := input.paramsBound
    have hi := input.indicesBound
    omega
  obtain ⟨sort, sortRep, sortEq⟩ := shape.resultSort (base := stage) sumBound
    (input.roles.mono native.initialToShape)
    (input.exactType.toTm.mono native.initialToShape) stageFacts stageGood sortLoads
  have countBound : ctors.length < 549755813888 := by rw [countEq]; exact input.ctorCountBound
  have loop : ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
      [input.rc, input.typePtr, .field (ind.params.toNat : F), .field (ind.indices.toNat : F),
        .field (ctors.length : F), .field (ind.lvls.toNat : F), input.blockPtr, .field i,
        shape.sortLevel, .field 0, .field 0] shape.ctorBefore shape.result shape.after shape.ctorCalls := by
    simpa [countEq, safe, L1.repBoolField] using shape.ctorRun
  have extended := native.initialToShape.trans shape.initial_to_ctors
  have blockRep := Bytes.repAddressRef_heapMono₂ Core.addrTy extended input.blockRep
  obtain ⟨projection, projectionShape⟩ := input.projectionSource
  have separate := native_ctors_not_former (base := base) family countBound projection projectionShape
    facts.tableWf good blockRep shape.ctorSubset loop
  have nameShape : input.annotated.name.isProjFnShape = false := by
    rw [input.stored.1]
    exact Decl.nat_keyOf_isProjFnShape_false base.t _
  have freshStage : ∀ ctor ∈ ctors, stage.env.find? ctor.1.name = none := by
    intro ctor member
    change (Ix.Kernel.Env.mk (.indInfo input.annotated (Ix.Kernel.nativeCapsAt parts isRec) :: base.env.consts)).find?
      ctor.1.name = none
    rw [Decl.find?_cons_indInfo_ne _ _ _ (by rw [input.stored.1]; exact (separate ctor member).symm)]
    exact freshCtors ctor member
  have noProjectionStage : ∀ field,
      stage.env.findProj? (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) field = none := by
    intro field
    change (Ix.Kernel.Env.mk (.indInfo input.annotated (Ix.Kernel.nativeCapsAt parts isRec) :: base.env.consts)).findProj?
      (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) field = none
    unfold Ix.Kernel.Env.findProj?
    rw [Decl.find?_cons_indInfo_ne _ _ _ (Decl.ne_projTableName_of_isProjFnShape_false nameShape _)]
    exact noProjection field
  have ctorNameShape : ∀ ctor ∈ ctors, ctor.1.name.isProjFnShape = false := by
    intro ctor member
    obtain ⟨slot, slotBound, rfl⟩ := List.getElem_of_mem member
    have named := native_ctor_slot_name (base := base) family countBound blockRep shape.ctorSubset loop
      slotBound (List.getElem?_eq_getElem slotBound)
    rw [named]
    exact Decl.nat_keyOf_isProjFnShape_false base.t _
  have fieldBounds := native_ctor_field_bounds (base := base) family countBound blockRep shape.ctorSubset loop
  let raw := L1.traceRecordCtx stage calls
  have records := L1.rawRecordFacts_of_hashed_trace (base := stage) observedRoot stageGood coverage
  have rawCovered := L1.traceRecordCtx_coverage stage shape.ctorSubset
  have peer := native_peer_reads (raw := raw) source projection projectionShape input.blockShape
    (by simpa only [Array.getElem?_toList] using input.memberAt) (input.oneFamily native good) facts.tableWf
  have peer' : Decl.OneTypePeerReads raw block
      (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)))
      (List.range ind.lvls.toNat).length ind.params.toNat ind.indices.toNat ctors.length i := by
    simpa only [List.length_range, countEq, raw, L1.traceRecordCtx, Core.ScopedCtx.κ, Core.Ctx.κ,
      stage, NativeFormerRunInput.stageCtx] using peer
  obtain ⟨runs, constructorChecks⟩ := Decl.native_ctor_scoped hLevels (cR := raw) (indIndex := i)
    (lps := List.range ind.lvls.toNat) (resSort := sort) (ind_lvl := sort)
    (by simp) (by simpa only [List.length_range] using input.levelsBound)
    input.paramsBound input.indicesBound countBound fieldBounds (fun _ => rfl)
    family levels varsBounded closed freshStage ctorsNotBasis ctorNameShape noProjectionStage
    stageFacts.store stageFacts records peer' shape.ctorSubset (stageGood.sub shape.ctorSubset) rawCovered
    (input.roles.mono extended) (input.exactType.toTm.mono extended) blockRep sortRep
    (by simpa only [List.length_range] using loop)
  refine ⟨sort, sortRep, sortEq, runs, fun ctorLoads => ?_⟩
  obtain ⟨sortss, length, outputs⟩ := constructorChecks ctorLoads
  exact ⟨sortss, length, outputs,
    Decl.native_ctor_outputs_to_runs family.1 length outputs (fun _ => rfl) closed⟩

/-- Actual reader frames and conversion checks construct the constructor family and all
raw type-scope data before the scoped semantic stage is applied. -/
theorem NativeFormerRunInput.constructorStage_of_reader_frames (hLevels : IxVM.Consistency.Levels) {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : L1.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {rawType : KExpr} {calls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind rawType calls)
    (native : input.NativeCall)
    (shape : Decl.NativeShapeCalls input.rc input.typePtr input.blockPtr (.field i)
      (L1.repBoolField ind.isUnsafe) ind.params.toNat ind.indices.toNat ind.ctors.size ind.lvls.toNat
      native.before calls)
    {parts : Ix.Kernel.InductiveShape .anon} {isRec : Bool}
    (params : parts.nP = ind.params.toNat) (indices : parts.nIdx = ind.indices.toNat)
    (safe : ind.isUnsafe = false)
    {rootName : String} {rootArgs : List (SourceValue F)} {before after : Heap F} {result : SourceValue F}
    (observedRoot : ObsFn Core.W rootName rootArgs before result after calls)
    (good : Core.Good base calls) (coverage : L1.CanonicalHashCoverage base.E calls)
    (facts : Core.CoreEnvFacts { base with lim := some input.limit })
    (freshFormer : base.env.find? (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) = none)
    (formerNotBasis : Ix.Kernel.reservedBasisNames.contains
      (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) = false)
    (noProjection : ∀ field, base.env.findProj? (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) field = none)
    (formerLoads : Core.ScopedLoadFacts
      (Decl.nativeFormerCheckCtx { base with lim := some input.limit } input.prelude))
    (sortLoads : Core.ScopedLoadFacts (Decl.nativeShapeSortCtx (input.stageCtx parts isRec) shape))
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
      cx.blob address = some bytes)
    (freshRows : ∀ row ∈ rows, base.env.find? row.1.name = none)
    (rowsNotBasis : ∀ row ∈ rows, Ix.Kernel.reservedBasisNames.contains row.1.name = false) :
    ∃ (annotated : List (KConstantVal × Nat)) (rawTypes : List KExpr),
    ∃ sort : KLevel,
      KernelLevels.RepKLevel shape.ctorBefore sort shape.sortLevel ∧
      (∀ binders level, input.annotated.type.stripPis (ind.params.toNat + ind.indices.toNat) =
        some (binders, .sort level) → Core.LvEq level sort) ∧
      ∃ runs : List (Decl.NativeCtorCoreRun calls),
        Core.ScopedLoadFacts (Decl.nativeCtorCoreCtx (input.stageCtx parts isRec) runs) →
        ∃ sortss : List (List KLevel),
          sortss.length = (rows.map (fun row => (row.1, row.2.2))).length ∧
          (∀ slot < (rows.map (fun row => (row.1, row.2.2))).length, ∃ ctor stored sorts,
            (rows.map (fun row => (row.1, row.2.2)))[slot]? = some ctor ∧ annotated[slot]? = some stored ∧ sortss[slot]? = some sorts ∧
            Decl.NativeCtorOut (input.stageCtx parts isRec).env
              (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) (List.range ind.lvls.toNat)
              ind.params.toNat ind.indices.toNat sort input.annotated.type
              (rawTypes.getD slot default) ctor stored sorts) ∧
          Ix.Kernel.Semantics.SumCtorsRunJ Ix.Kernel.Model.rulesJ
            (input.stageCtx parts isRec).env (input.stageCtx parts isRec).env
            (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) (List.range ind.lvls.toNat)
            ind.params.toNat ind.indices.toNat sort (Ix.Kernel.Level.isEquiv sort .zero == some true)
            false input.annotated (rows.map (fun row => (row.1, row.2.2))) annotated sortss := by
  obtain ⟨annotated, rawTypes, family, rowLength, rowProperties⟩ :=
    input.constructorFamily native shape safe good frames memberKeys keyed selfKeyed blobReads
  have countEq : (rows.map (fun row => (row.1, row.2.2))).length = ind.ctors.size := by
    simpa only [List.length_map] using rowLength
  refine ⟨annotated, rawTypes, ?_⟩
  apply input.constructorStage hLevels native shape params indices safe observedRoot good coverage facts
    freshFormer formerNotBasis noProjection formerLoads sortLoads family countEq
  · intro ctor member
    obtain ⟨row, inRows, rfl⟩ := List.mem_map.mp member
    exact (rowProperties row inRows).2.1
  · intro ctor member
    obtain ⟨row, inRows, rfl⟩ := List.mem_map.mp member
    exact (rowProperties row inRows).2.2.1
  · intro ctor member
    obtain ⟨row, inRows, rfl⟩ := List.mem_map.mp member
    exact (rowProperties row inRows).2.2.2.2
  · intro ctor member
    obtain ⟨row, inRows, rfl⟩ := List.mem_map.mp member
    exact freshRows row inRows
  · intro ctor member
    obtain ⟨row, inRows, rfl⟩ := List.mem_map.mp member
    exact rowsNotBasis row inRows


end IxVM.Refinement.Assembly
