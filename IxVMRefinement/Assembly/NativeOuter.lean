import IxVMRefinement.Assembly.NativeWalkedInputs
import IxVMRefinement.Decl.NativeShape

/-! # Outer native dispatch from constructed former inputs

The actual check selects its native or modeled branch. On the native branch, its observed
modeled verdict supplies the unique family; the original occurrence guard is then refined
using raw facts constructed from the same root trace.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

abbrev NativeFormerRunInput.NativeCall {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {rawType : Core.KExpr} {calls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind rawType calls) :=
  Decl.NativeInductShapeCall input.rc input.typePtr input.blockPtr (.field i) (Ingress.repBoolField ind.isUnsafe)
    ind.params.toNat ind.indices.toNat ind.ctors.size ind.lvls.toNat input.heap calls

/-- The constructed input exposes its actual route and native shape-stage calls. -/
theorem NativeFormerRunInput.dispatch {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {rawType : Core.KExpr} {calls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind rawType calls) :
    (∃ native : input.NativeCall,
      Nonempty (Decl.NativeShapeCalls input.rc input.typePtr input.blockPtr (.field i)
        (Ingress.repBoolField ind.isUnsafe) ind.params.toNat ind.indices.toNat ind.ctors.size ind.lvls.toNat
        native.before calls)) ∨ Decl.ModeledInductCall input.blockPtr input.heap calls := by
  rcases Decl.native_induct_dispatch input.checkedRun with native | modeled
  · obtain ⟨native⟩ := native
    let framed := native.mono input.checkSubset
    exact .inl ⟨framed, Decl.native_shape_calls framed.observed framed.subset⟩
  · obtain ⟨before, result, after, children, observed, nonzero, extended, member, included⟩ := modeled
    exact .inr ⟨before, result, after, children, observed, nonzero, extended,
      input.checkSubset _ member, fun call inside => input.checkSubset call (included call inside)⟩

/-- The actual native verdict identifies the input's unique indexed family. -/
theorem NativeFormerRunInput.oneFamily {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {rawType : Core.KExpr} {calls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind rawType calls)
    (native : input.NativeCall) (good : Core.Good base calls) :
    Ix.CompileCert.ReaderIndex.inductives members = #[(ZMod.val i, ind)] := by
  have few := native_block_inductive_count (base := base) source input.blockShape
    (good.sub native.modeSubset)
    (Bytes.repAddressRef_heapMono₂ Core.addrTy native.initialToMode input.blockRep) native.modeRun
  exact native_inductives_singleton few (by simpa only [Array.getElem?_toList] using input.memberAt)

/-- The exact type representation uses the input's declared positional level parameters. -/
theorem NativeFormerRunInput.exactType {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {rawType : Core.KExpr} {calls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind rawType calls) :
    Decl.TmExact base.κ 0 (fun _ => default) input.heap 0 input.annotated.type input.typePtr := by
  have represented := input.represented.2.2.2 0 (fun _ => default)
  have levels : input.annotated.levelParams = List.range ind.lvls.toNat := input.stored.2.1
  rwa [levels, Decl.posOf_range] at represented

/-- The actual native input and root trace construct the former's no-self conclusion.
Its sort check uses only the prelude's selected semantic loads. -/
theorem NativeFormerRunInput.noSelf {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {rawType : Core.KExpr} {calls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind rawType calls)
    (native : input.NativeCall)
    {rootName : String} {rootArgs : List (SourceValue F)} {before after : Heap F} {result : SourceValue F}
    (observed : ObsFn Core.W rootName rootArgs before result after calls)
    (good : Core.Good base calls) (coverage : Ingress.CanonicalHashCoverage base.E calls)
    (facts : Core.CoreEnvFacts { base with lim := some input.limit })
    (fresh : base.env.find? (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) = none)
    (notBasis : Ix.Kernel.reservedBasisNames.contains
      (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) = false)
    (noProjection : ∀ field, base.env.findProj? (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) field = none)
    (loads : Core.ScopedLoadFacts
      (Decl.nativeFormerCheckCtx { base with lim := some input.limit } input.prelude)) :
    input.annotated.type.mentionsConst (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) = false := by
  obtain ⟨_, _, _, _, inferred, _, _, _⟩ := input.checked facts good fresh notBasis loads
  have noFvars := Decl.annotates_hasFvar_false input.stored.2.2 input.noFvars
  have noProj := Decl.noProjAt_of_infer_full noProjection inferred noFvars
  let raw := Ingress.traceRecordCtx base calls
  have rawKeyed : raw.TableKeyed := ⟨rfl⟩
  obtain ⟨projection, projectionShape⟩ := input.projectionSource
  have peer := native_peer_reads (raw := raw) source projection projectionShape input.blockShape
    (by simpa only [Array.getElem?_toList] using input.memberAt) (input.oneFamily native good) facts.tableWf
  have records := Ingress.rawRecordFacts_of_hashed_trace observed good coverage
  exact input.prelude.noSelf peer records good (Ingress.traceRecordCtx_coverage base (fun _ member => member))
    input.exactType noProj input.blockRep

/-- The actual constant check supplies the closedness and resolution properties used by StoreInv. -/
theorem NativeFormerRunInput.typeProperties {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {rawType : Core.KExpr} {calls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind rawType calls)
    (checked : Ix.Kernel.Semantics.ConstantValCheckJ Ix.Kernel.Model.rulesJ base.env
      ⟨base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)), List.range ind.lvls.toNat, rawType⟩
      input.annotated) :
    input.annotated.type.hasFvar = false ∧
      input.annotated.type.allLevelParamsDefined input.annotated.levelParams = true ∧
      input.annotated.type.constsResolve base.env = true ∧
      input.annotated.type.looseBVarsBounded 0 = true := by
  obtain ⟨type, ⟨_, _, _, _, _, _, _, defined, resolved, _⟩, valueEq⟩ := checked
  have typeEq : input.annotated.type = type := by rw [valueEq]
  have levelsEq : input.annotated.levelParams = List.range ind.lvls.toNat := input.stored.2.1
  refine ⟨Decl.annotates_hasFvar_false input.stored.2.2 input.noFvars, ?_, ?_,
    Decl.annotates_looseBVarsBounded input.stored.2.2 0 input.varsBounded⟩
  · rw [typeEq, levelsEq]
    exact defined
  · rw [typeEq]
    exact resolved

/-- The semantic constructor stage keeps the actual role limit and supplied native caps. -/
abbrev NativeFormerRunInput.stageCtx {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {rawType : Core.KExpr} {calls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind rawType calls)
    (parts : Ix.Kernel.InductiveShape .anon) (isRec : Bool) : Core.Ctx :=
  { base with env := ⟨.indInfo input.annotated (Ix.Kernel.nativeCapsAt parts isRec) :: base.env.consts⟩
              lim := some input.limit }

/-- The actual former check and native shape guard construct the stage invariants. No raw
former telescope or independent type-property certificate is supplied by the caller. -/
theorem NativeFormerRunInput.stageFacts {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {rawType : Core.KExpr} {calls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind rawType calls)
    (native : input.NativeCall)
    (shape : Decl.NativeShapeCalls input.rc input.typePtr input.blockPtr (.field i)
      (Ingress.repBoolField ind.isUnsafe) ind.params.toNat ind.indices.toNat ind.ctors.size ind.lvls.toNat
      native.before calls)
    {parts : Ix.Kernel.InductiveShape .anon} {isRec : Bool}
    (params : parts.nP = ind.params.toNat) (indices : parts.nIdx = ind.indices.toNat)
    (facts : Core.CoreEnvFacts { base with lim := some input.limit }) (good : Core.Good base calls)
    (fresh : base.env.find? (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) = none)
    (notBasis : Ix.Kernel.reservedBasisNames.contains
      (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) = false)
    (loads : Core.ScopedLoadFacts
      (Decl.nativeFormerCheckCtx { base with lim := some input.limit } input.prelude)) :
    Core.CoreEnvFacts (input.stageCtx parts isRec) := by
  have checked := (input.checked facts good fresh notBasis loads).1
  have properties := input.typeProperties checked
  have named : input.annotated.name = base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)) := input.stored.1
  have freshAnnotated : base.env.find? input.annotated.name = none := by rwa [named]
  have keyShape : input.annotated.name.isProjFnShape = false := by
    rw [named]
    exact Decl.nat_keyOf_isProjFnShape_false base.t _
  have bound : parts.nP + parts.nIdx < 18446744069414584321 := by
    rw [params, indices]
    have hp := input.paramsBound
    have hi := input.indicesBound
    omega
  have represented := input.exactType.mono (native.initialToShape.trans shape.initial_to_guard)
  have guard : ObsFn Core.W "KernelCheck::former_decl_ok"
      [input.typePtr, .field (parts.nP : F), .field (parts.nIdx : F), .field (ind.ctors.size : F),
        input.blockPtr, .field i, shape.sortLevel]
      shape.sortAfter shape.guardResult shape.guardAfter shape.guardCalls := by
    simpa only [params, indices] using shape.guardRun
  exact Decl.coreEnvFacts_consNativeCapsAt_of_guard
    (c := { base with lim := some input.limit }) (shape := parts) (isRec := isRec)
    facts freshAnnotated keyShape properties bound represented guard


end IxVM.Refinement.Assembly
