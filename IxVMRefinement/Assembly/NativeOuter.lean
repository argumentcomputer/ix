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
    {source : L1.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {rawType : Core.KExpr} {calls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind rawType calls) :=
  Decl.NativeInductShapeCall input.rc input.typePtr input.blockPtr (.field i) (L1.repBoolField ind.isUnsafe)
    ind.params.toNat ind.indices.toNat ind.ctors.size ind.lvls.toNat input.heap calls

/-- The constructed input exposes its actual route and native shape-stage calls. -/
theorem NativeFormerRunInput.dispatch {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : L1.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {rawType : Core.KExpr} {calls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind rawType calls) :
    (∃ native : input.NativeCall,
      Nonempty (Decl.NativeShapeCalls input.rc input.typePtr input.blockPtr (.field i)
        (L1.repBoolField ind.isUnsafe) ind.params.toNat ind.indices.toNat ind.ctors.size ind.lvls.toNat
        native.before calls)) ∨ Decl.ModeledInductCall input.blockPtr input.heap calls := by
  rcases Decl.native_induct_dispatch input.checkedRun with ⟨native⟩ | modeled
  · let framed := native.mono input.checkSubset
    exact .inl ⟨framed, Decl.native_shape_calls framed.observed framed.subset⟩
  · obtain ⟨before, result, after, children, observed, nonzero, extended, member, included⟩ := modeled
    exact .inr ⟨before, result, after, children, observed, nonzero, extended,
      input.checkSubset _ member, fun call inside => input.checkSubset call (included call inside)⟩

/-- The actual native verdict identifies the input's unique indexed family. -/
theorem NativeFormerRunInput.oneFamily {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : L1.CanonicalRecordAt base.E (Core.ixAddr block)}
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
    {source : L1.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {rawType : Core.KExpr} {calls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind rawType calls) :
    Decl.TmExact base.κ 0 (fun _ => default) input.heap 0 input.annotated.type input.typePtr := by
  have represented := input.represented.2.2.2 0 (fun _ => default)
  have levels : input.annotated.levelParams = List.range ind.lvls.toNat := input.stored.2.1
  rwa [levels, Decl.posOf_range] at represented

/-- The actual native input and root trace construct the former's no-self conclusion.
Its sort check uses only the prelude's selected semantic loads. -/
theorem NativeFormerRunInput.noSelf {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : L1.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {rawType : Core.KExpr} {calls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind rawType calls)
    (native : input.NativeCall)
    {rootName : String} {rootArgs : List (SourceValue F)} {before after : Heap F} {result : SourceValue F}
    (observed : ObsFn Core.W rootName rootArgs before result after calls)
    (good : Core.Good base calls) (coverage : L1.CanonicalHashCoverage base.E calls)
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
  let raw := L1.traceRecordCtx base calls
  obtain ⟨projection, projectionShape⟩ := input.projectionSource
  have peer := native_peer_reads (raw := raw) source projection projectionShape input.blockShape
    (by simpa only [Array.getElem?_toList] using input.memberAt) (input.oneFamily native good) facts.tableWf
  have records := L1.rawRecordFacts_of_hashed_trace observed good coverage
  exact input.prelude.noSelf peer records good (L1.traceRecordCtx_coverage base (fun _ member => member))
    input.exactType noProj input.blockRep

end IxVM.Refinement.Assembly
