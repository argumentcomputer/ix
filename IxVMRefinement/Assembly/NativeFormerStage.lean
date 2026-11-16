import IxVMRefinement.Assembly.NativeOuter

/-! # Semantic former stages from actual native observations

The existing shape guard supplies the checked telescope whenever the family has no indices.
Its scoped constant check then builds the semantic former stage at the selected native caps,
including the environment extension and index-sort evidence used by the subsequent stages.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- The actual former guard distinguishes a checked telescope from the indexed alias case. -/
theorem NativeFormerRunInput.telescopeOrIndexed {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : L1.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {rawType : Core.KExpr} {calls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind rawType calls)
    (native : input.NativeCall)
    (shape : Decl.NativeShapeCalls input.rc input.typePtr input.blockPtr (.field i)
      (L1.repBoolField ind.isUnsafe) ind.params.toNat ind.indices.toNat ind.ctors.size ind.lvls.toNat
      native.before calls) :
    (∃ binders level,
      input.annotated.type.stripPis (ind.params.toNat + ind.indices.toNat) =
        some (binders, .sort level) ∧ binders.length = ind.params.toNat + ind.indices.toNat) ∨
      ind.indices.toNat ≠ 0 := by
  have bound : ind.params.toNat + ind.indices.toNat < 18446744069414584321 := by
    have hp := input.paramsBound
    have hi := input.indicesBound
    omega
  exact Decl.former_decl_ok_shape bound
    (input.exactType.mono (native.initialToShape.trans shape.initial_to_guard)) shape.guardRun

/-- A no-index family gets its complete semantic former stage from the actual guard and
selected prelude check. The output keeps the supplied recursion verdict and completed caps. -/
theorem NativeFormerRunInput.formerStage_noIndices {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : L1.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {rawType : Core.KExpr} {calls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind rawType calls)
    (native : input.NativeCall)
    (shape : Decl.NativeShapeCalls input.rc input.typePtr input.blockPtr (.field i)
      (L1.repBoolField ind.isUnsafe) ind.params.toNat ind.indices.toNat ind.ctors.size ind.lvls.toNat
      native.before calls)
    {parts : Ix.Kernel.InductiveShape .anon} {isRec : Bool}
    (former : parts.cvT =
      ⟨base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)), List.range ind.lvls.toNat, rawType⟩)
    (params : parts.nP = ind.params.toNat) (indices : parts.nIdx = ind.indices.toNat)
    (noIndices : ind.indices.toNat = 0)
    (facts : Core.CoreEnvFacts { base with lim := some input.limit }) (good : Core.Good base calls)
    (fresh : base.env.find? (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) = none)
    (notBasis : Ix.Kernel.reservedBasisNames.contains
      (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) = false)
    (loads : Core.ScopedLoadFacts
      (Decl.nativeFormerCheckCtx { base with lim := some input.limit } input.prelude)) :
    ∃ binders level,
      input.annotated.type.stripPis (parts.nP + parts.nIdx) = some (binders, .sort level) ∧
      Ix.Kernel.Semantics.SumIndRunJ Ix.Kernel.Model.rulesJ base.env parts
        (fun completed => Ix.Kernel.nativeCapsAt completed isRec)
        (input.stageCtx (parts.withSort level) isRec).env input.annotated (parts.withSort level) ∧
      Ix.Kernel.EnvExt base.env (input.stageCtx (parts.withSort level) isRec).env ∧
      ∃ openedVars sorts,
        Ix.Kernel.openPisAtFvars (parts.nP + parts.nIdx) input.annotated.type 0 =
          some (openedVars, .sort level) ∧
        Ix.Kernel.Semantics.FieldSortsJ Ix.Kernel.Model.rulesJ
          (input.stageCtx (parts.withSort level) isRec).env true false level parts.nP
          (openedVars.drop parts.nP) [] parts.nIdx sorts := by
  obtain ⟨binders, level, telescope, _⟩ :=
    (input.telescopeOrIndexed native shape).resolve_right (fun nonzero => nonzero noIndices)
  have telescope' : input.annotated.type.stripPis (parts.nP + parts.nIdx) =
      some (binders, .sort level) := by simpa only [params, indices] using telescope
  have checked : Ix.Kernel.Semantics.ConstantValCheckJ Ix.Kernel.Model.rulesJ
      base.env parts.cvT input.annotated := by
    simpa only [former] using (input.checked facts good fresh notBasis loads).1
  have named : input.annotated.name = base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)) :=
    input.stored.1
  have freshAnnotated : base.env.find? input.annotated.name = none := by rwa [named]
  have keyShape : input.annotated.name.isProjFnShape = false := by
    rw [named]
    exact Decl.nat_keyOf_isProjFnShape_false base.t _
  have extended : Ix.Kernel.EnvExt base.env (input.stageCtx (parts.withSort level) isRec).env :=
    Decl.envExt_cons_nonProj freshAnnotated (Decl.ne_projTableName_of_isProjFnShape_false keyShape)
  refine ⟨binders, level, telescope', ?_, extended, ?_⟩
  · exact ⟨input.annotated, level, binders, input.annotated, checked, .inl rfl,
      telescope', .inl rfl, rfl, rfl⟩
  · exact Decl.index_fieldSortsJ_of_former checked telescope' extended

end IxVM.Refinement.Assembly
