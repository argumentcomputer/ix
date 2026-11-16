import IxVMRefinement.Decl.NativeStageMetadata
import IxVMRefinement.Decl.NativeConstructorFieldChecks

/-! # Named-motive binder data from recorded constructor checks

A domain's inference and sort evidence are recovered from its position in the checked
constructor telescope. The complete native check retains the original annotation, its exact
rebuilt expression and final branch, and both opener lists. Named-motive binder data then
comes from those recorded checks at the constructed intermediate model.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model

universe u

/-- A product's actual inference and sort reduction determine its outer binder datum. -/
theorem inferred_product_sort_metadata {md : Mode} {env : Env md} {depth : Nat}
    {domain body inferred : Expr md} {metadata : BinderMeta} {sortLevel : Level}
    (typed : Rules.Infer env .full depth (.forallE domain body metadata) inferred)
    (sorted : Rules.Red env depth inferred (.sort sortLevel)) :
    metadata.pw = Level.zeronessOf sortLevel := by
  obtain ⟨_, _, _, _, _, _, _, _, datum, inferredEq⟩ := Rules.Infer.forallE_inv typed
  rw [inferredEq] at sorted
  obtain rfl := Expr.sort.inj (Rules.Red.rigid sorted rfl)
  exact datum.symm

/-- A selected domain of the actual checked header supplies its own inference and reduction.
The caller identifies the named-motive expression, without supplying a separate sort check. -/
theorem checked_named_natRec_domain_metadata_rules {V : Type u} [SetTheory V] {env : Env .anon}
    (model : EnvModelM V .verified env) {raw checked : ConstantVal .anon}
    (header : ConstantValCheckJ rulesJ env raw checked)
    {count slot : Nat} {openedVars : List (Expr .anon)} {residual domainVar : Expr .anon}
    (opened : openPisAtFvars count checked.type 0 = some (openedVars, residual))
    (atSlot : openedVars[slot]? = some domainVar)
    {elim kindSort : Level} {motiveName : Key .anon} {motiveLevels : List Level}
    {motiveCV : ConstantVal .anon} {motiveValue domain body step : Expr .anon}
    {hint : ReducibilityHint} {motiveMeta productMeta : BinderMeta}
    (zeroFound : env.find? natZeroName = some natZeroA)
    (recFound : env.find? natRecName = some natRecA)
    (motiveFound : env.find? motiveName = some (.defnInfo motiveCV motiveValue hint))
    (motiveHeader : motiveCV.type.instantiateLevelParams motiveCV.levelParams motiveLevels =
      .forallE (.const natName []) (.sort kindSort) motiveMeta)
    (domainShape : domainVar.fvarTypeD =
      .app (.app (.app (.app (.const natRecName [elim]) (.const motiveName motiveLevels))
        (.forallE domain body productMeta)) step) (.const natZeroName [])) :
    ∃ inferred resultSort,
      Rules.Infer env .full slot domainVar.fvarTypeD inferred ∧
      Rules.Red env slot inferred (.sort resultSort) ∧
      productMeta.pw = Level.zeronessOf resultSort := by
  obtain ⟨inferred, resultSort, typed, sorted⟩ :=
    checked_type_domain_checksJ judgeInv_rulesJ header opened slot domainVar atSlot
  refine ⟨inferred, resultSort, typed, sorted, ?_⟩
  exact named_natRec_zero_product_metadata_rules model zeroFound recFound motiveFound motiveHeader
    (by simpa only [domainShape] using typed) sorted

/-- The actual constructor normalization retains one rebuilt witness and derives each
original/final domain's checks. The named-motive and final-product data use these same checks;
no domain sort premise or equality of the two annotated frames is assumed. -/
theorem ReferenceReplay.native_constructor_named_domain_trace {V : Type u} [SetTheory V]
    {prefixFuel : Nat} {ev : Evidences .anon} {sourceOut env stage scope : Env .anon}
    {declarations : List (Declaration .anon)}
    (replay : ReferenceReplay prefixFuel ev Env.empty Env.empty declarations sourceOut env)
    {parts completed : InductiveShape .anon} {isRec : Bool} {former ctorFormer : ConstantVal .anon}
    (formerRun : SumIndRunJ rulesJ env parts (fun current => nativeCapsAt current isRec) stage former completed)
    {name : Key .anon} {levels : List LevelParam} {nP nI : Nat} {sortLevel : Level}
    {isProp large : Bool} {annotated : List (ConstantVal .anon × Nat)} {sortss : List (List Level)}
    (constructorRuns : SumCtorsRunJ rulesJ scope stage name levels nP nI sortLevel isProp large
      ctorFormer completed.ctors annotated sortss)
    {before : Env .anon} {T : Key .anon} {ctorLevels : List LevelParam}
    {params indices fields fuel : Nat} {ctorSort : Level} {ctorIsProp ctorLarge : Bool}
    {raw checkedFormer checked : ConstantVal .anon} {fieldSorts : List Level}
    (run : checkSumCtor (fueledOps .verified fuel) before stage T ctorLevels params indices ctorSort
      ctorIsProp ctorLarge raw fields checkedFormer = .ok (checked, fieldSorts))
    {elim kindSort : Level} {motiveName : Key .anon} {motiveLevels : List Level}
    {motiveCV : ConstantVal .anon} {motiveValue domain body step : Expr .anon}
    {hint : ReducibilityHint} {motiveMeta productMeta : BinderMeta}
    (zeroFound : stage.find? natZeroName = some natZeroA)
    (recFound : stage.find? natRecName = some natRecA)
    (motiveFound : stage.find? motiveName = some (.defnInfo motiveCV motiveValue hint))
    (motiveHeader : motiveCV.type.instantiateLevelParams motiveCV.levelParams motiveLevels =
      .forallE (.const natName []) (.sort kindSort) motiveMeta) :
    ∃ initial rebuilt originalVars originalResidual finalVars finalResidual,
      checkConstantVal (fueledOps .verified fuel) stage raw = .ok initial ∧
      normCtorVal (fueledOps .verified fuel) stage T params fields raw initial = .ok checked ∧
      ConstructorRebuildRun stage fuel T params fields initial.type rebuilt ∧
      (checked = initial ∨
        checkConstantVal (fueledOps .verified fuel) stage { raw with type := rebuilt } = .ok checked) ∧
      openPisAtFvars (params + fields) initial.type 0 = some (originalVars, originalResidual) ∧
      openPisAtFvars (params + fields) checked.type 0 = some (finalVars, finalResidual) ∧
      originalVars.length = params + fields ∧ finalVars.length = params + fields ∧
      ∀ slot original final, originalVars[slot]? = some original → finalVars[slot]? = some final →
        ∃ originalType originalSort finalType finalSort,
          inferTypeCore .verified stage fuel slot original.fvarTypeD = .ok originalType ∧
          ensureSortCore .verified stage fuel slot originalType = .ok originalSort ∧
          inferTypeCore .verified stage fuel slot final.fvarTypeD = .ok finalType ∧
          ensureSortCore .verified stage fuel slot finalType = .ok finalSort ∧
          (original.fvarTypeD =
            .app (.app (.app (.app (.const natRecName [elim]) (.const motiveName motiveLevels))
              (.forallE domain body productMeta)) step) (.const natZeroName []) →
            productMeta.pw = Level.zeronessOf originalSort) ∧
          (final.fvarTypeD =
            .app (.app (.app (.app (.const natRecName [elim]) (.const motiveName motiveLevels))
              (.forallE domain body productMeta)) step) (.const natZeroName []) →
            productMeta.pw = Level.zeronessOf finalSort) ∧
          (∀ finalDomain finalBody finalMeta, final.fvarTypeD = .forallE finalDomain finalBody finalMeta →
            finalMeta.pw = Level.zeronessOf finalSort) := by
  obtain ⟨model⟩ := replay.native_constructorStage_model (V := V) formerRun constructorRuns
  obtain ⟨initial, rebuilt, originalVars, originalResidual, finalVars, finalResidual,
    first, normalization, rebuild, lastBranch, originalOpen, finalOpen,
    originalCount, finalCount, domains⟩ := checkSumCtor_rebuild_domain_checks model.base2.wf run
  refine ⟨initial, rebuilt, originalVars, originalResidual, finalVars, finalResidual,
    first, normalization, rebuild, lastBranch, originalOpen, finalOpen, originalCount, finalCount, ?_⟩
  intro slot original final originalAt finalAt
  obtain ⟨originalType, originalSort, finalType, finalSort, originalInfer, originalSorted,
    finalInfer, finalSorted⟩ := domains slot original final originalAt finalAt
  refine ⟨originalType, originalSort, finalType, finalSort,
    originalInfer, originalSorted, finalInfer, finalSorted, ?_, ?_, ?_⟩
  · intro shape
    exact IxVM.Refinement.Decl.named_natRec_zero_product_metadata model zeroFound recFound
      motiveFound motiveHeader (by simpa only [shape] using originalInfer) originalSorted
  · intro shape
    exact IxVM.Refinement.Decl.named_natRec_zero_product_metadata model zeroFound recFound
      motiveFound motiveHeader (by simpa only [shape] using finalInfer) finalSorted
  · intro finalDomain finalBody finalMeta shape
    exact inferred_product_sort_metadata
      (Rules.inferTypeCore_bridge (by simpa only [shape] using finalInfer))
      (Rules.whnf_bridge (ensureSortCore_inv finalSorted))

end IxVM.Refinement.Decl
