import IxVMRefinement.Decl.DomainInstances
import IxVMRefinement.Decl.NativeSortDomain
import IxVMRefinement.Decl.NativeDomainMotive

/-! # Named-tail binder agreement from actual constructor checks

The alias's real accepted definition front supplies its sort conversion. Executable kernel
reduction, telescope rebuilding and annotation preserve the supported named-tail fragment.
Both actual domain checks then have the target's zero-ness, and product binder data agree.
The temporary stage model is used only for the closed declaration-front conversion.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model Ix.Kernel.Semantics

universe u

/-- A real alias-to-inductive definition supports original/final sort and product-datum
agreement across the recorded constructor normalization and annotation. -/
theorem normCtorVal_aliasTail_checked_sorts {V : Type u} [SetTheory V] {env : Env .anon}
    (model : EnvModelM V .verified env) (definitions : DefinitionsTyped env)
    {aliasName targetName : Key .anon} {targetLevels : List Level}
    {aliasCV targetCV : ConstantVal .anon} {hint : ReducibilityHint} {caps : IndCaps .anon}
    {declared actual : Level}
    (aliasFound : env.find? aliasName = some (.defnInfo aliasCV (.const targetName targetLevels) hint))
    (noLevels : aliasCV.levelParams = [])
    (targetFound : env.find? targetName = some (.indInfo targetCV caps))
    (aliasHeader : aliasCV.type = .sort declared)
    (targetHeader : targetCV.type.instantiateLevelParams targetCV.levelParams targetLevels = .sort actual)
    {fuel nP nF slot count : Nat} {T : Key .anon} {raw initial checked : ConstantVal .anon}
    {originalVars finalVars : List (Expr .anon)} {originalResidual finalResidual original final : Expr .anon}
    (first : checkConstantVal (fueledOps .verified fuel) env raw = .ok initial)
    (normalized : normCtorVal (fueledOps .verified fuel) env T nP nF raw initial = .ok checked)
    (originalOpen : openPisAtFvars (nP + nF) initial.type 0 = some (originalVars, originalResidual))
    (finalOpen : openPisAtFvars (nP + nF) checked.type 0 = some (finalVars, finalResidual))
    (originalAt : originalVars[nP + slot]? = some original)
    (finalAt : finalVars[nP + slot]? = some final)
    (shape : AliasTail aliasName targetName targetLevels count original.fvarTypeD) :
    ∃ originalType originalSort finalType finalSort,
      inferTypeCore .verified env fuel (nP + slot) original.fvarTypeD = .ok originalType ∧
      ensureSortCore .verified env fuel (nP + slot) originalType = .ok originalSort ∧
      inferTypeCore .verified env fuel (nP + slot) final.fvarTypeD = .ok finalType ∧
      ensureSortCore .verified env fuel (nP + slot) finalType = .ok finalSort ∧
      Level.zeronessOf originalSort = Level.zeronessOf actual ∧
      Level.zeronessOf finalSort = Level.zeronessOf actual ∧
      Level.zeronessOf originalSort = Level.zeronessOf finalSort ∧
      (∀ leftDomain leftBody leftMeta rightDomain rightBody rightMeta,
        original.fvarTypeD = .forallE leftDomain leftBody leftMeta →
        final.fvarTypeD = .forallE rightDomain rightBody rightMeta → leftMeta.pw = rightMeta.pw) := by
  exact (AliasTail.invariant model definitions aliasFound noLevels targetFound aliasHeader targetHeader).checked_sorts
    first normalized originalOpen finalOpen originalAt finalAt ⟨count, shape⟩

/-- The accepted prefix supplies both the stage model and the actual alias-definition checks;
no model, sort run, or PW correspondence at the final reader store is assumed. -/
theorem ReferenceReplay.native_constructor_aliasTail_trace {V : Type u} [SetTheory V]
    {prefixFuel : Nat} {ev : Evidences .anon} {sourceOut env stage scope : Env .anon}
    {declarations : List (Declaration .anon)}
    (replay : ReferenceReplay prefixFuel ev Env.empty Env.empty declarations sourceOut env)
    {parts completed : InductiveShape .anon} {isRec : Bool} {former ctorFormer : ConstantVal .anon}
    (formerRun : SumIndRunJ rulesJ env parts (fun current => nativeCapsAt current isRec) stage former completed)
    {name : Key .anon} {levels : List LevelParam} {nP nI : Nat} {sortLevel : Level}
    {isProp large : Bool} {annotated : List (ConstantVal .anon × Nat)} {sortss : List (List Level)}
    (constructorRuns : SumCtorsRunJ rulesJ scope stage name levels nP nI sortLevel isProp large
      ctorFormer completed.ctors annotated sortss)
    {aliasName targetName : Key .anon} {targetLevels : List Level}
    {aliasCV targetCV : ConstantVal .anon} {hint : ReducibilityHint} {caps : IndCaps .anon}
    {declared actual : Level}
    (aliasFound : stage.find? aliasName = some (.defnInfo aliasCV (.const targetName targetLevels) hint))
    (noLevels : aliasCV.levelParams = [])
    (targetFound : stage.find? targetName = some (.indInfo targetCV caps))
    (aliasHeader : aliasCV.type = .sort declared)
    (targetHeader : targetCV.type.instantiateLevelParams targetCV.levelParams targetLevels = .sort actual)
    {before : Env .anon} {T : Key .anon} {ctorLevels : List LevelParam}
    {params indices fields fuel : Nat} {ctorSort : Level} {ctorIsProp ctorLarge : Bool}
    {raw checkedFormer checked : ConstantVal .anon} {fieldSorts : List Level}
    (run : checkSumCtor (fueledOps .verified fuel) before stage T ctorLevels params indices ctorSort
      ctorIsProp ctorLarge raw fields checkedFormer = .ok (checked, fieldSorts)) :
    ∃ initial rebuilt originalVars originalResidual finalVars finalResidual,
      checkConstantVal (fueledOps .verified fuel) stage raw = .ok initial ∧
      normCtorVal (fueledOps .verified fuel) stage T params fields raw initial = .ok checked ∧
      ConstructorRebuildRun stage fuel T params fields initial.type rebuilt ∧
      (checked = initial ∨
        checkConstantVal (fueledOps .verified fuel) stage { raw with type := rebuilt } = .ok checked) ∧
      openPisAtFvars (params + fields) initial.type 0 = some (originalVars, originalResidual) ∧
      openPisAtFvars (params + fields) checked.type 0 = some (finalVars, finalResidual) ∧
      originalVars.length = params + fields ∧ finalVars.length = params + fields ∧
      ∀ slot original final count, originalVars[params + slot]? = some original →
        finalVars[params + slot]? = some final → AliasTail aliasName targetName targetLevels count original.fvarTypeD →
        ∃ originalType originalSort finalType finalSort,
          inferTypeCore .verified stage fuel (params + slot) original.fvarTypeD = .ok originalType ∧
          ensureSortCore .verified stage fuel (params + slot) originalType = .ok originalSort ∧
          inferTypeCore .verified stage fuel (params + slot) final.fvarTypeD = .ok finalType ∧
          ensureSortCore .verified stage fuel (params + slot) finalType = .ok finalSort ∧
          Level.zeronessOf originalSort = Level.zeronessOf actual ∧
          Level.zeronessOf finalSort = Level.zeronessOf actual ∧
          Level.zeronessOf originalSort = Level.zeronessOf finalSort ∧
          (∀ leftDomain leftBody leftMeta rightDomain rightBody rightMeta,
            original.fvarTypeD = .forallE leftDomain leftBody leftMeta →
            final.fvarTypeD = .forallE rightDomain rightBody rightMeta → leftMeta.pw = rightMeta.pw) := by
  obtain ⟨model⟩ := replay.native_constructorStage_model (V := V) formerRun constructorRuns
  have definitions := replay.definitionsTyped_from_empty.sumIndRunJ formerRun
  obtain ⟨initial, rebuilt, originalVars, originalResidual, finalVars, finalResidual,
    first, normalization, rebuild, lastBranch, originalOpen, finalOpen,
    originalCount, finalCount, _⟩ := checkSumCtor_rebuild_domain_checks model.base2.wf run
  refine ⟨initial, rebuilt, originalVars, originalResidual, finalVars, finalResidual,
    first, normalization, rebuild, lastBranch, originalOpen, finalOpen, originalCount, finalCount, ?_⟩
  intro slot original final count originalAt finalAt shape
  exact normCtorVal_aliasTail_checked_sorts model definitions aliasFound noLevels targetFound
    aliasHeader targetHeader first normalization originalOpen finalOpen originalAt finalAt shape

end IxVM.Refinement.Decl
