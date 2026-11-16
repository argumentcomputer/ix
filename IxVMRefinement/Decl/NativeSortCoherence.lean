import IxVMRefinement.Decl.DomainInstances
import IxVMRefinement.Decl.NativeSortDomain
import IxVMRefinement.Decl.NativeStageModel

/-! # Exact domain-sort agreement for computed sort-returning fields

Both recorded constructor checks infer the same successor sort for this fragment, including
beta redexes that erase an earlier recursive-field occurrence. The proof follows the actual
normalization and annotation trace and remains valid in contexts with no inhabitants.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model Ix.Kernel.Semantics

universe u

/-- The original and final checks return the same literal sort on a selected field in the
fragment. All four checking equations come from the actual first and final constant checks. -/
theorem normCtorVal_sortFunction_checked_sorts {env : Env .anon} {fuel nP nF slot : Nat} {T : Key .anon}
    {raw initial checked : ConstantVal .anon} {originalVars finalVars : List (Expr .anon)}
    {originalResidual finalResidual original final : Expr .anon} {sortLevel : Level}
    (first : checkConstantVal (fueledOps .verified fuel) env raw = .ok initial)
    (normalized : normCtorVal (fueledOps .verified fuel) env T nP nF raw initial = .ok checked)
    (originalOpen : openPisAtFvars (nP + nF) initial.type 0 = some (originalVars, originalResidual))
    (finalOpen : openPisAtFvars (nP + nF) checked.type 0 = some (finalVars, finalResidual))
    (originalAt : originalVars[nP + slot]? = some original)
    (finalAt : finalVars[nP + slot]? = some final)
    (shape : SortFunction sortLevel 0 original.fvarTypeD) :
    inferTypeCore .verified env fuel (nP + slot) original.fvarTypeD = .ok (.sort (.succ sortLevel)) ∧
    ensureSortCore .verified env fuel (nP + slot) (.sort (.succ sortLevel)) = .ok (.succ sortLevel) ∧
    inferTypeCore .verified env fuel (nP + slot) final.fvarTypeD = .ok (.sort (.succ sortLevel)) ∧
    ensureSortCore .verified env fuel (nP + slot) (.sort (.succ sortLevel)) = .ok (.succ sortLevel) := by
  have finalShape := normCtorVal_sortFunction_domain normalized originalOpen finalOpen originalAt finalAt shape
  obtain ⟨rawFinal, lastCheck⟩ : ∃ rawFinal,
      checkConstantVal (fueledOps .verified fuel) env rawFinal = .ok checked := by
    obtain ⟨rebuilt, _, same | lastCheck⟩ := normCtorVal_rebuild_trace normalized
    · exact ⟨raw, by rw [same]; exact first⟩
    · exact ⟨{ raw with type := rebuilt }, lastCheck⟩
  obtain ⟨originalType, originalSort, originalInfer, originalSorted⟩ :=
    checked_type_domain_checks first originalOpen (nP + slot) original originalAt
  obtain ⟨finalType, finalSort, finalInfer, finalSorted⟩ :=
    checked_type_domain_checks lastCheck finalOpen (nP + slot) final finalAt
  have originalTyped := Rules.inferTypeCore_bridge originalInfer
  have finalTyped := Rules.inferTypeCore_bridge finalInfer
  have originalTypeEq := shape.inferred_zero originalTyped
  have finalTypeEq := finalShape.inferred_zero finalTyped
  have originalSortEq := shape.checked_sort originalTyped (Rules.whnf_bridge (ensureSortCore_inv originalSorted))
  have finalSortEq := finalShape.checked_sort finalTyped (Rules.whnf_bridge (ensureSortCore_inv finalSorted))
  exact ⟨by simpa only [originalTypeEq] using originalInfer,
    by simpa only [originalTypeEq, originalSortEq] using originalSorted,
    by simpa only [finalTypeEq] using finalInfer,
    by simpa only [finalTypeEq, finalSortEq] using finalSorted⟩

/-- The accepted prefix and native stages construct one exact rebuild trace. Within it every
field in the fragment has identical original/final result sorts, with no caller sort check. -/
theorem ReferenceReplay.native_constructor_sortFunction_trace {V : Type u} [SetTheory V]
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
      ∀ slot original final level, originalVars[params + slot]? = some original →
        finalVars[params + slot]? = some final → SortFunction level 0 original.fvarTypeD →
        inferTypeCore .verified stage fuel (params + slot) original.fvarTypeD = .ok (.sort (.succ level)) ∧
        ensureSortCore .verified stage fuel (params + slot) (.sort (.succ level)) = .ok (.succ level) ∧
        inferTypeCore .verified stage fuel (params + slot) final.fvarTypeD = .ok (.sort (.succ level)) ∧
        ensureSortCore .verified stage fuel (params + slot) (.sort (.succ level)) = .ok (.succ level) := by
  obtain ⟨model⟩ := replay.native_constructorStage_model (V := V) formerRun constructorRuns
  obtain ⟨initial, rebuilt, originalVars, originalResidual, finalVars, finalResidual,
    first, normalization, rebuild, lastBranch, originalOpen, finalOpen,
    originalCount, finalCount, _⟩ := checkSumCtor_rebuild_domain_checks model.base2.wf run
  refine ⟨initial, rebuilt, originalVars, originalResidual, finalVars, finalResidual,
    first, normalization, rebuild, lastBranch, originalOpen, finalOpen, originalCount, finalCount, ?_⟩
  intro slot original final level originalAt finalAt shape
  exact normCtorVal_sortFunction_checked_sorts first normalization originalOpen finalOpen originalAt finalAt shape

/-- Product telescopes ending in a computed sort have the same original/final zero-ness.
Their domains may affect the numerical universe, so only the derived zero-ness is equated. -/
theorem normCtorVal_sortTail_checked_sorts {env : Env .anon} {fuel nP nF slot count : Nat} {T : Key .anon}
    {raw initial checked : ConstantVal .anon} {originalVars finalVars : List (Expr .anon)}
    {originalResidual finalResidual original final : Expr .anon} {sortLevel : Level}
    (first : checkConstantVal (fueledOps .verified fuel) env raw = .ok initial)
    (normalized : normCtorVal (fueledOps .verified fuel) env T nP nF raw initial = .ok checked)
    (originalOpen : openPisAtFvars (nP + nF) initial.type 0 = some (originalVars, originalResidual))
    (finalOpen : openPisAtFvars (nP + nF) checked.type 0 = some (finalVars, finalResidual))
    (originalAt : originalVars[nP + slot]? = some original)
    (finalAt : finalVars[nP + slot]? = some final)
    (shape : SortTail sortLevel count original.fvarTypeD) :
    ∃ originalType originalSort finalType finalSort,
      inferTypeCore .verified env fuel (nP + slot) original.fvarTypeD = .ok originalType ∧
      ensureSortCore .verified env fuel (nP + slot) originalType = .ok originalSort ∧
      inferTypeCore .verified env fuel (nP + slot) final.fvarTypeD = .ok finalType ∧
      ensureSortCore .verified env fuel (nP + slot) finalType = .ok finalSort ∧
      Level.zeronessOf originalSort = .never ∧ Level.zeronessOf finalSort = .never ∧
      Level.zeronessOf originalSort = Level.zeronessOf finalSort := by
  obtain ⟨originalType, originalSort, finalType, finalSort, originalInfer, originalSorted,
    finalInfer, finalSorted, originalZero, finalZero, equal, _⟩ :=
    (SortTail.invariant env sortLevel).checked_sorts first normalized originalOpen finalOpen originalAt finalAt ⟨count, shape⟩
  exact ⟨originalType, originalSort, finalType, finalSort, originalInfer, originalSorted,
    finalInfer, finalSorted, originalZero, finalZero, equal⟩

/-- The product-telescope generalization uses the same actual paired checks and rebuilt witness. -/
theorem ReferenceReplay.native_constructor_sortTail_trace {V : Type u} [SetTheory V]
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
      ∀ slot original final level count, originalVars[params + slot]? = some original →
        finalVars[params + slot]? = some final → SortTail level count original.fvarTypeD →
        ∃ originalType originalSort finalType finalSort,
          inferTypeCore .verified stage fuel (params + slot) original.fvarTypeD = .ok originalType ∧
          ensureSortCore .verified stage fuel (params + slot) originalType = .ok originalSort ∧
          inferTypeCore .verified stage fuel (params + slot) final.fvarTypeD = .ok finalType ∧
          ensureSortCore .verified stage fuel (params + slot) finalType = .ok finalSort ∧
          Level.zeronessOf originalSort = .never ∧ Level.zeronessOf finalSort = .never ∧
          Level.zeronessOf originalSort = Level.zeronessOf finalSort := by
  obtain ⟨model⟩ := replay.native_constructorStage_model (V := V) formerRun constructorRuns
  obtain ⟨initial, rebuilt, originalVars, originalResidual, finalVars, finalResidual,
    first, normalization, rebuild, lastBranch, originalOpen, finalOpen,
    originalCount, finalCount, _⟩ := checkSumCtor_rebuild_domain_checks model.base2.wf run
  refine ⟨initial, rebuilt, originalVars, originalResidual, finalVars, finalResidual,
    first, normalization, rebuild, lastBranch, originalOpen, finalOpen, originalCount, finalCount, ?_⟩
  intro slot original final level count originalAt finalAt shape
  exact normCtorVal_sortTail_checked_sorts first normalization originalOpen finalOpen originalAt finalAt shape

end IxVM.Refinement.Decl
