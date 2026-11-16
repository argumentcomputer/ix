import IxVMRefinement.Decl.ConstantOrigins
import IxVMRefinement.Decl.AliasInstantiation
import IxVMRefinement.Decl.NativeStageModel

/-! # A constructed constant family for a polymorphic alias instance

The only atoms are the chosen alias use and its actual universe-substituted inductive target.
The accepted prefix derives their common zero-ness, including the scope and arity needed by
substitution composition. The resulting family uses the common evaluator/rebuild protocol.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model Ix.Kernel.Semantics

universe u

/-- The two actual constant instances selected by one alias unfolding. -/
def aliasInstanceAtoms (aliasName : Key .anon) (useLevels : List Level)
    (targetName : Key .anon) (targetLevels : List Level) (name : Key .anon) (levels : List Level) : Prop :=
  (name = aliasName ∧ levels = useLevels) ∨ (name = targetName ∧ levels = targetLevels)

/-- Actual prefix checks construct every row and delta-closure obligation of the family. -/
theorem DefinitionsTyped.polymorphic_alias_family {V : Type u} [SetTheory V] {env : Env .anon}
    (model : EnvModelM V .verified env) (definitions : DefinitionsTyped env)
    {aliasName targetName : Key .anon} {aliasCV targetCV : ConstantVal .anon}
    {bodyLevels : List Level} {hint : ReducibilityHint} {caps : IndCaps .anon}
    {declared targetSort : Level}
    (aliasFound : env.find? aliasName = some (.defnInfo aliasCV (.const targetName bodyLevels) hint))
    (targetFound : env.find? targetName = some (.indInfo targetCV caps))
    (aliasHeader : aliasCV.type = .sort declared)
    (targetHeader : targetCV.type = .sort targetSort) (useLevels : List Level) :
    ConstantFamily env
      (aliasInstanceAtoms aliasName useLevels targetName
        (bodyLevels.map (Level.subst aliasCV.levelParams useLevels)))
      (Level.zeronessOf (Level.subst targetCV.levelParams
        (bodyLevels.map (Level.subst aliasCV.levelParams useLevels)) targetSort)) where
  row := by
    intro name levels member
    rcases member with ⟨nameEq, levelsEq⟩ | ⟨nameEq, levelsEq⟩
    · subst name levels
      refine ⟨.defnInfo aliasCV (.const targetName bodyLevels) hint,
        Level.subst aliasCV.levelParams useLevels declared, aliasFound, ?_, ?_⟩
      · change aliasCV.type.instantiateLevelParams aliasCV.levelParams useLevels = _
        rw [aliasHeader]
        rfl
      · exact definitions.polymorphic_alias_zero model aliasFound targetFound aliasHeader targetHeader useLevels
    · subst name levels
      refine ⟨.indInfo targetCV caps, _, targetFound, ?_, rfl⟩
      change targetCV.type.instantiateLevelParams targetCV.levelParams _ = _
      rw [targetHeader]
      rfl
  delta := by
    intro name levels out member unfolded
    rcases member with ⟨nameEq, levelsEq⟩ | ⟨nameEq, levelsEq⟩
    · subst name levels
      rw [constant_alias_unfoldAt aliasFound] at unfolded
      split at unfolded
      · obtain rfl := Option.some.inj unfolded
        exact ⟨targetName, _, rfl, .inr ⟨rfl, rfl⟩⟩
      · cases unfolded
    · subst name levels
      simp only [unfoldDefinition, Expr.getAppFn, targetFound] at unfolded
      cases unfolded

/-- The actual reference prefix and native stage produce the polymorphic origin invariant
and environment well-formedness required by the shared constructor-trace theorem. -/
theorem ReferenceReplay.native_polymorphic_alias_invariant {V : Type u} [SetTheory V]
    {prefixFuel : Nat} {ev : Evidences .anon} {sourceOut env stage scope : Env .anon}
    {declarations : List (Declaration .anon)}
    (replay : ReferenceReplay prefixFuel ev Env.empty Env.empty declarations sourceOut env)
    {parts completed : InductiveShape .anon} {isRec : Bool} {former ctorFormer : ConstantVal .anon}
    (formerRun : SumIndRunJ rulesJ env parts (fun current => nativeCapsAt current isRec) stage former completed)
    {name : Key .anon} {levels : List LevelParam} {nP nI : Nat} {sortLevel : Level}
    {isProp large : Bool} {annotated : List (ConstantVal .anon × Nat)} {sortss : List (List Level)}
    (constructorRuns : SumCtorsRunJ rulesJ scope stage name levels nP nI sortLevel isProp large
      ctorFormer completed.ctors annotated sortss)
    {aliasName targetName : Key .anon} {aliasCV targetCV : ConstantVal .anon}
    {bodyLevels : List Level} {hint : ReducibilityHint} {caps : IndCaps .anon}
    {declared targetSort : Level}
    (aliasFound : stage.find? aliasName = some (.defnInfo aliasCV (.const targetName bodyLevels) hint))
    (targetFound : stage.find? targetName = some (.indInfo targetCV caps))
    (aliasHeader : aliasCV.type = .sort declared)
    (targetHeader : targetCV.type = .sort targetSort) (useLevels : List Level) :
    EnvWF stage ∧ SyntacticDomainInvariant stage
      (fun e => ∃ count, ConstantTail
        (aliasInstanceAtoms aliasName useLevels targetName
          (bodyLevels.map (Level.subst aliasCV.levelParams useLevels))) count e)
      (Level.zeronessOf (Level.subst targetCV.levelParams
        (bodyLevels.map (Level.subst aliasCV.levelParams useLevels)) targetSort)) := by
  obtain ⟨model⟩ := replay.native_constructorStage_model (V := V) formerRun constructorRuns
  have definitions := replay.definitionsTyped_from_empty.sumIndRunJ formerRun
  exact ⟨model.base2.wf,
    (definitions.polymorphic_alias_family model aliasFound targetFound aliasHeader targetHeader useLevels).invariant⟩

/-- The polymorphic alias instance is constructed from the accepted prefix and consumed by
the same exact constructor-trace theorem as the earlier literal and monomorphic cases. -/
theorem ReferenceReplay.native_constructor_polymorphic_alias_trace {V : Type u} [SetTheory V]
    {prefixFuel : Nat} {ev : Evidences .anon} {sourceOut env stage scope : Env .anon}
    {declarations : List (Declaration .anon)}
    (replay : ReferenceReplay prefixFuel ev Env.empty Env.empty declarations sourceOut env)
    {parts completed : InductiveShape .anon} {isRec : Bool} {former ctorFormer : ConstantVal .anon}
    (formerRun : SumIndRunJ rulesJ env parts (fun current => nativeCapsAt current isRec) stage former completed)
    {name : Key .anon} {levels : List LevelParam} {nP nI : Nat} {sortLevel : Level}
    {isProp large : Bool} {annotated : List (ConstantVal .anon × Nat)} {sortss : List (List Level)}
    (constructorRuns : SumCtorsRunJ rulesJ scope stage name levels nP nI sortLevel isProp large
      ctorFormer completed.ctors annotated sortss)
    {aliasName targetName : Key .anon} {aliasCV targetCV : ConstantVal .anon}
    {bodyLevels : List Level} {hint : ReducibilityHint} {caps : IndCaps .anon}
    {declared targetSort : Level}
    (aliasFound : stage.find? aliasName = some (.defnInfo aliasCV (.const targetName bodyLevels) hint))
    (targetFound : stage.find? targetName = some (.indInfo targetCV caps))
    (aliasHeader : aliasCV.type = .sort declared)
    (targetHeader : targetCV.type = .sort targetSort) (useLevels : List Level)
    {before : Env .anon} {T : Key .anon} {ctorLevels : List LevelParam}
    {params indices fields fuel : Nat} {ctorSort : Level} {ctorIsProp ctorLarge : Bool}
    {raw checkedFormer checked : ConstantVal .anon} {fieldSorts : List Level}
    (run : checkSumCtor (fueledOps .verified fuel) before stage T ctorLevels params indices ctorSort
      ctorIsProp ctorLarge raw fields checkedFormer = .ok (checked, fieldSorts)) :
    ConstructorCoherenceTrace stage fuel T params fields raw checked
      (fun e => ∃ count, ConstantTail
        (aliasInstanceAtoms aliasName useLevels targetName
          (bodyLevels.map (Level.subst aliasCV.levelParams useLevels))) count e)
      (Level.zeronessOf (Level.subst targetCV.levelParams
        (bodyLevels.map (Level.subst aliasCV.levelParams useLevels)) targetSort)) := by
  obtain ⟨wellFormed, invariant⟩ := replay.native_polymorphic_alias_invariant (V := V)
    formerRun constructorRuns aliasFound targetFound aliasHeader targetHeader useLevels
  exact invariant.trace wellFormed run

end IxVM.Refinement.Decl
