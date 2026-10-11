import Ix.CompileCert.AnnotRules

namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics

/-- Concrete instances share the actual annotated reading when their universe
arguments evaluate equally. Locality is required only on the installed target
telescope; ambient valuations need not agree. -/
theorem AnnotatedAssociation.member_instance_reading {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (association : AnnotatedAssociation source target names)
    (sourceFacts : EnvModel V source) (targetModel : StrongInstalledModel V target)
    {name : Kernel.Name} {sourceEntry targetEntry : Kernel.ConstantInfo}
    (sourceLookup : source.find? name = some sourceEntry)
    (targetLookup : target.find? (names name) = some targetEntry)
    {sourceExpr targetExpr : Kernel.Expr}
    (bounded : targetExpr.allLevelParamsDefined targetEntry.toConstantVal.levelParams = true)
    (support : checkExprLiteralSupport source target sourceExpr = true)
    (compared : checkInstalledMemberExpr source target names name sourceExpr targetExpr = some true)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceEntry.toConstantVal.levelParams.length)
    (targetArity : targetUs.length = targetEntry.toConstantVal.levelParams.length)
    (arguments : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels))
    (depth : Nat) :
    denoteMeta (association.modelCore sourceFacts targetModel).base.acval source sourceLevels depth
      (sourceExpr.instantiateLevelParams sourceEntry.toConstantVal.levelParams sourceUs) =
    denoteMeta targetModel.internal.base2.acval target targetLevels depth
      (targetExpr.instantiateLevelParams targetEntry.toConstantVal.levelParams targetUs) := by
  rw [denotePInstLevels, denotePInstLevels]
  have telescopes := checkTelescopes_sound association.installed.telescopes
  refine (checkInstalledMemberExpr_annotated_reading_local targetModel telescopes sourceLookup
    support compared _ depth).trans ?_
  exact denoteMeta_params_at targetModel.internal.base2.acval_params
    (PullbackMap.fromEnvs_instance telescopes sourceLookup targetLookup sourceLevels targetLevels
      sourceUs targetUs sourceArity targetArity arguments) depth targetExpr bounded

/-- The same concrete-instance comparison preserves the reverse opening used
by nested recursor pins, including its binder annotation bits. -/
theorem AnnotatedAssociation.opened_member_instance_reading {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (association : AnnotatedAssociation source target names)
    (sourceFacts : EnvModel V source) (targetModel : StrongInstalledModel V target)
    {name : Kernel.Name} {sourceEntry targetEntry : Kernel.ConstantInfo}
    (sourceLookup : source.find? name = some sourceEntry)
    (targetLookup : target.find? (names name) = some targetEntry)
    {sourceExpr targetExpr : Kernel.Expr}
    (bounded : targetExpr.allLevelParamsDefined targetEntry.toConstantVal.levelParams = true)
    (support : checkExprLiteralSupport source target sourceExpr = true)
    (compared : checkInstalledMemberExpr source target names name sourceExpr targetExpr = some true)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceEntry.toConstantVal.levelParams.length)
    (targetArity : targetUs.length = targetEntry.toConstantVal.levelParams.length)
    (arguments : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels))
    (count depth : Nat) :
    denoteMeta (association.modelCore sourceFacts targetModel).base.acval source sourceLevels depth
      (Kernel.Verify.openRev 0 count
        (sourceExpr.instantiateLevelParams sourceEntry.toConstantVal.levelParams sourceUs)) =
    denoteMeta targetModel.internal.base2.acval target targetLevels depth
      (Kernel.Verify.openRev 0 count
        (targetExpr.instantiateLevelParams targetEntry.toConstantVal.levelParams targetUs)) := by
  rw [Kernel.Verify.openRev_instantiateLevelParams, Kernel.Verify.openRev_instantiateLevelParams,
    denotePInstLevels, denotePInstLevels]
  have telescopes := checkTelescopes_sound association.installed.telescopes
  refine (checkInstalledMemberExpr_opened_annotations targetModel telescopes sourceLookup
    support compared _ count depth).trans ?_
  exact denoteMeta_params_at targetModel.internal.base2.acval_params
    (PullbackMap.fromEnvs_instance telescopes sourceLookup targetLookup sourceLevels targetLevels
      sourceUs targetUs sourceArity targetArity arguments) depth _
    (openRev_allLevelParamsDefined bounded 0 count)

/-- All premises beyond the paired concrete universe arguments are discharged
by the checked installed type rows and the independent target installation. -/
theorem AnnotatedAssociation.type_instance_reading {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (association : AnnotatedAssociation source target names)
    (sourceFacts : EnvModel V source) (targetModel : StrongInstalledModel V target)
    {name : Kernel.Name} {sourceEntry targetEntry : Kernel.ConstantInfo}
    (sourceLookup : source.find? name = some sourceEntry)
    (targetLookup : target.find? (names name) = some targetEntry)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceEntry.toConstantVal.levelParams.length)
    (targetArity : targetUs.length = targetEntry.toConstantVal.levelParams.length)
    (arguments : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels)) :
    denoteMeta (association.modelCore sourceFacts targetModel).base.acval source sourceLevels 0
      (sourceEntry.toConstantVal.type.instantiateLevelParams sourceEntry.toConstantVal.levelParams sourceUs) =
    denoteMeta targetModel.internal.base2.acval target targetLevels 0
      (targetEntry.toConstantVal.type.instantiateLevelParams targetEntry.toConstantVal.levelParams targetUs) := by
  have member := Kernel.Semantics.Env.find?_mem sourceLookup
  have sourceName := Kernel.Semantics.Env.find?_name sourceLookup
  obtain ⟨_, actualTarget, actualLookup, compared⟩ :=
    checkInstalledTypes_member association.installed.types member
  rw [sourceName, targetLookup] at actualLookup
  cases Option.some.inj actualLookup
  rw [sourceName] at compared
  exact association.member_instance_reading sourceFacts targetModel sourceLookup targetLookup
    (targetModel.internal.base2.wf _ (Kernel.Semantics.Env.find?_mem targetLookup)).2.1
    (List.all_eq_true.mp association.types sourceEntry member) compared
    sourceLevels targetLevels sourceUs targetUs sourceArity targetArity arguments 0

/-- The actual type reading and its telescope use identical annotations on
both sides. This applies to both recursor and constructor rows, with no
replacement of the annotated fitting judgment by erased value equality. -/
theorem AnnotatedAssociation.type_instance_teleFit {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (association : AnnotatedAssociation source target names)
    (sourceFacts : EnvModel V source) (targetModel : StrongInstalledModel V target)
    {name : Kernel.Name} {sourceEntry targetEntry : Kernel.ConstantInfo}
    (sourceLookup : source.find? name = some sourceEntry)
    (targetLookup : target.find? (names name) = some targetEntry)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceEntry.toConstantVal.levelParams.length)
    (targetArity : targetUs.length = targetEntry.toConstantVal.levelParams.length)
    (arguments : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels))
    (ρ : Nat → V) (annotation residual : AnnotTerm) (spine : List AnnotTerm) :
    (denoteMeta (association.modelCore sourceFacts targetModel).base.acval source sourceLevels 0
      (sourceEntry.toConstantVal.type.instantiateLevelParams sourceEntry.toConstantVal.levelParams sourceUs) =
        some annotation ∧ TeleFitPA V ρ annotation spine residual) ↔
    (denoteMeta targetModel.internal.base2.acval target targetLevels 0
      (targetEntry.toConstantVal.type.instantiateLevelParams targetEntry.toConstantVal.levelParams targetUs) =
        some annotation ∧ TeleFitPA V ρ annotation spine residual) := by
  rw [association.type_instance_reading sourceFacts targetModel sourceLookup targetLookup
    sourceLevels targetLevels sourceUs targetUs sourceArity targetArity arguments]

end Ix.CompileCert
