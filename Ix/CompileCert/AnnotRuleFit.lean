import Ix.CompileCert.AnnotInstances

namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics

/-- Transfer the actual recursor and constructor telescope premises with the
same annotations and residuals. The constructor leaf is transported through
its own installed lookup and telescope, not through the recursor's telescope. -/
theorem InstalledRuleFrame.annotated_teleFit {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (association : AnnotatedAssociation source target names)
    (sourceFacts : EnvModel V source) (targetModel : StrongInstalledModel V target)
    {name : Kernel.Name} {index : Nat} (sourceFrame : InstalledRuleFrame source name index)
    (targetFrame : InstalledRuleFrame target (names name) index)
    (sourceLevels targetLevels : Kernel.Name → Nat)
    (sourceUs targetUs sourceCtorUs targetCtorUs : List Kernel.Level)
    (selection : RuleUniverseSelection sourceFrame sourceLevels sourceUs sourceCtorUs)
    (universes : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels))
    (constructorUniverses : sourceCtorUs.map (Kernel.Level.eval sourceLevels) =
      targetCtorUs.map (Kernel.Level.eval targetLevels))
    (ρ : Nat → V) (xs ys : List AnnotTerm) (typeRec typeCtor restRec restCtor : AnnotTerm)
    (recRead : denoteMeta (association.modelCore sourceFacts targetModel).base.acval source sourceLevels 0
      (sourceFrame.header.type.instantiateLevelParams sourceFrame.header.levelParams sourceUs) = some typeRec)
    (ctorRead : denoteMeta (association.modelCore sourceFacts targetModel).base.acval source sourceLevels 0
      (sourceFrame.constructor.type.instantiateLevelParams sourceFrame.constructor.levelParams sourceCtorUs) = some typeCtor)
    (recFit : TeleFitPA V ρ typeRec
      (xs ++ [AnnotTerm.mkAppN ((association.modelCore sourceFacts targetModel).base.acval sourceFrame.rule.ctor
        (Kernel.Level.substFn sourceLevels sourceFrame.constructor.levelParams sourceCtorUs)) ys]) restRec)
    (ctorFit : TeleFitPA V ρ typeCtor ys restCtor) :
    RuleUniverseSelection targetFrame targetLevels targetUs targetCtorUs ∧
    denoteMeta targetModel.internal.base2.acval target targetLevels 0
      (targetFrame.header.type.instantiateLevelParams targetFrame.header.levelParams targetUs) = some typeRec ∧
    denoteMeta targetModel.internal.base2.acval target targetLevels 0
      (targetFrame.constructor.type.instantiateLevelParams targetFrame.constructor.levelParams targetCtorUs) = some typeCtor ∧
    TeleFitPA V ρ typeRec
      (xs ++ [AnnotTerm.mkAppN (targetModel.internal.base2.acval targetFrame.rule.ctor
        (Kernel.Level.substFn targetLevels targetFrame.constructor.levelParams targetCtorUs)) ys]) restRec ∧
    TeleFitPA V ρ typeCtor ys restCtor := by
  have telescopes := checkTelescopes_sound association.installed.telescopes
  have targetSelection := sourceFrame.transfer_selection targetModel telescopes association.installed.recursors
    targetFrame (checkInstalledRuleLevelLinks_frame association.installed.levelLinks sourceFrame)
    selection universes constructorUniverses
  have headers := ((sourceFrame.checked_images targetModel telescopes association.installed.recursors
    targetFrame).2.2 (fun _ => 0)).header
  have targetCtorLookup : target.find? (names sourceFrame.rule.ctor) =
      some (.ctorInfo targetFrame.constructor targetFrame.constructorParams targetFrame.constructorFields) := by
    rw [headers.1]
    exact targetFrame.constructorLookup
  have recImage := association.type_instance_reading sourceFacts targetModel sourceFrame.recursorLookup
    targetFrame.recursorLookup sourceLevels targetLevels sourceUs targetUs selection.recursorArity
    targetSelection.recursorArity universes
  have ctorImage := association.type_instance_reading sourceFacts targetModel sourceFrame.constructorLookup
    targetCtorLookup sourceLevels targetLevels sourceCtorUs targetCtorUs selection.constructorArity
    targetSelection.constructorArity constructorUniverses
  have leaf := PullbackMap.fromEnvs_annotation_instance targetModel telescopes sourceFrame.constructorLookup
    targetCtorLookup sourceLevels targetLevels sourceCtorUs targetCtorUs selection.constructorArity
    targetSelection.constructorArity constructorUniverses
  change (association.modelCore sourceFacts targetModel).base.acval sourceFrame.rule.ctor
    (Kernel.Level.substFn sourceLevels sourceFrame.constructor.levelParams sourceCtorUs) =
      targetModel.internal.base2.acval (names sourceFrame.rule.ctor)
        (Kernel.Level.substFn targetLevels targetFrame.constructor.levelParams targetCtorUs) at leaf
  rw [headers.1] at leaf
  refine ⟨targetSelection, recImage.symm.trans recRead, ctorImage.symm.trans ctorRead, ?_, ctorFit⟩
  rw [← leaf]
  exact recFit

end Ix.CompileCert
