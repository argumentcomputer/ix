import Ix.CompileCert.AnnotTowerLevels
import Ix.CompileCert.AnnotTowers
import Ix.CompileCert.AnnotInstances
import Ix.CompileCert.AnnotNested

namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics

theorem projTele_allLevelParamsDefined {params : List Kernel.Name} {body : Kernel.Expr}
    (bounded : body.allLevelParamsDefined params = true) (count : Nat) :
    (Kernel.projTele count body).allLevelParamsDefined params = true := by
  induction count with
  | zero => exact bounded
  | succ count ih => simpa [Kernel.projTele, Kernel.Expr.allLevelParamsDefined, Kernel.Level.allParamsDefined] using ih

/-- All three semantic clauses of the stored projection table transfer on
the exact pulled annotation carrier. Original source shape and O5 facts
come from its independent installation; semantic laws come from the actual
associated target entry and complete body/level comparisons. -/
theorem InstalledTowerEntryComparison.tower_law {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (association : AnnotatedAssociation source target names)
    (sourceModel : StrongInstalledModel V source) (targetModel : StrongInstalledModel V target)
    {owner : Kernel.Name} {index : Nat} {sourceEntry targetEntry : Kernel.ProjEntry}
    (comparison : InstalledTowerEntryComparison source target names owner index sourceEntry targetEntry)
    (levels : Kernel.Name → Nat) :
    TowerEntryLaw (association.modelCore sourceModel.internal.base2 targetModel).base levels owner index sourceEntry := by
  have sourceLaw := sourceModel.internal.tower_ok levels owner index sourceEntry comparison.sourceLookup
  have targetLaw := targetModel.internal.tower_ok levels (names owner) index targetEntry comparison.targetLookup
  obtain ⟨sourceName, sourceIndex, sourceBound, ⟨sourceHeader, sourceCaps, sourceLookup, sourceParams, sourceEta⟩,
    sourceO5, sourceCtor, sourceCtorLookup, sourceCtorParams, sourceValues, _⟩ := sourceLaw
  obtain ⟨_, _, _, ⟨targetHeader, targetCaps, targetLookup, targetParams, _⟩,
    _, targetCtor, targetCtorLookup, targetCtorParams, targetValues, targetEta⟩ := targetLaw
  have mappedCtor : target.find? (names sourceEntry.ctor) =
      some (.ctorInfo targetCtor targetEntry.numParams targetEntry.numFields) := by
    rw [comparison.constructor]; exact targetCtorLookup
  have telescopes := checkTelescopes_sound association.installed.telescopes
  have arities : sourceEntry.levelParams.length = targetEntry.levelParams.length := by
    obtain ⟨actual, actualLookup, _, _, same⟩ := telescopes owner _ sourceLookup
    rw [targetLookup] at actualLookup
    cases Option.some.inj actualLookup
    simpa only [Kernel.ConstantInfo.toConstantVal, sourceParams, targetParams] using same
  have ownerLeaf : ∀ us, us.length = sourceEntry.levelParams.length →
      (association.modelCore sourceModel.internal.base2 targetModel).base.acval owner
        (Kernel.Level.substFn levels sourceEntry.levelParams us) =
      targetModel.internal.base2.acval (names owner) (Kernel.Level.substFn levels targetEntry.levelParams us) := by
    intro us arity
    have leaf := PullbackMap.fromEnvs_annotation_instance targetModel telescopes sourceLookup targetLookup
      levels levels us us (by simpa only [Kernel.ConstantInfo.toConstantVal, sourceParams] using arity)
      (by simpa only [Kernel.ConstantInfo.toConstantVal, targetParams, ← arities] using arity) rfl
    change (association.modelCore sourceModel.internal.base2 targetModel).base.acval owner
      (Kernel.Level.substFn levels sourceHeader.levelParams us) =
      targetModel.internal.base2.acval (names owner) (Kernel.Level.substFn levels targetHeader.levelParams us) at leaf
    simpa only [sourceParams, targetParams] using leaf
  have ctorLeaf : ∀ us, us.length = sourceEntry.levelParams.length →
      (association.modelCore sourceModel.internal.base2 targetModel).base.acval sourceEntry.ctor
        (Kernel.Level.substFn levels sourceEntry.levelParams us) =
      targetModel.internal.base2.acval targetEntry.ctor (Kernel.Level.substFn levels targetEntry.levelParams us) := by
    intro us arity
    have leaf := PullbackMap.fromEnvs_annotation_instance targetModel telescopes sourceCtorLookup mappedCtor
      levels levels us us (by simpa only [Kernel.ConstantInfo.toConstantVal, sourceCtorParams] using arity)
      (by simpa only [Kernel.ConstantInfo.toConstantVal, targetCtorParams, ← arities] using arity) rfl
    change (association.modelCore sourceModel.internal.base2 targetModel).base.acval sourceEntry.ctor
      (Kernel.Level.substFn levels sourceCtor.levelParams us) =
      targetModel.internal.base2.acval (names sourceEntry.ctor) (Kernel.Level.substFn levels targetCtor.levelParams us) at leaf
    simpa only [sourceCtorParams, targetCtorParams, comparison.constructor] using leaf
  refine ⟨sourceName, sourceIndex, sourceBound,
    ⟨sourceHeader, sourceCaps, sourceLookup, sourceParams, sourceEta⟩, sourceO5,
    sourceCtor, sourceCtorLookup, sourceCtorParams, ?_, ?_⟩
  · intro us arity
    have targetArity : us.length = targetEntry.levelParams.length := arity.trans arities
    obtain ⟨⟨sourceAnnotation, sourceRead, _⟩, _⟩ := sourceValues us arity
    obtain ⟨⟨targetAnnotation, targetRead, targetTyping⟩, ⟨targetCtorAnnotation, targetCtorRead, targetIota⟩⟩ :=
      targetValues us targetArity
    have sourceRawRead := sourceRead
    have targetRawRead := targetRead
    rw [← Kernel.projTele_instantiateLevelParams] at sourceRawRead targetRawRead
    have sourceReady := literalReady_of_reading sourceRawRead
    have targetReady := literalReady_of_reading targetRawRead
    rw [literalReady_instantiateLevels] at sourceReady targetReady
    have support := checkInstalledMemberExpr_literal_support comparison.body sourceReady targetReady
    have bounded := projTele_allLevelParamsDefined
      (Kernel.projEntry_body_wf targetModel.internal.base2.wf comparison.targetLookup).2.1 (targetEntry.numParams + 1)
    rw [← targetParams] at bounded
    have bodyImage := association.member_instance_reading sourceModel.internal.base2 targetModel sourceLookup targetLookup
      bounded support comparison.body levels levels us us
      (by simpa only [Kernel.ConstantInfo.toConstantVal, sourceParams] using arity)
      (by simpa only [Kernel.ConstantInfo.toConstantVal, targetParams] using targetArity) rfl 0
    simp only [Kernel.ConstantInfo.toConstantVal, sourceParams, targetParams,
      Kernel.projTele_instantiateLevelParams] at bodyImage
    have guard : TowerGuardAt levels sourceEntry us → TowerGuardAt levels targetEntry us := by
      have structImage := checkInstalledMemberSort_instance telescopes sourceLookup targetLookup comparison.structSort
        levels levels us us (by simpa only [Kernel.ConstantInfo.toConstantVal, sourceParams] using arity)
        (by simpa only [Kernel.ConstantInfo.toConstantVal, targetParams] using targetArity) rfl
      have fieldImage := checkInstalledMemberSort_instance telescopes sourceLookup targetLookup comparison.fieldSort
        levels levels us us (by simpa only [Kernel.ConstantInfo.toConstantVal, sourceParams] using arity)
        (by simpa only [Kernel.ConstantInfo.toConstantVal, targetParams] using targetArity) rfl
      simp only [Kernel.ConstantInfo.toConstantVal, sourceParams, targetParams] at structImage fieldImage
      intro sourceGuard targetZero
      exact fieldImage.symm.trans (sourceGuard (structImage.trans targetZero))
    refine ⟨⟨targetAnnotation, bodyImage.trans targetRead, ?_⟩, ⟨targetCtorAnnotation, ?_, ?_⟩⟩
    · intro sourceGuard ρ vs x rest count validOwner validX member peel
      rw [ownerLeaf us arity] at validOwner member
      have result := targetTyping (guard sourceGuard) ρ vs x rest
        (count.trans comparison.params) validOwner validX member peel
      simpa only [comparison.offset] using result
    · have image := association.type_instance_reading sourceModel.internal.base2 targetModel sourceCtorLookup mappedCtor
        levels levels us us (by simpa only [Kernel.ConstantInfo.toConstantVal, sourceCtorParams] using arity)
        (by simpa only [Kernel.ConstantInfo.toConstantVal, targetCtorParams] using targetArity) rfl
      exact image.trans targetCtorRead
    · intro sourceGuard ρ ys rest count valid fit
      rw [ctorLeaf us arity] at valid ⊢
      have result := targetIota (guard sourceGuard) ρ ys rest
        (by simpa only [comparison.params, comparison.fields] using count) valid fit
      simpa only [comparison.offset, comparison.params] using result
  · intro actualHeader actualCaps actualLookup us arity
    have same := Kernel.ConstantInfo.indInfo.inj (Option.some.inj (sourceLookup.symm.trans actualLookup))
    cases same.1
    have targetArity : us.length = targetEntry.levelParams.length := arity.trans arities
    obtain ⟨annotation, targetRead, graded, eta⟩ := targetEta targetHeader targetCaps targetLookup us targetArity
    have image := association.type_instance_reading sourceModel.internal.base2 targetModel sourceLookup targetLookup
      levels levels us us (by simpa only [Kernel.ConstantInfo.toConstantVal, sourceParams] using arity)
      (by simpa only [Kernel.ConstantInfo.toConstantVal, targetParams] using targetArity) rfl
    refine ⟨annotation, image.trans targetRead, graded, ?_⟩
    intro ρ ts rest x count fit member
    rw [ownerLeaf us arity] at member
    have result := eta ρ ts rest x (count.trans comparison.params) fit member
    rw [ctorLeaf us arity]
    simpa only [comparison.fields, comparison.offset] using result

/-- Complete coverage includes every stored source table entry, not just
ones reached by the expression comparison. -/
theorem AnnotatedAssociation.tower_ok {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (association : AnnotatedAssociation source target names)
    (sourceModel : StrongInstalledModel V source) (targetModel : StrongInstalledModel V target)
    (tables : checkInstalledTowers source target names = some true) (levels : Kernel.Name → Nat) :
    TowerOk (association.modelCore sourceModel.internal.base2 targetModel).base levels := by
  intro owner index entry lookup
  obtain ⟨targetEntry, compared⟩ := checkInstalledTowerEntry_sound lookup (checkInstalledTowers_entry tables lookup)
  exact compared.tower_law association sourceModel targetModel levels

end Ix.CompileCert
