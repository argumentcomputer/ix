import Ix.CompileCert.AnnotTowerLaws
import Ix.CompileCert.AnnotRecRules

namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics

/-- Additive S evidence: the original immutable-source/reader association and
annotated endpoint are retained, followed by complete source table coverage. -/
def checkSupportedArtifactTowerAssociation {input : Input} (accepted : AcceptedAssociation input)
    {support : Array Kernel.Declaration} (bundle : AdmittedSupport accepted.toAdmittedArtifact support)
    (source : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Option Bool :=
  bothChecks (checkSupportedArtifactAnnotatedAssociation accepted bundle source names)
    (checkInstalledTowers source bundle.env names)

theorem SourceConstructorCoverChecked.annotated_modelCore_towers (V : Type u) [Kernel.SetTheory V]
    {input : Input} {installed : SourceNormalizedInstallation input.source input.roots}
    {site : SourceProjectionSite input.source} (coverage : SourceConstructorCoverChecked installed site)
    (accepted : AcceptedAssociation input) {support : Array Kernel.Declaration}
    (bundle : AdmittedSupport accepted.toAdmittedArtifact support) (names : Kernel.Name → Kernel.Name)
    (checked : checkSupportedArtifactTowerAssociation accepted bundle coverage.env names = some true) :
    SemanticNamesAgree accepted names ∧
      ∃ targetModel : StrongInstalledModel V bundle.env,
      ∃ core : AnnotatedModelCore V coverage.env,
        core.base.acval = (PullbackMap.fromEnvs coverage.env bundle.env names).annotations
          targetModel.internal.base2.acval ∧ CapsOk core.base ∧
        (∀ levels, RecRules core.base levels) ∧ ∀ levels, TowerOk core.base levels := by
  obtain ⟨annotated, tables⟩ := bothChecks_true checked
  obtain ⟨original, annotationCheck⟩ := bothChecks_true annotated
  obtain ⟨nameCheck, _⟩ := bothChecks_true original
  obtain ⟨sourceModel⟩ := coverage.strong_model V
  obtain ⟨targetModel⟩ := bundle.strong_model V
  have association := checkAnnotatedAssociation_sound annotationCheck
  exact ⟨of_decide_eq_true (Option.some.inj nameCheck), targetModel,
    association.modelCore sourceModel.internal.base2 targetModel, rfl,
    association.caps_ok sourceModel.internal.base2 targetModel,
    association.rec_rules sourceModel targetModel, association.tower_ok sourceModel targetModel tables⟩

end Ix.CompileCert
