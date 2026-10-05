import Ix.CompileCert.AnnotReduceOps

namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics

/-- Additional admitted semantic receipts do not alter the immutable-source
association or the preceding annotation/table evidence tiers. -/
def checkSupportedArtifactReduceAssociation {input : Input} (accepted : AcceptedAssociation input)
    {support : Array Kernel.Declaration} (bundle : AdmittedSupport accepted.toAdmittedArtifact support)
    (source : Kernel.Env) (names operationCertificates elementCertificates : Kernel.Name → Kernel.Name) : Option Bool :=
  bothChecks (checkSupportedArtifactTowerAssociation accepted bundle source names)
    (checkReduceOperationReceipts source bundle.env names operationCertificates elementCertificates)

theorem SourceConstructorCoverChecked.annotated_modelCore_reduce (V : Type u) [Kernel.SetTheory V]
    {input : Input} {installed : SourceNormalizedInstallation input.source input.roots}
    {site : SourceProjectionSite input.source} (coverage : SourceConstructorCoverChecked installed site)
    (accepted : AcceptedAssociation input) {support : Array Kernel.Declaration}
    (bundle : AdmittedSupport accepted.toAdmittedArtifact support)
    (names operationCertificates elementCertificates : Kernel.Name → Kernel.Name)
    (checked : checkSupportedArtifactReduceAssociation accepted bundle coverage.env names
      operationCertificates elementCertificates = some true) :
    SemanticNamesAgree accepted names ∧
      ∃ targetModel : StrongInstalledModel V bundle.env,
      ∃ core : AnnotatedModelCore V coverage.env,
        core.base.acval = (PullbackMap.fromEnvs coverage.env bundle.env names).annotations
          targetModel.internal.base2.acval ∧ CapsOk core.base ∧
        (∀ levels, RecRules core.base levels) ∧ (∀ levels, TowerOk core.base levels) ∧ ReduceOps core.base := by
  obtain ⟨towerCheck, reduceCheck⟩ := bothChecks_true checked
  obtain ⟨annotated, tables⟩ := bothChecks_true towerCheck
  obtain ⟨original, annotationCheck⟩ := bothChecks_true annotated
  obtain ⟨nameCheck, _⟩ := bothChecks_true original
  obtain ⟨sourceModel⟩ := coverage.strong_model V
  obtain ⟨targetModel⟩ := bundle.strong_model V
  have association := checkAnnotatedAssociation_sound annotationCheck
  exact ⟨of_decide_eq_true (Option.some.inj nameCheck), targetModel,
    association.modelCore sourceModel.internal.base2 targetModel, rfl,
    association.caps_ok sourceModel.internal.base2 targetModel,
    association.rec_rules sourceModel targetModel, association.tower_ok sourceModel targetModel tables,
    association.reduce_ops sourceModel targetModel reduceCheck⟩

end Ix.CompileCert
