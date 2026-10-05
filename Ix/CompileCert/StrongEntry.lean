import Ix.CompileCert.AnnotStrong

namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics

/-- Environment-level evidence, usable for either the original independent
source installation or the separately recorded normalization route. -/
def checkStrongAssociation (source target : Kernel.Env)
    (names certificates operationCertificates elementCertificates : Kernel.Name → Kernel.Name)
    (levels : Kernel.Name → Kernel.Level) : Option Bool :=
  bothChecks (checkAnnotatedAssociation source target names)
    (bothChecks (checkInstalledTowers source target names)
      (bothChecks (checkReduceOperationReceipts source target names operationCertificates elementCertificates)
        (bothChecks (checkNatOperationReceipts source target names certificates levels)
          (checkDivModReceipts source target names certificates levels))))

theorem checkedStrongAssociation {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env}
    {names certificates operationCertificates elementCertificates : Kernel.Name → Kernel.Name}
    {levels : Kernel.Name → Kernel.Level}
    (sourceModel : StrongInstalledModel V source) (targetModel : StrongInstalledModel V target)
    (checked : checkStrongAssociation source target names certificates operationCertificates elementCertificates levels = some true) :
    ∃ pulled : StrongInstalledModel V source,
      pulled.internal.base2.acval = (PullbackMap.fromEnvs source target names).annotations targetModel.internal.base2.acval ∧
      pulled.public.cval = (PullbackMap.fromEnvs source target names).values targetModel.public.cval := by
  obtain ⟨annotation, rest⟩ := bothChecks_true checked
  obtain ⟨tables, rest⟩ := bothChecks_true rest
  obtain ⟨reduce, rest⟩ := bothChecks_true rest
  obtain ⟨nat, divMod⟩ := bothChecks_true rest
  let association := checkAnnotatedAssociation_sound annotation
  refine ⟨strongInstalledModelOfInternal
    (association.strongInternal sourceModel targetModel tables reduce nat divMod), rfl, ?_⟩
  rfl

/-- This endpoint is bound to the immutable source, complete original export,
its independent accepting fold, the closed artifact map, and actual admitted
support. It does not insert projection normalization into original syntax. -/
def checkSourceArtifactStrongAssociation {input : Input} (accepted : AcceptedAssociation input)
    {support : Array Kernel.Declaration} (bundle : AdmittedSupport accepted.toAdmittedArtifact support)
    (installed : SourceInstallation input.source input.roots)
    (names certificates operationCertificates elementCertificates : Kernel.Name → Kernel.Name)
    (levels : Kernel.Name → Kernel.Level) : Option Bool :=
  bothChecks (some (decide (SemanticNamesAgree accepted names)))
    (checkStrongAssociation installed.env bundle.env names certificates operationCertificates elementCertificates levels)

theorem SourceInstallation.artifact_strong_model (V : Type u) [Kernel.SetTheory V]
    {input : Input} (installed : SourceInstallation input.source input.roots)
    (accepted : AcceptedAssociation input) {support : Array Kernel.Declaration}
    (bundle : AdmittedSupport accepted.toAdmittedArtifact support)
    (names certificates operationCertificates elementCertificates : Kernel.Name → Kernel.Name)
    (levels : Kernel.Name → Kernel.Level)
    (checked : checkSourceArtifactStrongAssociation accepted bundle installed names certificates
      operationCertificates elementCertificates levels = some true) :
    SemanticNamesAgree accepted names ∧
      Kernel.Cached.checkDecls .verified [] installed.declarations = .ok installed.env ∧
      ∃ targetModel : StrongInstalledModel V bundle.env,
      ∃ sourceModel : StrongInstalledModel V installed.env,
        sourceModel.internal.base2.acval = (PullbackMap.fromEnvs installed.env bundle.env names).annotations
          targetModel.internal.base2.acval ∧
        sourceModel.public.cval = (PullbackMap.fromEnvs installed.env bundle.env names).values targetModel.public.cval := by
  obtain ⟨nameCheck, strongCheck⟩ := bothChecks_true checked
  obtain ⟨sourceModel⟩ := installed.strong_model V
  obtain ⟨targetModel⟩ := bundle.strong_model V
  obtain ⟨pulled, annotations, values⟩ := checkedStrongAssociation sourceModel targetModel strongCheck
  exact ⟨of_decide_eq_true (Option.some.inj nameCheck), installed.checked,
    targetModel, pulled, annotations, values⟩

end Ix.CompileCert
