import Ix.CompileCert.AnnotNatOps

namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics

/-- All fields use the identical target-derived annotated carrier. Source
facts come from its independent installation, never this construction. -/
noncomputable def AnnotatedAssociation.strongInternal {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names certificates : Kernel.Name → Kernel.Name}
    {levels : Kernel.Name → Kernel.Level} {operationCertificates elementCertificates : Kernel.Name → Kernel.Name}
    (association : AnnotatedAssociation source target names)
    (sourceModel : StrongInstalledModel V source) (targetModel : StrongInstalledModel V target)
    (tables : checkInstalledTowers source target names = some true)
    (reduce : checkReduceOperationReceipts source target names operationCertificates elementCertificates = some true)
    (nat : checkNatOperationReceipts source target names certificates levels = some true)
    (divMod : checkDivModReceipts source target names certificates levels = some true) :
    EnvModelM V .verified source where
  base2 := (association.modelCore sourceModel.internal.base2 targetModel).base
  acval_validV := (association.modelCore sourceModel.internal.base2 targetModel).valid
  type_reads := (association.modelCore sourceModel.internal.base2 targetModel).type_reads
  type_wellDenotedV := (association.modelCore sourceModel.internal.base2 targetModel).type_wellDenotedV
  mem_type := (association.modelCore sourceModel.internal.base2 targetModel).mem_type
  defn_reads := (association.modelCore sourceModel.internal.base2 targetModel).definitions
  nat_heads := (association.modelCore sourceModel.internal.base2 targetModel).nat_heads
  nat_ops := association.nat_ops sourceModel targetModel nat
  div_mod := association.div_mod sourceModel targetModel divMod
  eq_law := (association.modelCore sourceModel.internal.base2 targetModel).eq_law
  caps_ok := association.caps_ok sourceModel.internal.base2 targetModel
  rec_rules := association.rec_rules sourceModel targetModel
  reduce_ops := association.reduce_ops sourceModel targetModel reduce
  tower_ok := association.tower_ok sourceModel targetModel tables

private theorem fvarsBelow_zero_of_not_hasFvar :
    ∀ {e : Kernel.Expr}, e.hasFvar = false → Kernel.Expr.fvarsBelow 0 e := by
  intro e
  induction e <;> simp_all [Kernel.Expr.fvarsBelow, Kernel.Expr.hasFvar]

/-- Preserve definition values on precisely the internal carrier; choosing a
separate public model would lose the checked endpoint identities. -/
noncomputable def strongInstalledModelOfInternal {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (model : EnvModelM V .verified env) : StrongInstalledModel V env where
  internal := model
  definition_values := by
    intro header value hint present universes ρ
    have reading := model.defn_reads universes header value ⟨hint, present⟩
    have wellformed := (model.base2.wf _ present).2.2.2.2.1 header value hint rfl
    have denotes := Denotes_of_denoteMeta (V := V) model.base2.cval_closedL 0 value reading
      (fvarsBelow_zero_of_not_hasFvar wellformed.1) wellformed.2.2.2 ρ
      ⟨model.base2.acval_wellDenoted _ universes ρ, model.acval_validV _ universes ρ⟩
    rw [Kernel.Expr.closeN_of_hasFvar _ 0 0 wellformed.1, interp_cvalOf model.base2.cval_closedL] at denotes
    exact denotes


/-- The complete additive S check retains all previous correspondence tiers.
Its receipt tables are still producer obligations, not domain restrictions. -/
def checkSupportedArtifactStrongAssociation {input : Input} (accepted : AcceptedAssociation input)
    {support : Array Kernel.Declaration} (bundle : AdmittedSupport accepted.toAdmittedArtifact support)
    (source : Kernel.Env) (names certificates operationCertificates elementCertificates : Kernel.Name → Kernel.Name)
    (levels : Kernel.Name → Kernel.Level) : Option Bool :=
  bothChecks (checkSupportedArtifactReduceAssociation accepted bundle source names operationCertificates elementCertificates)
    (bothChecks (checkNatOperationReceipts source bundle.env names certificates levels)
      (checkDivModReceipts source bundle.env names certificates levels))

theorem SourceConstructorCoverChecked.annotated_strong_model (V : Type u) [Kernel.SetTheory V]
    {input : Input} {installed : SourceNormalizedInstallation input.source input.roots}
    {site : SourceProjectionSite input.source} (coverage : SourceConstructorCoverChecked installed site)
    (accepted : AcceptedAssociation input) {support : Array Kernel.Declaration}
    (bundle : AdmittedSupport accepted.toAdmittedArtifact support)
    (names certificates operationCertificates elementCertificates : Kernel.Name → Kernel.Name)
    (levels : Kernel.Name → Kernel.Level)
    (checked : checkSupportedArtifactStrongAssociation accepted bundle coverage.env names certificates
      operationCertificates elementCertificates levels = some true) :
    SemanticNamesAgree accepted names ∧
      ∃ targetModel : StrongInstalledModel V bundle.env,
      ∃ sourceModel : StrongInstalledModel V coverage.env,
        sourceModel.internal.base2.acval = (PullbackMap.fromEnvs coverage.env bundle.env names).annotations
          targetModel.internal.base2.acval := by
  obtain ⟨reduceCheck, operations⟩ := bothChecks_true checked
  obtain ⟨natCheck, divModCheck⟩ := bothChecks_true operations
  obtain ⟨towerCheck, reduceCheck⟩ := bothChecks_true reduceCheck
  obtain ⟨annotated, tables⟩ := bothChecks_true towerCheck
  obtain ⟨original, annotationCheck⟩ := bothChecks_true annotated
  obtain ⟨nameCheck, _⟩ := bothChecks_true original
  obtain ⟨sourceModel⟩ := coverage.strong_model V
  obtain ⟨targetModel⟩ := bundle.strong_model V
  have association := checkAnnotatedAssociation_sound annotationCheck
  exact ⟨of_decide_eq_true (Option.some.inj nameCheck), targetModel,
    strongInstalledModelOfInternal (association.strongInternal sourceModel targetModel tables reduceCheck natCheck divModCheck), rfl⟩

end Ix.CompileCert
