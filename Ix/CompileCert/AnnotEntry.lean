import Ix.CompileCert.Support
import Ix.CompileCert.AnnotModel
import Ix.CompileCert.AnnotSupport

/-! Executable installed annotation association. This is the checked core
needed by the strong-model construction, not completed source semantics:
operation/capability/recursor/tower laws and original-source normalization
remain obligations. The independent source installation is a separate input.
-/
namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics

structure AnnotatedAssociation (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Prop where
  installed : InstalledAssociation source target names
  reserved : checkReservedNameMap source names = true
  types : checkTypeLiteralSupport source target = true
  definitions : checkDefinitionLiteralSupport source target = true

def checkAnnotatedAssociation (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Option Bool :=
  bothChecks (checkInstalledAssociation source target names)
    (some (checkReservedNameMap source names && checkTypeLiteralSupport source target &&
      checkDefinitionLiteralSupport source target))

theorem checkAnnotatedAssociation_sound {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : checkAnnotatedAssociation source target names = some true) :
    AnnotatedAssociation source target names := by
  obtain ⟨installed, extra⟩ := bothChecks_true checked
  have facts := Option.some.inj extra
  simp only [Bool.and_eq_true] at facts
  exact ⟨checkInstalledAssociation_sound installed, facts.1.1, facts.1.2, facts.2⟩

open Kernel.SetTheory in
/-- Exact subset of EnvModelM established here. Keeping the remaining modeled
laws out of this record prevents a checked core from masquerading as a full
strong model or supplying checker soundness circularly. -/
structure AnnotatedModelCore (V : Type u) [Kernel.SetTheory V] (env : Kernel.Env) where
  base : EnvModel V env
  valid : ∀ name levels ρ, AnnotValid V ρ (base.acval name levels)
  type_reads : ∀ entry ∈ env.consts, ∀ levels,
    ∃ annotation, denoteMeta base.acval env levels 0 entry.toConstantVal.type = some annotation
  type_wellDenotedV : ∀ entry ∈ env.consts, ∀ levels annotation,
    denoteMeta base.acval env levels 0 entry.toConstantVal.type = some annotation →
      ∀ ρ : Nat → V, WellDenotedV V ρ annotation
  mem_type : ∀ entry ∈ env.consts, ∀ levels annotation,
    denoteMeta base.acval env levels 0 entry.toConstantVal.type = some annotation →
      ∀ ρ : Nat → V, interp V ρ (base.acval entry.name levels) ∈ˢ interp V ρ annotation
  definitions : Kernel.Model.AcvalDefnInst base
  nat_heads : ∀ levels, Kernel.Model.NatHeads base levels
  eq_law : Kernel.Model.EqLaw base

noncomputable def AnnotatedAssociation.modelCore {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : AnnotatedAssociation source target names)
    (sourceFacts : EnvModel V source) (targetModel : StrongInstalledModel V target) :
    AnnotatedModelCore V source where
  base := pulledAnnotatedBase sourceFacts targetModel (checkTelescopes_sound checked.installed.telescopes)
    checked.reserved
  valid := pulledAnnotatedBase_valid sourceFacts targetModel
    (checkTelescopes_sound checked.installed.telescopes) checked.reserved
  type_reads := by
    intro entry present levels
    obtain ⟨annotation, reading, _, _⟩ := checkInstalledTypes_annotated_local targetModel
      (checkTelescopes_sound checked.installed.telescopes) checked.types checked.installed.types entry present levels
    exact ⟨annotation, reading⟩
  type_wellDenotedV := by
    intro entry present levels annotation reading ρ
    obtain ⟨actual, actualRead, graded, _⟩ := checkInstalledTypes_annotated_local targetModel
      (checkTelescopes_sound checked.installed.telescopes) checked.types checked.installed.types entry present levels
    have same := Option.some.inj (actualRead.symm.trans reading)
    subst annotation
    exact graded ρ
  mem_type := by
    intro entry present levels annotation reading ρ
    obtain ⟨actual, actualRead, _, membership⟩ := checkInstalledTypes_annotated_local targetModel
      (checkTelescopes_sound checked.installed.telescopes) checked.types checked.installed.types entry present levels
    have same := Option.some.inj (actualRead.symm.trans reading)
    subst annotation
    exact membership ρ
  definitions := checkInstalledDefinitions_annotated_local targetModel
    (checkTelescopes_sound checked.installed.telescopes) checked.definitions checked.installed.definitions
  nat_heads := pulledAnnotatedBase_natHeads sourceFacts targetModel
    (checkTelescopes_sound checked.installed.telescopes) checked.reserved
  eq_law := pulledAnnotatedBase_eqLaw sourceFacts targetModel
    (checkTelescopes_sound checked.installed.telescopes) checked.reserved

/-- The new finite checker and independently installed source/target witnesses
yield the actual source annotated core. No source model premise is inferred
from target acceptance, and this theorem does not claim EnvModelM. -/
theorem checkedAnnotatedAssociation_core {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (sourceModel : StrongInstalledModel V source) (targetModel : StrongInstalledModel V target)
    (checked : checkAnnotatedAssociation source target names = some true) :
    Nonempty (AnnotatedModelCore V source) :=
  ⟨(checkAnnotatedAssociation_sound checked).modelCore sourceModel.internal.base2 targetModel⟩

/-- Preserve the accepted immutable-source/map association while checking the
actual independently installed normalized source and admitted support target. -/
def checkSupportedArtifactAnnotatedAssociation {input : Input} (accepted : AcceptedAssociation input)
    {support : Array Kernel.Declaration} (bundle : AdmittedSupport accepted.toAdmittedArtifact support)
    (source : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Option Bool :=
  bothChecks (checkSupportedArtifactInstalledAssociation accepted bundle source names)
    (checkAnnotatedAssociation source bundle.env names)

theorem SourceConstructorCoverChecked.annotated_modelCore (V : Type u) [Kernel.SetTheory V]
    {input : Input} {installed : SourceNormalizedInstallation input.source input.roots}
    {site : SourceProjectionSite input.source} (coverage : SourceConstructorCoverChecked installed site)
    (accepted : AcceptedAssociation input) {support : Array Kernel.Declaration}
    (bundle : AdmittedSupport accepted.toAdmittedArtifact support) (names : Kernel.Name → Kernel.Name)
    (checked : checkSupportedArtifactAnnotatedAssociation accepted bundle coverage.env names = some true) :
    SemanticNamesAgree accepted names ∧ Nonempty (AnnotatedModelCore V coverage.env) := by
  obtain ⟨original, annotated⟩ := bothChecks_true checked
  obtain ⟨nameCheck, _⟩ := bothChecks_true original
  obtain ⟨sourceModel⟩ := coverage.strong_model V
  obtain ⟨targetModel⟩ := bundle.strong_model V
  exact ⟨of_decide_eq_true (Option.some.inj nameCheck),
    checkedAnnotatedAssociation_core sourceModel targetModel annotated⟩

/-- Expose the exact supplied target witness and its annotation carrier.
This adds no semantic law or executable guard to the core construction. -/
theorem checkedAnnotatedAssociation_linked {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (sourceModel : StrongInstalledModel V source) (targetModel : StrongInstalledModel V target)
    (checked : checkAnnotatedAssociation source target names = some true) :
    ∃ core : AnnotatedModelCore V source,
      core.base.acval = (PullbackMap.fromEnvs source target names).annotations
        targetModel.internal.base2.acval := by
  exact ⟨(checkAnnotatedAssociation_sound checked).modelCore sourceModel.internal.base2 targetModel, rfl⟩

/-- Artifact-connected companion retaining the target model chosen from its
actual admitted support stream, together with the source core's exact carrier.
It does not claim that this core already satisfies the remaining EnvModelM laws. -/
theorem SourceConstructorCoverChecked.annotated_modelCore_linked (V : Type u) [Kernel.SetTheory V]
    {input : Input} {installed : SourceNormalizedInstallation input.source input.roots}
    {site : SourceProjectionSite input.source} (coverage : SourceConstructorCoverChecked installed site)
    (accepted : AcceptedAssociation input) {support : Array Kernel.Declaration}
    (bundle : AdmittedSupport accepted.toAdmittedArtifact support) (names : Kernel.Name → Kernel.Name)
    (checked : checkSupportedArtifactAnnotatedAssociation accepted bundle coverage.env names = some true) :
    SemanticNamesAgree accepted names ∧
      ∃ targetModel : StrongInstalledModel V bundle.env,
      ∃ core : AnnotatedModelCore V coverage.env,
        core.base.acval = (PullbackMap.fromEnvs coverage.env bundle.env names).annotations
          targetModel.internal.base2.acval := by
  obtain ⟨original, annotated⟩ := bothChecks_true checked
  obtain ⟨nameCheck, _⟩ := bothChecks_true original
  obtain ⟨sourceModel⟩ := coverage.strong_model V
  obtain ⟨targetModel⟩ := bundle.strong_model V
  exact ⟨of_decide_eq_true (Option.some.inj nameCheck), targetModel,
    checkedAnnotatedAssociation_linked sourceModel targetModel annotated⟩

end Ix.CompileCert
