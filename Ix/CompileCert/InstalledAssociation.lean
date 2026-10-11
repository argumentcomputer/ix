import Ix.CompileCert.CheckCompiled
import Ix.CompileCert.RuleLaws
import Ix.CompileCert.SourceNormalization

/-! # Installed association

The finite installed association (`InstalledAssociation`,
`checkInstalledAssociation`) and its soundness, on artifacts
(`checkArtifactInstalledAssociation`) and on source installations.
-/

namespace Ix.CompileCert

open Kernel.Reader
open Kernel.Admission

/-- Finite installed association evidence. The exact environments and forward
name function are indices, not fields which can be replaced after checking.
Raw checking bodies, immutable source records, and source normalization are
separate obligations; this receipt does not assert their correspondence. -/
structure InstalledAssociation (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Prop where
  telescopes : checkTelescopes source target names = true
  types : checkInstalledTypes source target names = true
  definitions : checkInstalledDefinitions source target names = true
  falsePin : checkInstalledPin source names Kernel.falseName 0 = true
  eqPin : checkInstalledPin source names Kernel.eqName 1 = true
  capabilities : checkInstalledCapabilities source target names = true
  etaAssociations : checkInstalledEtaAssociations source target names = some true
  recursors : checkInstalledRecursors source target names = true
  constructors : checkInstalledConstructors source target names = true
  levelLinks : checkInstalledRuleLevelLinks source target names = some true

/-- Executable aggregate. `none` retains unavailable comparison; `some false`
is certificate refusal, never established semantic disequality. A later
unavailable row need not override an earlier definite certificate failure.
The existing Boolean checks are retained as the exact proved interfaces. -/
def checkInstalledAssociation (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Option Bool :=
  bothChecks (checkInstalledComparisonAvailability source target names)
    (bothChecks (some (checkTelescopes source target names &&
      checkInstalledTypes source target names && checkInstalledDefinitions source target names &&
      checkInstalledPin source names Kernel.falseName 0 && checkInstalledPin source names Kernel.eqName 1 &&
      checkInstalledCapabilities source target names && checkInstalledRecursors source target names &&
      checkInstalledConstructors source target names))
      (bothChecks (checkInstalledEtaAssociations source target names)
        (checkInstalledRuleLevelLinks source target names)))

theorem checkInstalledAssociation_sound {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : checkInstalledAssociation source target names = some true) :
    InstalledAssociation source target names := by
  obtain ⟨_, checked⟩ := bothChecks_true checked
  obtain ⟨structural, semantic⟩ := bothChecks_true checked
  have fields := Option.some.inj structural
  simp only [Bool.and_eq_true] at fields
  obtain ⟨eta, links⟩ := bothChecks_true semantic
  exact ⟨fields.1.1.1.1.1.1.1, fields.1.1.1.1.1.1.2, fields.1.1.1.1.1.2,
    fields.1.1.1.1.2, fields.1.1.1.2, fields.1.1.2, eta, fields.1.2, fields.2, links⟩

/-- One accepted executable aggregate, plus both actual independent verified
folds, supplies the installed public-value/capability/universal-rule endpoint.
This does not identify the pull-back values with an independently chosen
source model, or discharge original-source annotation and normalization. -/
theorem checkedAssociation_universalRules (V : Type u) [Kernel.SetTheory V]
    (sourcePins targetPins : List Kernel.NatOpPinSet)
    (sourceDecls targetDecls : Array Kernel.Declaration)
    {sourceEnv targetEnv : Kernel.Env} (names : Kernel.Name → Kernel.Name)
    (sourceChecked : Kernel.Cached.checkDecls .verified sourcePins sourceDecls = .ok sourceEnv)
    (targetChecked : Kernel.Cached.checkDecls .verified targetPins targetDecls = .ok targetEnv)
    (checked : checkInstalledAssociation sourceEnv targetEnv names = some true) :
    Nonempty (StrongInstalledModel V sourceEnv) ∧
    ∃ (target : StrongInstalledModel V targetEnv) (source : PublicValueModel V sourceEnv),
      source.model.cval = (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval ∧
      PublicCapabilityLaws source.model.cval sourceEnv ∧ UniversalRuleSimulation target sourceEnv names := by
  have receipt := checkInstalledAssociation_sound checked
  exact checkedStreams_universalRules V sourcePins targetPins sourceDecls targetDecls names
    sourceChecked targetChecked receipt.telescopes receipt.types receipt.definitions receipt.falsePin
    receipt.eqPin receipt.capabilities receipt.etaAssociations receipt.recursors receipt.constructors receipt.levelLinks

/-- The semantic name map must agree with the accepted reader/export map for
every immutable source declaration, including every member of an alias fiber.
Source-only model/support names are not original declarations: their installed
associations are still checked separately over the complete source environment. -/
def SemanticNamesAgree {input : Input} (accepted : AcceptedAssociation input)
    (names : Kernel.Name → Kernel.Name) : Prop :=
  ∀ entry ∈ input.source.declarations,
    NameAgrees ⟨input.source, input.map, accepted.pins, noImages⟩ entry.name (names (sourceName entry.name))

instance {input : Input} (accepted : AcceptedAssociation input) (names : Kernel.Name → Kernel.Name) :
    Decidable (SemanticNamesAgree accepted names) :=
  inferInstanceAs (Decidable (∀ entry ∈ input.source.declarations,
    NameAgrees ⟨input.source, input.map, accepted.pins, noImages⟩ entry.name (names (sourceName entry.name))))

/-- Bind the installed aggregate to the exact admitted bytes' reader map.
Missing source-only support on the target remains refusal; support rows are
not removed to make this check succeed. -/
def checkArtifactInstalledAssociation {input : Input} (accepted : AcceptedAssociation input)
    (sourceEnv : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Option Bool :=
  bothChecks (some (decide (SemanticNamesAgree accepted names)))
    (checkInstalledAssociation sourceEnv accepted.env names)

theorem checkArtifactInstalledAssociation_sound {input : Input} (accepted : AcceptedAssociation input)
    {sourceEnv : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : checkArtifactInstalledAssociation accepted sourceEnv names = some true) :
    SemanticNamesAgree accepted names ∧ InstalledAssociation sourceEnv accepted.env names := by
  obtain ⟨nameCheck, association⟩ := bothChecks_true checked
  exact ⟨of_decide_eq_true (Option.some.inj nameCheck), checkInstalledAssociation_sound association⟩

/-- The direct original-stream route uses its own exact checked declarations.
Target installation is derived from byte admission, including the actual
prelude and native pin set; callers do not supply a substitute target fold. -/
theorem SourceInstallation.artifact_universalRules (V : Type u) [Kernel.SetTheory V]
    {input : Input} (source : SourceInstallation input.source input.roots)
    (accepted : AcceptedAssociation input) (names : Kernel.Name → Kernel.Name)
    (checked : checkArtifactInstalledAssociation accepted source.env names = some true) :
    SemanticNamesAgree accepted names ∧ Nonempty (StrongInstalledModel V source.env) ∧
    ∃ (target : StrongInstalledModel V accepted.env) (publicSource : PublicValueModel V source.env),
      publicSource.model.cval = (PullbackMap.fromEnvs source.env accepted.env names).values target.public.cval ∧
      PublicCapabilityLaws publicSource.model.cval source.env ∧ UniversalRuleSimulation target source.env names := by
  obtain ⟨nameCheck, association⟩ := bothChecks_true checked
  obtain ⟨targetPins, _, targetChecked⟩ := accepted.toAdmittedArtifact.checked_declarations
  exact ⟨of_decide_eq_true (Option.some.inj nameCheck),
    checkedAssociation_universalRules V [] targetPins source.declarations
      (Kernel.Frontend.preparePrelude accepted.prelude.ix accepted.declarations) names
      source.checked targetChecked association⟩

/-- The normalized route uses its independently checked normalized array,
while retaining the original records and source-owned normalization receipt.
The theorem gives installed laws only: the retained normalization receipt's
semantic pull-back to the immutable originals is not inferred from admission. -/
theorem SourceNormalizedInstallation.artifact_universalRules (V : Type u) [Kernel.SetTheory V]
    {input : Input} (source : SourceNormalizedInstallation input.source input.roots)
    (accepted : AcceptedAssociation input) (names : Kernel.Name → Kernel.Name)
    (checked : checkArtifactInstalledAssociation accepted source.env names = some true) :
    SemanticNamesAgree accepted names ∧ Nonempty (StrongInstalledModel V source.env) ∧
    ∃ (target : StrongInstalledModel V accepted.env) (publicSource : PublicValueModel V source.env),
      publicSource.model.cval = (PullbackMap.fromEnvs source.env accepted.env names).values target.public.cval ∧
      PublicCapabilityLaws publicSource.model.cval source.env ∧ UniversalRuleSimulation target source.env names := by
  obtain ⟨nameCheck, association⟩ := bothChecks_true checked
  obtain ⟨targetPins, _, targetChecked⟩ := accepted.toAdmittedArtifact.checked_declarations
  exact ⟨of_decide_eq_true (Option.some.inj nameCheck),
    checkedAssociation_universalRules V source.pins targetPins source.declarations.toArray
      (Kernel.Frontend.preparePrelude accepted.prelude.ix accepted.declarations) names
      source.checked targetChecked association⟩

end Ix.CompileCert
