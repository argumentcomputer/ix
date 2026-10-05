import Ix.CompileCert.Domain
import IxC.Kernel.Admission.Theorems
import IxC.Kernel.Verify.Cached.PushChain
import IxC.Kernel.Verify.Cached.BridgeCS4
import IxC.Kernel.Model.IndUnitLaw
import IxC.Kernel.Model.IOLicense
import IxC.Kernel.Model.Rules.RedSoundKit
import IxC.Kernel.Model.Rules.IotaSoundKit
import Ix.CompileCert.Installed
import Ix.CompileCert.AnnotationTrace
import Ix.CompileCert.SourceInstallation
import Ix.CompileCert.SourceNormalization
import Ix.CompileCert.SourceProjection
import Ix.CompileCert.CheckCompiled
import Ix.CompileCert.RuleLaws
import Ix.CompileCert.InstalledAssociation
import Ix.CompileCert.ProjectionPullback

/-! # Admission-connected direct-cone certification

The executable reads and admits the exact bytes before comparing an
independent source export against the reader stream. Its result carries
proofs of the checks actually performed. No producer-supplied proposition,
Boolean verdict, or `Named.original` field is accepted as correspondence.

This is a conservative foundation of C1, not completed W. Singleton definitions
may use the proved raw reader-normalization relation; its semantic pull-back
and complete source/export refinement remain separate obligations.
-/

namespace Ix.CompileCert

open Kernel.Reader
open Kernel.Admission

/-- Every original installed row keeps its complete identity and contents in
a certifier-owned extension. This compares structure, not cached hashes. -/
def InstalledRowsPreserved (original extended : Kernel.Env) : Prop :=
  ∀ entry ∈ original.consts, extended.find? entry.name = some entry

instance (original extended : Kernel.Env) : Decidable (InstalledRowsPreserved original extended) :=
  inferInstanceAs (Decidable (∀ entry ∈ original.consts, extended.find? entry.name = some entry))

def SupportFresh (original : Kernel.Env) (support : Array Kernel.Declaration) : Prop :=
  (support.toList.flatMap Kernel.Declaration.names).Nodup ∧
    ∀ name ∈ support.toList.flatMap Kernel.Declaration.names, original.find? name = none

instance (original : Kernel.Env) (support : Array Kernel.Declaration) :
    Decidable (SupportFresh original support) :=
  inferInstanceAs (Decidable ((support.toList.flatMap Kernel.Declaration.names).Nodup ∧
    ∀ name ∈ support.toList.flatMap Kernel.Declaration.names, original.find? name = none))

/-- Separate, checked target support; the original compiler bytes, reader
stream, hint function and admission receipt are retained unchanged. This
receipt does not assert semantic correspondence of proposed helper contents:
the installed association checks must establish that independently. -/
structure AdmittedSupport {input : ArtifactInput} (artifact : AdmittedArtifact input)
    (support : Array Kernel.Declaration) where
  fresh : SupportFresh artifact.env support
  pins : List Kernel.NatOpPinSet
  pins_checked : builtinNatOpPins = .ok pins
  env : Kernel.Env
  checked : Kernel.Cached.checkDecls .verified pins
    (Kernel.Frontend.preparePrelude artifact.prelude.ix artifact.declarations ++ support) = .ok env
  original_rows : InstalledRowsPreserved artifact.env env

inductive SupportError where
  | conflictingNames
  | setup (reason : String)
  | checking (error : Kernel.CheckError) (position : Nat)
  | changedOriginal

def checkAdmittedSupport {input : ArtifactInput} (artifact : AdmittedArtifact input)
    (support : Array Kernel.Declaration) : Except SupportError (AdmittedSupport artifact support) :=
  if fresh : SupportFresh artifact.env support then
    match pinsChecked : builtinNatOpPins with
    | .error reason => .error (.setup reason)
    | .ok pins =>
      match checked : Kernel.Cached.checkDecls .verified pins
          (Kernel.Frontend.preparePrelude artifact.prelude.ix artifact.declarations ++ support) with
      | .error (error, position) => .error (.checking error position)
      | .ok env =>
        if originalRows : InstalledRowsPreserved artifact.env env then
          .ok ⟨fresh, pins, pinsChecked, env, checked, originalRows⟩
        else .error .changedOriginal
  else .error .conflictingNames

theorem AdmittedSupport.strong_model (V : Type u) [Kernel.SetTheory V]
    {input : ArtifactInput} {artifact : AdmittedArtifact input} {support : Array Kernel.Declaration}
    (bundle : AdmittedSupport artifact support) : Nonempty (StrongInstalledModel V bundle.env) :=
  strongInstalledModel_exists V bundle.pins _ bundle.env bundle.checked

theorem AdmittedSupport.original_member {input : ArtifactInput} {artifact : AdmittedArtifact input}
    {support : Array Kernel.Declaration} (bundle : AdmittedSupport artifact support)
    {entry : Kernel.ConstantInfo} (present : entry ∈ artifact.env.consts) :
    bundle.env.find? entry.name = some entry ∧ entry ∈ bundle.env.consts := by
  have lookup := bundle.original_rows entry present
  exact ⟨lookup, Kernel.Semantics.Env.find?_mem lookup⟩

def checkSupportedArtifactInstalledAssociation {input : Input} (accepted : AcceptedAssociation input)
    {support : Array Kernel.Declaration} (bundle : AdmittedSupport accepted.toAdmittedArtifact support)
    (sourceEnv : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Option Bool :=
  bothChecks (some (decide (SemanticNamesAgree accepted names)))
    (checkInstalledAssociation sourceEnv bundle.env names)

/-- Actual source coverage stream versus a separate actual admitted target
support stream. The original bytes/map receipt and all original installed rows
are retained. This supplies the public model used by projection pull-back;
successful support generation and original D11 are still separate obligations. -/
theorem SourceConstructorCoverChecked.supported_universalRules (V : Type u) [Kernel.SetTheory V]
    {input : Input} {installed : SourceNormalizedInstallation input.source input.roots}
    {site : SourceProjectionSite input.source} (coverage : SourceConstructorCoverChecked installed site)
    (accepted : AcceptedAssociation input) {support : Array Kernel.Declaration}
    (bundle : AdmittedSupport accepted.toAdmittedArtifact support) (names : Kernel.Name → Kernel.Name)
    (checked : checkSupportedArtifactInstalledAssociation accepted bundle coverage.env names = some true) :
    SemanticNamesAgree accepted names ∧ Nonempty (StrongInstalledModel V coverage.env) ∧
    ∃ (target : StrongInstalledModel V bundle.env) (publicSource : PublicValueModel V coverage.env),
      publicSource.model.cval = (PullbackMap.fromEnvs coverage.env bundle.env names).values target.public.cval ∧
      PublicCapabilityLaws publicSource.model.cval coverage.env ∧ UniversalRuleSimulation target coverage.env names := by
  obtain ⟨nameCheck, association⟩ := bothChecks_true checked
  exact ⟨of_decide_eq_true (Option.some.inj nameCheck),
    checkedAssociation_universalRules V [] bundle.pins
      (installed.declarations ++ [Kernel.Declaration.thmDecl coverage.header coverage.value]).toArray
      (Kernel.Frontend.preparePrelude accepted.prelude.ix accepted.declarations ++ support) names
      coverage.checked bundle.checked association⟩

/-- Untrusted proposal generation for certifier-owned term helpers. Full
constant and projection-owner renaming is explicit; universe telescopes and
annotation data are retained. Admission and semantic association check the
result independently. Other declaration kinds need their own generator;
this partial helper is not a definition of the compiler's source domain. -/
def proposeRenamedSupport (names : Kernel.Name → Kernel.Name) :
    Kernel.Declaration → Except String Kernel.Declaration
  | .defnDecl header value hint => .ok (.defnDecl
      { header with name := names header.name, type := kernelRenameAll names header.type }
      (kernelRenameAll names value) hint)
  | .thmDecl header value => .ok (.thmDecl
      { header with name := names header.name, type := kernelRenameAll names header.type }
      (kernelRenameAll names value))
  | .opaqueDecl header value => .ok (.opaqueDecl
      { header with name := names header.name, type := kernelRenameAll names header.type }
      (kernelRenameAll names value))
  | _ => .error "term-support generator requires a definition, theorem, or opaque witness"

/-- Original-artifact semantics under a separate support model require their
own checked identity association. Structural row preservation alone is not
treated as conservation: projection lookup and capability/rule meaning must
also pass the installed semantic checks. Both actual folds supply their own
installation premises. -/
theorem AdmittedSupport.original_universalRules (V : Type u) [Kernel.SetTheory V]
    {input : ArtifactInput} {artifact : AdmittedArtifact input} {support : Array Kernel.Declaration}
    (bundle : AdmittedSupport artifact support)
    (identityChecked : checkInstalledAssociation artifact.env bundle.env id = some true) :
    Nonempty (StrongInstalledModel V artifact.env) ∧
    ∃ (target : StrongInstalledModel V bundle.env) (original : PublicValueModel V artifact.env),
      original.model.cval = (PullbackMap.fromEnvs artifact.env bundle.env id).values target.public.cval ∧
      PublicCapabilityLaws original.model.cval artifact.env ∧ UniversalRuleSimulation target artifact.env id := by
  obtain ⟨originalPins, _, originalChecked⟩ := artifact.checked_declarations
  exact checkedAssociation_universalRules V originalPins bundle.pins
    (Kernel.Frontend.preparePrelude artifact.prelude.ix artifact.declarations)
    (Kernel.Frontend.preparePrelude artifact.prelude.ix artifact.declarations ++ support) id
    originalChecked bundle.checked identityChecked

/-- Exact original-row preservation makes the identity pull-back's universe
selection literally the original assignment at every existing constant.
Absent names are deliberately outside this claim. -/
theorem AdmittedSupport.original_value {V : Type u}
    {input : ArtifactInput} {artifact : AdmittedArtifact input} {support : Array Kernel.Declaration}
    (bundle : AdmittedSupport artifact support)
    (values : Kernel.Name → (Kernel.Name → Nat) → V)
    {name : Kernel.Name} {entry : Kernel.ConstantInfo}
    (lookup : artifact.env.find? name = some entry) (levels : Kernel.Name → Nat) :
    (PullbackMap.fromEnvs artifact.env bundle.env id).values values name levels = values name levels := by
  have named := Kernel.Semantics.Env.find?_name lookup
  have extended := bundle.original_rows entry (Kernel.Semantics.Env.find?_mem lookup)
  rw [named] at extended
  simp only [PullbackMap.values, PullbackMap.fromEnvs, id_eq, lookup, extended,
    Kernel.Level.substFn_param_self]

/-- Build a source value model from one fixed target model. This interface
allows multiple associated streams to share the same target witness. -/
noncomputable def InstalledAssociation.valueModel {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (receipt : InstalledAssociation sourceEnv targetEnv names) (target : StrongInstalledModel V targetEnv) :
    PublicValueModel V sourceEnv :=
  (checkInstalledDefinitions_sound target (checkTelescopes_sound receipt.telescopes) receipt.definitions).valueModel
    (checkedPullbackTypes target receipt.telescopes receipt.types receipt.falsePin receipt.eqPin)
    (PullbackMap.fromEnvs_locality (checkTelescopes_sound receipt.telescopes))

theorem InstalledAssociation.public_laws {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (receipt : InstalledAssociation sourceEnv targetEnv names) (target : StrongInstalledModel V targetEnv)
    (sourceWf : Kernel.EnvWF sourceEnv) :
    PublicCapabilityLaws (receipt.valueModel target).model.cval sourceEnv ∧
      UniversalRuleSimulation target sourceEnv names :=
  ⟨checkedCapabilities_publicLaws sourceWf target (checkTelescopes_sound receipt.telescopes)
      receipt.types receipt.capabilities receipt.etaAssociations,
    checked_universal_rules sourceWf target (checkTelescopes_sound receipt.telescopes)
      receipt.types receipt.recursors receipt.constructors receipt.levelLinks⟩

/-- Source coverage and the original compiler artifact share one checked
support interpretation. Two unrelated existential target models would not
justify this composition. Original constants retain literally the target
model's values at the same assignments, while source values use their exact
checked name/telescope map. Full original annotation/normalization remains
outside this installed-stream theorem. -/
theorem SourceConstructorCoverChecked.combined_publicModels (V : Type u) [Kernel.SetTheory V]
    {input : Input} {installed : SourceNormalizedInstallation input.source input.roots}
    {site : SourceProjectionSite input.source} (coverage : SourceConstructorCoverChecked installed site)
    (accepted : AcceptedAssociation input) {support : Array Kernel.Declaration}
    (bundle : AdmittedSupport accepted.toAdmittedArtifact support) (names : Kernel.Name → Kernel.Name)
    (checked : checkSupportedArtifactInstalledAssociation accepted bundle coverage.env names = some true)
    (identityChecked : checkInstalledAssociation accepted.env bundle.env id = some true) :
    SemanticNamesAgree accepted names ∧
    ∃ (target : StrongInstalledModel V bundle.env) (source : PublicValueModel V coverage.env)
      (original : PublicValueModel V accepted.env),
      source.model.cval = (PullbackMap.fromEnvs coverage.env bundle.env names).values target.public.cval ∧
      (∀ name entry, accepted.env.find? name = some entry → ∀ levels,
        original.model.cval name levels = target.public.cval name levels) ∧
      (∀ name entry, accepted.env.find? (names name) = some entry → ∀ levels,
        source.model.cval name levels = original.model.cval (names name)
          ((PullbackMap.fromEnvs coverage.env bundle.env names).levels name levels)) ∧
      PublicCapabilityLaws source.model.cval coverage.env ∧
      PublicCapabilityLaws original.model.cval accepted.env ∧
      UniversalRuleSimulation target coverage.env names ∧ UniversalRuleSimulation target accepted.env id := by
  obtain ⟨nameCheck, sourceChecked⟩ := bothChecks_true checked
  have sourceReceipt := checkInstalledAssociation_sound sourceChecked
  have originalReceipt := checkInstalledAssociation_sound identityChecked
  obtain ⟨target⟩ := bundle.strong_model V
  obtain ⟨sourceStrong⟩ := coverage.strong_model V
  obtain ⟨originalStrong⟩ := accepted.toAdmittedArtifact.strong_model V
  let source := sourceReceipt.valueModel target
  let original := originalReceipt.valueModel target
  have sourceLaws := sourceReceipt.public_laws target sourceStrong.internal.base2.wf
  have originalLaws := originalReceipt.public_laws target originalStrong.internal.base2.wf
  refine ⟨of_decide_eq_true (Option.some.inj nameCheck), target, source, original, rfl, ?_, ?_,
    sourceLaws.1, originalLaws.1, sourceLaws.2, originalLaws.2⟩
  · intro name entry lookup levels
    exact bundle.original_value target.public.cval lookup levels
  · intro name entry lookup levels
    exact (bundle.original_value target.public.cval lookup
      ((PullbackMap.fromEnvs coverage.env bundle.env names).levels name levels)).symm

open Kernel.SetTheory in
/-- The projection value in the original compiler artifact's interpretation,
not merely its support extension, equals the source-only field selector.
Both interpretations are constructed from the same target witness. Exact
original target lookup is required; a fresh support helper cannot impersonate
the compiled projection. This is a local value theorem, not full D11 or S. -/
theorem SourceProjectionFunction.original_artifact_value {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    {receipt : SourceProjectionInstalled projection constructor}
    (function : SourceProjectionFunction receipt)
    {input : ArtifactInput} {artifact : AdmittedArtifact input} {support : Array Kernel.Declaration}
    (bundle : AdmittedSupport artifact support) (target : StrongInstalledModel V bundle.env)
    (originalReceipt : InstalledAssociation artifact.env bundle.env id)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation coverage.env bundle.env names)
    (types : checkInstalledTypes coverage.env bundle.env names = true)
    (model : Kernel.Model V coverage.env)
    (values : model.cval = (PullbackMap.fromEnvs coverage.env bundle.env names).values target.public.cval)
    {originalTarget : Kernel.ConstantInfo}
    (originalLookup : artifact.env.find? (names projection.header.name) = some originalTarget)
    (frame : InstalledEquationFrame bundle.env (names receipt.data.equation.name)
      (projection.site.owner.numParams + projection.site.ctor.numFields))
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = projection.site.owner.numParams)
    (parameterTyping : InstalledTelescope model.cval coverage.env levels ρ constructor.data.owner.type
      parameters (pushArguments ρ parameters) (.sort constructor.data.level)) :
    parameters.foldl app ((originalReceipt.valueModel target).model.cval (names projection.header.name)
      ((PullbackMap.fromEnvs coverage.env bundle.env names).levels projection.header.name levels)) =
      Kernel.SetModel.lamR (Kernel.regime levels function.data.binder.pw)
        (parameters.foldl app (model.cval (sourceName projection.site.ownerName) levels))
        (originalProjectionSelection projection.site model.cval levels parameters
          (SourceCoverValidFields constructor model levels ρ parameters)) := by
  have same : (originalReceipt.valueModel target).model.cval (names projection.header.name)
      ((PullbackMap.fromEnvs coverage.env bundle.env names).levels projection.header.name levels) =
      model.cval projection.header.name levels := by
    rw [values]
    exact bundle.original_value target.public.cval originalLookup _
  rw [same]
  exact function.value_eq_pullback target association types model values frame levels ρ
    parameters parameterCount parameterTyping

/-- A source-only public fired-rule law. The fresh argument representation is
fixed by the source semantic tuple; no target frame, target model, target
universe check or target annotation object occurs in this proposition.
Typing, universe selection and ordinary/nested/index guards are the source
rule's actual firing premises, not restrictions of compiler Dom. -/
def PublicRecursorLaws {V : Type u} [Kernel.SetTheory V]
    (values : Kernel.Name → (Kernel.Name → Nat) → V) (env : Kernel.Env) : Prop :=
  ∀ name index (frame : InstalledRuleFrame env name index) levels universes constructorUniverses,
    RuleUniverseSelection frame levels universes constructorUniverses →
    ∀ valuation arguments fields,
      RuleTupleTyping values env levels frame universes constructorUniverses valuation arguments fields →
      let depth := (arguments ++ fields).length
      let fresh := pushArguments valuation (arguments ++ fields)
      let argumentExpressions := (argumentVariables depth).take arguments.length
      let fieldExpressions := (argumentVariables depth).drop arguments.length
      SourceRuleComparisons values env levels frame universes constructorUniverses fresh
        argumentExpressions fieldExpressions arguments fields →
      ∃ value, Kernel.Denotes values env levels fresh
          (Kernel.Expr.mkAppN (.const name universes)
            (argumentExpressions ++ [Kernel.Expr.mkAppN (.const frame.rule.ctor constructorUniverses) fieldExpressions])) value ∧
        Kernel.Denotes values env levels fresh
          (Kernel.Expr.mkAppN (frame.rule.rhs.instantiateLevelParams frame.header.levelParams universes)
            (argumentExpressions.take frame.rulePrefix ++ fieldExpressions.drop frame.rule.ctorParams)) value

theorem checked_public_recursors {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (sourceWf : Kernel.EnvWF sourceEnv)
    (target : StrongInstalledModel V targetEnv) {names : Kernel.Name → Kernel.Name}
    (association : TelescopeAssociation sourceEnv targetEnv names)
    (types : checkInstalledTypes sourceEnv targetEnv names = true)
    (recursors : checkInstalledRecursors sourceEnv targetEnv names = true)
    (constructors : checkInstalledConstructors sourceEnv targetEnv names = true)
    (levelLinks : checkInstalledRuleLevelLinks sourceEnv targetEnv names = some true) :
    PublicRecursorLaws ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval) sourceEnv := by
  intro name index sourceFrame levels universes constructorUniverses sourceSelection valuation arguments fields typed
  dsimp only
  intro conditions
  obtain ⟨targetFrame, _, _, _, _, _, images⟩ := sourceFrame.checked_target target association recursors constructors
  have selection := sourceFrame.transfer_selection target association recursors targetFrame
    (checkInstalledRuleLevelLinks_frame levelLinks sourceFrame) sourceSelection rfl rfl
  have targetTyped := sourceFrame.checked_tuple_typing target association types targetFrame (images (fun _ => 0)).header
    levels levels universes universes constructorUniverses constructorUniverses
    sourceSelection.recursorArity selection.recursorArity sourceSelection.constructorArity selection.constructorArity
    rfl rfl typed
  obtain ⟨representation, depthEq, valuationEq⟩ := targetTyped.represented_exact
  obtain ⟨_, _, constructorTyped⟩ := typed.constructorTyped
  have fired := representation.checked_fired sourceWf association types recursors sourceFrame selection levels
    universes constructorUniverses sourceSelection.recursorArity sourceSelection.constructorArity
    rfl rfl constructorTyped (by simpa only [depthEq, valuationEq] using conditions)
  simpa only [depthEq, valuationEq] using fired

/-- Public source interpretation with definition values and actual source
capability/recursor laws. This is not the internal `EnvModelM`: annotation
validity and original-source D11 are not hidden fields or inferred facts. -/
structure PublicSemanticModel (V : Type u) [Kernel.SetTheory V] (env : Kernel.Env)
    extends PublicValueModel V env where
  capabilities : PublicCapabilityLaws model.cval env
  recursors : PublicRecursorLaws model.cval env

noncomputable def InstalledAssociation.semanticModel {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (receipt : InstalledAssociation sourceEnv targetEnv names) (target : StrongInstalledModel V targetEnv)
    (sourceWf : Kernel.EnvWF sourceEnv) : PublicSemanticModel V sourceEnv where
  toPublicValueModel := receipt.valueModel target
  capabilities := (receipt.public_laws target sourceWf).1
  recursors := checked_public_recursors sourceWf target (checkTelescopes_sound receipt.telescopes)
    receipt.types receipt.recursors receipt.constructors receipt.levelLinks

/-- Both verified folds supply their own installation premises. The returned
source public model contains source-only recursor laws, not an existential
target representation interface. Full source/reader/domain composition is
still outside this theorem. -/
theorem checkedStreams_publicSemanticModel (V : Type u) [Kernel.SetTheory V]
    (sourcePins targetPins : List Kernel.NatOpPinSet)
    (sourceDecls targetDecls : Array Kernel.Declaration)
    {sourceEnv targetEnv : Kernel.Env} (names : Kernel.Name → Kernel.Name)
    (sourceChecked : Kernel.Cached.checkDecls .verified sourcePins sourceDecls = .ok sourceEnv)
    (targetChecked : Kernel.Cached.checkDecls .verified targetPins targetDecls = .ok targetEnv)
    (checked : checkInstalledAssociation sourceEnv targetEnv names = some true) :
    Nonempty (StrongInstalledModel V sourceEnv) ∧
    ∃ (target : StrongInstalledModel V targetEnv) (source : PublicSemanticModel V sourceEnv),
      source.model.cval = (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval := by
  obtain ⟨sourceStrong⟩ := strongInstalledModel_exists V sourcePins sourceDecls sourceEnv sourceChecked
  obtain ⟨target⟩ := strongInstalledModel_exists V targetPins targetDecls targetEnv targetChecked
  exact ⟨⟨sourceStrong⟩, target,
    (checkInstalledAssociation_sound checked).semanticModel target sourceStrong.internal.base2.wf, rfl⟩

/-- Public semantic interpretations of the independently installed normalized
source and the original admitted artifact, both pulled back from one actual
support interpretation. Each contains its own source-only capability and
recursor laws. The two checked associations remain explicit executable
premises; structural row preservation alone is not semantic conservativity.
This does not identify either interpretation with an independently chosen
source model or discharge immutable-original normalization/annotation D11. -/
theorem SourceConstructorCoverChecked.combined_publicSemanticModels
    (V : Type u) [Kernel.SetTheory V]
    {input : Input} {installed : SourceNormalizedInstallation input.source input.roots}
    {site : SourceProjectionSite input.source} (coverage : SourceConstructorCoverChecked installed site)
    (accepted : AcceptedAssociation input) {support : Array Kernel.Declaration}
    (bundle : AdmittedSupport accepted.toAdmittedArtifact support) (names : Kernel.Name → Kernel.Name)
    (checked : checkSupportedArtifactInstalledAssociation accepted bundle coverage.env names = some true)
    (identityChecked : checkInstalledAssociation accepted.env bundle.env id = some true) :
    SemanticNamesAgree accepted names ∧
    ∃ (target : StrongInstalledModel V bundle.env) (source : PublicSemanticModel V coverage.env)
      (original : PublicSemanticModel V accepted.env),
      source.model.cval = (PullbackMap.fromEnvs coverage.env bundle.env names).values target.public.cval ∧
      (∀ name entry, accepted.env.find? name = some entry → ∀ levels,
        original.model.cval name levels = target.public.cval name levels) ∧
      (∀ name entry, accepted.env.find? (names name) = some entry → ∀ levels,
        source.model.cval name levels = original.model.cval (names name)
          ((PullbackMap.fromEnvs coverage.env bundle.env names).levels name levels)) := by
  obtain ⟨nameCheck, sourceChecked⟩ := bothChecks_true checked
  have sourceReceipt := checkInstalledAssociation_sound sourceChecked
  have originalReceipt := checkInstalledAssociation_sound identityChecked
  obtain ⟨target⟩ := bundle.strong_model V
  obtain ⟨sourceStrong⟩ := coverage.strong_model V
  obtain ⟨originalStrong⟩ := accepted.toAdmittedArtifact.strong_model V
  let source := sourceReceipt.semanticModel target sourceStrong.internal.base2.wf
  let original := originalReceipt.semanticModel target originalStrong.internal.base2.wf
  refine ⟨of_decide_eq_true (Option.some.inj nameCheck), target, source, original, rfl, ?_, ?_⟩
  · intro name entry lookup levels
    exact bundle.original_value target.public.cval lookup levels
  · intro name entry lookup levels
    exact (bundle.original_value target.public.cval lookup
      ((PullbackMap.fromEnvs coverage.env bundle.env names).levels name levels)).symm

/-- Exact original bindings take priority over separately proposed generated
helpers. This is only a name proposal; the installed association checker still
checks every source row and every compatible alias fiber. -/
def sourceAndHelperNames (original helpers : List (Kernel.Name × Kernel.Name))
    (name : Kernel.Name) : Kernel.Name :=
  match original.find? (fun pair => decide (pair.1 = name)) with
  | some pair => pair.2
  | none => match helpers.find? (fun pair => decide (pair.1 = name)) with
    | some pair => pair.2
    | none => name

theorem sourceAndHelperNames_original (original helpers : List (Kernel.Name × Kernel.Name))
    (name : Kernel.Name) (pair : Kernel.Name × Kernel.Name)
    (found : original.find? (fun pair => decide (pair.1 = name)) = some pair) :
    sourceAndHelperNames original helpers name = pair.2 := by
  simp [sourceAndHelperNames, found]

/-- Apply a known generated-family anchor to its suffix. The caller enumerates
the finite source-generated records first; this does not authorize arbitrary
ambient names merely because they have a familiar prefix. -/
def renameGeneratedSuffix (anchors : List (Kernel.Name × Kernel.Name))
    (name : Kernel.Name) : Option Kernel.Name :=
  match anchors.find? (fun pair => decide (pair.1 = name)) with
  | some pair => some pair.2
  | none => match name with
    | .anonymous => none
    | .str parent component => (renameGeneratedSuffix anchors parent).map (·.str component)
    | .num parent component => (renameGeneratedSuffix anchors parent).map (·.num component)

/-- Untrusted, finite helper-name proposal from the independently generated
source model stream and its original block evidence. Auxiliary constructors
use the modeller's exact owner/member/constructor naming recipe, rather than
assuming that an address-labelled constructor keeps its source last component.
No target environment is searched. Installation order, target helper existence,
kind, telescope, values, capabilities and rules remain checked separately.
This generator is not a totality or model-correspondence theorem. -/
def proposeSourceHelperBindings {source : Source} (proposal : SourceModelProposal source)
    (original : List (Kernel.Name × Kernel.Name)) : ExportM (List (Kernel.Name × Kernel.Name)) := do
  let mapped := sourceAndHelperNames original []
  let mut anchors := original.map fun (sourceName, targetName) =>
    (sourceName.str "_model", targetName.str "_model")
  let mut projections := []
  for evidence in proposal.blocks do
    let block := evidence.shape
    if !Kernel.Frontend.InModel.wants block then continue
    let some owner := block.types.head? | throw "source helper recipe has no owner"
    let some recursor := block.recs.find? (fun r => r.cv.name == owner.cv.name.str "rec")
      | throw "source helper recipe has no primary recursor"
    let some (_, afterParams) := recursor.cv.type.stripPis owner.nP
      | throw "source helper recipe parameter telescope"
    let some (motives, _) := afterParams.stripPis recursor.nM
      | throw "source helper recipe motive telescope"
    let members ← Kernel.Frontend.InModel.readMems owner.cv.levelParams owner.nP
      block.types (motives.map (·.1))
    for member in members do
      let recursorName ← match member.real? with
        | some index => match block.types[index]? with
          | some type => pure (type.cv.name.str "rec")
          | none => throw "source helper recipe member index"
        | none => pure (owner.cv.name.str s!"rec_{member.j + 1}")
      let some memberRecursor := block.recs.find? (fun r => r.cv.name == recursorName)
        | throw "source helper recipe member recursor"
      for rule in memberRecursor.rules do
        anchors := (Kernel.Frontend.InModel.auxCtorName owner.cv.name member.tag rule.ctor,
          Kernel.Frontend.InModel.auxCtorName (mapped owner.cv.name) member.tag (mapped rule.ctor)) :: anchors
    for type in block.types do
      for constructorName in type.ctors do
        let some constructor := block.ctors.find? (fun c => c.cv.name == constructorName)
          | throw "source helper recipe constructor"
        for index in List.range constructor.nF do
          projections := (Kernel.projFnName type.cv.name index,
            Kernel.projFnName (mapped type.cv.name) index) :: projections
  -- Reject conflicting source keys; compatible many-to-one target fibers are
  -- deliberately retained for the full per-row association checks.
  for pair in anchors do
    unless anchors.all (fun other => other.1 != pair.1 || other.2 == pair.2) do
      throw "conflicting source helper recipe bindings"
  let generated := proposal.declarations.toList.flatMap Kernel.Declaration.names
  return projections ++ generated.filterMap (fun name =>
    (renameGeneratedSuffix anchors name).map (name, ·))

end Ix.CompileCert
