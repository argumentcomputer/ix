import Ix.CompileCert.AnnotEntry

/-! Same-carrier assembly for the remaining strong-model laws. In particular,
the actual instantiated source type and target type share one annotated
reading; no erased-denotation equality is substituted for grading. -/
namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics

theorem AnnotatedAssociation.instantiated_type {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : AnnotatedAssociation source target names)
    (sourceFacts : EnvModel V source) (targetModel : StrongInstalledModel V target)
    (entry : Kernel.ConstantInfo) (present : entry ∈ source.consts)
    (levels : Kernel.Name → Nat) (universes : List Kernel.Level) :
    ∃ targetEntry, target.find? (names entry.name) = some targetEntry ∧
    ∃ annotation,
      denoteMeta (checked.modelCore sourceFacts targetModel).base.acval source levels 0
        (entry.toConstantVal.type.instantiateLevelParams entry.toConstantVal.levelParams universes) =
          some annotation ∧
      denoteMeta targetModel.internal.base2.acval target
        ((PullbackMap.fromEnvs source target names).levels entry.name
          (Kernel.Level.substFn levels entry.toConstantVal.levelParams universes)) 0
        targetEntry.toConstantVal.type = some annotation ∧
      ∀ ρ : Nat → V, WellDenotedV V ρ annotation := by
  obtain ⟨lookup, targetEntry, targetLookup, comparison⟩ :=
    checkInstalledTypes_member checked.installed.types present
  obtain ⟨annotation, reading⟩ := targetModel.internal.type_reads targetEntry
    (Kernel.Semantics.Env.find?_mem targetLookup)
    ((PullbackMap.fromEnvs source target names).levels entry.name
      (Kernel.Level.substFn levels entry.toConstantVal.levelParams universes))
  refine ⟨targetEntry, targetLookup, annotation, ?_, reading, ?_⟩
  · rw [denotePInstLevels]
    exact (checkInstalledMemberExpr_annotated_reading_local targetModel
      (checkTelescopes_sound checked.installed.telescopes) lookup
      (List.all_eq_true.mp checked.types entry present) comparison _ 0).trans reading
  · exact targetModel.internal.type_wellDenotedV targetEntry
      (Kernel.Semantics.Env.find?_mem targetLookup) _ annotation reading

/-- Owner-relative helper checks identify the exact annotated leaves, not
only their erased values. Each helper retains its own source telescope. -/
theorem checkInstalledFamilyMember_annotations {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} (targetModel : StrongInstalledModel V target)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation source target names)
    {owner member : Kernel.Name} {sourceOwner targetOwner : Kernel.ConstantInfo}
    (sourceLookup : source.find? owner = some sourceOwner)
    (targetLookup : target.find? (names owner) = some targetOwner)
    (checked : checkInstalledFamilyMember source target names owner member = some true)
    (levels : Kernel.Name → Nat) :
    (PullbackMap.fromEnvs source target names).annotations targetModel.internal.base2.acval member levels =
      targetModel.internal.base2.acval (names member)
        ((PullbackMap.fromEnvs source target names).levels owner levels) := by
  obtain ⟨sourceMember, targetMember, sourceMemberLookup, targetMemberLookup, _, compared⟩ :=
    checkInstalledFamilyMember_lookups targetLookup checked
  have reading := checkInstalledMemberExpr_annotated_reading_local targetModel association sourceLookup
    (by rfl) compared levels 0
  rw [denoteMeta_const sourceMemberLookup (by simp),
    denoteMeta_const targetMemberLookup (by simp)] at reading
  simpa only [Kernel.Level.substFn_param_self] using Option.some.inj reading

open Kernel.SetTheory in
/-- The complete unit capability law on the same pulled annotated carrier.
The target's exact type reading preserves TeleFit without rebuilding a
syntactic argument representation. Reserved target PUnit uses its installed
basis law; no target-name exclusion is added to the executable contract. -/
theorem AnnotatedAssociation.unit_law {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : AnnotatedAssociation source target names)
    (sourceFacts : EnvModel V source) (targetModel : StrongInstalledModel V target)
    {name : Kernel.Name} {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (lookup : source.find? name = some (.indInfo header caps))
    (enabled : caps.unitlike = true) (levels : Kernel.Name → Nat) :
    UnitLaw (checked.modelCore sourceFacts targetModel).base levels name header caps := by
  have named := Kernel.Semantics.Env.find?_name lookup
  change header.name = name at named
  subst name
  have present := Kernel.Semantics.Env.find?_mem lookup
  obtain ⟨_, targetHeader, targetCaps, targetLookup, headers, _⟩ :=
    checkInstalledCapabilities_member checked.installed.capabilities present
  intro universes arity
  obtain ⟨targetEntry, entryLookup, annotation, sourceRead, targetRead, graded⟩ :=
    checked.instantiated_type sourceFacts targetModel (.indInfo header caps) present levels universes
  have same := Option.some.inj (entryLookup.symm.trans targetLookup)
  subst targetEntry
  let targetLevels := (PullbackMap.fromEnvs source target names).levels header.name
    (Kernel.Level.substFn levels header.levelParams universes)
  have targetEnabled : targetCaps.unitlike = true := headers.2.1.symm.trans enabled
  have leaf : (checked.modelCore sourceFacts targetModel).base.acval header.name
      (Kernel.Level.substFn levels header.levelParams universes) =
      targetModel.internal.base2.acval (names header.name) targetLevels := rfl
  refine ⟨annotation, sourceRead, graded, ?_⟩
  intro ρ arguments rest x y count fit left right
  have targetCount : arguments.length = targetCaps.unitParams :=
    count.trans headers.2.2.2.2.2.1
  by_cases reserved : Kernel.reservedBasisNames.contains (names header.name) = true
  · apply targetModel.reserved_unit targetLookup reserved targetEnabled targetLevels
      arguments targetCount x y
    · simpa only [leaf, interp_cvalOf targetModel.internal.base2.cval_closedL,
        StrongInstalledModel.public, Kernel.Model.Model.ofEnvModelM] using left
    · simpa only [leaf, interp_cvalOf targetModel.internal.base2.cval_closedL,
        StrongInstalledModel.public, Kernel.Model.Model.ofEnvModelM] using right
  · have nonbasis : Kernel.reservedBasisNames.contains (names header.name) = false := by
      simpa using reserved
    obtain ⟨actual, actualRead, _, law⟩ := targetModel.internal.caps_ok.2
      (names header.name) targetHeader targetCaps targetLookup targetEnabled nonbasis
      targetLevels (targetHeader.levelParams.map Kernel.Level.param) (by simp)
    rw [denotePInstLevels, Kernel.Level.substFn_param_self] at actualRead
    have sameAnnotation : annotation = actual := Option.some.inj (targetRead.symm.trans actualRead)
    subst actual
    apply law ρ arguments rest x y targetCount fit
    · simpa only [leaf, Kernel.Level.substFn_param_self] using left
    · simpa only [leaf, Kernel.Level.substFn_param_self] using right

open Kernel.SetTheory in
/-- Full annotated eta capability, including exact owner-relative helper
leaves and the reserved target branch, from the current finite association. -/
theorem AnnotatedAssociation.eta_law {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : AnnotatedAssociation source target names)
    (sourceFacts : EnvModel V source) (targetModel : StrongInstalledModel V target)
    {name : Kernel.Name} {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (lookup : source.find? name = some (.indInfo header caps))
    (enabled : caps.eta = true) (levels : Kernel.Name → Nat) :
    EtaLaw (checked.modelCore sourceFacts targetModel).base levels name header caps := by
  have named := Kernel.Semantics.Env.find?_name lookup
  change header.name = name at named
  subst name
  have present := Kernel.Semantics.Env.find?_mem lookup
  obtain ⟨_, targetHeader, targetCaps, targetLookup, headers, _⟩ :=
    checkInstalledCapabilities_member checked.installed.capabilities present
  obtain ⟨family, constructor, projections⟩ :=
    checkInstalledEtaAssociations_sound checked.installed.etaAssociations present enabled
  intro universes arity
  obtain ⟨targetEntry, entryLookup, annotation, sourceRead, targetRead, graded⟩ :=
    checked.instantiated_type sourceFacts targetModel (.indInfo header caps) present levels universes
  have same := Option.some.inj (entryLookup.symm.trans targetLookup)
  subst targetEntry
  let sourceLevels := Kernel.Level.substFn levels header.levelParams universes
  let targetLevels := (PullbackMap.fromEnvs source target names).levels header.name sourceLevels
  have targetEnabled : targetCaps.eta = true := headers.1.symm.trans enabled
  have leaf : (checked.modelCore sourceFacts targetModel).base.acval header.name sourceLevels =
      targetModel.internal.base2.acval (names header.name) targetLevels := rfl
  have namedHelpers := headers.2.2.2.2.2.2 enabled
  have ctorLeaf := checkInstalledFamilyMember_annotations targetModel
    (checkTelescopes_sound checked.installed.telescopes) lookup targetLookup constructor sourceLevels
  rw [← namedHelpers.1] at ctorLeaf
  refine ⟨annotation, sourceRead, graded, ?_⟩
  intro ρ arguments rest x count fit member
  have targetCount : arguments.length = targetCaps.etaParams := count.trans headers.2.2.2.1
  have spineImage := etaFabArgsV_image
    (source := fun n => interp V ρ ((checked.modelCore sourceFacts targetModel).base.acval n sourceLevels))
    (target := fun n => interp V ρ (targetModel.internal.base2.acval n targetLevels))
    (sourceOwner := header.name) (targetOwner := names header.name) arguments x caps.etaFields
    (fun index bound => by
      have image := checkInstalledFamilyMember_annotations targetModel
        (checkTelescopes_sound checked.installed.telescopes) lookup targetLookup
        (projections index bound) sourceLevels
      rw [namedHelpers.2 index bound] at image
      exact congrArg (interp V ρ) image)
  change x = (etaFabArgsV
    (fun n => interp V ρ ((checked.modelCore sourceFacts targetModel).base.acval n sourceLevels))
    header.name arguments x caps.etaFields).foldl app
    (interp V ρ ((checked.modelCore sourceFacts targetModel).base.acval caps.etaCtor sourceLevels))
  rw [spineImage, show (checked.modelCore sourceFacts targetModel).base.acval caps.etaCtor sourceLevels =
    targetModel.internal.base2.acval targetCaps.etaCtor targetLevels from ctorLeaf,
    headers.2.2.2.2.1]
  rw [leaf] at member
  by_cases reserved : Kernel.reservedBasisNames.contains (names header.name) = true
  · obtain ⟨_, constructorEntry, _, constructorLookup, _⟩ :=
      checkInstalledFamilyMember_lookups targetLookup constructor
    rw [← namedHelpers.1] at constructorLookup
    have targetMember : x ∈ˢ arguments.foldl app
        (targetModel.public.cval (names header.name) targetLevels) := by
      simpa only [interp_cvalOf targetModel.internal.base2.cval_closedL,
        StrongInstalledModel.public, Kernel.Model.Model.ofEnvModelM] using member
    have law := targetModel.reserved_eta targetLookup reserved targetEnabled
      ⟨constructorEntry, constructorLookup⟩ targetLevels arguments targetCount x targetMember
    simpa only [interp_cvalOf targetModel.internal.base2.cval_closedL,
      StrongInstalledModel.public, Kernel.Model.Model.ofEnvModelM] using law
  · have nonbasis : Kernel.reservedBasisNames.contains (names header.name) = false := by
      simpa using reserved
    have stored := (checkInstalledEtaAt_sound targetLookup family).resolve_left reserved
    obtain ⟨actual, actualRead, _, law⟩ := targetModel.internal.caps_ok.1
      (names header.name) targetHeader targetCaps targetLookup targetEnabled nonbasis stored
      targetLevels (targetHeader.levelParams.map Kernel.Level.param) (by simp)
    rw [denotePInstLevels, Kernel.Level.substFn_param_self] at actualRead
    have sameAnnotation : annotation = actual := Option.some.inj (targetRead.symm.trans actualRead)
    subst actual
    have result := law ρ arguments rest x targetCount fit
    simp only [Kernel.Level.substFn_param_self] at result
    exact result member

theorem AnnotatedAssociation.caps_ok {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : AnnotatedAssociation source target names)
    (sourceFacts : EnvModel V source) (targetModel : StrongInstalledModel V target) :
    CapsOk (checked.modelCore sourceFacts targetModel).base := by
  constructor
  · intro name header caps lookup enabled _ _ levels
    exact checked.eta_law sourceFacts targetModel lookup enabled levels
  · intro name header caps lookup enabled _ levels
    exact checked.unit_law sourceFacts targetModel lookup enabled levels

/-- The existing artifact check now supplies the full capability field on
its exact target-derived source core. No additional acceptance guard appears. -/
theorem SourceConstructorCoverChecked.annotated_modelCore_caps (V : Type u) [Kernel.SetTheory V]
    {input : Input} {installed : SourceNormalizedInstallation input.source input.roots}
    {site : SourceProjectionSite input.source} (coverage : SourceConstructorCoverChecked installed site)
    (accepted : AcceptedAssociation input) {support : Array Kernel.Declaration}
    (bundle : AdmittedSupport accepted.toAdmittedArtifact support) (names : Kernel.Name → Kernel.Name)
    (checked : checkSupportedArtifactAnnotatedAssociation accepted bundle coverage.env names = some true) :
    SemanticNamesAgree accepted names ∧
      ∃ targetModel : StrongInstalledModel V bundle.env,
      ∃ core : AnnotatedModelCore V coverage.env,
        core.base.acval = (PullbackMap.fromEnvs coverage.env bundle.env names).annotations
          targetModel.internal.base2.acval ∧ CapsOk core.base := by
  obtain ⟨original, annotated⟩ := bothChecks_true checked
  obtain ⟨nameCheck, _⟩ := bothChecks_true original
  obtain ⟨sourceModel⟩ := coverage.strong_model V
  obtain ⟨targetModel⟩ := bundle.strong_model V
  have association := checkAnnotatedAssociation_sound annotated
  exact ⟨of_decide_eq_true (Option.some.inj nameCheck), targetModel,
    association.modelCore sourceModel.internal.base2 targetModel, rfl,
    association.caps_ok sourceModel.internal.base2 targetModel⟩

end Ix.CompileCert
