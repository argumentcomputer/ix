import Ix.CompileCert.AnnotRuleFit
import Ix.CompileCert.AnnotRulePins

namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics

/-- The full annotated fired-rule law on the pulled source carrier. The
source's semantic firing premises are transported to the selected actual
target rule, rather than replaced by extra checker acceptance premises. -/
theorem AnnotatedAssociation.rec_rule {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (association : AnnotatedAssociation source target names)
    (sourceModel : StrongInstalledModel V source) (targetModel : StrongInstalledModel V target)
    {name : Kernel.Name} {header : Kernel.ConstantVal} {major rulePrefix : Nat} {rules : List Kernel.RecRule}
    (lookup : source.find? name = some (.recInfo header major rulePrefix rules))
    {index : Nat} {rule : Kernel.RecRule} (selected : rules[index]? = some rule)
    (fires : rule.fire ≠ .inert) (levels : Kernel.Name → Nat) :
    RecRuleLaw (association.modelCore sourceModel.internal.base2 targetModel).base levels
      name header major rulePrefix rule := by
  have sourceLaw := sourceModel.internal.rec_rules levels name header major rulePrefix rules lookup rule
    (List.mem_of_getElem? selected) fires
  have present := Kernel.Semantics.Env.find?_mem lookup
  refine ⟨sourceLaw.1, ?_⟩
  intro universes arity
  obtain ⟨_, _, _, _, _, _, annotation, sourceRead, _, graded⟩ :=
    association.rule_rhs sourceModel targetModel present selected fires levels universes
  refine ⟨annotation, sourceRead, graded, ?_, ?_⟩
  · intro nestedLevels pins nested pinIndex below
    exact association.nested_pin sourceModel targetModel present selected nested pinIndex below levels universes
  · intro constructor constructorParams constructorFields constructorLookup constructorUniverses ρ xs ys
      typeRec typeCtor restRec restCtor xsCount ysCount ctorArity assignment plainParameters nestedParameters
      indexPin recRead ctorRead recFit ctorFit
    let sourceFrame : InstalledRuleFrame source name index := {
      header := header, major := major, rulePrefix := rulePrefix, rules := rules, rule := rule,
      constructor := constructor, constructorParams := constructorParams, constructorFields := constructorFields,
      recursorLookup := lookup, ruleLookup := selected, fires := fires, constructorLookup := constructorLookup }
    have telescopes := checkTelescopes_sound association.installed.telescopes
    obtain ⟨targetFrame, _, targetMajor, targetPrefix, _, _, images⟩ := sourceFrame.checked_target targetModel
      telescopes association.installed.recursors association.installed.constructors
    have headers := (images (fun _ => 0)).header
    have sourceSelection : RuleUniverseSelection sourceFrame levels universes constructorUniverses :=
      ⟨arity, ctorArity, assignment⟩
    obtain ⟨targetSelection, targetRecRead, targetCtorRead, targetRecFit, targetCtorFit⟩ :=
      sourceFrame.annotated_teleFit association sourceModel.internal.base2 targetModel targetFrame levels levels
        universes universes constructorUniverses constructorUniverses sourceSelection rfl rfl
        ρ xs ys typeRec typeCtor restRec restCtor recRead ctorRead recFit ctorFit
    have targetLaw := targetModel.internal.rec_rules levels (names name) targetFrame.header targetFrame.major
      targetFrame.rulePrefix targetFrame.rules targetFrame.recursorLookup targetFrame.rule
      (List.mem_of_getElem? targetFrame.ruleLookup) targetFrame.fires
    obtain ⟨targetAnnotation, targetRead, _, _, targetFired⟩ := targetLaw.2 universes targetSelection.recursorArity
    have rhsImage := sourceFrame.annotated_rhs_instance association sourceModel targetModel targetFrame
      levels levels universes universes arity targetSelection.recursorArity rfl
    have sameAnnotation : targetAnnotation = annotation :=
      Option.some.inj (targetRead.symm.trans (rhsImage.symm.trans sourceRead))
    subst targetAnnotation
    have comparisons := sourceFrame.checked_comparisons association.installed.recursors targetFrame
    have targetPlain : targetFrame.rule.paramsBlind = false → targetFrame.rule.fire = .plain →
        ∀ i, i < targetFrame.rule.ctorParams → i < targetFrame.major →
          interp V ρ (ys.getD i default) = interp V ρ (xs.getD i default) := by
      intro blind plain i below majorBound
      have sourcePlain : rule.fire = .plain := by
        have fireCheck := comparisons.2.1
        change checkInstalledFire source target names name rule.fire targetFrame.rule.fire = some true at fireCheck
        rw [plain] at fireCheck
        cases shape : rule.fire <;> simp [checkInstalledFire, shape] at fireCheck ⊢
      apply plainParameters (headers.2.2.2.2.2.trans blind) sourcePlain i
      · exact headers.2.2.1 ▸ below
      · simpa only [targetMajor] using majorBound
    have targetNested : ∀ lvls pins, targetFrame.rule.fire = .nested lvls pins →
        ∀ i, i < targetFrame.rule.ctorParams → ∀ pinAnnotation,
          denoteMeta targetModel.internal.base2.acval target levels targetFrame.rulePrefix
            (Kernel.Verify.openRev 0 targetFrame.rulePrefix
              ((pins.getD i default).instantiateLevelParams targetFrame.header.levelParams universes)) = some pinAnnotation →
          interp V ρ (ys.getD i default) =
            interp V ρ (AnnotTerm.instRevChain (xs.take targetFrame.rulePrefix) pinAnnotation) := by
      intro targetLevels targetPins targetNested i targetBelow pinAnnotation targetPinRead
      have fireCheck := comparisons.2.1
      change checkInstalledFire source target names name rule.fire targetFrame.rule.fire = some true at fireCheck
      rw [targetNested] at fireCheck
      obtain ⟨sourceLevels, sourcePins, sourceNested⟩ :
          ∃ ls ps, rule.fire = .nested ls ps := by
        cases shape : rule.fire with
        | inert => simp [checkInstalledFire, shape] at fireCheck
        | plain => simp [checkInstalledFire, shape] at fireCheck
        | nested ls ps => exact ⟨ls, ps, rfl⟩
      have below : i < rule.ctorParams := headers.2.2.1 ▸ targetBelow
      have pinImage := sourceFrame.annotated_pin_instance association sourceModel targetModel targetFrame
        sourceNested targetNested i below levels levels universes universes arity targetSelection.recursorArity rfl
      have sourcePinRead := pinImage.trans targetPinRead
      have result := nestedParameters sourceLevels sourcePins sourceNested i below pinAnnotation sourcePinRead
      simpa only [targetPrefix] using result
    have targetIndex : IotaIndexPin (V := V) ρ restCtor targetFrame.rule.ctorParams
        targetFrame.major targetFrame.rulePrefix xs := by
      simpa only [targetMajor, targetPrefix, ← headers.2.2.1] using indexPin
    have fired := targetFired targetFrame.constructor targetFrame.constructorParams targetFrame.constructorFields
      targetFrame.constructorLookup constructorUniverses ρ xs ys typeRec typeCtor restRec restCtor
      (by simpa only [targetMajor] using xsCount)
      (by simpa only [← headers.2.2.1, ← headers.2.1] using ysCount)
      targetSelection.constructorArity targetSelection.assignment targetPlain targetNested targetIndex
      targetRecRead targetCtorRead targetRecFit targetCtorFit
    have targetCtorLookup : target.find? (names rule.ctor) =
        some (.ctorInfo targetFrame.constructor targetFrame.constructorParams targetFrame.constructorFields) := by
      rw [headers.1]
      exact targetFrame.constructorLookup
    have recLeaf := PullbackMap.fromEnvs_annotation_instance targetModel telescopes lookup targetFrame.recursorLookup
      levels levels universes universes arity targetSelection.recursorArity rfl
    have ctorLeaf := PullbackMap.fromEnvs_annotation_instance targetModel telescopes constructorLookup targetCtorLookup
      levels levels constructorUniverses constructorUniverses ctorArity targetSelection.constructorArity rfl
    change (association.modelCore sourceModel.internal.base2 targetModel).base.acval name
      (Kernel.Level.substFn levels header.levelParams universes) = _ at recLeaf
    change (association.modelCore sourceModel.internal.base2 targetModel).base.acval rule.ctor
      (Kernel.Level.substFn levels constructor.levelParams constructorUniverses) = _ at ctorLeaf
    rw [headers.1] at ctorLeaf
    rw [recLeaf, ctorLeaf]
    simpa only [targetPrefix, ← headers.2.2.1, sourceFrame, Kernel.ConstantInfo.toConstantVal] using fired

/-- Every actual installed source rule receives the full annotated law on
the same pulled carrier. Inert rules are treated exactly as in RecRules. -/
theorem AnnotatedAssociation.rec_rules {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (association : AnnotatedAssociation source target names)
    (sourceModel : StrongInstalledModel V source) (targetModel : StrongInstalledModel V target)
    (levels : Kernel.Name → Nat) :
    RecRules (association.modelCore sourceModel.internal.base2 targetModel).base levels := by
  intro name header major rulePrefix rules lookup rule member fires
  obtain ⟨index, inside, rfl⟩ := List.mem_iff_getElem.mp member
  exact association.rec_rule sourceModel targetModel lookup (List.getElem?_eq_getElem inside) fires levels

/-- The unchanged artifact endpoint supplies capability and full recursor
laws on its exact pulled carrier. Both model witnesses come from the actual
independent verified streams; neither is inferred from the other. -/
theorem SourceConstructorCoverChecked.annotated_modelCore_recursors (V : Type u) [Kernel.SetTheory V]
    {input : Input} {installed : SourceNormalizedInstallation input.source input.roots}
    {site : SourceProjectionSite input.source} (coverage : SourceConstructorCoverChecked installed site)
    (accepted : AcceptedAssociation input) {support : Array Kernel.Declaration}
    (bundle : AdmittedSupport accepted.toAdmittedArtifact support) (names : Kernel.Name → Kernel.Name)
    (checked : checkSupportedArtifactAnnotatedAssociation accepted bundle coverage.env names = some true) :
    SemanticNamesAgree accepted names ∧
      ∃ targetModel : StrongInstalledModel V bundle.env,
      ∃ core : AnnotatedModelCore V coverage.env,
        core.base.acval = (PullbackMap.fromEnvs coverage.env bundle.env names).annotations
          targetModel.internal.base2.acval ∧ CapsOk core.base ∧ ∀ levels, RecRules core.base levels := by
  obtain ⟨original, annotated⟩ := bothChecks_true checked
  obtain ⟨nameCheck, _⟩ := bothChecks_true original
  obtain ⟨sourceModel⟩ := coverage.strong_model V
  obtain ⟨targetModel⟩ := bundle.strong_model V
  have association := checkAnnotatedAssociation_sound annotated
  exact ⟨of_decide_eq_true (Option.some.inj nameCheck), targetModel,
    association.modelCore sourceModel.internal.base2 targetModel, rfl,
    association.caps_ok sourceModel.internal.base2 targetModel,
    association.rec_rules sourceModel targetModel⟩

end Ix.CompileCert
