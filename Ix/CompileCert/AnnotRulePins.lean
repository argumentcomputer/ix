import Ix.CompileCert.AnnotRuleChecks

namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics

/-- The kernel's existing fallback pin also has no undeclared universe
parameters. This lemma preserves that exact read convention. -/
theorem pin_getD_allLevelParamsDefined {pins : List Kernel.Expr} {params : List Kernel.Name}
    (bounded : ∀ pin ∈ pins, pin.allLevelParamsDefined params = true) (index : Nat) :
    (pins.getD index default).allLevelParamsDefined params = true := by
  by_cases inside : index < pins.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some]
    exact bounded _ (List.getElem_mem inside)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
    rfl

/-- Concrete-instance correspondence for a selected actual nested pin. The
independent installations discharge readability and parameter bounds; the
finite rule check supplies the source/target association at the same index. -/
theorem InstalledRuleFrame.annotated_pin_instance {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (association : AnnotatedAssociation source target names)
    (sourceModel : StrongInstalledModel V source) (targetModel : StrongInstalledModel V target)
    {name : Kernel.Name} {index : Nat} (sourceFrame : InstalledRuleFrame source name index)
    (targetFrame : InstalledRuleFrame target (names name) index)
    {sourcePinLevels targetPinLevels : List Kernel.Level} {sourcePins targetPins : List Kernel.Expr}
    (sourceNested : sourceFrame.rule.fire = .nested sourcePinLevels sourcePins)
    (targetNested : targetFrame.rule.fire = .nested targetPinLevels targetPins)
    (pinIndex : Nat) (below : pinIndex < sourceFrame.rule.ctorParams)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceFrame.header.levelParams.length)
    (targetArity : targetUs.length = targetFrame.header.levelParams.length)
    (arguments : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels)) :
    denoteMeta (association.modelCore sourceModel.internal.base2 targetModel).base.acval source sourceLevels sourceFrame.rulePrefix
      (Kernel.Verify.openRev 0 sourceFrame.rulePrefix
        ((sourcePins.getD pinIndex default).instantiateLevelParams sourceFrame.header.levelParams sourceUs)) =
    denoteMeta targetModel.internal.base2.acval target targetLevels targetFrame.rulePrefix
      (Kernel.Verify.openRev 0 targetFrame.rulePrefix
        ((targetPins.getD pinIndex default).instantiateLevelParams targetFrame.header.levelParams targetUs)) := by
  have telescopes := checkTelescopes_sound association.installed.telescopes
  have shapes := sourceFrame.checked_images targetModel telescopes association.installed.recursors targetFrame
  obtain ⟨headers, fireCheck, _⟩ := sourceFrame.checked_comparisons association.installed.recursors targetFrame
  rw [sourceNested, targetNested] at fireCheck
  have pinsCheck := (bothChecks_true fireCheck).2
  have pinCheck := checkInstalledMemberExprs_getD sourceFrame.recursorLookup targetFrame.recursorLookup pinsCheck pinIndex
  have sourceLaw := sourceModel.internal.rec_rules (fun _ => 0) name sourceFrame.header sourceFrame.major
    sourceFrame.rulePrefix sourceFrame.rules sourceFrame.recursorLookup sourceFrame.rule
    (List.mem_of_getElem? sourceFrame.ruleLookup) sourceFrame.fires
  have targetLaw := targetModel.internal.rec_rules (fun _ => 0) (names name) targetFrame.header targetFrame.major
    targetFrame.rulePrefix targetFrame.rules targetFrame.recursorLookup targetFrame.rule
    (List.mem_of_getElem? targetFrame.ruleLookup) targetFrame.fires
  obtain ⟨_, _, _, sourcePinLaw, _⟩ := sourceLaw.2 (sourceFrame.header.levelParams.map Kernel.Level.param) (by simp)
  obtain ⟨_, _, _, targetPinLaw, _⟩ := targetLaw.2 (targetFrame.header.levelParams.map Kernel.Level.param) (by simp)
  obtain ⟨_, sourceRead, _⟩ := sourcePinLaw sourcePinLevels sourcePins sourceNested pinIndex below
  have targetBelow : pinIndex < targetFrame.rule.ctorParams := by rw [← headers.2.2.1]; exact below
  obtain ⟨_, targetRead, _⟩ := targetPinLaw targetPinLevels targetPins targetNested pinIndex targetBelow
  rw [Kernel.Verify.openRev_instantiateLevelParams, denotePInstLevels, Kernel.Level.substFn_param_self] at sourceRead targetRead
  have sourceReady := literalReady_of_reading sourceRead
  have targetReady := literalReady_of_reading targetRead
  rw [literalReady_openRev] at sourceReady targetReady
  have support := checkInstalledMemberExpr_literal_support pinCheck sourceReady targetReady
  have wf := targetModel.internal.base2.wf _ (Kernel.Semantics.Env.find?_mem targetFrame.recursorLookup)
  have ruleWf := wf.2.2.2.2.2.1 targetFrame.header targetFrame.major targetFrame.rulePrefix targetFrame.rules
    rfl targetFrame.rule (List.mem_of_getElem? targetFrame.ruleLookup)
  have bounded := pin_getD_allLevelParamsDefined
    (fun pin member => ((ruleWf.2.2.2.2 targetPinLevels targetPins targetNested).2.2.1 pin member).2.1) pinIndex
  rw [← shapes.2.1]
  exact association.opened_member_instance_reading sourceModel.internal.base2 targetModel
    sourceFrame.recursorLookup targetFrame.recursorLookup bounded support pinCheck
    sourceLevels targetLevels sourceUs targetUs sourceArity targetArity arguments
    sourceFrame.rulePrefix sourceFrame.rulePrefix

end Ix.CompileCert
