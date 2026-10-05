import Ix.CompileCert.AnnotRuleFit

namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics

theorem InstalledRuleFrame.checked_comparisons
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : checkInstalledRecursors source target names = true)
    {name : Kernel.Name} {index : Nat} (sourceFrame : InstalledRuleFrame source name index)
    (targetFrame : InstalledRuleFrame target (names name) index) :
    InstalledRuleHeader names sourceFrame.rule targetFrame.rule ∧
    checkInstalledFire source target names name sourceFrame.rule.fire targetFrame.rule.fire = some true ∧
    checkInstalledMemberExpr source target names name sourceFrame.rule.rhs targetFrame.rule.rhs = some true := by
  obtain ⟨_, header, rules, lookup, compared⟩ := checkInstalledRecursors_member checked
    (Kernel.Semantics.Env.find?_mem sourceFrame.recursorLookup)
  have sourceName : sourceFrame.header.name = name := Kernel.Semantics.Env.find?_name sourceFrame.recursorLookup
  rw [sourceName, targetFrame.recursorLookup] at lookup
  have same := Kernel.ConstantInfo.recInfo.inj (Option.some.inj lookup)
  rw [← same.2.2.2, sourceName] at compared
  obtain ⟨rule, selected, headers, fire, rhs⟩ := checkInstalledRules_at compared sourceFrame.ruleLookup
  rw [targetFrame.ruleLookup] at selected
  cases Option.some.inj selected
  exact ⟨headers, fire, rhs⟩

/-- RHS annotations agree for the actual selected rules at arbitrary paired
concrete instances. Independent installation supplies readability and target
parameter coverage; only the existing rule comparison supplies association. -/
theorem InstalledRuleFrame.annotated_rhs_instance {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (association : AnnotatedAssociation source target names)
    (sourceModel : StrongInstalledModel V source) (targetModel : StrongInstalledModel V target)
    {name : Kernel.Name} {index : Nat} (sourceFrame : InstalledRuleFrame source name index)
    (targetFrame : InstalledRuleFrame target (names name) index)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceFrame.header.levelParams.length)
    (targetArity : targetUs.length = targetFrame.header.levelParams.length)
    (arguments : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels)) :
    denoteMeta (association.modelCore sourceModel.internal.base2 targetModel).base.acval source sourceLevels 0
      (sourceFrame.rule.rhs.instantiateLevelParams sourceFrame.header.levelParams sourceUs) =
    denoteMeta targetModel.internal.base2.acval target targetLevels 0
      (targetFrame.rule.rhs.instantiateLevelParams targetFrame.header.levelParams targetUs) := by
  have compared := (sourceFrame.checked_comparisons association.installed.recursors targetFrame).2.2
  have sourceLaw := sourceModel.internal.rec_rules (fun _ => 0) name sourceFrame.header sourceFrame.major
    sourceFrame.rulePrefix sourceFrame.rules sourceFrame.recursorLookup sourceFrame.rule
    (List.mem_of_getElem? sourceFrame.ruleLookup) sourceFrame.fires
  have targetLaw := targetModel.internal.rec_rules (fun _ => 0) (names name) targetFrame.header targetFrame.major
    targetFrame.rulePrefix targetFrame.rules targetFrame.recursorLookup targetFrame.rule
    (List.mem_of_getElem? targetFrame.ruleLookup) targetFrame.fires
  obtain ⟨_, sourceRead, _⟩ := sourceLaw.2 (sourceFrame.header.levelParams.map Kernel.Level.param) (by simp)
  obtain ⟨_, targetRead, _⟩ := targetLaw.2 (targetFrame.header.levelParams.map Kernel.Level.param) (by simp)
  rw [denotePInstLevels, Kernel.Level.substFn_param_self] at sourceRead targetRead
  have support := checkInstalledMemberExpr_literal_support_of_readings compared sourceRead targetRead
  have wf := targetModel.internal.base2.wf _ (Kernel.Semantics.Env.find?_mem targetFrame.recursorLookup)
  have ruleWf := wf.2.2.2.2.2.1 targetFrame.header targetFrame.major targetFrame.rulePrefix targetFrame.rules
    rfl targetFrame.rule (List.mem_of_getElem? targetFrame.ruleLookup)
  exact association.member_instance_reading sourceModel.internal.base2 targetModel sourceFrame.recursorLookup
    targetFrame.recursorLookup ruleWf.2.1 support compared sourceLevels targetLevels sourceUs targetUs
    sourceArity targetArity arguments 0

end Ix.CompileCert
