import Ix.CompileCert.AnnotLaws
import Ix.CompileCert.AnnotRules

namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics

theorem checkInstalledMemberExprs_getD {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    {name : Kernel.Name} {sourceOwner targetOwner : Kernel.ConstantInfo}
    (sourceLookup : source.find? name = some sourceOwner)
    (targetLookup : target.find? (names name) = some targetOwner)
    {sources targets : List Kernel.Expr}
    (checked : checkInstalledMemberExprs source target names name sources targets = some true)
    (index : Nat) :
    checkInstalledMemberExpr source target names name (sources.getD index default)
      (targets.getD index default) = some true := by
  induction sources generalizing targets index with
  | nil =>
    cases targets with
    | nil =>
      simp only [List.getD_eq_getElem?_getD, List.getElem?_nil, Option.getD_none]
      simp only [checkInstalledMemberExpr, sourceLookup, targetLookup]
      rfl
    | cons => simp [checkInstalledMemberExprs] at checked
  | cons head tail ih =>
    cases targets with
    | nil => simp [checkInstalledMemberExprs] at checked
    | cons targetHead targetTail =>
      obtain ⟨first, rest⟩ := bothChecks_true checked
      cases index with
      | zero => exact first
      | succ index => exact ih rest index

theorem checkInstalledMemberExpr_literal_support {source target : Kernel.Env}
    {names : Kernel.Name → Kernel.Name} {name : Kernel.Name} {s t : Kernel.Expr}
    (checked : checkInstalledMemberExpr source target names name s t = some true)
    (sourceReady : literalReady source s = true) (targetReady : literalReady target t = true) :
    checkExprLiteralSupport source target s = true := by
  cases hs : source.find? name with
  | none => simp [checkInstalledMemberExpr, hs] at checked
  | some sourceOwner =>
    cases ht : target.find? (names name) with
    | none => simp [checkInstalledMemberExpr, hs, ht] at checked
    | some targetOwner =>
      simp only [checkInstalledMemberExpr, hs, ht] at checked
      split at checked
      · exact checkInstalledExpr_literal_support checked sourceReady targetReady
      · contradiction

/-- The actual nested pin reads under the pulled source carrier and carries
the required context-guarded instRevChain grading. Independent source and
target rule laws supply readability; their interpretations are not identified.
The remaining fired-rule equality and index-pin assembly are separate. -/
theorem AnnotatedAssociation.nested_pin {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : AnnotatedAssociation source target names)
    (sourceModel : StrongInstalledModel V source) (targetModel : StrongInstalledModel V target)
    {header : Kernel.ConstantVal} {major rulePrefix : Nat} {rules : List Kernel.RecRule}
    (present : Kernel.ConstantInfo.recInfo header major rulePrefix rules ∈ source.consts)
    {index : Nat} {rule : Kernel.RecRule} (selected : rules[index]? = some rule)
    {nestedLevels : List Kernel.Level} {pins : List Kernel.Expr}
    (nested : rule.fire = .nested nestedLevels pins)
    (pinIndex : Nat) (below : pinIndex < rule.ctorParams)
    (levels : Kernel.Name → Nat) (universes : List Kernel.Level) :
    ∃ annotation,
      denoteMeta (checked.modelCore sourceModel.internal.base2 targetModel).base.acval source levels rulePrefix
        (Kernel.Verify.openRev 0 rulePrefix
          ((pins.getD pinIndex default).instantiateLevelParams header.levelParams universes)) = some annotation ∧
      ∀ (ρ : Nat → V) (arguments : List AnnotTerm) (typeAnnotation residual : AnnotTerm),
        arguments.length = rulePrefix →
        (∀ argument ∈ arguments, WellDenotedV V ρ argument) →
        denoteMeta (checked.modelCore sourceModel.internal.base2 targetModel).base.acval source levels 0
          (header.type.instantiateLevelParams header.levelParams universes) = some typeAnnotation →
        TeleFitPA V ρ typeAnnotation arguments residual →
        WellDenotedV V ρ (Kernel.Model.AnnotTerm.instRevChain arguments annotation) := by
  have association := checkTelescopes_sound checked.installed.telescopes
  obtain ⟨sourceLookup, targetHeader, targetRules, targetLookup, compared⟩ :=
    checkInstalledRecursors_member checked.installed.recursors present
  obtain ⟨targetRule, targetSelected, headers, fireCheck, _⟩ := checkInstalledRules_at compared selected
  have fires : rule.fire ≠ .inert := by rw [nested]; intro h; cases h
  have targetFires := (checkInstalledFire_sound targetModel association sourceLookup fireCheck
    (fun _ => 0)).fires fires
  obtain ⟨targetNestedLevels, targetPins, targetNested, pinsCheck⟩ :
      ∃ ls ps, targetRule.fire = .nested ls ps ∧
        checkInstalledMemberExprs source target names header.name pins ps = some true := by
    rw [nested] at fireCheck
    cases targetShape : targetRule.fire with
    | inert => simp [checkInstalledFire, targetShape] at fireCheck
    | plain => simp [checkInstalledFire, targetShape] at fireCheck
    | nested ls ps =>
      simp only [checkInstalledFire, targetShape] at fireCheck
      exact ⟨ls, ps, rfl, (bothChecks_true fireCheck).2⟩
  have pinCheck := checkInstalledMemberExprs_getD sourceLookup targetLookup pinsCheck pinIndex
  have sourceLaw := sourceModel.internal.rec_rules (fun _ => 0) header.name header major rulePrefix rules
    sourceLookup rule (List.mem_of_getElem? selected) fires
  obtain ⟨_, _, _, sourcePinsLaw, _⟩ := sourceLaw.2
    (header.levelParams.map Kernel.Level.param) (by simp)
  obtain ⟨sourcePin, sourceRead, _⟩ := sourcePinsLaw nestedLevels pins nested pinIndex below
  rw [Kernel.Verify.openRev_instantiateLevelParams, denotePInstLevels,
    Kernel.Level.substFn_param_self] at sourceRead
  have sourceReady := literalReady_of_reading sourceRead
  rw [literalReady_openRev] at sourceReady
  let sourceLevels := Kernel.Level.substFn levels header.levelParams universes
  let targetLevels := (PullbackMap.fromEnvs source target names).levels header.name sourceLevels
  have targetLaw := targetModel.internal.rec_rules targetLevels (names header.name) targetHeader
    major rulePrefix targetRules targetLookup targetRule (List.mem_of_getElem? targetSelected) targetFires
  obtain ⟨_, _, _, targetPinsLaw, _⟩ := targetLaw.2
    (targetHeader.levelParams.map Kernel.Level.param) (by simp)
  have targetBelow : pinIndex < targetRule.ctorParams := by rw [← headers.2.2.1]; exact below
  obtain ⟨annotation, targetRead, targetGraded⟩ := targetPinsLaw targetNestedLevels targetPins targetNested
    pinIndex targetBelow
  rw [Kernel.Verify.openRev_instantiateLevelParams, denotePInstLevels,
    Kernel.Level.substFn_param_self] at targetRead
  have targetReady := literalReady_of_reading targetRead
  rw [literalReady_openRev] at targetReady
  have support := checkInstalledMemberExpr_literal_support pinCheck sourceReady targetReady
  refine ⟨annotation, ?_, ?_⟩
  · rw [Kernel.Verify.openRev_instantiateLevelParams, denotePInstLevels]
    exact (checkInstalledMemberExpr_opened_annotations targetModel association sourceLookup support
      pinCheck sourceLevels rulePrefix rulePrefix).trans targetRead
  · intro ρ arguments typeAnnotation residual count valid typeRead fit
    obtain ⟨targetEntry, entryLookup, actualType, sourceTypeRead, targetTypeRead, _⟩ :=
      checked.instantiated_type sourceModel.internal.base2 targetModel (.recInfo header major rulePrefix rules)
        present levels universes
    have sameEntry := Option.some.inj (entryLookup.symm.trans targetLookup)
    subst targetEntry
    have sameType : actualType = typeAnnotation := Option.some.inj (sourceTypeRead.symm.trans typeRead)
    subst typeAnnotation
    apply targetGraded ρ arguments actualType residual count valid _ fit
    rw [denotePInstLevels, Kernel.Level.substFn_param_self]
    exact targetTypeRead

end Ix.CompileCert
