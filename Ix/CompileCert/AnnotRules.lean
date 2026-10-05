import Ix.CompileCert.AnnotReady

/-! Actual installed rule annotations. Source readability is obtained from
its own verified model; it is never inferred from the admitted target. -/
namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics

theorem literalReady_instantiateLevels (env : Kernel.Env) (e : Kernel.Expr)
    (params : List Kernel.Name) (universes : List Kernel.Level) :
    literalReady env (e.instantiateLevelParams params universes) = literalReady env e := by
  induction e <;> simp_all only [Kernel.Expr.instantiateLevelParams, literalReady]

theorem literalReady_openRev (env : Kernel.Env) (e : Kernel.Expr) (d count : Nat) :
    literalReady env (Kernel.Verify.openRev d count e) = literalReady env e := by
  induction count with
  | zero => rfl
  | succ count ih => rw [Kernel.Verify.openRev, literalReady_instantiateFVar, ih]

theorem openRev_allLevelParamsDefined {e : Kernel.Expr} {params : List Kernel.Name}
    (bounded : e.allLevelParamsDefined params = true) (d count : Nat) :
    (Kernel.Verify.openRev d count e).allLevelParamsDefined params = true := by
  induction count with
  | zero => exact bounded
  | succ count ih =>
    exact Kernel.Expr.allLevelParamsDefined_instantiate1 (by rfl) 0 ih

theorem AnnotatedSyntax.openRev {sa ta se te sl tl s t}
    (image : AnnotatedSyntax sa ta se te sl tl s t) (d count : Nat) :
    AnnotatedSyntax sa ta se te sl tl (Kernel.Verify.openRev d count s) (Kernel.Verify.openRev d count t) := by
  induction count with
  | zero => exact image
  | succ count ih => exact ih.instantiate1 (.fvar (d + count) (.sort .zero) (.sort .zero)) 0

/-- Opening a checked raw pin retains the exact annotation relation and
recovers the source assignment only on its actual owner telescope. -/
theorem checkInstalledMemberExpr_opened_annotations {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (targetModel : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    {name : Kernel.Name} {sourceEntry : Kernel.ConstantInfo}
    (lookup : sourceEnv.find? name = some sourceEntry) {source target : Kernel.Expr}
    (support : checkExprLiteralSupport sourceEnv targetEnv source = true)
    (checked : checkInstalledMemberExpr sourceEnv targetEnv names name source target = some true)
    (levels : Kernel.Name → Nat) (count depth : Nat) :
    denoteMeta ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations targetModel.internal.base2.acval)
      sourceEnv levels depth (Kernel.Verify.openRev 0 count source) =
    denoteMeta targetModel.internal.base2.acval targetEnv
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels name levels) depth
      (Kernel.Verify.openRev 0 count target) := by
  obtain ⟨targetEntry, targetLookup, sourceUnique, targetUnique, sameArity⟩ :=
    association name sourceEntry lookup
  simp only [checkInstalledMemberExpr, lookup, targetLookup] at checked
  split at checked
  next bounded =>
    have structural := checkInstalledExpr_annotatedSyntax_local targetModel association _
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels name levels) support checked
    have image := ((structural.openRev 0 count).opened depth).reading
    refine (denoteMeta_params_at ?_ ?_ depth _ (openRev_allLevelParamsDefined bounded 0 count)).trans image
    · intro constant info present first second agree
      exact PullbackMap.annotations_params targetModel association present first second agree
    · intro parameter present
      simp only [PullbackMap.fromEnvs, lookup, targetLookup]
      exact (UniverseImage.telescope_recovery levels sourceUnique targetUnique sameArity parameter present).symm
  next => contradiction

theorem checkInstalledRules_at {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    {name : Kernel.Name} {sources targets : List Kernel.RecRule}
    (checked : checkInstalledRules source target names name sources targets = some true)
    {index : Nat} {rule : Kernel.RecRule} (selected : sources[index]? = some rule) :
    ∃ targetRule, targets[index]? = some targetRule ∧ InstalledRuleHeader names rule targetRule ∧
      checkInstalledFire source target names name rule.fire targetRule.fire = some true ∧
      checkInstalledMemberExpr source target names name rule.rhs targetRule.rhs = some true := by
  induction sources generalizing targets index with
  | nil => simp at selected
  | cons head tail ih =>
    cases targets with
    | nil => simp [checkInstalledRules] at checked
    | cons targetHead targetTail =>
      obtain ⟨header, rest⟩ := bothChecks_true checked
      obtain ⟨fire, rest⟩ := bothChecks_true rest
      obtain ⟨rhs, remaining⟩ := bothChecks_true rest
      cases index with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
        subst rule
        exact ⟨targetHead, rfl, of_decide_eq_true (Option.some.inj header), fire, rhs⟩
      | succ index => exact ih remaining selected

/-- An actual fired rule's RHS reads on the pulled carrier with the target's
full annotation grading. All support conditions come from the two installed
models and the existing indexed rule comparison. This is the carried-RHS
portion of RecRuleLaw, not its remaining nested-pin or firing clauses. -/
theorem AnnotatedAssociation.rule_rhs {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : AnnotatedAssociation source target names)
    (sourceModel : StrongInstalledModel V source) (targetModel : StrongInstalledModel V target)
    {header : Kernel.ConstantVal} {major rulePrefix : Nat} {rules : List Kernel.RecRule}
    (present : Kernel.ConstantInfo.recInfo header major rulePrefix rules ∈ source.consts)
    {index : Nat} {rule : Kernel.RecRule} (selected : rules[index]? = some rule)
    (fires : rule.fire ≠ .inert) (levels : Kernel.Name → Nat) (universes : List Kernel.Level) :
    rulePrefix ≤ major ∧
    ∃ targetHeader targetRules targetRule,
      target.find? (names header.name) = some (.recInfo targetHeader major rulePrefix targetRules) ∧
      targetRules[index]? = some targetRule ∧
      ∃ annotation,
        denoteMeta (checked.modelCore sourceModel.internal.base2 targetModel).base.acval source levels 0
          (rule.rhs.instantiateLevelParams header.levelParams universes) = some annotation ∧
        denoteMeta targetModel.internal.base2.acval target
          ((PullbackMap.fromEnvs source target names).levels header.name
            (Kernel.Level.substFn levels header.levelParams universes)) 0 targetRule.rhs = some annotation ∧
        ∀ ρ : Nat → V, WellDenotedV V ρ annotation := by
  have association := checkTelescopes_sound checked.installed.telescopes
  obtain ⟨sourceLookup, targetHeader, targetRules, targetLookup, compared⟩ :=
    checkInstalledRecursors_member checked.installed.recursors present
  obtain ⟨targetRule, targetSelected, _, fireCheck, rhsCheck⟩ := checkInstalledRules_at compared selected
  have sourceMember := List.mem_of_getElem? selected
  have targetMember := List.mem_of_getElem? targetSelected
  have targetFires := (checkInstalledFire_sound targetModel association sourceLookup fireCheck
    (fun _ => 0)).fires fires
  have sourceLaw := sourceModel.internal.rec_rules (fun _ => 0) header.name header major rulePrefix rules
    sourceLookup rule sourceMember fires
  obtain ⟨sourceAnnotation, sourceRead, _⟩ := sourceLaw.2
    (header.levelParams.map Kernel.Level.param) (by simp)
  rw [denotePInstLevels, Kernel.Level.substFn_param_self] at sourceRead
  let targetLevels := (PullbackMap.fromEnvs source target names).levels header.name
    (Kernel.Level.substFn levels header.levelParams universes)
  have targetLaw := targetModel.internal.rec_rules targetLevels (names header.name) targetHeader
    major rulePrefix targetRules targetLookup targetRule targetMember targetFires
  obtain ⟨annotation, targetRead, graded, _⟩ := targetLaw.2
    (targetHeader.levelParams.map Kernel.Level.param) (by simp)
  rw [denotePInstLevels, Kernel.Level.substFn_param_self] at targetRead
  have support := checkInstalledMemberExpr_literal_support_of_readings rhsCheck sourceRead targetRead
  refine ⟨sourceLaw.1, targetHeader, targetRules, targetRule, targetLookup, targetSelected,
    annotation, ?_, targetRead, graded⟩
  rw [denotePInstLevels]
  exact (checkInstalledMemberExpr_annotated_reading_local targetModel association sourceLookup support
    rhsCheck _ 0).trans targetRead

end Ix.CompileCert
