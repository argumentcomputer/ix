import Ix.CompileCert.RuleParameterRecipe

/-! # Complete open witnesses for source firing tuples

The public source rule law permits two different fitting parameter spines
at a plain `paramsBlind` rule. Its witness therefore uses the constructor's
own parameter variables in that case. Ordinary compared rules and nested
rules retain the existing recursor-side recipe. This distinction is derived
from the original firing conditions, not imposed as a new caller premise.

The resulting dependent field telescope can be joined to the real recursor
prefix after capture-avoiding weakening. The join retains the original
ambient fresh-variable valuation: it is an open witness, not yet a proof
that the closed `leanRuleStatement` exporter or an installed target row has
that exact annotated telescope. All existing certification relations and
runtime entry points are unchanged.
-/

namespace Ix.CompileCert

/-- A complete parameter witness, including the independent constructor
parameters of a plain parameter-blind rule. This is not a replacement for
`leanRuleStatement` or the kernel's reduction recipe. -/
def InstalledRuleFrame.firingParameterRecipe {env : Kernel.Env}
    {name : Kernel.Name} {index : Nat} (frame : InstalledRuleFrame env name index)
    (universes : List Kernel.Level)
    (argumentExpressions fieldExpressions : List Kernel.Expr) : List Kernel.Expr :=
  if frame.rule.fire = .plain ∧ frame.rule.paramsBlind = true then
    fieldExpressions.take frame.rule.ctorParams
  else frame.openParameterRecipe universes argumentExpressions

/-- The total witness reads the actual constructor parameter values in
every firing mode. The independent field readings supply the blind branch;
no equality with the recursor parameters is asserted in that branch. -/
theorem SourceRuleComparisons.firingParameterRecipe_reading
    {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {name : Kernel.Name} {index : Nat}
    {frame : InstalledRuleFrame env name index}
    {universes constructorUniverses : List Kernel.Level} {valuation : Nat → V}
    {argumentExpressions fieldExpressions : List Kernel.Expr} {arguments fields : List V}
    (firing : SourceRuleComparisons values env levels frame universes constructorUniverses
      valuation argumentExpressions fieldExpressions arguments fields)
    (argumentReadings : DenotesSpine values env levels valuation argumentExpressions arguments)
    (fieldReadings : DenotesSpine values env levels valuation fieldExpressions fields) :
    DenotesSpine values env levels valuation
      (frame.firingParameterRecipe universes argumentExpressions fieldExpressions)
      (fields.take frame.rule.ctorParams) := by
  unfold InstalledRuleFrame.firingParameterRecipe
  split
  · exact fieldReadings.take frame.rule.ctorParams
  · rename_i compared
    rcases firing.openParameterRecipe_reading argumentReadings with blind | readings
    · exact False.elim (compared blind)
    · exact readings

/-- All parameter witnesses are derived from the actual public tuple.
This includes the plain parameter-blind branch, and preserves the actual
constructor universe instance and every dependent binder annotation. -/
theorem RuleTupleTyping.firing_recipe_fields
    {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    (sourceWf : Kernel.EnvWF env) {levels : Kernel.Name → Nat}
    {name : Kernel.Name} {index : Nat} {frame : InstalledRuleFrame env name index}
    {universes constructorUniverses : List Kernel.Level}
    {valuation : Nat → V} {arguments fields : List V}
    (typed : RuleTupleTyping values env levels frame universes constructorUniverses
      valuation arguments fields)
    (firing : SourceRuleComparisons values env levels frame universes constructorUniverses
      (pushArguments valuation (arguments ++ fields))
      ((argumentVariables (arguments ++ fields).length).take arguments.length)
      ((argumentVariables (arguments ++ fields).length).drop arguments.length) arguments fields) :
    let fresh := pushArguments valuation (arguments ++ fields)
    let argumentExpressions := (argumentVariables (arguments ++ fields).length).take arguments.length
    let fieldExpressions := (argumentVariables (arguments ++ fields).length).drop arguments.length
    let parameters := frame.firingParameterRecipe universes argumentExpressions fieldExpressions
    parameters.length = frame.rule.ctorParams ∧
      ∃ fieldType result,
        Kernel.Expr.instPisAtLift parameters
          (frame.constructor.type.instantiateLevelParams
            frame.constructor.levelParams constructorUniverses) = some fieldType ∧
        InstalledTelescope values env levels fresh fieldType (fields.drop frame.rule.ctorParams)
          (pushArguments fresh (fields.drop frame.rule.ctorParams)) result := by
  dsimp only
  let fresh := pushArguments valuation (arguments ++ fields)
  have readings := DenotesSpine.argumentVariables values env levels valuation (arguments ++ fields)
  have argumentReadings : DenotesSpine values env levels fresh
      ((argumentVariables (arguments ++ fields).length).take arguments.length) arguments := by
    simpa only [List.take_left] using readings.take arguments.length
  have fieldReadings : DenotesSpine values env levels fresh
      ((argumentVariables (arguments ++ fields).length).drop arguments.length) fields := by
    simpa only [List.drop_left] using readings.drop arguments.length
  have parameters := firing.firingParameterRecipe_reading argumentReadings fieldReadings
  have count := parameters.length
  rw [List.length_take, firing.fieldCount, Nat.min_eq_left (Nat.le_add_right _ _)] at count
  refine ⟨count, ?_⟩
  obtain ⟨finalValuation, result, constructorTyped⟩ :=
    (typed.rebase sourceWf fresh).constructorTyped
  have splitTyped : InstalledTelescope values env levels fresh
      (frame.constructor.type.instantiateLevelParams frame.constructor.levelParams constructorUniverses)
      (fields.take frame.rule.ctorParams ++ fields.drop frame.rule.ctorParams)
      finalValuation result := by
    simpa only [List.take_append_drop] using constructorTyped
  exact splitTyped.instPisAtLift_prefix parameters

/-- Split an actual dependent tuple at an argument boundary. The residual
and both valuations are outputs of the original tuple, not independent
typing assumptions about a proposed prefix. -/
theorem InstalledTelescope.split_arguments
    {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {valuation finalValuation : Nat → V}
    {expression result : Kernel.Expr} {first second : List V}
    (typed : InstalledTelescope values env levels valuation expression
      (first ++ second) finalValuation result) :
    ∃ middle,
      InstalledTelescope values env levels valuation expression first
        (pushArguments valuation first) middle ∧
      InstalledTelescope values env levels (pushArguments valuation first) middle
        second finalValuation result := by
  induction first generalizing valuation expression with
  | nil => exact ⟨expression, .nil, typed⟩
  | cons argument rest ih =>
    cases typed with
    | cons domainRead argumentTyped tail =>
      obtain ⟨middle, leading, trailing⟩ := ih tail
      exact ⟨middle, .cons domainRead argumentTyped leading, trailing⟩

theorem ruleRowForalls_append (first second : List (Kernel.Expr × Kernel.BinderMeta))
    (body : Kernel.Expr) :
    ruleRowForalls (first ++ second) body = ruleRowForalls first (ruleRowForalls second body) := by
  induction first with
  | nil => rfl
  | cons binder rest ih =>
    rcases binder with ⟨domain, metadata⟩
    simp only [List.cons_append, ruleRowForalls, ih]

/-- Extract the actual recursor prefix used by the source firing tuple.
The take is intentional: an installed frame alone does not prove that its
stored prefix count is at most its major position. No new bound premise or
claim about successful source installation is hidden here. -/
theorem RuleTupleTyping.firing_recursor_prefix
    {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {name : Kernel.Name} {index : Nat}
    {frame : InstalledRuleFrame env name index}
    {universes constructorUniverses : List Kernel.Level}
    {valuation : Nat → V} {arguments fields : List V}
    (typed : RuleTupleTyping values env levels frame universes constructorUniverses
      valuation arguments fields) :
    ∃ binders residual,
      (frame.header.type.instantiateLevelParams frame.header.levelParams universes).stripPis
        (arguments.take frame.rulePrefix).length = some (binders, residual) ∧
      binders.length = (arguments.take frame.rulePrefix).length ∧
      ∀ body, InstalledTelescope values env levels valuation (ruleRowForalls binders body)
        (arguments.take frame.rulePrefix)
        (pushArguments valuation (arguments.take frame.rulePrefix)) body := by
  obtain ⟨finalValuation, result, recursorTyped⟩ := typed.recursorTyped
  have splitTyped : InstalledTelescope values env levels valuation
      (frame.header.type.instantiateLevelParams frame.header.levelParams universes)
      (arguments.take frame.rulePrefix ++
        (arguments.drop frame.rulePrefix ++ [fields.foldl Kernel.SetTheory.app
          (values frame.rule.ctor
            (Kernel.Level.substFn levels frame.constructor.levelParams constructorUniverses))]))
      finalValuation result := by
    simpa only [← List.append_assoc, List.take_append_drop] using recursorTyped
  obtain ⟨residual, leading, _⟩ := splitTyped.split_arguments
  obtain ⟨binders, stripped, count, rows⟩ := leading.ruleRow_binders
  exact ⟨binders, residual, stripped, count, rows⟩

/-- Join the real recursor prefix to the complete constructor-field witness.
The field type is lifted over exactly the consumed prefix values. Its
dependent domains, metadata, final residual and valuation remain tied to
that operation. The result covers blind, compared and nested firing modes.

This open witness retains the ambient source tuple. Identifying it with
the closed exported rule statement still requires the generator and
annotation bridge; this theorem does not assert that identification. -/
theorem RuleTupleTyping.firing_open_row
    {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    (sourceWf : Kernel.EnvWF env) {levels : Kernel.Name → Nat}
    {name : Kernel.Name} {index : Nat} {frame : InstalledRuleFrame env name index}
    {universes constructorUniverses : List Kernel.Level}
    {valuation : Nat → V} {arguments fields : List V}
    (typed : RuleTupleTyping values env levels frame universes constructorUniverses
      valuation arguments fields)
    (firing : SourceRuleComparisons values env levels frame universes constructorUniverses
      (pushArguments valuation (arguments ++ fields))
      ((argumentVariables (arguments ++ fields).length).take arguments.length)
      ((argumentVariables (arguments ++ fields).length).drop arguments.length) arguments fields) :
    let fresh := pushArguments valuation (arguments ++ fields)
    let prefixValues := arguments.take frame.rulePrefix
    let fieldValues := fields.drop frame.rule.ctorParams
    let parameters := frame.firingParameterRecipe universes
      ((argumentVariables (arguments ++ fields).length).take arguments.length)
      ((argumentVariables (arguments ++ fields).length).drop arguments.length)
    ∃ prefixBinders recursorResidual fieldType fieldBinders fieldResidual,
      (frame.header.type.instantiateLevelParams frame.header.levelParams universes).stripPis
        prefixValues.length = some (prefixBinders, recursorResidual) ∧
      prefixBinders.length = prefixValues.length ∧
      Kernel.Expr.instPisAtLift parameters
        (frame.constructor.type.instantiateLevelParams
          frame.constructor.levelParams constructorUniverses) = some fieldType ∧
      (fieldType.liftLooseBVars prefixValues.length 0).stripPis frame.rule.nfields =
        some (fieldBinders, fieldResidual) ∧
      fieldBinders.length = frame.rule.nfields ∧
      ∀ body, InstalledTelescope values env levels fresh
        (ruleRowForalls (prefixBinders ++ fieldBinders) body)
        (prefixValues ++ fieldValues) (pushArguments fresh (prefixValues ++ fieldValues)) body := by
  dsimp only
  let fresh := pushArguments valuation (arguments ++ fields)
  let prefixValues := arguments.take frame.rulePrefix
  obtain ⟨prefixBinders, recursorResidual, prefixStripped, prefixCount, prefixRows⟩ :=
    (typed.rebase sourceWf fresh).firing_recursor_prefix
  obtain ⟨_, fieldType, result, instantiated, fieldsTyped⟩ :=
    typed.firing_recipe_fields sourceWf firing
  have related : ValuationLift prefixValues.length 0 fresh
      (pushArguments fresh prefixValues) := by
    intro position
    simpa [Nat.add_comm] using pushArguments_above prefixValues fresh position
  obtain ⟨_, lifted⟩ := fieldsTyped.lift related
  obtain ⟨fieldBinders, stripped, count, fieldRows⟩ := lifted.ruleRow_binders
  have fieldCount : (fields.drop frame.rule.ctorParams).length = frame.rule.nfields := by
    rw [List.length_drop, firing.fieldCount]
    omega
  rw [fieldCount] at stripped count
  refine ⟨prefixBinders, recursorResidual, fieldType, fieldBinders, _,
    prefixStripped, prefixCount, instantiated, stripped, count, ?_⟩
  intro body
  rw [ruleRowForalls_append, pushArguments_append]
  exact (prefixRows (ruleRowForalls fieldBinders body)).append (fieldRows body)

/-- Recover the complete capture-avoiding residual of an actual public
application. The constructor-index guard can now be applied to the same
residual the executable telescope operation computes. -/
theorem DenotedApplication.instPisAtLift_result
    {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {valuation : Nat → V}
    {expression result : Kernel.Expr} {expressions : List Kernel.Expr} {arguments : List V}
    (application : DenotedApplication values env levels valuation expression
      expressions arguments result) :
    Kernel.Expr.instPisAtLift expressions expression = some result := by
  induction application with
  | nil => rfl
  | cons _ _ _ _ ih => exact ih

/-- The source's actual index-comparison guard yields the generated
constructor residual and the recursor's index values from the real tuple.
It is used with the exact application derived from constructor typing,
not with an independently supplied residual or a target recursor frame. -/
theorem RuleTupleTyping.firing_constructor_indices
    {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    (sourceWf : Kernel.EnvWF env) {levels : Kernel.Name → Nat}
    {name : Kernel.Name} {index : Nat} {frame : InstalledRuleFrame env name index}
    {universes constructorUniverses : List Kernel.Level}
    {valuation : Nat → V} {arguments fields : List V}
    (typed : RuleTupleTyping values env levels frame universes constructorUniverses
      valuation arguments fields)
    (firing : SourceRuleComparisons values env levels frame universes constructorUniverses
      (pushArguments valuation (arguments ++ fields))
      ((argumentVariables (arguments ++ fields).length).take arguments.length)
      ((argumentVariables (arguments ++ fields).length).drop arguments.length) arguments fields) :
    let fresh := pushArguments valuation (arguments ++ fields)
    let fieldExpressions := (argumentVariables (arguments ++ fields).length).drop arguments.length
    ∃ head indices indexValues,
      Kernel.Expr.instPisAtLift fieldExpressions
        (frame.constructor.type.instantiateLevelParams
          frame.constructor.levelParams constructorUniverses) =
        some (Kernel.Expr.mkAppN head indices) ∧
      DenotesSpine values env levels fresh indices indexValues ∧
      indexValues.drop frame.rule.ctorParams = arguments.drop frame.rulePrefix := by
  dsimp only
  let fresh := pushArguments valuation (arguments ++ fields)
  obtain ⟨finalValuation, result, constructorTyped⟩ :=
    (typed.rebase sourceWf fresh).constructorTyped
  have fieldReadings : DenotesSpine values env levels fresh
      ((argumentVariables (arguments ++ fields).length).drop arguments.length) fields := by
    simpa only [List.drop_left] using
      (DenotesSpine.argumentVariables values env levels valuation
        (arguments ++ fields)).drop arguments.length
  obtain ⟨residual, application⟩ := DenotedApplication.of_telescope constructorTyped fieldReadings
  obtain ⟨head, indices, indexValues, shape, indexReadings, valuesMatch⟩ :=
    firing.indices residual application
  exact ⟨head, indices, indexValues,
    application.instPisAtLift_result.trans (congrArg some shape), indexReadings, valuesMatch⟩

end Ix.CompileCert
