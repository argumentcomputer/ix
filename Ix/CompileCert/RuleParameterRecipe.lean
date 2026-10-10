import Ix.CompileCert.RuleSourceTuples

/-! # Open parameter recipes at actual source firing tuples

This UNCOMPILED proof slice connects the parameter expressions prescribed by
an installed firing mode to the actual constructor-field telescope. The
ordinary and nested comparisons are exactly `SourceRuleComparisons`; their
denotations and the constructor tuple are not replaced by source restrictions.

The result deliberately retains the plain `paramsBlind` case as an explicit
alternative. That route does not compare its two fitting parameter spines.
No theorem below changes `PublicRecursorLaws`, assumes their equality, or
claims to have proved its parameter-blind branch. The raw source exporter,
installed annotations and full row-coverage connection remain separate.
-/

namespace Ix.CompileCert

/-- The open-expression version of the installed parameter recipe. Nested
pins use the same `instSeqLift` operation as `SourceRuleComparisons.nested`.
This is proof infrastructure, not a replacement for kernel reduction. -/
def InstalledRuleFrame.openParameterRecipe {env : Kernel.Env}
    {name : Kernel.Name} {index : Nat} (frame : InstalledRuleFrame env name index)
    (universes : List Kernel.Level) (argumentExpressions : List Kernel.Expr) :
    List Kernel.Expr :=
  match frame.rule.fire with
  | .nested _ pins => pins.map fun pin =>
      Kernel.Expr.instSeqLift (argumentExpressions.take frame.rulePrefix)
        (frame.rulePrefix - 1)
        (pin.instantiateLevelParams frame.header.levelParams universes)
  | _ => argumentExpressions.take frame.rule.ctorParams

/-- Every firing mode is covered. For comparison-bearing modes, the actual
recipe reads the actual constructor parameters. The only residual alternative
is the real plain parameter-blind flag, not an assumed recipe agreement. -/
theorem SourceRuleComparisons.openParameterRecipe_reading
    {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {name : Kernel.Name} {index : Nat}
    {frame : InstalledRuleFrame env name index}
    {universes constructorUniverses : List Kernel.Level} {valuation : Nat → V}
    {argumentExpressions fieldExpressions : List Kernel.Expr} {arguments fields : List V}
    (firing : SourceRuleComparisons values env levels frame universes constructorUniverses
      valuation argumentExpressions fieldExpressions arguments fields)
    (argumentReadings : DenotesSpine values env levels valuation argumentExpressions arguments) :
    (frame.rule.fire = .plain ∧ frame.rule.paramsBlind = true) ∨
      DenotesSpine values env levels valuation
        (frame.openParameterRecipe universes argumentExpressions)
        (fields.take frame.rule.ctorParams) := by
  cases shape : frame.rule.fire with
  | inert => exact False.elim (frame.fires shape)
  | plain =>
    cases blind : frame.rule.paramsBlind with
    | false =>
      apply Or.inr
      rw [InstalledRuleFrame.openParameterRecipe, shape, firing.plain blind shape]
      exact argumentReadings.take frame.rule.ctorParams
    | true => exact Or.inl ⟨shape, blind⟩
  | nested nestedLevels pins =>
    apply Or.inr
    simpa only [InstalledRuleFrame.openParameterRecipe, shape] using
      firing.nested nestedLevels pins shape

/-- The original public firing tuple supplies every representative needed
by the recipe theorem. A caller does not provide a syntactic parameter tuple,
successful telescope read, field typing or parameter-agreement certificate.
All instantiated binder metadata and dependent field domains are retained.

The plain parameter-blind alternative is intentionally unresolved here; it
does not become a premise restricting the promised public rule law. -/
theorem RuleTupleTyping.generated_parameter_field_row
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
    (frame.rule.fire = .plain ∧ frame.rule.paramsBlind = true) ∨
      ∃ fieldType binders result,
        Kernel.Expr.instPisAtLift (frame.openParameterRecipe universes argumentExpressions)
          (frame.constructor.type.instantiateLevelParams
            frame.constructor.levelParams constructorUniverses) = some fieldType ∧
        fieldType.stripPis frame.rule.nfields = some (binders, result) ∧
        binders.length = frame.rule.nfields ∧
        ∀ body, InstalledTelescope values env levels fresh (ruleRowForalls binders body)
          (fields.drop frame.rule.ctorParams)
          (pushArguments fresh (fields.drop frame.rule.ctorParams)) body := by
  dsimp only
  let fresh := pushArguments valuation (arguments ++ fields)
  have argumentReadings : DenotesSpine values env levels fresh
      ((argumentVariables (arguments ++ fields).length).take arguments.length) arguments := by
    simpa only [List.take_left] using
      (DenotesSpine.argumentVariables values env levels valuation
        (arguments ++ fields)).take arguments.length
  rcases firing.openParameterRecipe_reading argumentReadings with blind | parameterReadings
  · exact Or.inl blind
  · apply Or.inr
    obtain ⟨finalValuation, result, constructorTyped⟩ :=
      (typed.rebase sourceWf fresh).constructorTyped
    have splitTyped : InstalledTelescope values env levels fresh
        (frame.constructor.type.instantiateLevelParams
          frame.constructor.levelParams constructorUniverses)
        (fields.take frame.rule.ctorParams ++ fields.drop frame.rule.ctorParams)
        finalValuation result := by
      simpa only [List.take_append_drop] using constructorTyped
    obtain ⟨fieldType, finalResult, instantiated, fieldsTyped⟩ :=
      splitTyped.instPisAtLift_prefix parameterReadings
    obtain ⟨binders, stripped, count, replaceBody⟩ := fieldsTyped.ruleRow_binders
    have fieldCount : (fields.drop frame.rule.ctorParams).length = frame.rule.nfields := by
      rw [List.length_drop, firing.fieldCount]
      omega
    rw [fieldCount] at stripped count
    exact ⟨fieldType, binders, finalResult, instantiated, stripped, count, replaceBody⟩

/-- The source invariant supplies the actual nested major-domain shape and
pin scope. The original firing judgment supplies the missing pin count, even
when the input expressions are open. This does not assume raw exporter success
or identify an independently installed annotation with its raw source. -/
theorem SourceRuleComparisons.nested_recipe_shape
    {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    (sourceWf : Kernel.EnvWF env) {levels : Kernel.Name → Nat}
    {name : Kernel.Name} {index : Nat} {frame : InstalledRuleFrame env name index}
    {universes constructorUniverses nestedLevels : List Kernel.Level}
    {valuation : Nat → V} {argumentExpressions fieldExpressions pins : List Kernel.Expr}
    {arguments fields : List V}
    (firing : SourceRuleComparisons values env levels frame universes constructorUniverses
      valuation argumentExpressions fieldExpressions arguments fields)
    (nested : frame.rule.fire = .nested nestedLevels pins) :
    frame.rulePrefix ≤ frame.major ∧
    pins.length = frame.rule.ctorParams ∧
    (∀ pin ∈ pins, pin.hasFvar = false ∧
      pin.allLevelParamsDefined frame.header.levelParams = true ∧
      pin.constsResolve env = true ∧ pin.looseBVarsBounded frame.rulePrefix = true) ∧
    ∃ binders domain body metadata family,
      frame.header.type.stripPis frame.major = some (binders, .forallE domain body metadata) ∧
      domain.getAppFn = .const family nestedLevels ∧
      domain.getAppArgs =
        pins.map (Kernel.Expr.liftLooseBVars (frame.major - frame.rulePrefix) 0) ++
          (List.range (frame.major - frame.rulePrefix)).map
            (fun i => Kernel.Expr.bvar (frame.major - frame.rulePrefix - 1 - i)) := by
  have wf := sourceWf _ (Kernel.Semantics.Env.find?_mem frame.recursorLookup)
  have ruleWf := wf.2.2.2.2.2.1 frame.header frame.major frame.rulePrefix frame.rules rfl
    frame.rule (List.mem_of_getElem? frame.ruleLookup)
  have shape := ruleWf.2.2.2.2 nestedLevels pins nested
  have length := (firing.nested nestedLevels pins nested).length
  have pinCount : pins.length = frame.rule.ctorParams := by
    simp only [List.length_map, List.length_take] at length
    rw [firing.fieldCount] at length
    omega
  exact ⟨shape.1, pinCount, shape.2.2.1, shape.2.2.2⟩

/-- Source universe selection already equates the constructor's actual
semantic instance with its generated universe recipe. This holds for every
value interpretation, including the target-derived public source one; it does
not prove the recipe's syntactic arity or transport the constructor telescope. -/
theorem RuleUniverseSelection.constructor_value
    {V : Type u} {env : Kernel.Env} {name : Kernel.Name} {index : Nat}
    {frame : InstalledRuleFrame env name index} {levels : Kernel.Name → Nat}
    {universes constructorUniverses : List Kernel.Level}
    (selection : RuleUniverseSelection frame levels universes constructorUniverses)
    (values : Kernel.Name → (Kernel.Name → Nat) → V) :
    values frame.rule.ctor
        (Kernel.Level.substFn levels frame.constructor.levelParams constructorUniverses) =
      values frame.rule.ctor (Kernel.Level.substFn levels frame.constructor.levelParams
        (frame.universeComparands.map (Kernel.Level.subst frame.header.levelParams universes))) := by
  rw [← frame.universeComparands_instance universes]
  exact congrArg (values frame.rule.ctor) selection.assignment

end Ix.CompileCert
