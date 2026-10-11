import Ix.CompileCert.RuleRows

/-! # Source-side preparation of firing-row tuples

The source rule exporter substitutes open parameter expressions with
`sourceInstantiate`. Its kernel counterpart is `instPisAtLift`, not `instPis`.
The first bridge below retains the complete optional result of this operation
whenever the original expression and supplied arguments have exported.

The semantic bridge then starts from the existing `RuleTupleTyping` of a real
source firing instance. It derives a typed constructor-field suffix, including
the exact dependent binder domains, in the same fresh valuation used by
`PublicRecursorLaws`. No target recursor frame or source strong model is used.

This is an UNCOMPILED additive slice. Joining that suffix to the actual
recursor prefix, matching the exported `leanRuleStatement` and the installed
theorem's annotations, and deriving the complete checked row remain open.
No existing checker, runtime, public endpoint or source domain changes here.
-/

namespace Ix.CompileCert

/-- Retain an unsuccessful telescope read as `none`; a successful residual is
exported by the same independent expression exporter as the rule statement. -/
def exportRuleResidual (cx : TermContext) : Option Lean.Expr → ExportM (Option Kernel.Expr)
  | none => .ok none
  | some expression => some <$> exportExpr cx expression

theorem exportExpr_sourceDropMData (cx : TermContext) (source : Lean.Expr) :
    exportExpr cx (sourceDropMData source) = exportExpr cx source := by
  induction source with
  | mdata metadata expression ih => exact ih
  | _ => rfl

private theorem sourceDropMData_not_mdata (source : Lean.Expr)
    (metadata : Lean.MData) (body : Lean.Expr) :
    sourceDropMData source ≠ .mdata metadata body := by
  induction source with
  | mdata metadata expression ih => exact ih
  | _ => simp only [sourceDropMData, reduceCtorEq, not_false_eq_true]

/-- The actual open-telescope operation used twice in `leanRuleStatement`
commutes with export. Missing forall binders remain `none`; no successful
source telescope read is assumed. Export failures outside the stated actual
expression/argument exports are not reclassified as shape failures. -/
theorem exportExpr_sourceInstForalls {cx : TermContext}
    {arguments : List Lean.Expr} {targetArguments : List Kernel.Expr}
    {source : Lean.Expr} {target : Kernel.Expr}
    (sourceExported : exportExpr cx source = .ok target)
    (argumentsExported : arguments.mapM (exportExpr cx) = .ok targetArguments) :
    exportRuleResidual cx (sourceInstForalls arguments source) =
      .ok (Kernel.Expr.instPisAtLift targetArguments target) := by
  induction arguments generalizing source target targetArguments with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at argumentsExported
    subst targetArguments
    simp only [sourceInstForalls, exportRuleResidual, sourceExported,
      Functor.map, Except.map, Kernel.Expr.instPisAtLift]
  | cons argument arguments ih =>
    cases headExported : exportExpr cx argument with
    | error why =>
      simp [List.mapM_cons, headExported, bind, Except.bind] at argumentsExported
    | ok targetArgument =>
      cases tailExported : arguments.mapM (exportExpr cx) with
      | error why =>
        simp [List.mapM_cons, headExported, tailExported, bind, Except.bind] at argumentsExported
      | ok targetTail =>
        simp only [List.mapM_cons, headExported, tailExported, bind, Except.bind,
          pure, Except.pure, Except.ok.injEq] at argumentsExported
        subst targetArguments
        have droppedExported : exportExpr cx (sourceDropMData source) = .ok target :=
          (exportExpr_sourceDropMData cx source).trans sourceExported
        simp only [sourceInstForalls]
        cases dropped : sourceDropMData source with
        | mdata metadata body =>
          exact False.elim (sourceDropMData_not_mdata source metadata body dropped)
        | forallE name domain body info =>
          rw [dropped] at droppedExported
          cases domainExported : exportExpr cx domain with
          | error why =>
            simp [exportExpr, domainExported, bind, Except.bind] at droppedExported
          | ok targetDomain =>
            cases bodyExported : exportExpr cx body with
            | error why =>
              simp [exportExpr, domainExported, bodyExported, bind, Except.bind] at droppedExported
            | ok targetBody =>
              simp only [exportExpr, domainExported, bodyExported, bind, Except.bind,
                pure, Except.pure, Except.ok.injEq] at droppedExported
              subst target
              exact ih (exportExpr_instantiate bodyExported headExported 0) tailExported
        | _ =>
          simp only [dropped, exportExpr, bind, Except.bind, pure, Except.pure] at droppedExported
          repeat' split at droppedExported
          all_goals try contradiction
          all_goals simp only [Except.ok.injEq] at droppedExported
          all_goals subst target
          all_goals rfl

/-- Consume a prefix of an actual dependent tuple at expressions denoting
that prefix's values. The remaining tuple is derived, with the actual
capture-avoiding residual and final valuation. No prefix-read success or
independently asserted typing of the substituted suffix is required. -/
theorem InstalledTelescope.instPisAtLift_prefix {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {valuation finalValuation : Nat → V}
    {expression result : Kernel.Expr} {parameterExpressions : List Kernel.Expr}
    {parameters arguments : List V}
    (typed : InstalledTelescope values env levels valuation expression
      (parameters ++ arguments) finalValuation result)
    (readings : DenotesSpine values env levels valuation parameterExpressions parameters) :
    ∃ residual finalResult,
      Kernel.Expr.instPisAtLift parameterExpressions expression = some residual ∧
      InstalledTelescope values env levels valuation residual arguments
        (pushArguments valuation arguments) finalResult := by
  induction readings generalizing expression finalValuation result with
  | nil =>
    refine ⟨expression, result, rfl, ?_⟩
    have final := typed.final_valuation
    simpa only [List.nil_append, final] using typed
  | cons argumentRead restRead ih =>
    cases typed with
    | cons domainRead argumentTyped rest =>
      obtain ⟨_, substituted⟩ := rest.instantiate1Lift (depth := 0) rfl argumentRead
      obtain ⟨residual, finalResult, computed, suffix⟩ := ih substituted
      exact ⟨residual, finalResult, computed, suffix⟩

/-- Recover every consumed annotated binder from the actual typed telescope.
The same dependent domains type the same tuple for any residual row body.
Neither binder annotations nor dependencies on earlier arguments are erased. -/
theorem InstalledTelescope.ruleRow_binders {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {valuation finalValuation : Nat → V}
    {expression result : Kernel.Expr} {arguments : List V}
    (typed : InstalledTelescope values env levels valuation expression
      arguments finalValuation result) :
    ∃ binders,
      expression.stripPis arguments.length = some (binders, result) ∧
      binders.length = arguments.length ∧
      ∀ body, InstalledTelescope values env levels valuation
        (ruleRowForalls binders body) arguments finalValuation body := by
  induction typed with
  | nil => exact ⟨[], rfl, rfl, fun _ => .nil⟩
  | @cons valuation domain body binder argument domainValue arguments finalValuation result
      domainRead argumentTyped rest ih =>
    obtain ⟨binders, stripped, count, replacement⟩ := ih
    refine ⟨(domain, binder) :: binders, ?_, congrArg Nat.succ count, ?_⟩
    · simp only [List.length_cons, Kernel.Expr.stripPis, stripped, Option.map_some]
    · intro rowBody
      exact .cons domainRead argumentTyped (replacement rowBody)

/-- Every source tuple, including arbitrary semantic values with no closed
syntactic representative, supplies its actual constructor parameters in the
canonical fresh-variable valuation. Substitution succeeds and types the
remaining fields. `count` is arbitrary; the firing corollary selects the
stored rule's count and derives its field length from the original guards. -/
theorem RuleTupleTyping.constructor_parameter_instance {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    (sourceWf : Kernel.EnvWF env) {levels : Kernel.Name → Nat}
    {name : Kernel.Name} {index : Nat} {frame : InstalledRuleFrame env name index}
    {universes constructorUniverses : List Kernel.Level}
    {valuation : Nat → V} {arguments fields : List V}
    (typed : RuleTupleTyping values env levels frame universes constructorUniverses
      valuation arguments fields) (count : Nat) :
    let fresh := pushArguments valuation (arguments ++ fields)
    let parameters := ((argumentVariables (arguments ++ fields).length).drop arguments.length).take count
    ∃ residual finalResult,
      Kernel.Expr.instPisAtLift parameters
        (frame.constructor.type.instantiateLevelParams
          frame.constructor.levelParams constructorUniverses) = some residual ∧
      InstalledTelescope values env levels fresh residual (fields.drop count)
        (pushArguments fresh (fields.drop count)) finalResult := by
  dsimp only
  let fresh := pushArguments valuation (arguments ++ fields)
  obtain ⟨finalValuation, result, constructorTyped⟩ :=
    (typed.rebase sourceWf fresh).constructorTyped
  have fieldReadings : DenotesSpine values env levels fresh
      ((argumentVariables (arguments ++ fields).length).drop arguments.length) fields := by
    simpa only [List.drop_left] using
      (DenotesSpine.argumentVariables values env levels valuation (arguments ++ fields)).drop arguments.length
  have splitTyped : InstalledTelescope values env levels fresh
      (frame.constructor.type.instantiateLevelParams frame.constructor.levelParams constructorUniverses)
      (fields.take count ++ fields.drop count) finalValuation result := by
    simpa only [List.take_append_drop] using constructorTyped
  exact splitTyped.instPisAtLift_prefix (fieldReadings.take count)

/-- The original firing guards determine the complete field telescope's
length. Its actual binder domains type the real field suffix for any row
body, without a proposed-tuple typing premise, a target frame, or a restriction
to plain, nonindexed or nonnested rules. This is the field half of the row;
the actual exported recursor-prefix join remains a separate obligation. -/
theorem RuleTupleTyping.firing_field_row {V : Type u} [Kernel.SetTheory V]
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
    let parameters := ((argumentVariables (arguments ++ fields).length).drop arguments.length).take
      frame.rule.ctorParams
    ∃ fieldType binders result,
      Kernel.Expr.instPisAtLift parameters
        (frame.constructor.type.instantiateLevelParams
          frame.constructor.levelParams constructorUniverses) = some fieldType ∧
      fieldType.stripPis frame.rule.nfields = some (binders, result) ∧
      binders.length = frame.rule.nfields ∧
      ∀ body, InstalledTelescope values env levels fresh (ruleRowForalls binders body)
        (fields.drop frame.rule.ctorParams)
        (pushArguments fresh (fields.drop frame.rule.ctorParams)) body := by
  dsimp only
  obtain ⟨fieldType, result, computed, fieldsTyped⟩ :=
    typed.constructor_parameter_instance sourceWf frame.rule.ctorParams
  obtain ⟨binders, stripped, count, replaceBody⟩ := fieldsTyped.ruleRow_binders
  have fieldCount : (fields.drop frame.rule.ctorParams).length = frame.rule.nfields := by
    rw [List.length_drop, firing.fieldCount]
    omega
  rw [fieldCount] at stripped count
  exact ⟨fieldType, binders, result, computed, stripped, count, replaceBody⟩

/-- Open parameters distinguish the source export's operation from the
non-lifting instantiator. This is a structural sensitivity control, not a
counterexample to a checked compiler or a claim about the diagnostic result. -/
theorem open_rule_parameter_control (binder : Kernel.BinderMeta) :
    Kernel.Expr.instPis
      (.forallE (.sort .zero) (.forallE (.sort .zero) (.bvar 1) binder) binder)
      [.bvar 0] = some (.forallE (.sort .zero) (.bvar 0) binder) ∧
    Kernel.Expr.instPisAtLift [.bvar 0]
      (.forallE (.sort .zero) (.forallE (.sort .zero) (.bvar 1) binder) binder) =
        some (.forallE (.sort .zero) (.bvar 1) binder) := ⟨rfl, rfl⟩

/-- A closed replacement is the adjacent case where both operations agree. -/
theorem closed_rule_parameter_neighbour (binder : Kernel.BinderMeta) :
    Kernel.Expr.instPis
      (.forallE (.sort .zero) (.forallE (.sort .zero) (.bvar 1) binder) binder)
      [.sort .zero] = some (.forallE (.sort .zero) (.sort .zero) binder) ∧
    Kernel.Expr.instPisAtLift [.sort .zero]
      (.forallE (.sort .zero) (.forallE (.sort .zero) (.bvar 1) binder) binder) =
        some (.forallE (.sort .zero) (.sort .zero) binder) := ⟨rfl, rfl⟩

end Ix.CompileCert
