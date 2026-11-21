import Aiur.Scalar.Semantics.WithCalls
import Aiur.Scalar.Circuit.CompileFacts

namespace Aiur.Scalar.Circuit.Compiler

def localsEnvironment (locals : List (String × Var)) (assignment : Var → F) : Environment F :=
  locals.map fun binding => (binding.1, assignment binding.2)

/-- Every existing equation and active call is justified under one simultaneous assignment. -/
structure BuildState.Valid [Field F] (state : BuildState F) (calls : CallRelation F)
    (assignment : Var → F) : Prop where
  constraints : Satisfies state.constraints.toList assignment
  calls : ∀ send ∈ state.sends.toList, send.enable.denote assignment = 1 →
    calls send.channel (send.args.map (ArithExpr.denote assignment)) (assignment send.result)

structure BuildState.WellFormed (state : BuildState F) : Prop where
  constraints : ∀ polynomial ∈ state.constraints.toList, polynomial.inBounds state.nextVar = true
  sends : ∀ send ∈ state.sends.toList, send.inBounds state.nextVar = true

theorem BuildState.Valid.of_subset [Field F] {before after : BuildState F}
    {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid calls assignment)
    (constraints : ∀ polynomial ∈ before.constraints.toList, polynomial ∈ after.constraints.toList)
    (sends : ∀ send ∈ before.sends.toList, send ∈ after.sends.toList) :
    before.Valid calls assignment :=
  ⟨fun polynomial member => valid.constraints polynomial (constraints polynomial member),
    fun send member => valid.calls send (sends send member)⟩

/-- The default branch's inverse witnesses force every explicit equality to fail. -/
theorem excludeLiterals_sound [Field F] {selector scrutinee : ArithExpr F} {literals : List F}
    {before after : BuildState F}
    (compiled : (excludeLiterals selector scrutinee literals).run before = .ok ((), after))
    {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid calls assignment) :
    before.Valid calls assignment ∧
      (selector.denote assignment = 1 → ∀ literal ∈ literals, scrutinee.denote assignment ≠ literal) := by
  cases literals with
  | nil =>
      simp [excludeLiterals, StateT.run, StateT.pure, pure, Except.pure] at compiled
      subst after
      exact ⟨valid, by simp⟩
  | cons value rest =>
      cases restRun : excludeLiterals selector scrutinee rest {
          before with nextVar := before.nextVar + 1
                      constraints := before.constraints.push
                        (.mul selector (.sub (.mul (.sub scrutinee (.const value))
                          (.var before.nextVar)) (.const 1))) } with
      | error error =>
          simp [excludeLiterals, StateT.run, StateT.bind, bind, Except.bind, restRun] at compiled
      | ok output =>
          rcases output with ⟨finished, state⟩
          cases finished
          simp [excludeLiterals, StateT.run, StateT.bind, bind, Except.bind, restRun] at compiled
          subst after
          obtain ⟨middleValid, restExcluded⟩ := excludeLiterals_sound restRun valid
          refine ⟨middleValid.of_subset (fun equation member => by simp [member])
            (fun _ member => member), ?_⟩
          intro active literal member
          rcases List.mem_cons.mp member with same | member
          · subst literal
            have equation := middleValid.constraints
              (.mul selector (.sub (.mul (.sub scrutinee (.const value))
                (.var before.nextVar)) (.const 1))) (by simp)
            apply default_excludes_literal
            simpa [ArithExpr.denote, active] using equation
          · exact restExcluded active literal member
termination_by literals.length

mutual
  /-- The first conclusion transports validity backwards; the second handles active expressions. -/
  theorem lowerExpr_sound [Field F] [DecidableEq F]
    {function : String} {locals : List (String × Var)} {enable : ArithExpr F} {expr : Expr F}
    {before after : BuildState F} {polynomial : ArithExpr F}
    (compiled : (lowerExpr function locals enable expr).run before = .ok (polynomial, after))
    {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid calls assignment) :
    before.Valid calls assignment ∧
      (enable.denote assignment = 1 →
        EvalExprWith calls (localsEnvironment locals assignment) expr (polynomial.denote assignment)) := by
    cases expr with
    | literal value =>
        simp [lowerExpr, StateT.run, StateT.pure, pure, Except.pure] at compiled
        rcases compiled with ⟨rfl, rfl⟩
        exact ⟨valid, fun _ => .literal⟩
    | var name =>
        cases found : locals.find? (·.1 == name) with
        | none =>
            simp [lowerExpr, found, StateT.run] at compiled
            cases compiled
        | some binding =>
            rcases binding with ⟨bindingName, id⟩
            have same : bindingName = name := by simpa using List.find?_some found
            subst bindingName
            simp [lowerExpr, found, StateT.run, StateT.pure, pure, Except.pure] at compiled
            rcases compiled with ⟨rfl, rfl⟩
            refine ⟨valid, fun _ => .var ?_⟩
            simp [localsEnvironment, List.find?_map, Function.comp_def, found, ArithExpr.denote]
    | neg expr =>
        cases lowered : lowerExpr function locals enable expr before with
        | error error =>
            simp [lowerExpr, StateT.run, StateT.bind, bind, Except.bind, lowered] at compiled
        | ok output =>
            rcases output with ⟨inner, state⟩
            simp [lowerExpr, StateT.run, StateT.bind, StateT.pure, bind, pure,
              Except.bind, Except.pure, lowered] at compiled
            rcases compiled with ⟨rfl, rfl⟩
            obtain ⟨beforeValid, evaluated⟩ := lowerExpr_sound lowered valid
            refine ⟨beforeValid, fun active => ?_⟩
            simpa [ArithExpr.denote] using EvalExprWith.neg (evaluated active)
    | binary op left right =>
        cases leftRun : lowerExpr function locals enable left before with
        | error error =>
            simp [lowerExpr, StateT.run, StateT.bind, bind, Except.bind, leftRun] at compiled
        | ok output =>
            rcases output with ⟨leftPolynomial, middle⟩
            cases rightRun : lowerExpr function locals enable right middle with
            | error error =>
                simp [lowerExpr, StateT.run, StateT.bind, bind, Except.bind, leftRun, rightRun] at compiled
            | ok output =>
                rcases output with ⟨rightPolynomial, state⟩
                cases op with
                | add | sub | mul =>
                    simp [lowerExpr, StateT.run, StateT.bind, StateT.pure, bind, pure,
                      Except.bind, Except.pure, leftRun, rightRun] at compiled
                    rcases compiled with ⟨rfl, rfl⟩
                    obtain ⟨middleValid, rightEval⟩ := lowerExpr_sound rightRun valid
                    obtain ⟨beforeValid, leftEval⟩ := lowerExpr_sound leftRun middleValid
                    refine ⟨beforeValid, fun active => ?_⟩
                    first
                    | exact .add (leftEval active) (rightEval active)
                    | exact .sub (leftEval active) (rightEval active)
                    | exact .mul (leftEval active) (rightEval active)
                | div =>
                    simp [lowerExpr, fresh, guarded, constrain, StateT.run, StateT.bind,
                      StateT.pure, bind, pure, Except.bind, Except.pure, leftRun, rightRun] at compiled
                    rcases compiled with ⟨rfl, rfl⟩
                    have stateValid : state.Valid calls assignment :=
                      valid.of_subset (fun equation member => by simp [member]) (fun _ member => member)
                    obtain ⟨middleValid, rightEval⟩ := lowerExpr_sound rightRun stateValid
                    obtain ⟨beforeValid, leftEval⟩ := lowerExpr_sound leftRun middleValid
                    refine ⟨beforeValid, fun active => ?_⟩
                    have equation := valid.constraints
                      (.mul enable (.sub (.mul rightPolynomial (.var state.nextVar)) (.const 1))) (by simp)
                    have inverseEquation : rightPolynomial.denote assignment * assignment state.nextVar - 1 = 0 := by
                      simpa [ArithExpr.denote, active] using equation
                    have evaluated := EvalExprWith.div (leftEval active) (rightEval active)
                      (inverse_nonzero inverseEquation)
                    simpa [ArithExpr.denote, inverse_eq inverseEquation, div_eq_mul_inv] using evaluated
    | call name args =>
        cases argsRun : lowerArgs function locals enable args before with
        | error error =>
            simp [lowerExpr, StateT.run, StateT.bind, bind, Except.bind, argsRun] at compiled
        | ok output =>
            rcases output with ⟨arguments, state⟩
            simp [lowerExpr, fresh, boolean, constrain, StateT.run, StateT.bind,
              StateT.pure, bind, pure, Except.bind, Except.pure, argsRun] at compiled
            rcases compiled with ⟨rfl, rfl⟩
            have stateValid : state.Valid calls assignment :=
              valid.of_subset (fun equation member => by simp [member]) (fun send member => by simp [member])
            obtain ⟨beforeValid, argumentsEval⟩ := lowerArgs_sound argsRun stateValid
            refine ⟨beforeValid, fun active => .call (argumentsEval active) ?_⟩
            exact valid.calls ⟨name, arguments, state.nextVar, enable⟩ (by simp) active
    | matchValue scrutinee arms =>
        cases checked : checkPatterns function arms [] with
        | error error =>
            simp [lowerExpr, checked, StateT.run, StateT.bind, bind, Except.bind] at compiled
        | ok checkedUnit =>
            cases checkedUnit
            cases scrutineeRun : lowerExpr function locals enable scrutinee before with
            | error error =>
                simp [lowerExpr, checked, StateT.run, StateT.bind, bind, Except.bind,
                  scrutineeRun] at compiled
            | ok output =>
                rcases output with ⟨scrutineePolynomial, middle⟩
                cases armsRun : lowerArms function locals scrutineePolynomial middle.nextVar
                    (literalPatterns arms) arms { middle with nextVar := middle.nextVar + 1 } with
                | error error =>
                    simp [lowerExpr, checked, StateT.run, StateT.bind, bind, Except.bind,
                      scrutineeRun, armsRun] at compiled
                | ok output =>
                    rcases output with ⟨selectors, state⟩
                    simp [lowerExpr, checked, StateT.run, StateT.bind,
                      StateT.pure, bind, pure, Except.bind, Except.pure, scrutineeRun, armsRun] at compiled
                    rcases compiled with ⟨rfl, rfl⟩
                    have stateValid : state.Valid calls assignment :=
                      valid.of_subset (fun equation member => by simp [member]) (fun _ member => member)
                    obtain ⟨middleValid, armsEval⟩ := lowerArms_sound checked
                      (fun _ member => member) armsRun stateValid
                    obtain ⟨beforeValid, scrutineeEval⟩ := lowerExpr_sound scrutineeRun
                      ⟨middleValid.constraints, middleValid.calls⟩
                    refine ⟨beforeValid, fun active => ?_⟩
                    have equations : Satisfies (selectionConstraints enable selectors) assignment :=
                      fun equation member => valid.constraints equation (by simp [member])
                    have selection : SelectorsValid (1 : F) (selectors.map (ArithExpr.denote assignment)) := by
                      simpa [active] using (selectionConstraints_satisfies enable selectors assignment).mp equations
                    obtain ⟨head, tail, shape, _, _⟩ := selection.active
                    have oneMember : (1 : F) ∈ selectors.map (ArithExpr.denote assignment) := by
                      rw [shape]
                      simp
                    obtain ⟨selector, member, selected⟩ := List.mem_map.mp oneMember
                    obtain ⟨body, arm, _, bodyEval⟩ := armsEval ⟨selector, member, selected⟩
                    exact .matchValue (scrutineeEval active) arm bodyEval
  termination_by sizeOf expr

  theorem lowerArgs_sound [Field F] [DecidableEq F]
      {function : String} {locals : List (String × Var)} {enable : ArithExpr F} {args : List (Expr F)}
      {before after : BuildState F} {polynomials : List (ArithExpr F)}
      (compiled : (lowerArgs function locals enable args).run before = .ok (polynomials, after))
      {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid calls assignment) :
      before.Valid calls assignment ∧
        (enable.denote assignment = 1 → EvalArgsWith calls (localsEnvironment locals assignment)
          args (polynomials.map (ArithExpr.denote assignment))) := by
    cases args with
    | nil =>
        simp [lowerArgs, StateT.run, StateT.pure, pure, Except.pure] at compiled
        rcases compiled with ⟨rfl, rfl⟩
        exact ⟨valid, fun _ => .nil⟩
    | cons head tail =>
        cases headRun : lowerExpr function locals enable head before with
        | error error =>
            simp [lowerArgs, StateT.run, StateT.bind, bind, Except.bind, headRun] at compiled
        | ok output =>
            rcases output with ⟨headPolynomial, middle⟩
            cases tailRun : lowerArgs function locals enable tail middle with
            | error error =>
                simp [lowerArgs, StateT.run, StateT.bind, bind, Except.bind, headRun, tailRun] at compiled
            | ok output =>
                rcases output with ⟨tailPolynomials, finalState⟩
                simp [lowerArgs, StateT.run, StateT.bind, StateT.pure, bind, pure,
                  Except.bind, Except.pure, headRun, tailRun] at compiled
                rcases compiled with ⟨rfl, rfl⟩
                obtain ⟨middleValid, tailEval⟩ := lowerArgs_sound tailRun valid
                obtain ⟨beforeValid, headEval⟩ := lowerExpr_sound headRun middleValid
                exact ⟨beforeValid, fun active => .cons (headEval active) (tailEval active)⟩
  termination_by sizeOf args

  /--
  A selected arm evaluates the match result variable.
  The extra alternative distinguishes a matching literal from a default that excludes
  every explicit pattern; this is needed when skipping earlier arms in the induction.
  -/
  theorem lowerArms_sound [Field F] [DecidableEq F]
      {function : String} {locals : List (String × Var)} {scrutinee : ArithExpr F} {result : Var}
      {literals : List F} {arms : List (Pattern F × Expr F)}
      (checked : checkPatterns function arms [] = .ok ())
      (covers : ∀ literal ∈ literalPatterns arms, literal ∈ literals)
      {before after : BuildState F} {selectors : List (ArithExpr F)}
      (compiled : (lowerArms function locals scrutinee result literals arms).run before = .ok (selectors, after))
      {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid calls assignment) :
      before.Valid calls assignment ∧
        ((∃ selector ∈ selectors, selector.denote assignment = 1) →
          ∃ body, SelectArm (scrutinee.denote assignment) arms body ∧
            (scrutinee.denote assignment ∈ literalPatterns arms ∨
              ∀ literal ∈ literals, scrutinee.denote assignment ≠ literal) ∧
            EvalExprWith calls (localsEnvironment locals assignment) body (assignment result)) := by
    cases arms with
    | nil =>
        simp [lowerArms, StateT.run, StateT.pure, pure, Except.pure] at compiled
        rcases compiled with ⟨rfl, rfl⟩
        exact ⟨valid, by simp⟩
    | cons arm rest =>
        cases armEq : arm
        rename_i pattern body
        simp only [armEq] at checked covers compiled ⊢
        cases pattern with
        | literal value =>
            have distinct := ((checkPatterns_spec function ((.literal value, body) :: rest) []).mp checked).1
            have tailDistinct : value ∉ literalPatterns rest ∧ (literalPatterns rest).Nodup := by
              simpa [literalPatterns] using distinct
            have checkedRest : checkPatterns function rest [] = .ok () :=
              (checkPatterns_spec function rest []).mpr ⟨tailDistinct.2, by simp⟩
            have coversRest : ∀ literal ∈ literalPatterns rest, literal ∈ literals :=
              fun literal member => covers literal (by simp [literalPatterns, member])
            cases bodyRun : lowerExpr function locals (.var before.nextVar) body {
                before with nextVar := before.nextVar + 1
                            constraints := before.constraints.push
                              (.mul (.var before.nextVar) (.sub scrutinee (.const value))) } with
            | error error =>
                simp [lowerArms, StateT.run, StateT.bind, bind, Except.bind, bodyRun] at compiled
            | ok output =>
                rcases output with ⟨bodyPolynomial, middle⟩
                cases restRun : lowerArms function locals scrutinee result literals rest {
                    middle with
                    constraints := middle.constraints.push
                      (.mul (.var before.nextVar) (.sub (.var result) bodyPolynomial)) } with
                | error error =>
                    simp [lowerArms, StateT.run, StateT.bind, bind, Except.bind, bodyRun, restRun] at compiled
                | ok output =>
                    rcases output with ⟨restSelectors, state⟩
                    simp [lowerArms, StateT.run, StateT.bind, StateT.pure, bind, pure,
                      Except.bind, Except.pure, bodyRun, restRun] at compiled
                    rcases compiled with ⟨rfl, rfl⟩
                    obtain ⟨resultValid, restEval⟩ := lowerArms_sound checkedRest coversRest restRun valid
                    have middleValid : middle.Valid calls assignment :=
                      resultValid.of_subset (fun equation member => by simp [member]) (fun _ member => member)
                    obtain ⟨patternValid, bodyEval⟩ := lowerExpr_sound bodyRun middleValid
                    refine ⟨patternValid.of_subset (fun equation member => by simp [member])
                      (fun _ member => member), ?_⟩
                    intro selection
                    by_cases active : assignment before.nextVar = 1
                    · have patternEquation := patternValid.constraints
                        (.mul (.var before.nextVar) (.sub scrutinee (.const value))) (by simp)
                      have equal : scrutinee.denote assignment = value := sub_eq_zero.mp
                        (by simpa [ArithExpr.denote, active] using patternEquation)
                      have resultEquation := resultValid.constraints
                        (.mul (.var before.nextVar) (.sub (.var result) bodyPolynomial)) (by simp)
                      have output : assignment result = bodyPolynomial.denote assignment := sub_eq_zero.mp
                        (by simpa [ArithExpr.denote, active] using resultEquation)
                      refine ⟨body, ?_, Or.inl (by simp [literalPatterns, equal]), ?_⟩
                      · rw [equal]; exact .literal
                      · rw [output]; exact bodyEval active
                    · have tailSelected : ∃ selector ∈ restSelectors, selector.denote assignment = 1 := by
                        obtain ⟨selector, member, enabled⟩ := selection
                        rcases List.mem_cons.mp member with same | member
                        · subst selector; exact (active enabled).elim
                        · exact ⟨selector, member, enabled⟩
                      obtain ⟨selectedBody, selected, reason, evaluated⟩ := restEval tailSelected
                      have different : value ≠ scrutinee.denote assignment := by
                        intro equal
                        rcases reason with member | excluded
                        · rw [← equal] at member
                          exact tailDistinct.1 member
                        · exact excluded value (covers value (by simp [literalPatterns])) equal.symm
                      refine ⟨selectedBody, .skip different selected, ?_, evaluated⟩
                      rcases reason with member | excluded
                      · exact Or.inl (by simp [literalPatterns, member])
                      · exact Or.inr excluded
        | wildcard =>
            cases excludedRun : excludeLiterals (.var before.nextVar) scrutinee literals
                { before with nextVar := before.nextVar + 1 } with
            | error error =>
                simp [lowerArms, StateT.run, StateT.bind, bind, Except.bind, excludedRun] at compiled
            | ok output =>
                rcases output with ⟨finished, middle⟩
                cases finished
                cases bodyRun : lowerExpr function locals (.var before.nextVar) body middle with
                | error error =>
                    simp [lowerArms, StateT.run, StateT.bind, bind, Except.bind, excludedRun, bodyRun] at compiled
                | ok output =>
                    rcases output with ⟨bodyPolynomial, state⟩
                    simp [lowerArms, StateT.run, StateT.bind, StateT.pure, bind, pure,
                      Except.bind, Except.pure, excludedRun, bodyRun] at compiled
                    rcases compiled with ⟨rfl, rfl⟩
                    have stateValid : state.Valid calls assignment :=
                      valid.of_subset (fun equation member => by simp [member]) (fun _ member => member)
                    obtain ⟨middleValid, bodyEval⟩ := lowerExpr_sound bodyRun stateValid
                    obtain ⟨beforeValid, excluded⟩ := excludeLiterals_sound excludedRun middleValid
                    refine ⟨⟨beforeValid.constraints, beforeValid.calls⟩, ?_⟩
                    rintro ⟨selector, member, active⟩
                    have same := List.mem_singleton.mp member
                    subst selector
                    change assignment before.nextVar = 1 at active
                    have resultEquation := valid.constraints
                      (.mul (.var before.nextVar) (.sub (.var result) bodyPolynomial)) (by simp)
                    have output : assignment result = bodyPolynomial.denote assignment := sub_eq_zero.mp
                      (by simpa [ArithExpr.denote, active] using resultEquation)
                    refine ⟨body, .wildcard, Or.inr (excluded active), ?_⟩
                    rw [output]
                    exact bodyEval active
  termination_by sizeOf arms
end

end Aiur.Scalar.Circuit.Compiler
