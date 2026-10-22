import Aiur.Tuple.Circuit.PatternCorrectness
import Aiur.Tuple.Circuit.ValueCorrectness

namespace Aiur.Tuple.Circuit.Compiler

set_option maxHeartbeats 800000

mutual
  /-- A satisfying assignment recovers evaluation whenever this expression is enabled. -/
  theorem lowerExpr_sound [Field F] [DecidableEq F]
      {program : Program F} {function : String} {locals : Locals F}
      {enable : ArithExpr F} {expr : Expr F} {output : Symbolic F}
      {before after : BuildState F}
      (compiled : lowerExpr program function locals enable expr before = .ok (output, after))
      {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid calls assignment) :
      before.Valid calls assignment ∧ (enable.denote assignment = 1 →
        EvalExprWith calls (localsEnvironment locals assignment) expr
          (output.map (ArithExpr.denote assignment))) := by
    cases expr with
    | literal value =>
        simp only [lowerExpr, pure_ok] at compiled
        obtain ⟨rfl, rfl⟩ := compiled
        exact ⟨valid, fun _ => by simpa only [Value.map, Scalar.Circuit.ArithExpr.denote] using EvalExprWith.literal⟩
    | var name =>
        cases found : locals.find? (·.1 == name) with
        | none => simp [lowerExpr, found] at compiled
        | some binding =>
            obtain ⟨bindingName, value⟩ := binding
            have same : bindingName = name := by simpa using List.find?_some found
            subst bindingName
            simp only [lowerExpr, found, pure_ok] at compiled
            obtain ⟨rfl, rfl⟩ := compiled
            exact ⟨valid, fun _ => .var (by
              simp [localsEnvironment, List.find?_map, Function.comp_def, found])⟩
    | tuple items =>
        simp only [lowerExpr] at compiled
        obtain ⟨values, middle, itemsRun, finished⟩ := bind_ok.mp compiled
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        obtain ⟨beforeValid, evaluated⟩ := lowerArgs_sound itemsRun valid
        exact ⟨beforeValid, fun active => by
          simpa only [Value.map] using EvalExprWith.tuple (evaluated active)⟩
    | project value index =>
        simp only [lowerExpr] at compiled
        obtain ⟨input, middle, valueRun, rest⟩ := bind_ok.mp compiled
        cases input with
        | field => simp at rest
        | tuple items =>
            cases projected : items[index]? with
            | none => simp [projected] at rest
            | some result =>
                simp only [projected, pure_ok] at rest
                obtain ⟨rfl, rfl⟩ := rest
                obtain ⟨beforeValid, evaluated⟩ := lowerExpr_sound valueRun valid
                refine ⟨beforeValid, fun active => .project (evaluated active) ?_⟩
                simp [Value.map, projectValue, List.getElem?_map, projected, pure, Except.pure]
    | letValue pattern value body =>
        simp only [lowerExpr] at compiled
        obtain ⟨input, s₁, valueRun, rest⟩ := bind_ok.mp compiled
        obtain ⟨⟨test, bindings⟩, s₂, patternRun, rest⟩ := bind_ok.mp rest
        obtain ⟨finished, s₃, guardRun, bodyRun⟩ := bind_ok.mp rest
        cases finished
        obtain ⟨s₃Valid, bodyEval⟩ := lowerExpr_sound bodyRun valid
        obtain ⟨s₂Valid, equation⟩ := constrain_valid guardRun s₃Valid
        obtain ⟨s₁Valid, matched⟩ := lowerPattern_sound patternRun s₂Valid
        obtain ⟨beforeValid, valueEval⟩ := lowerExpr_sound valueRun s₁Valid
        refine ⟨beforeValid, fun active => ?_⟩
        change enable.denote assignment * (test.denote assignment - 1) = 0 at equation
        have testOne : test.denote assignment = 1 := by
          simpa [active, sub_eq_zero] using equation
        rcases matched with ⟨matched, _⟩ | ⟨_, testZero⟩
        · exact .letValue (valueEval active) matched (by
            simpa only [localsEnvironment_append] using bodyEval active)
        · exact (zero_ne_one (testZero.symm.trans testOne)).elim
    | neg value =>
        simp only [lowerExpr] at compiled
        obtain ⟨input, s₁, valueRun, rest⟩ := bind_ok.mp compiled
        obtain ⟨polynomial, s₂, fieldRun, finished⟩ := bind_ok.mp rest
        obtain ⟨rfl, rfl⟩ := asField_ok fieldRun
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        obtain ⟨beforeValid, evaluated⟩ := lowerExpr_sound valueRun valid
        exact ⟨beforeValid, fun active => .neg (evaluated active) (by
          simp [Value.map, evalNeg, ArithExpr.denote, Scalar.Circuit.ArithExpr.denote])⟩
    | binary op left right =>
        simp only [lowerExpr] at compiled
        obtain ⟨leftValue, s₁, leftRun, rest⟩ := bind_ok.mp compiled
        obtain ⟨leftPoly, s₂, leftField, rest⟩ := bind_ok.mp rest
        obtain ⟨rfl, rfl⟩ := asField_ok leftField
        obtain ⟨rightValue, s₃, rightRun, rest⟩ := bind_ok.mp rest
        obtain ⟨rightPoly, s₄, rightField, rest⟩ := bind_ok.mp rest
        obtain ⟨rfl, rfl⟩ := asField_ok rightField
        cases op with
        | add | sub | mul =>
            obtain ⟨rfl, rfl⟩ := pure_ok.mp rest
            obtain ⟨s₁Valid, rightEval⟩ := lowerExpr_sound rightRun valid
            obtain ⟨beforeValid, leftEval⟩ := lowerExpr_sound leftRun s₁Valid
            exact ⟨beforeValid, fun active => .binary (leftEval active) (rightEval active) (by
              simp [Value.map, evalBinOp, ArithExpr.denote, Scalar.Circuit.ArithExpr.denote])⟩
        | div =>
            obtain ⟨inverse, s₅, freshRun, rest⟩ := bind_ok.mp rest
            obtain ⟨finished, s₆, inverseRun, finishedRun⟩ := bind_ok.mp rest
            cases finished
            obtain ⟨rfl, rfl⟩ := pure_ok.mp finishedRun
            obtain ⟨s₅Valid, equation⟩ := constrain_valid inverseRun valid
            have s₃Valid := fresh_valid freshRun s₅Valid
            obtain ⟨s₁Valid, rightEval⟩ := lowerExpr_sound rightRun s₃Valid
            obtain ⟨beforeValid, leftEval⟩ := lowerExpr_sound leftRun s₁Valid
            refine ⟨beforeValid, fun active => .binary (leftEval active) (rightEval active) ?_⟩
            change enable.denote assignment * (rightPoly.denote assignment * assignment inverse - 1) = 0
              at equation
            rw [active, one_mul] at equation
            simp [Value.map, evalBinOp, ArithExpr.denote, Scalar.Circuit.ArithExpr.denote,
              Scalar.Circuit.inverse_nonzero equation, Scalar.Circuit.inverse_eq equation, div_eq_mul_inv]
    | call name args =>
        cases found : program.findFunction? name with
        | none => simp [lowerExpr, found] at compiled
        | some callee =>
            simp only [lowerExpr, found] at compiled
            obtain ⟨arguments, s₁, argsRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨result, s₂, resultRun, rest⟩ := bind_ok.mp rest
            obtain ⟨finished, s₃, booleanRun, rest⟩ := bind_ok.mp rest
            cases finished
            simp [StateT.bind, bind, Except.bind, StateT.pure, pure, Except.pure] at rest
            obtain ⟨rfl, rfl⟩ := rest
            have s₃Valid : s₃.Valid calls assignment :=
              valid.of_subset (fun _ member => member) (fun _ member => by simp [member])
            have s₂Valid := (boolean_valid booleanRun s₃Valid).1
            have s₁Valid := freshValue_valid resultRun s₂Valid
            obtain ⟨beforeValid, argsEval⟩ := lowerArgs_sound argsRun s₁Valid
            refine ⟨beforeValid, fun active => .call (argsEval active) ?_⟩
            simpa only [Value.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using
              valid.calls ⟨name, arguments, result, enable⟩ (by simp) active
    | matchValue scrutinee arms =>
        simp only [lowerExpr] at compiled
        obtain ⟨checked, s₁, checkRun, rest⟩ := bind_ok.mp compiled
        obtain ⟨_, rfl⟩ := lift_eq_ok checkRun
        obtain ⟨type, s₂, typeRun, rest⟩ := bind_ok.mp rest
        obtain ⟨_, rfl⟩ := lift_eq_ok typeRun
        obtain ⟨input, s₃, scrutineeRun, rest⟩ := bind_ok.mp rest
        obtain ⟨result, s₄, resultRun, rest⟩ := bind_ok.mp rest
        obtain ⟨selectors, s₅, armsRun, rest⟩ := bind_ok.mp rest
        obtain ⟨finished, s₆, exclusionRun, rest⟩ := bind_ok.mp rest
        cases finished
        obtain ⟨finished, s₇, sumRun, finishedRun⟩ := bind_ok.mp rest
        cases finished
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finishedRun
        obtain ⟨s₆Valid, sumEquation⟩ := constrain_valid sumRun valid
        have s₅Valid := excludePairs_valid exclusionRun s₆Valid
        obtain ⟨s₄Valid, armsEval⟩ := lowerArms_sound armsRun s₅Valid
        have s₃Valid := freshValue_valid resultRun s₄Valid
        obtain ⟨beforeValid, scrutineeEval⟩ := lowerExpr_sound scrutineeRun s₃Valid
        refine ⟨beforeValid, fun active => ?_⟩
        have sum : (selectors.map (ArithExpr.denote assignment)).sum = 1 := by
          have equation := sub_eq_zero.mp sumEquation
          simpa [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote,
            Scalar.Circuit.ArithExpr.denote_foldl_add, active] using equation
        have nonzero : ∃ selector ∈ selectors, selector.denote assignment ≠ 0 := by
          by_contra absent
          push Not at absent
          have zero : (selectors.map (ArithExpr.denote assignment)).sum = 0 :=
            List.sum_eq_zero (by simpa using absent)
          exact zero_ne_one (zero.symm.trans sum)
        obtain ⟨selector, member, activeSelector⟩ := nonzero
        obtain ⟨_, bindings, body, selected, evaluated⟩ := armsEval selector member activeSelector
        exact .matchValue (scrutineeEval active) selected evaluated
  termination_by sizeOf expr

  theorem lowerArgs_sound [Field F] [DecidableEq F]
      {program : Program F} {function : String} {locals : Locals F} {enable : ArithExpr F}
      {args : List (Expr F)} {outputs : List (Symbolic F)} {before after : BuildState F}
      (compiled : lowerArgs program function locals enable args before = .ok (outputs, after))
      {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid calls assignment) :
      before.Valid calls assignment ∧ (enable.denote assignment = 1 →
        EvalArgsWith calls (localsEnvironment locals assignment) args
          (outputs.map (Value.map (ArithExpr.denote assignment)))) := by
    cases args with
    | nil =>
        simp only [lowerArgs, pure_ok] at compiled
        obtain ⟨rfl, rfl⟩ := compiled
        exact ⟨valid, fun _ => .nil⟩
    | cons arg args =>
        simp only [lowerArgs] at compiled
        obtain ⟨head, middle, headRun, rest⟩ := bind_ok.mp compiled
        obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp rest
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        obtain ⟨middleValid, tailEval⟩ := lowerArgs_sound tailRun valid
        obtain ⟨beforeValid, headEval⟩ := lowerExpr_sound headRun middleValid
        exact ⟨beforeValid, fun active => .cons (headEval active) (tailEval active)⟩
  termination_by sizeOf args

  /-- Any selected occurrence is exactly the first matching source arm. -/
  theorem lowerArms_sound [Field F] [DecidableEq F]
      {program : Program F} {function : String} {locals : Locals F}
      {scrutinee result : Symbolic F} {remaining : ArithExpr F}
      {arms : List (Pattern F × Expr F)} {selectors : List (ArithExpr F)}
      {before after : BuildState F}
      (compiled : lowerArms program function locals scrutinee result remaining arms before =
        .ok (selectors, after))
      {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid calls assignment) :
      before.Valid calls assignment ∧
        ∀ selector ∈ selectors, selector.denote assignment ≠ 0 →
          remaining.denote assignment ≠ 0 ∧
            ∃ bindings body,
              selectArm (scrutinee.map (ArithExpr.denote assignment)) arms = some (bindings, body) ∧
              EvalExprWith calls (bindings ++ localsEnvironment locals assignment) body
                (result.map (ArithExpr.denote assignment)) := by
    cases arms with
    | nil =>
        simp only [lowerArms, pure_ok] at compiled
        obtain ⟨rfl, rfl⟩ := compiled
        exact ⟨valid, by simp⟩
    | cons arm arms =>
        rcases hArm : arm with ⟨pattern, body⟩
        simp only [hArm, lowerArms] at compiled
        obtain ⟨⟨test, bindings⟩, s₁, patternRun, rest⟩ := bind_ok.mp compiled
        obtain ⟨selector, s₂, freshRun, rest⟩ := bind_ok.mp rest
        obtain ⟨finished, s₃, booleanRun, rest⟩ := bind_ok.mp rest
        cases finished
        obtain ⟨finished, s₄, equationRun, rest⟩ := bind_ok.mp rest
        cases finished
        obtain ⟨bodyValue, s₅, bodyRun, rest⟩ := bind_ok.mp rest
        obtain ⟨finished, s₆, valueRun, rest⟩ := bind_ok.mp rest
        cases finished
        have headFacts (endValid : s₆.Valid calls assignment) :
            before.Valid calls assignment ∧
            PatternTest (pattern.bindings (scrutinee.map (ArithExpr.denote assignment)))
              (test.denote assignment) (localsEnvironment bindings assignment) ∧
            assignment selector = remaining.denote assignment * test.denote assignment ∧
            (assignment selector = 0 ∨ assignment selector = 1) ∧
            (assignment selector = 1 → EvalExprWith calls
              (localsEnvironment bindings assignment ++ localsEnvironment locals assignment) body
              (result.map (ArithExpr.denote assignment))) := by
          obtain ⟨s₅Valid, resultEq⟩ := constrainValue_sound valueRun endValid
          obtain ⟨s₄Valid, bodyEval⟩ := lowerExpr_sound bodyRun s₅Valid
          obtain ⟨s₃Valid, equation⟩ := constrain_valid equationRun s₄Valid
          obtain ⟨s₂Valid, boolean⟩ := boolean_valid booleanRun s₃Valid
          have s₁Valid := fresh_valid freshRun s₂Valid
          obtain ⟨beforeValid, matched⟩ := lowerPattern_sound patternRun s₁Valid
          refine ⟨beforeValid, matched, sub_eq_zero.mp equation, boolean, fun active => ?_⟩
          rw [resultEq active]
          simpa only [localsEnvironment_append] using bodyEval active
        have headSelected (endValid : s₆.Valid calls assignment) (active : assignment selector ≠ 0) :
            remaining.denote assignment ≠ 0 ∧
            ∃ matched body', selectArm (scrutinee.map (ArithExpr.denote assignment))
                ((pattern, body) :: arms) = some (matched, body') ∧
              EvalExprWith calls (matched ++ localsEnvironment locals assignment) body'
                (result.map (ArithExpr.denote assignment)) := by
          obtain ⟨_, matched, equation, boolean, evaluated⟩ := headFacts endValid
          have one := boolean.resolve_left active
          have remainingNonzero : remaining.denote assignment ≠ 0 := by
            intro zero
            exact active (by simp [zero] at equation; exact equation)
          refine ⟨remainingNonzero, localsEnvironment bindings assignment, body, ?_, evaluated one⟩
          rcases matched with ⟨matched, _⟩ | ⟨_, zero⟩
          · simp [selectArm, matched]
          · exact (active (by simpa [zero] using equation)).elim
        split at rest
        · obtain ⟨rfl, rfl⟩ := pure_ok.mp rest
          refine ⟨(headFacts valid).1, ?_⟩
          intro chosen member active
          obtain rfl := List.mem_singleton.mp member
          exact headSelected valid active
        · simp only [pure_bind] at rest
          obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp rest
          obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
          obtain ⟨s₆Valid, tailEval⟩ := lowerArms_sound tailRun valid
          obtain ⟨beforeValid, matched, _, _, _⟩ := headFacts s₆Valid
          refine ⟨beforeValid, ?_⟩
          intro chosen member active
          rcases List.mem_cons.mp member with same | member
          · subst chosen
            exact headSelected s₆Valid active
          · obtain ⟨remainingNonzero, selectedBindings, selectedBody, selected, evaluated⟩ :=
              tailEval chosen member active
            change remaining.denote assignment * (1 - test.denote assignment) ≠ 0
              at remainingNonzero
            have nonzero := (mul_ne_zero_iff.mp remainingNonzero).1
            refine ⟨nonzero, selectedBindings, selectedBody, ?_, evaluated⟩
            rcases matched with ⟨_, one⟩ | ⟨unmatched, _⟩
            · exact (remainingNonzero (by simp [one])).elim
            · simpa only [selectArm, unmatched] using selected
  termination_by sizeOf arms
  decreasing_by
    all_goals simp_all only [Prod.mk.sizeOf_spec, List.cons.sizeOf_spec]
    all_goals omega
end

end Aiur.Tuple.Circuit.Compiler
