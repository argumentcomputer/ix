import Aiur.Scalar.Circuit.MatchWitness

namespace Aiur.Scalar.Circuit.Compiler

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
mutual
  /--
  Expression completeness under an active enable. New variables extend the initial
  assignment, preserving its values and all earlier constraints and call premises.
  This includes providing witnesses for every inactive branch of a compiled match.
  -/
  theorem lowerExpr_complete [Field F] [DecidableEq F]
      {function : String} {locals : List (String × Var)} {enable : ArithExpr F} {expr : Expr F}
      {before after : BuildState F} {polynomial : ArithExpr F}
      (compiled : (lowerExpr function locals enable expr).run before = .ok (polynomial, after))
      (layout : before.WellFormed)
      (localsBound : ∀ binding ∈ locals, binding.2 < before.nextVar)
      (enableBound : enable.inBounds before.nextVar = true)
      {calls : CallRelation F} {initial : List F} (size : initial.length = before.nextVar)
      (valid : before.Valid calls (Row.assignment ⟨function, initial⟩))
      (active : enable.denote (Row.assignment ⟨function, initial⟩) = 1)
      {result : F}
      (body : EvalExprWith calls
        (localsEnvironment locals (Row.assignment ⟨function, initial⟩)) expr result) :
      ∃ values, initial.IsPrefix values ∧ values.length = after.nextVar ∧
        after.WellFormed ∧ polynomial.inBounds after.nextVar = true ∧
        after.Valid calls (Row.assignment ⟨function, values⟩) ∧
        polynomial.denote (Row.assignment ⟨function, values⟩) = result := by
    cases expr with
    | literal value =>
        simp [lowerExpr, StateT.run, StateT.pure, pure, Except.pure] at compiled
        rcases compiled with ⟨rfl, rfl⟩
        cases body
        exact ⟨initial, ⟨[], by simp⟩, size, layout, rfl, valid, rfl⟩
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
            refine ⟨initial, ⟨[], by simp⟩, size, layout, ?_, valid, ?_⟩
            · simpa [ArithExpr.inBounds] using localsBound (name, id) (List.mem_of_find?_eq_some found)
            · cases body with
              | var lookup =>
                  simpa [localsEnvironment, List.find?_map, Function.comp_def, found,
                    ArithExpr.denote] using lookup
    | neg expr =>
        cases lowered : lowerExpr function locals enable expr before with
        | error error =>
            simp [lowerExpr, StateT.run, StateT.bind, bind, Except.bind, lowered] at compiled
        | ok output =>
            rcases output with ⟨inner, state⟩
            simp [lowerExpr, StateT.run, StateT.bind, StateT.pure, bind, pure,
              Except.bind, Except.pure, lowered] at compiled
            rcases compiled with ⟨rfl, rfl⟩
            cases body with
            | neg operand =>
                obtain ⟨values, extension, finalSize, finalLayout, innerBound, finalValid, value⟩ :=
                  lowerExpr_complete lowered layout localsBound enableBound size valid active operand
                refine ⟨values, extension, finalSize, finalLayout, ?_, finalValid, ?_⟩
                · simpa [ArithExpr.inBounds] using innerBound
                · simp [ArithExpr.denote, value]
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
                have operands {x y : F}
                    (leftEval : EvalExprWith calls
                      (localsEnvironment locals (Row.assignment ⟨function, initial⟩)) left x)
                    (rightEval : EvalExprWith calls
                      (localsEnvironment locals (Row.assignment ⟨function, initial⟩)) right y) :
                    ∃ values, initial.IsPrefix values ∧ values.length = state.nextVar ∧
                      state.WellFormed ∧ leftPolynomial.inBounds state.nextVar = true ∧
                      rightPolynomial.inBounds state.nextVar = true ∧
                      state.Valid calls (Row.assignment ⟨function, values⟩) ∧
                      leftPolynomial.denote (Row.assignment ⟨function, values⟩) = x ∧
                      rightPolynomial.denote (Row.assignment ⟨function, values⟩) = y := by
                  obtain ⟨firstValues, firstExtension, firstSize, firstLayout, leftBound, firstValid, leftValue⟩ :=
                    lowerExpr_complete leftRun layout localsBound enableBound size valid active leftEval
                  have increase : before.nextVar ≤ middle.nextVar := by
                    rw [← size, ← firstSize]
                    exact firstExtension.length_le
                  obtain ⟨values, extension, finalSize, finalLayout, rightBound, finalValid, rightValue⟩ :=
                    lowerExpr_complete rightRun firstLayout
                      (fun binding member => lt_of_lt_of_le (localsBound binding member) increase)
                      (ArithExpr.inBounds_mono increase enableBound) firstSize firstValid
                      (by rw [denote_of_prefix firstExtension size enableBound]; exact active)
                      (by rw [localsEnvironment_of_prefix firstExtension size localsBound]; exact rightEval)
                  have nextIncrease : middle.nextVar ≤ state.nextVar := by
                    rw [← firstSize, ← finalSize]
                    exact extension.length_le
                  refine ⟨values, firstExtension.trans extension, finalSize, finalLayout,
                    ArithExpr.inBounds_mono nextIncrease leftBound, rightBound, finalValid, ?_, rightValue⟩
                  rw [denote_of_prefix extension firstSize leftBound]
                  exact leftValue
                cases body with
                | add leftEval rightEval | sub leftEval rightEval | mul leftEval rightEval =>
                    simp [lowerExpr, StateT.run, StateT.bind, StateT.pure, bind, pure,
                      Except.bind, Except.pure, leftRun, rightRun] at compiled
                    rcases compiled with ⟨rfl, rfl⟩
                    obtain ⟨values, extension, finalSize, finalLayout, leftBound, rightBound,
                      finalValid, leftValue, rightValue⟩ := operands leftEval rightEval
                    refine ⟨values, extension, finalSize, finalLayout, ?_, finalValid, ?_⟩
                    · simp [ArithExpr.inBounds, leftBound, rightBound]
                    · simp [ArithExpr.denote, leftValue, rightValue]
                | div leftEval rightEval nonzero =>
                    rename_i x y
                    simp [lowerExpr, StateT.run, StateT.bind, StateT.pure, bind, pure,
                      Except.bind, Except.pure, leftRun, rightRun] at compiled
                    rcases compiled with ⟨rfl, rfl⟩
                    obtain ⟨values, extension, finalSize, finalLayout, leftBound, rightBound,
                      finalValid, leftValue, rightValue⟩ := operands leftEval rightEval
                    let finished := values ++ [y⁻¹]
                    have extended : values.IsPrefix finished := List.prefix_append _ _
                    have inverse : Row.assignment ⟨function, finished⟩ state.nextVar = y⁻¹ := by
                      simp [Row.assignment, finished, ← finalSize]
                    have increase : before.nextVar ≤ state.nextVar := by
                      rw [← size, ← finalSize]
                      exact extension.length_le
                    have finalEnable := ArithExpr.inBounds_mono increase enableBound
                    have activeFinal : enable.denote (Row.assignment ⟨function, finished⟩) = 1 := by
                      rw [denote_of_prefix (extension.trans extended) size enableBound]
                      exact active
                    have leftFinal : leftPolynomial.denote (Row.assignment ⟨function, finished⟩) = x := by
                      rw [denote_of_prefix extended finalSize leftBound]
                      exact leftValue
                    have rightFinal : rightPolynomial.denote (Row.assignment ⟨function, finished⟩) = y := by
                      rw [denote_of_prefix extended finalSize rightBound]
                      exact rightValue
                    have equationBound :
                        (ArithExpr.mul enable (.sub (.mul rightPolynomial (.var state.nextVar)) (.const 1))).inBounds
                          (state.nextVar + 1) = true := by
                      simp [ArithExpr.inBounds, ArithExpr.inBounds_mono (Nat.le_succ _) finalEnable,
                        ArithExpr.inBounds_mono (Nat.le_succ _) rightBound]
                    have oldValid := finalValid.of_prefix finalLayout finalSize extended
                    have freshValid : { state with nextVar := state.nextVar + 1 }.Valid calls
                        (Row.assignment ⟨function, finished⟩) := ⟨oldValid.constraints, oldValid.calls⟩
                    refine ⟨finished, extension.trans extended, by simp [finished, finalSize],
                      finalLayout.fresh.constrain equationBound, ?_, freshValid.constrain ?_, ?_⟩
                    · simp [ArithExpr.inBounds, ArithExpr.inBounds_mono (Nat.le_succ _) leftBound]
                    · simp [ArithExpr.denote, activeFinal, rightFinal, inverse, nonzero]
                    · simp [ArithExpr.denote, leftFinal, inverse, div_eq_mul_inv]
    | call name args =>
        cases argsRun : lowerArgs function locals enable args before with
        | error error =>
            simp [lowerExpr, StateT.run, StateT.bind, bind, Except.bind, argsRun] at compiled
        | ok output =>
            rcases output with ⟨arguments, state⟩
            simp [lowerExpr, boolean, StateT.run, StateT.bind, StateT.pure, bind, pure,
              Except.bind, Except.pure, argsRun] at compiled
            rcases compiled with ⟨rfl, rfl⟩
            cases body with
            | call argsEval callee =>
                obtain ⟨values, extension, finalSize, finalLayout, argsBound, finalValid, argsValue⟩ :=
                  lowerArgs_complete argsRun layout localsBound enableBound size valid active argsEval
                let finished := values ++ [result]
                have extended : values.IsPrefix finished := List.prefix_append _ _
                have output : Row.assignment ⟨function, finished⟩ state.nextVar = result := by
                  simp [Row.assignment, finished, ← finalSize]
                have increase : before.nextVar ≤ state.nextVar := by
                  rw [← size, ← finalSize]
                  exact extension.length_le
                have finalEnable := ArithExpr.inBounds_mono (Nat.le_succ _)
                  (ArithExpr.inBounds_mono increase enableBound)
                have activeFinal : enable.denote (Row.assignment ⟨function, finished⟩) = 1 := by
                  rw [denote_of_prefix (extension.trans extended) size enableBound]
                  exact active
                have argumentsUnchanged : arguments.map (ArithExpr.denote (Row.assignment ⟨function, finished⟩)) =
                    arguments.map (ArithExpr.denote (Row.assignment ⟨function, values⟩)) := by
                  apply List.map_congr_left
                  exact fun argument member => denote_of_prefix extended finalSize (argsBound argument member)
                have booleanBound : (ArithExpr.mul enable (.sub enable (.const 1))).inBounds
                    (state.nextVar + 1) = true := by simp [ArithExpr.inBounds, finalEnable]
                have sendBound : (⟨name, arguments, state.nextVar, enable⟩ : Send F).inBounds
                    (state.nextVar + 1) = true := by
                  simp only [Send.inBounds, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
                  exact ⟨⟨Nat.lt_succ_self _, finalEnable⟩,
                    fun argument member => ArithExpr.inBounds_mono (Nat.le_succ _) (argsBound argument member)⟩
                have oldValid := finalValid.of_prefix finalLayout finalSize extended
                have freshValid : { state with nextVar := state.nextVar + 1 }.Valid calls
                    (Row.assignment ⟨function, finished⟩) := ⟨oldValid.constraints, oldValid.calls⟩
                have booleanZero : (ArithExpr.mul enable (.sub enable (.const 1))).denote
                    (Row.assignment ⟨function, finished⟩) = 0 := by simp [ArithExpr.denote, activeFinal]
                have withBoolean := finalLayout.fresh.constrain booleanBound
                have withBooleanValid := freshValid.constrain booleanZero
                refine ⟨finished, extension.trans extended, by simp [finished, finalSize],
                  ⟨withBoolean.constraints, ?_⟩, by simp [ArithExpr.inBounds],
                  ⟨withBooleanValid.constraints, ?_⟩, output⟩
                · intro send member
                  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
                  rcases member with member | rfl
                  · exact withBoolean.sends send member
                  · exact sendBound
                · intro send member enabled
                  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
                  rcases member with member | rfl
                  · exact withBooleanValid.calls send member enabled
                  · change calls name _ _
                    rw [argumentsUnchanged, argsValue, output]
                    exact callee
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
                    simp [lowerExpr, checked, StateT.run, StateT.bind, StateT.pure, bind, pure,
                      Except.bind, Except.pure, scrutineeRun, armsRun] at compiled
                    rcases compiled with ⟨rfl, rfl⟩
                    cases body with
                    | matchValue scrutineeEval selected branch =>
                        obtain ⟨middleValues, firstExtension, middleSize, middleLayout, scrutineeBound,
                          middleValid, scrutineeValue⟩ :=
                          lowerExpr_complete scrutineeRun layout localsBound enableBound size valid active scrutineeEval
                        let padded := middleValues ++ [result]
                        have extended : middleValues.IsPrefix padded := List.prefix_append _ _
                        have first := firstExtension.trans extended
                        have paddedSize : padded.length = middle.nextVar + 1 := by simp [padded, middleSize]
                        have increase : before.nextVar ≤ middle.nextVar + 1 := by
                          rw [← size, ← paddedSize]
                          exact first.length_le
                        have oldValid := middleValid.of_prefix middleLayout middleSize extended
                        have freshValid : { middle with nextVar := middle.nextVar + 1 }.Valid calls
                            (Row.assignment ⟨function, padded⟩) := ⟨oldValid.constraints, oldValid.calls⟩
                        obtain ⟨values, extension, finalSize, finalLayout, selectorsBound, finalValid, selectorsValid⟩ :=
                          lowerArms_complete (output := result) armsRun middleLayout.fresh
                            (fun binding member => lt_of_lt_of_le (localsBound binding member) increase)
                            (ArithExpr.inBounds_mono (Nat.le_succ _) scrutineeBound) (Nat.lt_succ_self _)
                            paddedSize freshValid
                            ((denote_of_prefix extended middleSize scrutineeBound).trans scrutineeValue)
                            (by rw [← middleSize]; exact assignment_append_value _ _ _) selected
                            (fun _ member => Or.inl member)
                            (by rw [localsEnvironment_of_prefix first size localsBound]; exact branch)
                        have total := first.trans extension
                        have finalIncrease : before.nextVar ≤ state.nextVar := by
                          rw [← size, ← finalSize]
                          exact total.length_le
                        have finalEnable := ArithExpr.inBounds_mono finalIncrease enableBound
                        have selectedEquations : Satisfies (selectionConstraints enable selectors)
                            (Row.assignment ⟨function, values⟩) := by
                          apply (selectionConstraints_satisfies _ _ _).mpr
                          rw [denote_of_prefix total size enableBound, active]
                          exact selectorsValid
                        have outputBound : middle.nextVar < state.nextVar := by
                          have length := extension.length_le
                          rw [paddedSize, finalSize] at length
                          omega
                        refine ⟨values, total, finalSize,
                          finalLayout.constrainMany (selectionConstraints_inBounds finalEnable selectorsBound),
                          by simpa [ArithExpr.inBounds] using outputBound,
                          finalValid.constrainMany selectedEquations, ?_⟩
                        change Row.assignment ⟨function, values⟩ middle.nextVar = result
                        rw [value_of_prefix extension paddedSize (Nat.lt_succ_self _), ← middleSize]
                        exact assignment_append_value _ _ _
  termination_by sizeOf expr

  theorem lowerArgs_complete [Field F] [DecidableEq F]
      {function : String} {locals : List (String × Var)} {enable : ArithExpr F} {args : List (Expr F)}
      {before after : BuildState F} {polynomials : List (ArithExpr F)}
      (compiled : (lowerArgs function locals enable args).run before = .ok (polynomials, after))
      (layout : before.WellFormed)
      (localsBound : ∀ binding ∈ locals, binding.2 < before.nextVar)
      (enableBound : enable.inBounds before.nextVar = true)
      {calls : CallRelation F} {initial : List F} (size : initial.length = before.nextVar)
      (valid : before.Valid calls (Row.assignment ⟨function, initial⟩))
      (active : enable.denote (Row.assignment ⟨function, initial⟩) = 1)
      {results : List F}
      (body : EvalArgsWith calls
        (localsEnvironment locals (Row.assignment ⟨function, initial⟩)) args results) :
      ∃ values, initial.IsPrefix values ∧ values.length = after.nextVar ∧
        after.WellFormed ∧ (∀ polynomial ∈ polynomials, polynomial.inBounds after.nextVar = true) ∧
        after.Valid calls (Row.assignment ⟨function, values⟩) ∧
        polynomials.map (ArithExpr.denote (Row.assignment ⟨function, values⟩)) = results := by
    cases args with
    | nil =>
        simp [lowerArgs, StateT.run, StateT.pure, pure, Except.pure] at compiled
        rcases compiled with ⟨rfl, rfl⟩
        cases body
        exact ⟨initial, ⟨[], by simp⟩, size, layout, by simp, valid, rfl⟩
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
                rcases output with ⟨tailPolynomials, state⟩
                simp [lowerArgs, StateT.run, StateT.bind, StateT.pure, bind, pure,
                  Except.bind, Except.pure, headRun, tailRun] at compiled
                rcases compiled with ⟨rfl, rfl⟩
                cases body with
                | cons headEval tailEval =>
                    obtain ⟨firstValues, firstExtension, firstSize, firstLayout, headBound, firstValid, headValue⟩ :=
                      lowerExpr_complete headRun layout localsBound enableBound size valid active headEval
                    have increase : before.nextVar ≤ middle.nextVar := by
                      rw [← size, ← firstSize]
                      exact firstExtension.length_le
                    obtain ⟨values, extension, finalSize, finalLayout, tailBounds, finalValid, tailValue⟩ :=
                      lowerArgs_complete tailRun firstLayout
                        (fun binding member => lt_of_lt_of_le (localsBound binding member) increase)
                        (ArithExpr.inBounds_mono increase enableBound) firstSize firstValid
                        (by rw [denote_of_prefix firstExtension size enableBound]; exact active)
                        (by rw [localsEnvironment_of_prefix firstExtension size localsBound]; exact tailEval)
                    have nextIncrease : middle.nextVar ≤ state.nextVar := by
                      rw [← firstSize, ← finalSize]
                      exact extension.length_le
                    refine ⟨values, firstExtension.trans extension, finalSize, finalLayout, ?_, finalValid, ?_⟩
                    · intro polynomial member
                      rcases List.mem_cons.mp member with rfl | member
                      · exact ArithExpr.inBounds_mono nextIncrease headBound
                      · exact tailBounds polynomial member
                    · simp only [List.map_cons, tailValue]
                      rw [denote_of_prefix extension firstSize headBound, headValue]
  termination_by sizeOf args

  /-- Construct the selected arm and disable every other retained arm. -/
  theorem lowerArms_complete [Field F] [DecidableEq F]
      {function : String} {locals : List (String × Var)} {scrutinee : ArithExpr F} {result : Var}
      {literals : List F} {arms : List (Pattern F × Expr F)}
      {before after : BuildState F} {selectors : List (ArithExpr F)}
      (compiled : (lowerArms function locals scrutinee result literals arms).run before = .ok (selectors, after))
      (layout : before.WellFormed)
      (localsBound : ∀ binding ∈ locals, binding.2 < before.nextVar)
      (scrutineeBound : scrutinee.inBounds before.nextVar = true) (resultBound : result < before.nextVar)
      {calls : CallRelation F} {initial : List F} (size : initial.length = before.nextVar)
      (valid : before.Valid calls (Row.assignment ⟨function, initial⟩))
      {value output : F} (scrutineeValue : scrutinee.denote (Row.assignment ⟨function, initial⟩) = value)
      (outputValue : Row.assignment ⟨function, initial⟩ result = output)
      {selectedBody : Expr F} (selected : SelectArm value arms selectedBody)
      (priorExcluded : ∀ literal ∈ literals, literal ∈ literalPatterns arms ∨ value ≠ literal)
      (body : EvalExprWith calls (localsEnvironment locals (Row.assignment ⟨function, initial⟩)) selectedBody output) :
      ∃ values, initial.IsPrefix values ∧ values.length = after.nextVar ∧ after.WellFormed ∧
        (∀ selector ∈ selectors, selector.inBounds after.nextVar = true) ∧
        after.Valid calls (Row.assignment ⟨function, values⟩) ∧
        SelectorsValid (1 : F) (selectors.map (ArithExpr.denote (Row.assignment ⟨function, values⟩))) := by
    cases arms with
    | nil => cases selected
    | cons arm rest =>
        cases armEq : arm
        rename_i pattern armBody
        simp only [armEq] at compiled selected priorExcluded
        cases pattern with
        | literal literal =>
            let patternEquation : ArithExpr F :=
              .mul (.var before.nextVar) (.sub scrutinee (.const literal))
            let start : BuildState F := {
              before with nextVar := before.nextVar + 1
                          constraints := before.constraints.push patternEquation }
            have startLayout : start.WellFormed := layout.fresh.constrain (by
              simp [patternEquation, ArithExpr.inBounds,
                ArithExpr.inBounds_mono (Nat.le_succ _) scrutineeBound])
            have startLocals : ∀ binding ∈ locals, binding.2 < start.nextVar :=
              fun binding member => lt_of_lt_of_le (localsBound binding member) (Nat.le_succ _)
            cases bodyRun : lowerExpr function locals (.var before.nextVar) armBody start with
            | error error =>
                simp [lowerArms, StateT.run, StateT.bind, bind, Except.bind, start,
                  patternEquation, bodyRun] at compiled
            | ok lowered =>
                rcases lowered with ⟨bodyPolynomial, middle⟩
                let resultEquation : ArithExpr F :=
                  .mul (.var before.nextVar) (.sub (.var result) bodyPolynomial)
                let next : BuildState F := { middle with constraints := middle.constraints.push resultEquation }
                cases restRun : lowerArms function locals scrutinee result literals rest next with
                | error error =>
                    simp [lowerArms, StateT.run, StateT.bind, bind, Except.bind, start,
                      patternEquation, next, resultEquation, bodyRun, restRun] at compiled
                | ok lowered =>
                    rcases lowered with ⟨restSelectors, state⟩
                    simp [lowerArms, StateT.run, StateT.bind, StateT.pure, bind, pure,
                      Except.bind, Except.pure, start, patternEquation, next, resultEquation,
                      bodyRun, restRun] at compiled
                    rcases compiled with ⟨rfl, rfl⟩
                    cases selected with
                    | literal =>
                        let padded := initial ++ [1]
                        have extended : initial.IsPrefix padded := List.prefix_append _ _
                        have paddedSize : padded.length = start.nextVar := by simp [padded, start, size]
                        have selectorValue : Row.assignment ⟨function, padded⟩ before.nextVar = (1 : F) := by
                          rw [← size]
                          exact assignment_append_value _ _ _
                        have scrutineePadded :=
                          (denote_of_prefix (function := function) extended size scrutineeBound).trans scrutineeValue
                        have oldValid := valid.of_prefix layout size extended
                        have freshValid : { before with nextVar := before.nextVar + 1 }.Valid calls
                            (Row.assignment ⟨function, padded⟩) := ⟨oldValid.constraints, oldValid.calls⟩
                        have startValid : start.Valid calls (Row.assignment ⟨function, padded⟩) :=
                          freshValid.constrain (by simp [patternEquation, ArithExpr.denote, scrutineePadded])
                        obtain ⟨bodyValues, bodyExtension, middleSize, middleLayout, bodyBound, middleValid, bodyValue⟩ :=
                          lowerExpr_complete bodyRun startLayout startLocals
                            (by simp [start, ArithExpr.inBounds]) paddedSize startValid selectorValue
                            (by rw [localsEnvironment_of_prefix extended size localsBound]; exact body)
                        have first := extended.trans bodyExtension
                        have selectorBound : before.nextVar < middle.nextVar := by
                          have length := bodyExtension.length_le
                          simp only [paddedSize, start, middleSize] at length
                          omega
                        have increase : before.nextVar ≤ middle.nextVar := Nat.le_of_lt selectorBound
                        have outputMiddle := (value_of_prefix (function := function) first size resultBound).trans outputValue
                        have nextLayout : next.WellFormed := middleLayout.constrain (by
                          simp [resultEquation, ArithExpr.inBounds, selectorBound, bodyBound,
                            lt_of_lt_of_le resultBound increase])
                        have nextValid : next.Valid calls (Row.assignment ⟨function, bodyValues⟩) :=
                          middleValid.constrain (by simp [resultEquation, ArithExpr.denote, outputMiddle, bodyValue])
                        obtain ⟨values, extension, finalSize, finalLayout, restBound, finalValid, restZero, _⟩ :=
                          lowerArms_inactive_complete restRun nextLayout
                            (fun binding member => lt_of_lt_of_le (localsBound binding member) increase)
                            (ArithExpr.inBounds_mono increase scrutineeBound)
                            (lt_of_lt_of_le resultBound increase) middleSize nextValid
                        have nextIncrease : middle.nextVar ≤ state.nextVar := by
                          rw [← middleSize, ← finalSize]
                          exact extension.length_le
                        have selectorFinal := (value_of_prefix (function := function)
                          (bodyExtension.trans extension) paddedSize (Nat.lt_succ_self _)).trans selectorValue
                        refine ⟨values, first.trans extension, finalSize, finalLayout, ?_, finalValid, ?_⟩
                        · intro selector member
                          rcases List.mem_cons.mp member with rfl | member
                          · simpa [ArithExpr.inBounds] using lt_of_lt_of_le selectorBound nextIncrease
                          · exact restBound selector member
                        · simp only [List.map_cons, ArithExpr.denote, selectorFinal]
                          apply SelectorsValid.single (before := []) (by simp)
                          intro value present
                          obtain ⟨selector, selectorMember, same⟩ := List.mem_map.mp present
                          rw [← same]
                          exact restZero selector selectorMember
                    | skip different selectedRest =>
                        let padded := initial ++ [0]
                        have extended : initial.IsPrefix padded := List.prefix_append _ _
                        have paddedSize : padded.length = start.nextVar := by simp [padded, start, size]
                        have selectorValue : Row.assignment ⟨function, padded⟩ before.nextVar = (0 : F) := by
                          rw [← size]
                          exact assignment_append_value _ _ _
                        have oldValid := valid.of_prefix layout size extended
                        have freshValid : { before with nextVar := before.nextVar + 1 }.Valid calls
                            (Row.assignment ⟨function, padded⟩) := ⟨oldValid.constraints, oldValid.calls⟩
                        have startValid : start.Valid calls (Row.assignment ⟨function, padded⟩) :=
                          freshValid.constrain (by simp [patternEquation, ArithExpr.denote, selectorValue])
                        obtain ⟨bodyValues, bodyExtension, middleSize, middleLayout, bodyBound, middleValid, _⟩ :=
                          lowerExpr_inactive_complete bodyRun startLayout startLocals
                            (by simp [start, ArithExpr.inBounds]) paddedSize startValid selectorValue
                        have first := extended.trans bodyExtension
                        have selectorBound : before.nextVar < middle.nextVar := by
                          have length := bodyExtension.length_le
                          simp only [paddedSize, start, middleSize] at length
                          omega
                        have increase : before.nextVar ≤ middle.nextVar := Nat.le_of_lt selectorBound
                        have selectorMiddle :=
                          (value_of_prefix (function := function) bodyExtension paddedSize (Nat.lt_succ_self _)).trans selectorValue
                        have nextLayout : next.WellFormed := middleLayout.constrain (by
                          simp [resultEquation, ArithExpr.inBounds, selectorBound, bodyBound,
                            lt_of_lt_of_le resultBound increase])
                        have nextValid : next.Valid calls (Row.assignment ⟨function, bodyValues⟩) :=
                          middleValid.constrain (by simp [resultEquation, ArithExpr.denote, selectorMiddle])
                        have restExcluded : ∀ nextLiteral ∈ literals,
                            nextLiteral ∈ literalPatterns rest ∨ value ≠ nextLiteral := by
                          intro nextLiteral member
                          rcases priorExcluded nextLiteral member with retained | excluded
                          · simp only [literalPatterns, List.mem_cons] at retained
                            rcases retained with rfl | retained
                            · exact Or.inr different.symm
                            · exact Or.inl retained
                          · exact Or.inr excluded
                        obtain ⟨values, extension, finalSize, finalLayout, restBound, finalValid, restValid⟩ :=
                          lowerArms_complete (output := output) restRun nextLayout
                            (fun binding member => lt_of_lt_of_le (localsBound binding member) increase)
                            (ArithExpr.inBounds_mono increase scrutineeBound)
                            (lt_of_lt_of_le resultBound increase) middleSize nextValid
                            ((denote_of_prefix first size scrutineeBound).trans scrutineeValue)
                            ((value_of_prefix first size resultBound).trans outputValue)
                            selectedRest restExcluded
                            (by rw [localsEnvironment_of_prefix first size localsBound]; exact body)
                        have nextIncrease : middle.nextVar ≤ state.nextVar := by
                          rw [← middleSize, ← finalSize]
                          exact extension.length_le
                        have selectorFinal := (value_of_prefix (function := function)
                          (bodyExtension.trans extension) paddedSize (Nat.lt_succ_self _)).trans selectorValue
                        refine ⟨values, first.trans extension, finalSize, finalLayout, ?_, finalValid, ?_⟩
                        · intro selector member
                          rcases List.mem_cons.mp member with rfl | member
                          · simpa [ArithExpr.inBounds] using lt_of_lt_of_le selectorBound nextIncrease
                          · exact restBound selector member
                        · simpa only [List.map_cons, ArithExpr.denote, selectorFinal] using restValid.zero_cons
        | wildcard =>
            cases selected
            cases excludedRun : excludeLiterals (.var before.nextVar) scrutinee literals
                { before with nextVar := before.nextVar + 1 } with
            | error error =>
                simp [lowerArms, StateT.run, StateT.bind, bind, Except.bind, excludedRun] at compiled
            | ok lowered =>
                rcases lowered with ⟨finished, middle⟩
                cases finished
                cases bodyRun : lowerExpr function locals (.var before.nextVar) selectedBody middle with
                | error error =>
                    simp [lowerArms, StateT.run, StateT.bind, bind, Except.bind, excludedRun, bodyRun] at compiled
                | ok lowered =>
                    rcases lowered with ⟨bodyPolynomial, state⟩
                    simp [lowerArms, StateT.run, StateT.bind, StateT.pure, bind, pure,
                      Except.bind, Except.pure, excludedRun, bodyRun] at compiled
                    rcases compiled with ⟨rfl, rfl⟩
                    let padded := initial ++ [1]
                    have extended : initial.IsPrefix padded := List.prefix_append _ _
                    have paddedSize : padded.length = before.nextVar + 1 := by simp [padded, size]
                    have selectorValue : Row.assignment ⟨function, padded⟩ before.nextVar = (1 : F) := by
                      rw [← size]
                      exact assignment_append_value _ _ _
                    have scrutineePadded :=
                      (denote_of_prefix (function := function) extended size scrutineeBound).trans scrutineeValue
                    have oldValid := valid.of_prefix layout size extended
                    have freshValid : { before with nextVar := before.nextVar + 1 }.Valid calls
                        (Row.assignment ⟨function, padded⟩) := ⟨oldValid.constraints, oldValid.calls⟩
                    have excluded : ∀ literal ∈ literals,
                        scrutinee.denote (Row.assignment ⟨function, padded⟩) ≠ literal := by
                      intro literal member
                      rw [scrutineePadded]
                      rcases priorExcluded literal member with impossible | different
                      · simp [literalPatterns] at impossible
                      · exact different
                    obtain ⟨middleValues, middleExtension, middleSize, middleLayout, middleValid⟩ :=
                      excludeLiterals_complete excludedRun layout.fresh
                        (by simp [ArithExpr.inBounds])
                        (ArithExpr.inBounds_mono (Nat.le_succ _) scrutineeBound)
                        paddedSize freshValid selectorValue excluded
                    have first := extended.trans middleExtension
                    have selectorBound : before.nextVar < middle.nextVar := by
                      have length := middleExtension.length_le
                      rw [paddedSize, middleSize] at length
                      omega
                    have increase : before.nextVar ≤ middle.nextVar := Nat.le_of_lt selectorBound
                    have selectorMiddle := (value_of_prefix (function := function)
                      middleExtension paddedSize (Nat.lt_succ_self _)).trans selectorValue
                    obtain ⟨values, extension, finalSize, finalLayout, bodyBound, finalValid, bodyValue⟩ :=
                      lowerExpr_complete bodyRun middleLayout
                        (fun binding member => lt_of_lt_of_le (localsBound binding member) increase)
                        (by simpa [ArithExpr.inBounds] using selectorBound) middleSize middleValid selectorMiddle
                        (by rw [localsEnvironment_of_prefix first size localsBound]; exact body)
                    have total := first.trans extension
                    have nextIncrease : middle.nextVar ≤ state.nextVar := by
                      rw [← middleSize, ← finalSize]
                      exact extension.length_le
                    have selectorFinal := (value_of_prefix (function := function)
                      (middleExtension.trans extension) paddedSize (Nat.lt_succ_self _)).trans selectorValue
                    have outputFinal := (value_of_prefix (function := function) total size resultBound).trans outputValue
                    refine ⟨values, total, finalSize, finalLayout.constrain ?_, ?_, finalValid.constrain ?_, ?_⟩
                    · simp [ArithExpr.inBounds, bodyBound, lt_of_lt_of_le selectorBound nextIncrease,
                        lt_of_lt_of_le resultBound (le_trans increase nextIncrease)]
                    · simpa [ArithExpr.inBounds] using lt_of_lt_of_le selectorBound nextIncrease
                    · simp [ArithExpr.denote, outputFinal, bodyValue]
                    · simpa [ArithExpr.denote, selectorFinal] using
                        (SelectorsValid.single (before := []) (after := []) (by simp) (by simp) :
                          SelectorsValid (1 : F) [1])
  termination_by sizeOf arms

end

end Aiur.Scalar.Circuit.Compiler
