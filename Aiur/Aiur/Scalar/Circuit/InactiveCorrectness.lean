import Aiur.Scalar.Circuit.WitnessBasic

namespace Aiur.Scalar.Circuit.Compiler

/-- Default inverse equations need no nonzero differences when the selector is zero. -/
theorem excludeLiterals_inactive [Field F] {selector scrutinee : ArithExpr F} {literals : List F}
    {before after : BuildState F}
    (compiled : (excludeLiterals selector scrutinee literals).run before = .ok ((), after))
    (layout : before.WellFormed)
    (selectorBound : selector.inBounds before.nextVar = true)
    (scrutineeBound : scrutinee.inBounds before.nextVar = true)
    {assignment : Var → F} (inactive : selector.denote assignment = 0) :
    InactiveExtension before after assignment ∧ after.WellFormed := by
  cases literals with
  | nil =>
      simp [excludeLiterals, StateT.run, StateT.pure, pure, Except.pure] at compiled
      subst after
      exact ⟨.refl _ _, layout⟩
  | cons value rest =>
      let equation : ArithExpr F :=
        .mul selector (.sub (.mul (.sub scrutinee (.const value)) (.var before.nextVar)) (.const 1))
      let next : BuildState F := {
        before with nextVar := before.nextVar + 1
                    constraints := before.constraints.push equation }
      cases restRun : excludeLiterals selector scrutinee rest next with
      | error error =>
          simp [excludeLiterals, StateT.run, StateT.bind, bind, Except.bind, next, equation,
            restRun] at compiled
      | ok output =>
          rcases output with ⟨finished, state⟩
          cases finished
          simp [excludeLiterals, StateT.run, StateT.bind, bind, Except.bind, next, equation,
            restRun] at compiled
          subst after
          have equationBound : equation.inBounds (before.nextVar + 1) = true := by
            simp [equation, ArithExpr.inBounds, ArithExpr.inBounds_mono (Nat.le_succ _) selectorBound,
              ArithExpr.inBounds_mono (Nat.le_succ _) scrutineeBound]
          have nextLayout : next.WellFormed := layout.fresh.constrain equationBound
          obtain ⟨extension, finalLayout⟩ := excludeLiterals_inactive restRun nextLayout
            (ArithExpr.inBounds_mono (Nat.le_succ _) selectorBound)
            (ArithExpr.inBounds_mono (Nat.le_succ _) scrutineeBound) inactive
          have first : InactiveExtension before next assignment :=
            (InactiveExtension.fresh before assignment).trans
              (InactiveExtension.constrain _ (by simp [equation, ArithExpr.denote, inactive]))
          exact ⟨first.trans extension, finalLayout⟩
termination_by literals.length

mutual
  /-- With a zero enable, setting every fresh variable to zero satisfies the emitted code. -/
  theorem lowerExpr_inactive [Field F] [DecidableEq F]
      {function : String} {locals : List (String × Var)} {enable : ArithExpr F} {expr : Expr F}
      {before after : BuildState F} {polynomial : ArithExpr F}
      (compiled : (lowerExpr function locals enable expr).run before = .ok (polynomial, after))
      (layout : before.WellFormed)
      (localsBound : ∀ binding ∈ locals, binding.2 < before.nextVar)
      (enableBound : enable.inBounds before.nextVar = true)
      {assignment : Var → F} (inactive : enable.denote assignment = 0)
      (zeros : ∀ id, before.nextVar ≤ id → assignment id = 0) :
      InactiveExtension before after assignment ∧ after.WellFormed ∧
        polynomial.inBounds after.nextVar = true := by
    cases expr with
    | literal value =>
        simp [lowerExpr, StateT.run, StateT.pure, pure, Except.pure] at compiled
        rcases compiled with ⟨rfl, rfl⟩
        exact ⟨.refl _ _, layout, rfl⟩
    | var name =>
        cases found : locals.find? (·.1 == name) with
        | none =>
            simp [lowerExpr, found, StateT.run] at compiled
            cases compiled
        | some binding =>
            rcases binding with ⟨bindingName, id⟩
            simp [lowerExpr, found, StateT.run, StateT.pure, pure, Except.pure] at compiled
            rcases compiled with ⟨rfl, rfl⟩
            refine ⟨.refl _ _, layout, ?_⟩
            simpa [ArithExpr.inBounds] using
              localsBound (bindingName, id) (List.mem_of_find?_eq_some found)
    | neg expr =>
        cases lowered : lowerExpr function locals enable expr before with
        | error error =>
            simp [lowerExpr, StateT.run, StateT.bind, bind, Except.bind, lowered] at compiled
        | ok output =>
            rcases output with ⟨inner, state⟩
            simp [lowerExpr, StateT.run, StateT.bind, StateT.pure, bind, pure,
              Except.bind, Except.pure, lowered] at compiled
            rcases compiled with ⟨rfl, rfl⟩
            obtain ⟨extension, finalLayout, bounded⟩ :=
              lowerExpr_inactive lowered layout localsBound enableBound inactive zeros
            exact ⟨extension, finalLayout, by simpa [ArithExpr.inBounds] using bounded⟩
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
                obtain ⟨leftExtension, middleLayout, leftBound⟩ :=
                  lowerExpr_inactive leftRun layout localsBound enableBound inactive zeros
                obtain ⟨rightExtension, stateLayout, rightBound⟩ := lowerExpr_inactive rightRun middleLayout
                  (fun binding member => lt_of_lt_of_le (localsBound binding member) leftExtension.increase)
                  (ArithExpr.inBounds_mono leftExtension.increase enableBound) inactive
                  (fun id bound => zeros id (le_trans leftExtension.increase bound))
                have extension := leftExtension.trans rightExtension
                have leftFinal := ArithExpr.inBounds_mono rightExtension.increase leftBound
                cases op with
                | add | sub | mul =>
                    simp [lowerExpr, StateT.run, StateT.bind, StateT.pure, bind, pure,
                      Except.bind, Except.pure, leftRun, rightRun] at compiled
                    rcases compiled with ⟨rfl, rfl⟩
                    exact ⟨extension, stateLayout, by simp [ArithExpr.inBounds, leftFinal, rightBound]⟩
                | div =>
                    simp [lowerExpr, StateT.run, StateT.bind, StateT.pure, bind, pure,
                      Except.bind, Except.pure, leftRun, rightRun] at compiled
                    rcases compiled with ⟨rfl, rfl⟩
                    have enableFinal := ArithExpr.inBounds_mono
                      (le_trans extension.increase (Nat.le_succ _)) enableBound
                    refine ⟨extension.trans ((InactiveExtension.fresh state assignment).trans
                      (InactiveExtension.constrain _ (by simp [ArithExpr.denote, inactive]))),
                      stateLayout.fresh.constrain ?_, ?_⟩
                    · simp [ArithExpr.inBounds, enableFinal,
                        ArithExpr.inBounds_mono (Nat.le_succ _) rightBound]
                    · simp [ArithExpr.inBounds, ArithExpr.inBounds_mono (Nat.le_succ _) leftFinal]
    | call name args =>
        cases argsRun : lowerArgs function locals enable args before with
        | error error =>
            simp [lowerExpr, StateT.run, StateT.bind, bind, Except.bind, argsRun] at compiled
        | ok output =>
            rcases output with ⟨arguments, state⟩
            simp [lowerExpr, boolean, StateT.run, StateT.bind, StateT.pure, bind, pure,
              Except.bind, Except.pure, argsRun] at compiled
            rcases compiled with ⟨rfl, rfl⟩
            obtain ⟨extension, stateLayout, argsBound⟩ :=
              lowerArgs_inactive argsRun layout localsBound enableBound inactive zeros
            have enableFinal := ArithExpr.inBounds_mono
              (le_trans extension.increase (Nat.le_succ _)) enableBound
            have booleanBound : (ArithExpr.mul enable (.sub enable (.const 1))).inBounds
                (state.nextVar + 1) = true := by simp [ArithExpr.inBounds, enableFinal]
            have withBoolean := stateLayout.fresh.constrain booleanBound
            refine ⟨extension.trans ((InactiveExtension.fresh state assignment).trans
              ((InactiveExtension.constrain _ (by simp [ArithExpr.denote, inactive])).trans
                (InactiveExtension.send _ inactive))), withBoolean.send ?_, ?_⟩
            · simp only [Send.inBounds, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
              exact ⟨⟨Nat.lt_succ_self _, enableFinal⟩,
                fun arg member => ArithExpr.inBounds_mono (Nat.le_succ _) (argsBound arg member)⟩
            · simp [ArithExpr.inBounds]
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
                    obtain ⟨scrutineeExtension, middleLayout, scrutineeBound⟩ :=
                      lowerExpr_inactive scrutineeRun layout localsBound enableBound inactive zeros
                    have first := scrutineeExtension.trans (InactiveExtension.fresh middle assignment)
                    obtain ⟨armsExtension, stateLayout, selectorsBound, selectorsZero⟩ :=
                      lowerArms_inactive armsRun middleLayout.fresh
                        (fun binding member => lt_of_lt_of_le (localsBound binding member) first.increase)
                        (ArithExpr.inBounds_mono (Nat.le_succ _) scrutineeBound) (Nat.lt_succ_self _)
                        (fun id bound => zeros id (le_trans first.increase bound))
                    have extension := first.trans armsExtension
                    have enableFinal := ArithExpr.inBounds_mono extension.increase enableBound
                    refine ⟨extension.trans (InactiveExtension.constrainMany _
                      (selectionConstraints_zero inactive selectorsZero)),
                      stateLayout.constrainMany (selectionConstraints_inBounds enableFinal selectorsBound), ?_⟩
                    simp only [ArithExpr.inBounds, decide_eq_true_eq]
                    exact lt_of_lt_of_le (Nat.lt_succ_self _) armsExtension.increase
  termination_by sizeOf expr

  theorem lowerArgs_inactive [Field F] [DecidableEq F]
      {function : String} {locals : List (String × Var)} {enable : ArithExpr F} {args : List (Expr F)}
      {before after : BuildState F} {polynomials : List (ArithExpr F)}
      (compiled : (lowerArgs function locals enable args).run before = .ok (polynomials, after))
      (layout : before.WellFormed)
      (localsBound : ∀ binding ∈ locals, binding.2 < before.nextVar)
      (enableBound : enable.inBounds before.nextVar = true)
      {assignment : Var → F} (inactive : enable.denote assignment = 0)
      (zeros : ∀ id, before.nextVar ≤ id → assignment id = 0) :
      InactiveExtension before after assignment ∧ after.WellFormed ∧
        ∀ polynomial ∈ polynomials, polynomial.inBounds after.nextVar = true := by
    cases args with
    | nil =>
        simp [lowerArgs, StateT.run, StateT.pure, pure, Except.pure] at compiled
        rcases compiled with ⟨rfl, rfl⟩
        exact ⟨.refl _ _, layout, by simp⟩
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
                obtain ⟨headExtension, middleLayout, headBound⟩ :=
                  lowerExpr_inactive headRun layout localsBound enableBound inactive zeros
                obtain ⟨tailExtension, stateLayout, tailBounds⟩ := lowerArgs_inactive tailRun middleLayout
                  (fun binding member => lt_of_lt_of_le (localsBound binding member) headExtension.increase)
                  (ArithExpr.inBounds_mono headExtension.increase enableBound) inactive
                  (fun id bound => zeros id (le_trans headExtension.increase bound))
                refine ⟨headExtension.trans tailExtension, stateLayout, ?_⟩
                intro polynomial member
                rcases List.mem_cons.mp member with rfl | member
                · exact ArithExpr.inBounds_mono tailExtension.increase headBound
                · exact tailBounds polynomial member
  termination_by sizeOf args

  /-- All arms can be disabled simultaneously, including their nested matches and calls. -/
  theorem lowerArms_inactive [Field F] [DecidableEq F]
      {function : String} {locals : List (String × Var)} {scrutinee : ArithExpr F} {result : Var}
      {literals : List F} {arms : List (Pattern F × Expr F)}
      {before after : BuildState F} {selectors : List (ArithExpr F)}
      (compiled : (lowerArms function locals scrutinee result literals arms).run before = .ok (selectors, after))
      (layout : before.WellFormed)
      (localsBound : ∀ binding ∈ locals, binding.2 < before.nextVar)
      (scrutineeBound : scrutinee.inBounds before.nextVar = true)
      (resultBound : result < before.nextVar)
      {assignment : Var → F} (zeros : ∀ id, before.nextVar ≤ id → assignment id = 0) :
      InactiveExtension before after assignment ∧ after.WellFormed ∧
        (∀ selector ∈ selectors, selector.inBounds after.nextVar = true) ∧
        (∀ selector ∈ selectors, selector.denote assignment = 0) := by
    cases arms with
    | nil =>
        simp [lowerArms, StateT.run, StateT.pure, pure, Except.pure] at compiled
        rcases compiled with ⟨rfl, rfl⟩
        exact ⟨.refl _ _, layout, by simp, by simp⟩
    | cons arm rest =>
        cases armEq : arm
        rename_i pattern body
        simp only [armEq] at compiled ⊢
        have selectorZero : assignment before.nextVar = 0 := zeros _ (Nat.le_refl _)
        cases pattern with
        | literal value =>
            let patternEquation : ArithExpr F :=
              .mul (.var before.nextVar) (.sub scrutinee (.const value))
            let start : BuildState F := {
              before with nextVar := before.nextVar + 1
                          constraints := before.constraints.push patternEquation }
            have first : InactiveExtension before start assignment :=
              (InactiveExtension.fresh before assignment).trans
                (InactiveExtension.constrain _ (by simp [patternEquation, ArithExpr.denote, selectorZero]))
            have startLayout : start.WellFormed := layout.fresh.constrain (by
              simp [patternEquation, ArithExpr.inBounds,
                ArithExpr.inBounds_mono (Nat.le_succ _) scrutineeBound])
            cases bodyRun : lowerExpr function locals (.var before.nextVar) body start with
            | error error =>
                simp [lowerArms, StateT.run, StateT.bind, bind, Except.bind, start,
                  patternEquation, bodyRun] at compiled
            | ok output =>
                rcases output with ⟨bodyPolynomial, middle⟩
                obtain ⟨bodyExtension, middleLayout, bodyBound⟩ := lowerExpr_inactive bodyRun startLayout
                  (fun binding member => lt_of_lt_of_le (localsBound binding member) first.increase)
                  (by simp [start, ArithExpr.inBounds]) selectorZero
                  (fun id bound => zeros id (le_trans first.increase bound))
                have extension := first.trans bodyExtension
                have selectorBound : before.nextVar < middle.nextVar :=
                  lt_of_lt_of_le (Nat.lt_succ_self _) bodyExtension.increase
                let resultEquation : ArithExpr F :=
                  .mul (.var before.nextVar) (.sub (.var result) bodyPolynomial)
                let next : BuildState F := { middle with constraints := middle.constraints.push resultEquation }
                have nextLayout : next.WellFormed := middleLayout.constrain (by
                  simp [resultEquation, ArithExpr.inBounds, selectorBound, bodyBound,
                    lt_of_lt_of_le resultBound extension.increase])
                have nextExtension : InactiveExtension before next assignment := extension.trans
                  (InactiveExtension.constrain _ (by simp [resultEquation, ArithExpr.denote, selectorZero]))
                cases restRun : lowerArms function locals scrutinee result literals rest next with
                | error error =>
                    simp [lowerArms, StateT.run, StateT.bind, bind, Except.bind, start,
                      patternEquation, next, resultEquation, bodyRun, restRun] at compiled
                | ok output =>
                    rcases output with ⟨restSelectors, state⟩
                    simp [lowerArms, StateT.run, StateT.bind, StateT.pure, bind, pure,
                      Except.bind, Except.pure, start, patternEquation, next, resultEquation,
                      bodyRun, restRun] at compiled
                    rcases compiled with ⟨rfl, rfl⟩
                    obtain ⟨restExtension, finalLayout, restBound, restZero⟩ :=
                      lowerArms_inactive restRun nextLayout
                        (fun binding member => lt_of_lt_of_le (localsBound binding member) nextExtension.increase)
                        (ArithExpr.inBounds_mono nextExtension.increase scrutineeBound)
                        (lt_of_lt_of_le resultBound nextExtension.increase)
                        (fun id bound => zeros id (le_trans nextExtension.increase bound))
                    refine ⟨nextExtension.trans restExtension, finalLayout, ?_, ?_⟩
                    · intro selector member
                      rcases List.mem_cons.mp member with rfl | member
                      · simp only [ArithExpr.inBounds, decide_eq_true_eq]
                        exact lt_of_lt_of_le selectorBound restExtension.increase
                      · exact restBound selector member
                    · intro selector member
                      rcases List.mem_cons.mp member with rfl | member
                      · exact selectorZero
                      · exact restZero selector member
        | wildcard =>
            cases excludedRun : excludeLiterals (.var before.nextVar) scrutinee literals
                { before with nextVar := before.nextVar + 1 } with
            | error error =>
                simp [lowerArms, StateT.run, StateT.bind, bind, Except.bind, excludedRun] at compiled
            | ok output =>
                rcases output with ⟨finished, middle⟩
                cases finished
                obtain ⟨excludedExtension, middleLayout⟩ := excludeLiterals_inactive excludedRun layout.fresh
                  (by simp [ArithExpr.inBounds]) (ArithExpr.inBounds_mono (Nat.le_succ _) scrutineeBound)
                  selectorZero
                have first := (InactiveExtension.fresh before assignment).trans excludedExtension
                have selectorBound : before.nextVar < middle.nextVar :=
                  lt_of_lt_of_le (Nat.lt_succ_self _) excludedExtension.increase
                cases bodyRun : lowerExpr function locals (.var before.nextVar) body middle with
                | error error =>
                    simp [lowerArms, StateT.run, StateT.bind, bind, Except.bind, excludedRun, bodyRun] at compiled
                | ok output =>
                    rcases output with ⟨bodyPolynomial, state⟩
                    simp [lowerArms, StateT.run, StateT.bind, StateT.pure, bind, pure,
                      Except.bind, Except.pure, excludedRun, bodyRun] at compiled
                    rcases compiled with ⟨rfl, rfl⟩
                    obtain ⟨bodyExtension, stateLayout, bodyBound⟩ := lowerExpr_inactive bodyRun middleLayout
                      (fun binding member => lt_of_lt_of_le (localsBound binding member) first.increase)
                      (by simpa [ArithExpr.inBounds] using selectorBound) selectorZero
                      (fun id bound => zeros id (le_trans first.increase bound))
                    have extension := first.trans bodyExtension
                    have selectorFinal := lt_of_lt_of_le selectorBound bodyExtension.increase
                    refine ⟨extension.trans (InactiveExtension.constrain _
                      (by simp [ArithExpr.denote, selectorZero])), stateLayout.constrain ?_, ?_, ?_⟩
                    · simp [ArithExpr.inBounds, bodyBound, selectorFinal,
                        lt_of_lt_of_le resultBound extension.increase]
                    · simpa [ArithExpr.inBounds] using selectorFinal
                    · simpa [ArithExpr.denote] using selectorZero
  termination_by sizeOf arms
end

/-- A finite witness for inactive code, with no assumption that the expression evaluates. -/
theorem lowerExpr_inactive_complete [Field F] [DecidableEq F]
    {function : String} {locals : List (String × Var)} {enable : ArithExpr F} {expr : Expr F}
    {before after : BuildState F} {polynomial : ArithExpr F}
    (compiled : (lowerExpr function locals enable expr).run before = .ok (polynomial, after))
    (layout : before.WellFormed)
    (localsBound : ∀ binding ∈ locals, binding.2 < before.nextVar)
    (enableBound : enable.inBounds before.nextVar = true)
    {calls : CallRelation F} {initial : List F} (size : initial.length = before.nextVar)
    (valid : before.Valid calls (Row.assignment ⟨function, initial⟩))
    (inactive : enable.denote (Row.assignment ⟨function, initial⟩) = 0) :
    ∃ values, initial.IsPrefix values ∧ values.length = after.nextVar ∧
      after.WellFormed ∧ polynomial.inBounds after.nextVar = true ∧
      after.Valid calls (Row.assignment ⟨function, values⟩) ∧
      InactiveExtension before after (Row.assignment ⟨function, values⟩) := by
  obtain ⟨extension, finalLayout, bounded⟩ := lowerExpr_inactive compiled layout localsBound enableBound
    inactive (fun id bound => by
      simp [Row.assignment, List.getElem?_eq_none (show initial.length ≤ id by omega)])
  refine ⟨initial ++ List.replicate (after.nextVar - before.nextVar) 0,
    List.prefix_append _ _, ?_, finalLayout, bounded, ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate, size]
    exact Nat.add_sub_of_le extension.increase
  · rw [assignment_append_zeros]
    exact extension.valid valid
  · rw [assignment_append_zeros]
    exact extension

/-- A finite witness disabling an entire arm list while preserving the match result. -/
theorem lowerArms_inactive_complete [Field F] [DecidableEq F]
    {function : String} {locals : List (String × Var)} {scrutinee : ArithExpr F} {result : Var}
    {literals : List F} {arms : List (Pattern F × Expr F)}
    {before after : BuildState F} {selectors : List (ArithExpr F)}
    (compiled : (lowerArms function locals scrutinee result literals arms).run before = .ok (selectors, after))
    (layout : before.WellFormed)
    (localsBound : ∀ binding ∈ locals, binding.2 < before.nextVar)
    (scrutineeBound : scrutinee.inBounds before.nextVar = true) (resultBound : result < before.nextVar)
    {calls : CallRelation F} {initial : List F} (size : initial.length = before.nextVar)
    (valid : before.Valid calls (Row.assignment ⟨function, initial⟩)) :
    ∃ values, initial.IsPrefix values ∧ values.length = after.nextVar ∧ after.WellFormed ∧
      (∀ selector ∈ selectors, selector.inBounds after.nextVar = true) ∧
      after.Valid calls (Row.assignment ⟨function, values⟩) ∧
      (∀ selector ∈ selectors, selector.denote (Row.assignment ⟨function, values⟩) = 0) ∧
      InactiveExtension before after (Row.assignment ⟨function, values⟩) := by
  obtain ⟨extension, finalLayout, bounded, zeros⟩ := lowerArms_inactive compiled layout localsBound
    scrutineeBound resultBound (assignment := Row.assignment ⟨function, initial⟩)
    (fun id bound => by simp [Row.assignment, List.getElem?_eq_none (show initial.length ≤ id by omega)])
  refine ⟨initial ++ List.replicate (after.nextVar - before.nextVar) 0,
    List.prefix_append _ _, ?_, finalLayout, bounded, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate, size]
    exact Nat.add_sub_of_le extension.increase
  · rw [assignment_append_zeros]
    exact extension.valid valid
  · rw [assignment_append_zeros]
    exact zeros
  · rw [assignment_append_zeros]
    exact extension

end Aiur.Scalar.Circuit.Compiler
