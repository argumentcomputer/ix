import Aiur.Tuple.Circuit.SelectorWitness

namespace Aiur.Tuple.Circuit.Compiler

set_option maxHeartbeats 1600000

mutual
  /-- Disabled expressions still admit all unconditional pattern-test witnesses. -/
  theorem lowerExpr_inactive [Field F] [DecidableEq F]
      {program : Program F} {function : String} {locals : Locals F}
      {enable : ArithExpr F} {expr : Expr F} {output : Symbolic F} {before after : BuildState F}
      (compiled : lowerExpr program function locals enable expr before = .ok (output, after))
      {calls : CallRelation F} {initial : Var → F}
      (layout : before.WellFormed) (valid : before.Valid calls initial)
      (localsBound : LocalsBounded before.nextVar locals)
      (enableBound : enable.inBounds before.nextVar = true) (inactive : enable.denote initial = 0) :
      ∃ assignment, Extension calls before after initial assignment ∧ Bounded after.nextVar output := by
    cases expr with
    | literal value =>
        simp only [lowerExpr, pure_ok] at compiled
        obtain ⟨rfl, rfl⟩ := compiled
        exact ⟨initial, .refl layout valid, bounded_field.mpr rfl⟩
    | var name =>
        cases found : locals.find? (·.1 == name) with
        | none => simp [lowerExpr, found] at compiled
        | some binding =>
            obtain ⟨bindingName, value⟩ := binding
            simp only [lowerExpr, found, pure_ok] at compiled
            obtain ⟨rfl, rfl⟩ := compiled
            exact ⟨initial, .refl layout valid, localsBound _ (List.mem_of_find?_eq_some found)⟩
    | tuple items =>
        simp only [lowerExpr] at compiled
        obtain ⟨values, middle, itemsRun, finished⟩ := bind_ok.mp compiled
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        obtain ⟨assignment, extension, bounded⟩ :=
          lowerArgs_inactive itemsRun layout valid localsBound enableBound inactive
        exact ⟨assignment, extension, bounded_tuple.mpr bounded⟩
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
                obtain ⟨assignment, extension, bounded⟩ :=
                  lowerExpr_inactive valueRun layout valid localsBound enableBound inactive
                exact ⟨assignment, extension,
                  bounded_tuple.mp bounded result (List.mem_of_getElem? projected)⟩
    | letValue pattern value body =>
        simp only [lowerExpr] at compiled
        obtain ⟨input, s₁, valueRun, rest⟩ := bind_ok.mp compiled
        obtain ⟨⟨test, bindings⟩, s₂, patternRun, rest⟩ := bind_ok.mp rest
        obtain ⟨finished, s₃, guardRun, bodyRun⟩ := bind_ok.mp rest
        cases finished
        obtain ⟨a, e₁, inputBound⟩ := lowerExpr_inactive valueRun layout valid localsBound enableBound inactive
        obtain ⟨b, e₂, testBound, bindingsBound⟩ := lowerPattern_complete patternRun e₁.layout e₁.valid inputBound
        have chainExt := e₁.trans e₂
        have e₃ := guarded_complete guardRun e₂.layout e₂.valid (chainExt.bound enableBound)
          (by simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using testBound)
          (Or.inl ((chainExt.polynomial enableBound).trans inactive))
        obtain ⟨c, e₄, bodyBound⟩ := lowerExpr_inactive bodyRun e₃.layout e₃.valid
          (localsBounded_append.mpr ⟨bindingsBound.mono e₃.increase, localsBound.mono (chainExt.trans e₃).increase⟩)
          ((chainExt.trans e₃).bound enableBound) (((chainExt.trans e₃).polynomial enableBound).trans inactive)
        exact ⟨c, (chainExt.trans e₃).trans e₄, bodyBound⟩
    | neg value =>
        simp only [lowerExpr] at compiled
        obtain ⟨input, s₁, valueRun, rest⟩ := bind_ok.mp compiled
        obtain ⟨polynomial, s₂, fieldRun, finished⟩ := bind_ok.mp rest
        obtain ⟨rfl, rfl⟩ := asField_ok fieldRun
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        obtain ⟨a, extension, bounded⟩ := lowerExpr_inactive valueRun layout valid localsBound enableBound inactive
        exact ⟨a, extension, by simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using bounded⟩
    | binary op left right =>
        simp only [lowerExpr] at compiled
        obtain ⟨leftValue, s₁, leftRun, rest⟩ := bind_ok.mp compiled
        obtain ⟨leftPoly, s₂, leftField, rest⟩ := bind_ok.mp rest
        obtain ⟨rfl, rfl⟩ := asField_ok leftField
        obtain ⟨rightValue, s₃, rightRun, rest⟩ := bind_ok.mp rest
        obtain ⟨rightPoly, s₄, rightField, rest⟩ := bind_ok.mp rest
        obtain ⟨rfl, rfl⟩ := asField_ok rightField
        obtain ⟨a, e₁, leftBound⟩ := lowerExpr_inactive leftRun layout valid localsBound enableBound inactive
        obtain ⟨b, e₂, rightBound⟩ := lowerExpr_inactive rightRun e₁.layout e₁.valid
          (localsBound.mono e₁.increase) (e₁.bound enableBound) ((e₁.polynomial enableBound).trans inactive)
        have chainExt := e₁.trans e₂
        have lb := bounded_field.mp (leftBound.mono e₂.increase)
        have rb := bounded_field.mp rightBound
        cases op with
        | add | sub | mul =>
            obtain ⟨rfl, rfl⟩ := pure_ok.mp rest
            exact ⟨b, chainExt, by simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using And.intro lb rb⟩
        | div =>
            obtain ⟨inverse, s₅, freshRun, rest⟩ := bind_ok.mp rest
            obtain ⟨finished, s₆, inverseRun, finishedRun⟩ := bind_ok.mp rest
            cases finished
            obtain ⟨rfl, rfl⟩ := pure_ok.mp finishedRun
            obtain ⟨c, e₃, invBound, _⟩ := fresh_complete freshRun e₂.layout e₂.valid 0
            have ib : (ArithExpr.var inverse : ArithExpr F).inBounds s₅.nextVar = true := by
              simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using invBound
            have e₄ := guarded_complete inverseRun e₃.layout e₃.valid ((chainExt.trans e₃).bound enableBound)
              (by simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using And.intro (e₃.bound rb) ib)
              (Or.inl (((chainExt.trans e₃).polynomial enableBound).trans inactive))
            exact ⟨c, (chainExt.trans e₃).trans e₄, by
              simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using
                And.intro ((e₃.trans e₄).bound lb) (e₄.bound ib)⟩
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
            obtain ⟨a, e₁, argsBound⟩ := lowerArgs_inactive argsRun layout valid localsBound enableBound inactive
            obtain ⟨b, e₂, resultBound, _⟩ := freshValue_complete resultRun e₁.layout e₁.valid
              (zeroValue callee.result) (zeroValue_type _)
            have chainExt := e₁.trans e₂
            have e₃ := boolean_complete booleanRun e₂.layout e₂.valid (chainExt.bound enableBound)
              (Or.inl ((chainExt.polynomial enableBound).trans inactive))
            have e₄ := send_complete e₃.layout e₃.valid ⟨name, arguments, result, enable⟩
              (send_bounded (fun value h => (argsBound value h).mono (e₂.trans e₃).increase)
                (resultBound.mono e₃.increase) ((chainExt.trans e₃).bound enableBound)) (by
                  intro active
                  have zero := ((chainExt.trans e₃).polynomial enableBound).trans inactive
                  exact (zero_ne_one (zero.symm.trans active)).elim)
            exact ⟨b, (chainExt.trans e₃).trans e₄, resultBound.mono (e₃.trans e₄).increase⟩
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
        obtain ⟨a, e₁, inputBound⟩ := lowerExpr_inactive scrutineeRun layout valid localsBound enableBound inactive
        obtain ⟨b, e₂, resultBound, _⟩ := freshValue_complete resultRun e₁.layout e₁.valid
          (zeroValue type) (zeroValue_type _)
        have chainExt := e₁.trans e₂
        obtain ⟨c, e₃, selectorsBound, selectorsZero⟩ := lowerArms_inactive armsRun e₂.layout e₂.valid
          (localsBound.mono chainExt.increase) (inputBound.mono e₂.increase) resultBound
          (chainExt.bound enableBound) ((chainExt.polynomial enableBound).trans inactive)
        have selection := Scalar.Circuit.SelectorsValid.zeros
          (selectors := selectors.map (ArithExpr.denote c)) (by
          simpa only [List.forall_mem_map] using selectorsZero)
        have e₄ := excludePairs_complete exclusionRun e₃.layout e₃.valid selectorsBound selection.exclusive
        have e₅ := sum_complete sumRun e₄.layout e₄.valid
          (fun p h => e₄.bound (selectorsBound p h)) (((chainExt.trans e₃).trans e₄).bound enableBound)
          (by rw [((chainExt.trans e₃).trans e₄).polynomial enableBound, inactive]; exact selection.sum)
        exact ⟨c, ((chainExt.trans e₃).trans e₄).trans e₅, resultBound.mono ((e₃.trans e₄).trans e₅).increase⟩
  termination_by sizeOf expr

  theorem lowerArgs_inactive [Field F] [DecidableEq F]
      {program : Program F} {function : String} {locals : Locals F} {enable : ArithExpr F}
      {args : List (Expr F)} {outputs : List (Symbolic F)} {before after : BuildState F}
      (compiled : lowerArgs program function locals enable args before = .ok (outputs, after))
      {calls : CallRelation F} {initial : Var → F}
      (layout : before.WellFormed) (valid : before.Valid calls initial)
      (localsBound : LocalsBounded before.nextVar locals)
      (enableBound : enable.inBounds before.nextVar = true) (inactive : enable.denote initial = 0) :
      ∃ assignment, Extension calls before after initial assignment ∧
        ∀ value ∈ outputs, Bounded after.nextVar value := by
    cases args with
    | nil =>
        simp only [lowerArgs, pure_ok] at compiled
        obtain ⟨rfl, rfl⟩ := compiled
        exact ⟨initial, .refl layout valid, by simp⟩
    | cons arg args =>
        simp only [lowerArgs] at compiled
        obtain ⟨head, middle, headRun, rest⟩ := bind_ok.mp compiled
        obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp rest
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        obtain ⟨a, e₁, headBound⟩ := lowerExpr_inactive headRun layout valid localsBound enableBound inactive
        obtain ⟨b, e₂, tailBound⟩ := lowerArgs_inactive tailRun e₁.layout e₁.valid
          (localsBound.mono e₁.increase) (e₁.bound enableBound) ((e₁.polynomial enableBound).trans inactive)
        refine ⟨b, e₁.trans e₂, ?_⟩
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact headBound.mono e₂.increase
        · exact tailBound value member
  termination_by sizeOf args

  theorem lowerArms_inactive [Field F] [DecidableEq F]
      {program : Program F} {function : String} {locals : Locals F}
      {scrutinee result : Symbolic F} {remaining : ArithExpr F}
      {arms : List (Pattern F × Expr F)} {selectors : List (ArithExpr F)} {before after : BuildState F}
      (compiled : lowerArms program function locals scrutinee result remaining arms before = .ok (selectors, after))
      {calls : CallRelation F} {initial : Var → F}
      (layout : before.WellFormed) (valid : before.Valid calls initial)
      (localsBound : LocalsBounded before.nextVar locals)
      (inputBound : Bounded before.nextVar scrutinee) (resultBound : Bounded before.nextVar result)
      (remainingBound : remaining.inBounds before.nextVar = true) (inactive : remaining.denote initial = 0) :
      ∃ assignment, Extension calls before after initial assignment ∧
        (∀ selector ∈ selectors, selector.inBounds after.nextVar = true) ∧
        (∀ selector ∈ selectors, selector.denote assignment = 0) := by
    cases arms with
    | nil =>
        simp only [lowerArms, pure_ok] at compiled
        obtain ⟨rfl, rfl⟩ := compiled
        exact ⟨initial, .refl layout valid, by simp, by simp⟩
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
        obtain ⟨a, e₁, testBound, bindingsBound⟩ := lowerPattern_complete patternRun layout valid inputBound
        obtain ⟨b, e₂, idBound, selZero⟩ := fresh_complete freshRun e₁.layout e₁.valid 0
        have selectorBound : (ArithExpr.var selector : ArithExpr F).inBounds s₂.nextVar = true := by
          simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using idBound
        have e₃ := boolean_complete booleanRun e₂.layout e₂.valid selectorBound (Or.inl selZero)
        have chainExt := (e₁.trans e₂).trans e₃
        have e₄ := constrain_complete equationRun e₃.layout e₃.valid
          (by simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using
            And.intro (e₃.bound selectorBound) (And.intro (chainExt.bound remainingBound) ((e₂.trans e₃).bound testBound)))
          (by change b selector - remaining.denote b * test.denote b = 0
              rw [selZero, chainExt.polynomial remainingBound, inactive]; simp)
        obtain ⟨c, e₅, bodyBound⟩ := lowerExpr_inactive bodyRun e₄.layout e₄.valid
          (localsBounded_append.mpr ⟨bindingsBound.mono ((e₂.trans e₃).trans e₄).increase,
            localsBound.mono (chainExt.trans e₄).increase⟩)
          ((e₃.trans e₄).bound selectorBound)
          (by simpa only [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] using selZero)
        have selZeroC : (ArithExpr.var selector : ArithExpr F).denote c = 0 :=
          ((e₃.trans e₄).trans e₅).polynomial selectorBound |>.trans selZero
        have headExt := (chainExt.trans e₄).trans e₅
        have e₆ := constrainValue_complete valueRun e₅.layout e₅.valid
          (((e₃.trans e₄).trans e₅).bound selectorBound) (resultBound.mono headExt.increase) bodyBound (Or.inl selZeroC)
        have total := headExt.trans e₆
        have finalBound := (((e₃.trans e₄).trans e₅).trans e₆).bound selectorBound
        split at rest
        · obtain ⟨rfl, rfl⟩ := pure_ok.mp rest
          exact ⟨c, total, by simpa using finalBound, by simpa using selZeroC⟩
        · simp only [pure_bind] at rest
          obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp rest
          obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
          have nextBound : (ArithExpr.mul remaining (.sub (.const 1) test)).inBounds s₆.nextVar = true := by
            simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using
              And.intro (total.bound remainingBound) (((((e₂.trans e₃).trans e₄).trans e₅).trans e₆).bound testBound)
          have nextZero : (ArithExpr.mul remaining (.sub (.const 1) test)).denote c = 0 := by
            change remaining.denote c * (1 - test.denote c) = 0
            rw [total.polynomial remainingBound, inactive, zero_mul]
          obtain ⟨d, tailExt, tailBound, tailZero⟩ := lowerArms_inactive tailRun total.layout total.valid
            (localsBound.mono total.increase) (inputBound.mono total.increase) (resultBound.mono total.increase)
            nextBound nextZero
          refine ⟨d, total.trans tailExt, ?_, ?_⟩
          · intro p member
            rcases List.mem_cons.mp member with rfl | member
            · exact tailExt.bound finalBound
            · exact tailBound p member
          · intro p member
            rcases List.mem_cons.mp member with rfl | member
            · exact (tailExt.polynomial finalBound).trans selZeroC
            · exact tailZero p member
  termination_by sizeOf arms
  decreasing_by
    all_goals simp only [*, Prod.mk.sizeOf_spec, List.cons.sizeOf_spec]
    all_goals omega
end

end Aiur.Tuple.Circuit.Compiler
