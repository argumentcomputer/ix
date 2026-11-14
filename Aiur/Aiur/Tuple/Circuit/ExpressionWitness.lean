import Aiur.Tuple.Circuit.InactiveWitness
import Aiur.Tuple.TypecheckFacts

namespace Aiur.Tuple.Circuit.Compiler

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000

@[simp] theorem localsEnvironment_types [Field F] (locals : Locals F) (assignment : Var → F) :
    environmentTypes (localsEnvironment locals assignment) = locals.map (fun binding => (binding.1, binding.2.type)) := by
  simp [environmentTypes, localsEnvironment, List.map_map, Value.type_map]

mutual
  /-- Source evaluation supplies witnesses for the actual tuple compiler. -/
  theorem lowerExpr_complete [Field F] [DecidableEq F]
      {program : Program F} {function : String} {locals : Locals F}
      {enable : ArithExpr F} {expr : Expr F} {output : Symbolic F} {before after : BuildState F}
      (compiled : lowerExpr program function locals enable expr before = .ok (output, after))
      {calls : CallRelation F} (typed : CallsTyped program calls) {initial : Var → F}
      (layout : before.WellFormed) (valid : before.Valid calls initial)
      (localsBound : LocalsBounded before.nextVar locals)
      (enableBound : enable.inBounds before.nextVar = true) (active : enable.denote initial = 1)
      {value : Value F} (evaluated : EvalExprWith calls (localsEnvironment locals initial) expr value) :
      ∃ assignment, Extension calls before after initial assignment ∧ Bounded after.nextVar output ∧
        output.map (ArithExpr.denote assignment) = value := by
    cases expr with
    | literal literal =>
        cases evaluated
        simp only [lowerExpr, pure_ok] at compiled
        obtain ⟨rfl, rfl⟩ := compiled
        exact ⟨initial, .refl layout valid, bounded_field.mpr rfl, by simp [Value.map, ArithExpr.denote, Scalar.Circuit.ArithExpr.denote]⟩
    | var name =>
        cases evaluated with
        | var lookup =>
            cases found : locals.find? (·.1 == name) with
            | none => simp [lowerExpr, found] at compiled
            | some binding =>
                obtain ⟨bindingName, result⟩ := binding
                simp only [lowerExpr, found, pure_ok] at compiled
                obtain ⟨rfl, rfl⟩ := compiled
                refine ⟨initial, .refl layout valid, localsBound _ (List.mem_of_find?_eq_some found), ?_⟩
                simpa [localsEnvironment, List.find?_map, Function.comp_def, found] using
                  congrArg (Option.map Prod.snd) lookup
    | tuple items =>
        cases evaluated with
        | tuple itemsEval =>
            simp only [lowerExpr] at compiled
            obtain ⟨values, middle, itemsRun, finished⟩ := bind_ok.mp compiled
            obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
            obtain ⟨a, extension, bounded, valuesEq⟩ :=
              lowerArgs_complete itemsRun typed layout valid localsBound enableBound active itemsEval
            exact ⟨a, extension, bounded_tuple.mpr bounded, by simp only [Value.map, valuesEq]⟩
    | project expr index =>
        cases evaluated with
        | project inputEval projected =>
            simp only [lowerExpr] at compiled
            obtain ⟨input, middle, inputRun, rest⟩ := bind_ok.mp compiled
            cases input with
            | field => simp at rest
            | tuple items =>
                cases found : items[index]? with
                | none => simp [found] at rest
                | some result =>
                    simp only [found, pure_ok] at rest
                    obtain ⟨rfl, rfl⟩ := rest
                    obtain ⟨a, extension, bounded, inputEq⟩ :=
                      lowerExpr_complete inputRun typed layout valid localsBound enableBound active inputEval
                    refine ⟨a, extension, bounded_tuple.mp bounded result (List.mem_of_getElem? found), ?_⟩
                    rw [← inputEq] at projected
                    simpa [Value.map, projectValue, List.getElem?_map, found, pure, Except.pure] using projected
    | letValue pattern expr body =>
        cases evaluated with
        | letValue inputEval matched bodyEval =>
            simp only [lowerExpr] at compiled
            obtain ⟨input, s₁, inputRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨⟨test, bindings⟩, s₂, patternRun, rest⟩ := bind_ok.mp rest
            obtain ⟨finished, s₃, guardRun, bodyRun⟩ := bind_ok.mp rest
            cases finished
            obtain ⟨a, e₁, inputBound, inputEq⟩ :=
              lowerExpr_complete inputRun typed layout valid localsBound enableBound active inputEval
            obtain ⟨b, e₂, testBound, bindingsBound⟩ := lowerPattern_complete patternRun e₁.layout e₁.valid inputBound
            have chainExt := e₁.trans e₂
            have patternTest := (lowerPattern_sound patternRun e₂.valid).2
            rw [e₂.value inputBound, inputEq, matched] at patternTest
            obtain ⟨bindingsEq, testOne⟩ : _ ∧ test.denote b = 1 := by
              rcases patternTest with ⟨same, one⟩ | ⟨impossible, _⟩
              · exact ⟨Option.some.inj same, one⟩
              · cases impossible
            have e₃ := guarded_complete guardRun e₂.layout e₂.valid (chainExt.bound enableBound)
              (by simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using testBound)
              (Or.inr (by change test.denote b - 1 = 0; simp [testOne]))
            obtain ⟨c, e₄, bodyBound, bodyEq⟩ := lowerExpr_complete bodyRun typed e₃.layout e₃.valid
              (localsBounded_append.mpr ⟨bindingsBound.mono e₃.increase, localsBound.mono (chainExt.trans e₃).increase⟩)
              ((chainExt.trans e₃).bound enableBound) (((chainExt.trans e₃).polynomial enableBound).trans active)
              (by rw [localsEnvironment_append, ← bindingsEq, chainExt.locals localsBound]; exact bodyEval)
            exact ⟨c, (chainExt.trans e₃).trans e₄, bodyBound, bodyEq⟩
    | neg expr =>
        cases evaluated with
        | neg inputEval operation =>
            simp only [lowerExpr] at compiled
            obtain ⟨input, s₁, inputRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨polynomial, s₂, fieldRun, finished⟩ := bind_ok.mp rest
            obtain ⟨rfl, rfl⟩ := asField_ok fieldRun
            obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
            obtain ⟨a, extension, bounded, inputEq⟩ :=
              lowerExpr_complete inputRun typed layout valid localsBound enableBound active inputEval
            refine ⟨a, extension, by simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using bounded, ?_⟩
            rw [← inputEq] at operation
            simpa [Value.map, evalNeg, ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] using operation
    | binary op left right =>
        cases evaluated with
        | binary leftEval rightEval operation =>
            simp only [lowerExpr] at compiled
            obtain ⟨leftValue, s₁, leftRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨leftPoly, s₂, leftField, rest⟩ := bind_ok.mp rest
            obtain ⟨rfl, rfl⟩ := asField_ok leftField
            obtain ⟨rightValue, s₃, rightRun, rest⟩ := bind_ok.mp rest
            obtain ⟨rightPoly, s₄, rightField, rest⟩ := bind_ok.mp rest
            obtain ⟨rfl, rfl⟩ := asField_ok rightField
            obtain ⟨a, e₁, leftBound, leftEq⟩ :=
              lowerExpr_complete leftRun typed layout valid localsBound enableBound active leftEval
            obtain ⟨b, e₂, rightBound, rightEq⟩ := lowerExpr_complete rightRun typed e₁.layout e₁.valid
              (localsBound.mono e₁.increase) (e₁.bound enableBound) ((e₁.polynomial enableBound).trans active)
              (by rw [e₁.locals localsBound]; exact rightEval)
            have chainExt := e₁.trans e₂
            have lb := bounded_field.mp (leftBound.mono e₂.increase)
            have rb := bounded_field.mp rightBound
            have leftEqB := (e₂.value leftBound).trans leftEq
            rw [← leftEqB, ← rightEq] at operation
            cases op with
            | add | sub | mul =>
                obtain ⟨rfl, rfl⟩ := pure_ok.mp rest
                exact ⟨b, chainExt, by
                  simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using And.intro lb rb,
                  by simpa [Value.map, evalBinOp, ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] using operation⟩
            | div =>
                have nonzero : rightPoly.denote b ≠ 0 := by
                  intro zero
                  simp [Value.map, evalBinOp, zero] at operation
                have quotient : Value.field (leftPoly.denote b / rightPoly.denote b) = value := by
                  simpa [Value.map, evalBinOp, nonzero] using operation
                obtain ⟨inverse, s₅, freshRun, rest⟩ := bind_ok.mp rest
                obtain ⟨finished, s₆, inverseRun, finishedRun⟩ := bind_ok.mp rest
                cases finished
                obtain ⟨rfl, rfl⟩ := pure_ok.mp finishedRun
                obtain ⟨c, e₃, invBound, invEq⟩ := fresh_complete freshRun e₂.layout e₂.valid (rightPoly.denote b)⁻¹
                have ib : (ArithExpr.var inverse : ArithExpr F).inBounds s₅.nextVar = true := by
                  simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using invBound
                have e₄ := guarded_complete inverseRun e₃.layout e₃.valid ((chainExt.trans e₃).bound enableBound)
                  (by simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using And.intro (e₃.bound rb) ib)
                  (Or.inr (by
                    change rightPoly.denote c * c inverse - 1 = 0
                    rw [e₃.polynomial rb, invEq]
                    simp [nonzero]))
                refine ⟨c, (chainExt.trans e₃).trans e₄, ?_, ?_⟩
                · simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using
                    And.intro ((e₃.trans e₄).bound lb) (e₄.bound ib)
                · simp only [Value.map]
                  change Value.field (leftPoly.denote c * c inverse) = value
                  rw [e₃.polynomial lb, invEq, ← div_eq_mul_inv]
                  exact quotient
    | call name args =>
        cases evaluated with
        | call argsEval calleeEval =>
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
                obtain ⟨a, e₁, argsBound, argsEq⟩ :=
                  lowerArgs_complete argsRun typed layout valid localsBound enableBound active argsEval
                obtain ⟨b, e₂, resultBound, resultEq⟩ := freshValue_complete resultRun e₁.layout e₁.valid
                  value (typed _ _ _ calleeEval callee found)
                have chainExt := e₁.trans e₂
                have e₃ := boolean_complete booleanRun e₂.layout e₂.valid (chainExt.bound enableBound)
                  (Or.inr ((chainExt.polynomial enableBound).trans active))
                have e₄ := send_complete e₃.layout e₃.valid ⟨name, arguments, result, enable⟩
                  (send_bounded (fun value h => (argsBound value h).mono (e₂.trans e₃).increase)
                    (resultBound.mono e₃.increase) ((chainExt.trans e₃).bound enableBound)) (by
                      intro _
                      simp only [e₂.values argsBound, argsEq, resultEq]
                      exact calleeEval)
                exact ⟨b, (chainExt.trans e₃).trans e₄, resultBound.mono (e₃.trans e₄).increase,
                  by simpa only [Value.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using resultEq⟩
    | matchValue scrutinee arms =>
        have allEval := evaluated
        cases evaluated with
        | matchValue inputEval selected branchEval =>
            simp only [lowerExpr] at compiled
            obtain ⟨checked, s₁, checkRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨_, rfl⟩ := lift_eq_ok checkRun
            obtain ⟨type, s₂, typeRun, rest⟩ := bind_ok.mp rest
            obtain ⟨inferred, rfl⟩ := lift_eq_ok typeRun
            have shape : value.type = type := by
              apply allEval.type typed function type
              rw [localsEnvironment_types]
              cases h : inferType program function (locals.map fun (name, value) => (name, value.type))
                  (.matchValue scrutinee arms) <;> simp_all [Except.mapError]
            obtain ⟨input, s₃, inputRun, rest⟩ := bind_ok.mp rest
            obtain ⟨result, s₄, resultRun, rest⟩ := bind_ok.mp rest
            obtain ⟨selectors, s₅, armsRun, rest⟩ := bind_ok.mp rest
            obtain ⟨finished, s₆, exclusionRun, rest⟩ := bind_ok.mp rest
            cases finished
            obtain ⟨finished, s₇, sumRun, finishedRun⟩ := bind_ok.mp rest
            cases finished
            obtain ⟨rfl, rfl⟩ := pure_ok.mp finishedRun
            obtain ⟨a, e₁, inputBound, inputEq⟩ :=
              lowerExpr_complete inputRun typed layout valid localsBound enableBound active inputEval
            obtain ⟨b, e₂, resultBound, resultEq⟩ := freshValue_complete resultRun e₁.layout e₁.valid value shape
            have chainExt := e₁.trans e₂
            obtain ⟨c, e₃, selectorsBound, selection⟩ := lowerArms_complete armsRun typed e₂.layout e₂.valid
              (localsBound.mono chainExt.increase) (inputBound.mono e₂.increase) resultBound
              (chainExt.bound enableBound) ((chainExt.polynomial enableBound).trans active)
              (by rw [e₂.value inputBound, inputEq]; exact selected)
              (by
                rw [chainExt.locals localsBound, Value.map_map]
                change EvalExprWith calls _ _ (result.map b)
                rw [resultEq]
                exact branchEval)
            have e₄ := excludePairs_complete exclusionRun e₃.layout e₃.valid selectorsBound selection.exclusive
            have e₅ := sum_complete sumRun e₄.layout e₄.valid
              (fun p h => e₄.bound (selectorsBound p h)) (((chainExt.trans e₃).trans e₄).bound enableBound)
              (by rw [((chainExt.trans e₃).trans e₄).polynomial enableBound, active]; exact selection.sum)
            exact ⟨c, ((chainExt.trans e₃).trans e₄).trans e₅,
              resultBound.mono ((e₃.trans e₄).trans e₅).increase,
              by simpa only [Value.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using (e₃.variables resultBound).trans resultEq⟩
  termination_by sizeOf expr

  theorem lowerArgs_complete [Field F] [DecidableEq F]
      {program : Program F} {function : String} {locals : Locals F} {enable : ArithExpr F}
      {args : List (Expr F)} {outputs : List (Symbolic F)} {before after : BuildState F}
      (compiled : lowerArgs program function locals enable args before = .ok (outputs, after))
      {calls : CallRelation F} (typed : CallsTyped program calls) {initial : Var → F}
      (layout : before.WellFormed) (valid : before.Valid calls initial)
      (localsBound : LocalsBounded before.nextVar locals)
      (enableBound : enable.inBounds before.nextVar = true) (active : enable.denote initial = 1)
      {values : List (Value F)} (evaluated : EvalArgsWith calls (localsEnvironment locals initial) args values) :
      ∃ assignment, Extension calls before after initial assignment ∧
        (∀ value ∈ outputs, Bounded after.nextVar value) ∧
        outputs.map (Value.map (ArithExpr.denote assignment)) = values := by
    cases args with
    | nil =>
        cases evaluated
        simp only [lowerArgs, pure_ok] at compiled
        obtain ⟨rfl, rfl⟩ := compiled
        exact ⟨initial, .refl layout valid, by simp, rfl⟩
    | cons arg args =>
        cases evaluated with
        | cons headEval tailEval =>
            simp only [lowerArgs] at compiled
            obtain ⟨head, middle, headRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp rest
            obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
            obtain ⟨a, e₁, headBound, headEq⟩ :=
              lowerExpr_complete headRun typed layout valid localsBound enableBound active headEval
            obtain ⟨b, e₂, tailBound, tailEq⟩ := lowerArgs_complete tailRun typed e₁.layout e₁.valid
              (localsBound.mono e₁.increase) (e₁.bound enableBound) ((e₁.polynomial enableBound).trans active)
              (by rw [e₁.locals localsBound]; exact tailEval)
            refine ⟨b, e₁.trans e₂, ?_, ?_⟩
            · intro value member
              rcases List.mem_cons.mp member with rfl | member
              · exact headBound.mono e₂.increase
              · exact tailBound value member
            · simp only [List.map_cons, e₂.value headBound, headEq, tailEq]
  termination_by sizeOf args

  theorem lowerArms_complete [Field F] [DecidableEq F]
      {program : Program F} {function : String} {locals : Locals F}
      {scrutinee result : Symbolic F} {remaining : ArithExpr F}
      {arms : List (Pattern F × Expr F)} {selectors : List (ArithExpr F)} {before after : BuildState F}
      (compiled : lowerArms program function locals scrutinee result remaining arms before = .ok (selectors, after))
      {calls : CallRelation F} (typed : CallsTyped program calls) {initial : Var → F}
      (layout : before.WellFormed) (valid : before.Valid calls initial)
      (localsBound : LocalsBounded before.nextVar locals)
      (inputBound : Bounded before.nextVar scrutinee) (resultBound : Bounded before.nextVar result)
      (remainingBound : remaining.inBounds before.nextVar = true) (active : remaining.denote initial = 1)
      {matched : Environment F} {body : Expr F}
      (selected : selectArm (scrutinee.map (ArithExpr.denote initial)) arms = some (matched, body))
      (evaluated : EvalExprWith calls (matched ++ localsEnvironment locals initial) body
        (result.map (ArithExpr.denote initial))) :
      ∃ assignment, Extension calls before after initial assignment ∧
        (∀ selector ∈ selectors, selector.inBounds after.nextVar = true) ∧
        Scalar.Circuit.SelectorsValid (1 : F) (selectors.map (ArithExpr.denote assignment)) := by
    cases arms with
    | nil => simp [selectArm] at selected
    | cons arm arms =>
        rcases hArm : arm with ⟨pattern, branch⟩
        simp only [hArm, lowerArms] at compiled
        obtain ⟨⟨test, bindings⟩, s₁, patternRun, rest⟩ := bind_ok.mp compiled
        obtain ⟨selector, s₂, freshRun, rest⟩ := bind_ok.mp rest
        obtain ⟨finished, s₃, booleanRun, rest⟩ := bind_ok.mp rest
        cases finished
        obtain ⟨finished, s₄, equationRun, rest⟩ := bind_ok.mp rest
        cases finished
        obtain ⟨bodyValue, s₅, bodyRun, rest⟩ := bind_ok.mp rest
        obtain ⟨finished, s₆, valueRun, armsRest⟩ := bind_ok.mp rest
        cases finished
        obtain ⟨a, e₁, testBound, bindingsBound⟩ := lowerPattern_complete patternRun layout valid inputBound
        have patternTest := (lowerPattern_sound patternRun e₁.valid).2
        rw [e₁.value inputBound] at patternTest
        have testBool : test.denote a = 0 ∨ test.denote a = 1 := by
          rcases patternTest with ⟨_, one⟩ | ⟨_, zero⟩
          · exact Or.inr one
          · exact Or.inl zero
        obtain ⟨b, e₂, idBound, selEq⟩ := fresh_complete freshRun e₁.layout e₁.valid (test.denote a)
        have selectorBound : (ArithExpr.var selector : ArithExpr F).inBounds s₂.nextVar = true := by
          simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using idBound
        have e₃ := boolean_complete booleanRun e₂.layout e₂.valid selectorBound (by
          change b selector = 0 ∨ b selector = 1; rw [selEq]; exact testBool)
        have chainExt := (e₁.trans e₂).trans e₃
        have e₄ := constrain_complete equationRun e₃.layout e₃.valid
          (by simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using
            And.intro (e₃.bound selectorBound) (And.intro (chainExt.bound remainingBound) ((e₂.trans e₃).bound testBound)))
          (by change b selector - remaining.denote b * test.denote b = 0
              rw [selEq, chainExt.polynomial remainingBound, active, e₂.polynomial testBound]; simp)
        have localsBound' : LocalsBounded s₄.nextVar (bindings ++ locals) :=
          localsBounded_append.mpr ⟨bindingsBound.mono ((e₂.trans e₃).trans e₄).increase,
            localsBound.mono (chainExt.trans e₄).increase⟩
        rcases patternTest with ⟨matchedHead, testOne⟩ | ⟨unmatchedHead, testZero⟩
        · have selectedHead : matched = localsEnvironment bindings a ∧ body = branch := by
            simpa only [hArm, selectArm, matchedHead, Option.some.injEq, Prod.mk.injEq] using selected.symm
          obtain ⟨rfl, rfl⟩ := selectedHead
          have selOne : (ArithExpr.var selector : ArithExpr F).denote b = 1 := selEq.trans testOne
          obtain ⟨c, e₅, bodyBound, bodyEq⟩ := lowerExpr_complete bodyRun typed e₄.layout e₄.valid localsBound'
            ((e₃.trans e₄).bound selectorBound) selOne (by
              rw [localsEnvironment_append, e₂.locals bindingsBound, (chainExt.trans e₄).locals localsBound]
              exact evaluated)
          have headExt := (chainExt.trans e₄).trans e₅
          have selOneC := (((e₃.trans e₄).trans e₅).polynomial selectorBound).trans selOne
          have e₆ := constrainValue_complete valueRun e₅.layout e₅.valid
            (((e₃.trans e₄).trans e₅).bound selectorBound) (resultBound.mono headExt.increase) bodyBound
            (Or.inr ((headExt.value resultBound).trans bodyEq.symm))
          have total := headExt.trans e₆
          have finalBound := (((e₃.trans e₄).trans e₅).trans e₆).bound selectorBound
          split at armsRest
          · obtain ⟨rfl, rfl⟩ := pure_ok.mp armsRest
            refine ⟨c, total, by simpa using finalBound, ?_⟩
            simpa only [List.map_cons, List.map_nil, selOneC, List.nil_append] using
              (Scalar.Circuit.SelectorsValid.single (before := []) (after := []) (by simp) (by simp) :
                Scalar.Circuit.SelectorsValid (1 : F) [1])
          · simp only [pure_bind] at armsRest
            obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp armsRest
            obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
            have testFinal := ((((e₂.trans e₃).trans e₄).trans e₅).trans e₆).bound testBound
            have nextBound : (ArithExpr.mul remaining (.sub (.const 1) test)).inBounds s₆.nextVar = true := by
              simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using
                And.intro (total.bound remainingBound) testFinal
            have nextZero : (ArithExpr.mul remaining (.sub (.const 1) test)).denote c = 0 := by
              change remaining.denote c * (1 - test.denote c) = 0
              rw [((((e₂.trans e₃).trans e₄).trans e₅).trans e₆).polynomial testBound, testOne]
              simp
            obtain ⟨d, tailExt, tailBound, tailZero⟩ := lowerArms_inactive tailRun total.layout total.valid
              (localsBound.mono total.increase) (inputBound.mono total.increase) (resultBound.mono total.increase)
              nextBound nextZero
            refine ⟨d, total.trans tailExt, ?_, ?_⟩
            · intro p member
              rcases List.mem_cons.mp member with rfl | member
              · exact tailExt.bound finalBound
              · exact tailBound p member
            · have one := (tailExt.polynomial finalBound).trans selOneC
              simp only [List.map_cons, one]
              exact Scalar.Circuit.SelectorsValid.single (before := []) (by simp)
                (by simpa only [List.forall_mem_map] using tailZero)
        · have selectedTail : selectArm (scrutinee.map (ArithExpr.denote initial)) arms = some (matched, body) := by
            simpa only [hArm, selectArm, unmatchedHead] using selected
          have selZero : (ArithExpr.var selector : ArithExpr F).denote b = 0 := selEq.trans testZero
          obtain ⟨c, e₅, bodyBound⟩ := lowerExpr_inactive bodyRun e₄.layout e₄.valid localsBound'
            ((e₃.trans e₄).bound selectorBound) selZero
          have headExt := (chainExt.trans e₄).trans e₅
          have selZeroC := (((e₃.trans e₄).trans e₅).polynomial selectorBound).trans selZero
          have e₆ := constrainValue_complete valueRun e₅.layout e₅.valid
            (((e₃.trans e₄).trans e₅).bound selectorBound) (resultBound.mono headExt.increase) bodyBound (Or.inl selZeroC)
          have total := headExt.trans e₆
          have finalBound := (((e₃.trans e₄).trans e₅).trans e₆).bound selectorBound
          split at armsRest
          · rename_i irrefutable
            have one := lowerPattern_irrefutable patternRun irrefutable a
            exact (zero_ne_one (testZero.symm.trans one)).elim
          · simp only [pure_bind] at armsRest
            obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp armsRest
            obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
            have testFinal := ((((e₂.trans e₃).trans e₄).trans e₅).trans e₆).bound testBound
            have nextBound : (ArithExpr.mul remaining (.sub (.const 1) test)).inBounds s₆.nextVar = true := by
              simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using
                And.intro (total.bound remainingBound) testFinal
            have nextOne : (ArithExpr.mul remaining (.sub (.const 1) test)).denote c = 1 := by
              change remaining.denote c * (1 - test.denote c) = 1
              rw [total.polynomial remainingBound, active,
                ((((e₂.trans e₃).trans e₄).trans e₅).trans e₆).polynomial testBound, testZero]
              simp
            obtain ⟨d, tailExt, tailBound, selection⟩ := lowerArms_complete tailRun typed total.layout total.valid
              (localsBound.mono total.increase) (inputBound.mono total.increase) (resultBound.mono total.increase)
              nextBound nextOne (by rw [total.value inputBound]; exact selectedTail)
              (by rw [total.locals localsBound, total.value resultBound]; exact evaluated)
            refine ⟨d, total.trans tailExt, ?_, ?_⟩
            · intro p member
              rcases List.mem_cons.mp member with rfl | member
              · exact tailExt.bound finalBound
              · exact tailBound p member
            · have zero := (tailExt.polynomial finalBound).trans selZeroC
              simpa only [List.map_cons, zero] using selection.zero_cons
  termination_by sizeOf arms
  decreasing_by
    all_goals simp only [*, Prod.mk.sizeOf_spec, List.cons.sizeOf_spec]
    all_goals omega
end

end Aiur.Tuple.Circuit.Compiler
